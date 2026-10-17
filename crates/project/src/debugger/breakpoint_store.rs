//! Module for managing breakpoints in a project.
//!
//! Breakpoints are separate from a session because they're not associated with any particular debug session. They can also be set up without a session running.
use anyhow::{Context as _, Result, anyhow};
pub use breakpoints_in_file::{BreakpointSessionState, BreakpointWithPosition};
use breakpoints_in_file::{BreakpointsInFile, StatefulBreakpoint};
use collections::{BTreeMap, HashMap, HashSet, VecDeque};
use dap::{StackFrameId, client::SessionId};
use futures::{
    StreamExt as _,
    channel::{mpsc, oneshot},
};
use gpui::{
    App, AppContext, AsyncApp, Context, Entity, EntityId, EventEmitter, Subscription, Task,
};
use itertools::Itertools;
use language::{Buffer, BufferSnapshot, proto::serialize_anchor as serialize_text_anchor};
use rpc::{
    AnyProtoClient, TypedEnvelope,
    proto::{self},
};
use std::{cell::Cell, hash::Hash, ops::Range, path::Path, sync::Arc};
use text::{Bias, Point, PointUtf16, Unclipped};
use util::{ResultExt as _, maybe};

use crate::{
    ProjectPath,
    buffer_store::{BufferStore, BufferStoreEvent},
    worktree_store::WorktreeStore,
};

use super::session::ThreadId;

mod breakpoints_in_file {
    use collections::{HashMap, HashSet};
    use language::BufferEvent;

    use super::*;

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct BreakpointWithPosition {
        pub position: text::Anchor,
        pub bp: Breakpoint,
    }

    /// A breakpoint with per-session data about it's state (as seen by the Debug Adapter).
    #[derive(Clone, Debug)]
    pub struct StatefulBreakpoint {
        pub bp: BreakpointWithPosition,
        pub session_state: HashMap<SessionId, BreakpointSessionState>,
    }

    impl StatefulBreakpoint {
        pub(super) fn new(bp: BreakpointWithPosition) -> Self {
            Self {
                bp,
                session_state: Default::default(),
            }
        }
        pub(super) fn position(&self) -> &text::Anchor {
            &self.bp.position
        }
    }

    #[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
    pub struct BreakpointSessionState {
        /// Session-specific identifier for the breakpoint, as assigned by Debug Adapter.
        pub id: u64,
        pub verified: bool,
    }
    #[derive(Clone)]
    pub(super) struct BreakpointsInFile {
        pub(super) buffer: Entity<Buffer>,
        // TODO: This is.. less than ideal, as it's O(n) and does not return entries in order. We'll have to change TreeMap to support passing in the context for comparisons
        pub(super) breakpoints: Vec<StatefulBreakpoint>,
        _subscription: Arc<Subscription>,
    }

    impl BreakpointsInFile {
        pub(super) fn new(buffer: Entity<Buffer>, cx: &mut Context<BreakpointStore>) -> Self {
            let subscription = Arc::from(cx.subscribe(
                &buffer,
                |breakpoint_store, buffer, event, cx| match event {
                    BufferEvent::Saved => {
                        if let Some(abs_path) = BreakpointStore::abs_path_from_buffer(&buffer, cx) {
                            cx.emit(BreakpointStoreEvent::BreakpointsUpdated(
                                abs_path,
                                BreakpointUpdatedReason::FileSaved,
                            ));
                        }
                    }
                    BufferEvent::FileHandleChanged => {
                        let entity_id = buffer.entity_id();

                        if buffer
                            .read(cx)
                            .file()
                            .is_none_or(|f| f.disk_state().is_deleted())
                        {
                            breakpoint_store.remove_breakpoints_of_buffer(entity_id, cx);
                            return;
                        }

                        if let Some(abs_path) = BreakpointStore::abs_path_from_buffer(&buffer, cx) {
                            if breakpoint_store.breakpoints.contains_key(&abs_path) {
                                return;
                            }

                            if let Some(old_path) = breakpoint_store
                                .breakpoints
                                .iter()
                                .find(|(_, in_file)| in_file.buffer.entity_id() == entity_id)
                                .map(|values| values.0)
                                .cloned()
                            {
                                breakpoint_store.on_file_rename(old_path, abs_path, cx);
                            }
                        }
                    }
                    _ => {}
                },
            ));

            BreakpointsInFile {
                buffer,
                breakpoints: Vec::new(),
                _subscription: subscription,
            }
        }

        pub(super) fn merge_restored(
            &mut self,
            restored: BreakpointsInFile,
            cx: &App,
        ) -> Vec<text::Anchor> {
            let source = restored.buffer.read(cx).snapshot();
            let destination = self.buffer.read(cx).snapshot();
            let same_buffer = restored.buffer == self.buffer;
            let max_row = destination.max_point_utf16().row;
            let mut added = Vec::new();
            let mut occupied_rows = self
                .breakpoints
                .iter()
                .map(|breakpoint| {
                    destination
                        .summary_for_anchor::<PointUtf16>(breakpoint.position())
                        .row
                })
                .collect::<HashSet<_>>();
            for mut breakpoint in restored.breakpoints {
                let row = source
                    .summary_for_anchor::<PointUtf16>(breakpoint.position())
                    .row;
                if row > max_row || !occupied_rows.insert(row) {
                    continue;
                }
                if !same_buffer {
                    breakpoint.bp.position = destination.anchor_after(PointUtf16::new(row, 0));
                }
                added.push(*breakpoint.position());
                self.breakpoints.push(breakpoint);
            }
            added
        }
    }
}

#[derive(Clone)]
struct RemoteBreakpointStore {
    upstream_client: AnyProtoClient,
    upstream_project_id: u64,
}

#[derive(Clone)]
enum BreakpointStoreMode {
    Local,
    Remote(RemoteBreakpointStore),
}

#[derive(Clone, PartialEq)]
pub struct ActiveStackFrame {
    pub session_id: SessionId,
    pub thread_id: ThreadId,
    pub stack_frame_id: StackFrameId,
    pub path: Arc<Path>,
    pub position: text::Anchor,
}

pub struct BreakpointStore {
    buffer_store: Entity<BufferStore>,
    worktree_store: Entity<WorktreeStore>,
    breakpoints: BTreeMap<Arc<Path>, BreakpointsInFile>,
    pending_restored: BTreeMap<Arc<Path>, Vec<SourceBreakpoint>>,
    restoring_paths: collections::HashSet<Arc<Path>>,
    pending_restored_buffers: Option<Subscription>,
    downstream_client: Option<(AnyProtoClient, u64)>,
    active_stack_frame: Option<ActiveStackFrame>,
    active_debug_line_pane_id: Option<EntityId>,
    remote_snapshots_in_flight: HashMap<Arc<Path>, u64>,
    remote_snapshots_received: u64,
    remote_snapshot_versions: HashMap<Arc<Path>, u64>,
    downstream_version: Cell<u64>,
    collaborators: HashSet<proto::PeerId>,
    remote_edits: HashMap<RemoteEditSender, VecDeque<RemoteBreakpointEdit>>,
    remote_edit_buffers: HashMap<EntityId, Subscription>,
    upstream_requests: Option<(mpsc::UnboundedSender<proto::ToggleBreakpoint>, Task<()>)>,
    // E.g ssh
    mode: BreakpointStoreMode,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum RemoteEditSender {
    Collaborator(proto::PeerId),
    Direct(proto::PeerId),
}

struct RemoteBreakpointEdit {
    buffer: Entity<Buffer>,
    breakpoint: BreakpointWithPosition,
    edit: proto::BreakpointEdit,
    applied: oneshot::Sender<Result<()>>,
}

impl BreakpointStore {
    pub fn init(client: &AnyProtoClient) {
        client.add_entity_request_handler(Self::handle_toggle_breakpoint);
        client.add_entity_message_handler(Self::handle_breakpoints_for_file);
    }
    pub fn local(worktree_store: Entity<WorktreeStore>, buffer_store: Entity<BufferStore>) -> Self {
        BreakpointStore {
            breakpoints: BTreeMap::new(),
            pending_restored: BTreeMap::new(),
            restoring_paths: collections::HashSet::default(),
            pending_restored_buffers: None,
            mode: BreakpointStoreMode::Local,
            buffer_store,
            worktree_store,
            downstream_client: None,
            active_stack_frame: Default::default(),
            active_debug_line_pane_id: None,
            remote_snapshots_in_flight: HashMap::default(),
            remote_snapshots_received: 0,
            remote_snapshot_versions: HashMap::default(),
            downstream_version: Cell::new(0),
            collaborators: HashSet::default(),
            remote_edits: HashMap::default(),
            remote_edit_buffers: HashMap::default(),
            upstream_requests: None,
        }
    }

    pub(crate) fn remote(
        upstream_project_id: u64,
        upstream_client: AnyProtoClient,
        buffer_store: Entity<BufferStore>,
        worktree_store: Entity<WorktreeStore>,
    ) -> Self {
        BreakpointStore {
            breakpoints: BTreeMap::new(),
            pending_restored: BTreeMap::new(),
            restoring_paths: collections::HashSet::default(),
            pending_restored_buffers: None,
            mode: BreakpointStoreMode::Remote(RemoteBreakpointStore {
                upstream_client,
                upstream_project_id,
            }),
            buffer_store,
            worktree_store,
            downstream_client: None,
            active_stack_frame: Default::default(),
            active_debug_line_pane_id: None,
            remote_snapshots_in_flight: HashMap::default(),
            remote_snapshots_received: 0,
            remote_snapshot_versions: HashMap::default(),
            downstream_version: Cell::new(0),
            collaborators: HashSet::default(),
            remote_edits: HashMap::default(),
            remote_edit_buffers: HashMap::default(),
            upstream_requests: None,
        }
    }

    pub fn shared(&mut self, project_id: u64, downstream_client: AnyProtoClient) {
        self.downstream_client = Some((downstream_client, project_id));
    }

    pub(crate) fn unshared(&mut self, cx: &mut Context<Self>) {
        self.downstream_client.take();
        self.collaborators.clear();
        self.remote_edits.clear();
        self.remote_edit_buffers.clear();

        cx.notify();
    }

    pub(crate) fn set_collaborators(
        &mut self,
        collaborators: impl IntoIterator<Item = proto::PeerId>,
    ) {
        self.collaborators = collaborators.into_iter().collect();
        let collaborators = &self.collaborators;
        self.remote_edits.retain(|sender, _| match sender {
            RemoteEditSender::Collaborator(peer_id) => collaborators.contains(peer_id),
            RemoteEditSender::Direct(_) => true,
        });
        self.retain_remote_edit_buffers();
    }

    pub(crate) fn collaborator_added(&mut self, peer_id: proto::PeerId) {
        self.collaborators.insert(peer_id);
    }

    pub(crate) fn collaborator_removed(&mut self, peer_id: proto::PeerId) {
        self.collaborators.remove(&peer_id);
        self.remote_edits
            .remove(&RemoteEditSender::Collaborator(peer_id));
        self.retain_remote_edit_buffers();
    }

    pub(crate) fn collaborator_renamed(
        &mut self,
        old_peer_id: proto::PeerId,
        new_peer_id: proto::PeerId,
    ) {
        if self.collaborators.remove(&old_peer_id) {
            self.collaborators.insert(new_peer_id);
        }
        if let Some(edits) = self
            .remote_edits
            .remove(&RemoteEditSender::Collaborator(old_peer_id))
        {
            self.remote_edits
                .insert(RemoteEditSender::Collaborator(new_peer_id), edits);
        }
    }

    async fn handle_breakpoints_for_file(
        this: Entity<Self>,
        message: TypedEnvelope<proto::BreakpointsForFile>,
        mut cx: AsyncApp,
    ) -> Result<()> {
        let path = Arc::<Path>::from(Path::new(&message.payload.path));
        let version = message.payload.version;
        let snapshot = this.update(&mut cx, |this, _| {
            if version != 0 {
                if this
                    .remote_snapshot_versions
                    .get(&path)
                    .is_some_and(|latest_version| *latest_version >= version)
                {
                    return None;
                }
                this.remote_snapshot_versions.insert(path.clone(), version);
            }
            this.remote_snapshots_received += 1;
            this.remote_snapshots_in_flight
                .insert(path.clone(), this.remote_snapshots_received);
            Some(this.remote_snapshots_received)
        });
        let Some(snapshot) = snapshot else {
            return Ok(());
        };
        if message.payload.breakpoints.is_empty() {
            this.update(&mut cx, |this, cx| {
                this.finish_remote_snapshot(&path, snapshot);
                if this.breakpoints.remove(&path).is_some() {
                    this.send_breakpoints_downstream(&path);
                    cx.notify();
                }
            });
            return Ok(());
        }

        let breakpoints = message
            .payload
            .breakpoints
            .into_iter()
            .filter_map(|breakpoint| {
                let position = language::proto::deserialize_anchor(breakpoint.position?)?;
                let session_state = breakpoint
                    .session_state
                    .iter()
                    .map(|(session_id, state)| {
                        let state = BreakpointSessionState {
                            id: state.id,
                            verified: state.verified,
                        };
                        (SessionId::from_proto(*session_id), state)
                    })
                    .collect();
                let breakpoint = Breakpoint::from_proto(breakpoint)?;
                let bp = BreakpointWithPosition {
                    position,
                    bp: breakpoint,
                };

                Some(StatefulBreakpoint { bp, session_state })
            })
            .collect::<Vec<_>>();

        let open_buffer = this.update(&mut cx, |this, cx| {
            let Some(project_path) = this
                .worktree_store
                .read(cx)
                .project_path_for_absolute_path(message.payload.path.as_ref(), cx)
            else {
                this.finish_remote_snapshot(&path, snapshot);
                return None;
            };
            Some(this.buffer_store.update(cx, |buffer_store, cx| {
                buffer_store.open_buffer(project_path, cx)
            }))
        });
        let open_buffer = open_buffer.context("Invalid project path")?;
        let buffer = async {
            let buffer = open_buffer.await?;
            Self::wait_for_remote_anchors(
                &buffer,
                breakpoints.iter().map(|breakpoint| *breakpoint.position()),
                &mut cx,
            )
            .await?;
            anyhow::Ok(buffer)
        }
        .await;

        this.update(&mut cx, move |this, cx| {
            if !this.finish_remote_snapshot(&path, snapshot) {
                return anyhow::Ok(());
            }
            let buffer = buffer?;
            let buffer_snapshot = buffer.read(cx).snapshot();
            let breakpoints = breakpoints
                .into_iter()
                .filter(|breakpoint| buffer_snapshot.can_resolve(breakpoint.position()))
                .collect::<Vec<_>>();
            let file_breakpoints = this
                .breakpoints
                .remove(&path)
                .filter(|file_breakpoints| file_breakpoints.buffer == buffer);
            if !breakpoints.is_empty() {
                let mut file_breakpoints =
                    file_breakpoints.unwrap_or_else(|| BreakpointsInFile::new(buffer, cx));
                file_breakpoints.breakpoints = breakpoints;
                this.breakpoints.insert(path.clone(), file_breakpoints);
            }
            this.send_breakpoints_downstream(&path);
            cx.notify();
            anyhow::Ok(())
        })
    }

    async fn wait_for_remote_anchors(
        buffer: &Entity<Buffer>,
        anchors: impl IntoIterator<Item = text::Anchor>,
        cx: &mut AsyncApp,
    ) -> Result<()> {
        buffer
            .update(cx, |buffer, _| {
                let buffer_id = buffer.remote_id();
                let anchors = anchors
                    .into_iter()
                    .filter(|anchor| anchor.buffer_id == buffer_id)
                    .collect::<Vec<_>>();
                buffer.wait_for_anchors(anchors)
            })
            .await
    }

    fn enqueue_remote_edit(
        &mut self,
        sender: RemoteEditSender,
        edit: RemoteBreakpointEdit,
        cx: &mut Context<Self>,
    ) -> Result<()> {
        if let RemoteEditSender::Collaborator(peer_id) = sender {
            anyhow::ensure!(
                self.collaborators.contains(&peer_id),
                "Peer {peer_id} is not a collaborator of this project"
            );
        }
        self.remote_edit_buffers
            .entry(edit.buffer.entity_id())
            .or_insert_with(|| {
                cx.observe(&edit.buffer, |breakpoint_store, _, cx| {
                    breakpoint_store.apply_remote_edits(cx)
                })
            });
        self.remote_edits.entry(sender).or_default().push_back(edit);
        self.apply_remote_edits(cx);
        Ok(())
    }

    fn apply_remote_edits(&mut self, cx: &mut Context<Self>) {
        let senders = self.remote_edits.keys().copied().collect::<Vec<_>>();
        for sender in senders {
            while let Some((edit, readiness)) = self.pop_ready_remote_edit(sender, cx) {
                let RemoteBreakpointEdit {
                    buffer,
                    breakpoint,
                    edit,
                    applied,
                } = edit;
                let result = readiness.map(|()| match edit {
                    proto::BreakpointEdit::Toggle => {
                        self.toggle_breakpoint(buffer, breakpoint, BreakpointEditAction::Toggle, cx)
                    }
                    proto::BreakpointEdit::Set => {
                        self.apply_upstream_edit(buffer, breakpoint, true, cx)
                    }
                    proto::BreakpointEdit::Remove => {
                        self.apply_upstream_edit(buffer, breakpoint, false, cx)
                    }
                    proto::BreakpointEdit::Superseded => {}
                });
                applied.send(result).ok();
            }
        }
        self.retain_remote_edit_buffers();
    }

    fn retain_remote_edit_buffers(&mut self) {
        let remote_edits = &self.remote_edits;
        self.remote_edit_buffers.retain(|buffer_id, _| {
            remote_edits
                .values()
                .flatten()
                .any(|edit| edit.buffer.entity_id() == *buffer_id)
        });
    }

    fn pop_ready_remote_edit(
        &mut self,
        sender: RemoteEditSender,
        cx: &App,
    ) -> Option<(RemoteBreakpointEdit, Result<()>)> {
        let edits = self.remote_edits.get_mut(&sender)?;
        let readiness = match edits.front() {
            Some(edit) => {
                let buffer = edit.buffer.read(cx);
                let position = edit.breakpoint.position;
                if position.buffer_id != buffer.remote_id() {
                    Err(anyhow!(
                        "Breakpoint position {position:?} belongs to another buffer"
                    ))
                } else if buffer.can_resolve(&position) {
                    Ok(())
                } else if position.timestamp().replica_id == buffer.replica_id() {
                    Err(anyhow!(
                        "Breakpoint position {position:?} refers to an edit this replica never made"
                    ))
                } else {
                    return None;
                }
            }
            None => {
                self.remote_edits.remove(&sender);
                return None;
            }
        };
        let edit = edits.pop_front()?;
        if edits.is_empty() {
            self.remote_edits.remove(&sender);
        }
        Some((edit, readiness))
    }

    fn finish_remote_snapshot(&mut self, path: &Arc<Path>, snapshot: u64) -> bool {
        let latest = self.remote_snapshots_in_flight.get(path) == Some(&snapshot);
        if latest {
            self.remote_snapshots_in_flight.remove(path);
        }
        latest
    }

    async fn handle_toggle_breakpoint(
        this: Entity<Self>,
        message: TypedEnvelope<proto::ToggleBreakpoint>,
        mut cx: AsyncApp,
    ) -> Result<proto::Ack> {
        let sender = match message.original_sender_id {
            Some(peer_id) => RemoteEditSender::Collaborator(peer_id),
            None => RemoteEditSender::Direct(message.sender_id),
        };
        let path = this
            .update(&mut cx, |this, cx| {
                this.worktree_store
                    .read(cx)
                    .project_path_for_absolute_path(message.payload.path.as_ref(), cx)
            })
            .context("Could not resolve provided abs path")?;
        let buffer = this
            .update(&mut cx, |this, cx| {
                this.buffer_store.read(cx).get_by_path(&path)
            })
            .context("Could not find buffer for a given path")?;
        let edit = message.payload.edit();
        let breakpoint = message
            .payload
            .breakpoint
            .context("Breakpoint not present in RPC payload")?;
        let position = language::proto::deserialize_anchor(
            breakpoint
                .position
                .context("Anchor not present in RPC payload")?,
        )
        .context("Anchor deserialization failed")?;
        let breakpoint =
            Breakpoint::from_proto(breakpoint).context("Could not deserialize breakpoint")?;
        let breakpoint = BreakpointWithPosition {
            position,
            bp: breakpoint,
        };

        let (applied, edit_applied) = oneshot::channel();
        this.update(&mut cx, |this, cx| {
            this.enqueue_remote_edit(
                sender,
                RemoteBreakpointEdit {
                    buffer,
                    breakpoint,
                    edit,
                    applied,
                },
                cx,
            )
        })?;
        edit_applied
            .await
            .context("Breakpoint edit was cancelled")??;
        Ok(proto::Ack {})
    }

    pub(crate) fn broadcast(&self) {
        for path in self.breakpoints.keys() {
            self.send_breakpoints_downstream(path);
        }
    }

    pub(crate) fn update_session_breakpoint(
        &mut self,
        session_id: SessionId,
        _: dap::BreakpointEventReason,
        breakpoint: dap::Breakpoint,
    ) {
        maybe!({
            let event_id = breakpoint.id?;

            let state = self
                .breakpoints
                .values_mut()
                .find_map(|breakpoints_in_file| {
                    breakpoints_in_file
                        .breakpoints
                        .iter_mut()
                        .find_map(|state| {
                            let state = state.session_state.get_mut(&session_id)?;

                            if state.id == event_id {
                                Some(state)
                            } else {
                                None
                            }
                        })
                })?;

            state.verified = breakpoint.verified;
            Some(())
        });
    }

    pub(super) fn mark_breakpoints_verified(
        &mut self,
        session_id: SessionId,
        abs_path: &Path,

        it: impl Iterator<Item = (BreakpointWithPosition, BreakpointSessionState)>,
    ) {
        maybe!({
            let breakpoints = self.breakpoints.get_mut(abs_path)?;
            for (breakpoint, state) in it {
                if let Some(to_update) = breakpoints
                    .breakpoints
                    .iter_mut()
                    .find(|bp| *bp.position() == breakpoint.position)
                {
                    to_update
                        .session_state
                        .entry(session_id)
                        .insert_entry(state);
                }
            }
            Some(())
        });
    }

    pub fn abs_path_from_buffer(buffer: &Entity<Buffer>, cx: &App) -> Option<Arc<Path>> {
        worktree::File::from_dyn(buffer.read(cx).file())
            .map(|file| file.worktree.read(cx).absolutize(&file.path))
            .map(Arc::<Path>::from)
    }

    pub fn toggle_breakpoint(
        &mut self,
        buffer: Entity<Buffer>,
        mut breakpoint: BreakpointWithPosition,
        edit_action: BreakpointEditAction,
        cx: &mut Context<Self>,
    ) {
        let Some(abs_path) = Self::abs_path_from_buffer(&buffer, cx) else {
            return;
        };
        let row = buffer
            .read(cx)
            .summary_for_anchor::<PointUtf16>(&breakpoint.position)
            .row;
        self.forget_pending_restored(&abs_path, row);

        let breakpoint_set = self.file_breakpoints_for_buffer(&abs_path, buffer, cx);
        let previous_breakpoints = breakpoint_positions(&breakpoint_set.breakpoints);

        match edit_action {
            BreakpointEditAction::Toggle => {
                let len_before = breakpoint_set.breakpoints.len();
                breakpoint_set
                    .breakpoints
                    .retain(|value| breakpoint != value.bp);
                if len_before == breakpoint_set.breakpoints.len() {
                    // We did not remove any breakpoint, hence let's toggle one.
                    breakpoint_set
                        .breakpoints
                        .push(StatefulBreakpoint::new(breakpoint.clone()));
                }
            }
            BreakpointEditAction::InvertState => {
                if let Some(bp) = breakpoint_set
                    .breakpoints
                    .iter_mut()
                    .find(|value| breakpoint == value.bp)
                {
                    let bp = &mut bp.bp.bp;
                    if bp.is_enabled() {
                        bp.state = BreakpointState::Disabled;
                    } else {
                        bp.state = BreakpointState::Enabled;
                    }
                } else {
                    breakpoint.bp.state = BreakpointState::Disabled;
                    breakpoint_set
                        .breakpoints
                        .push(StatefulBreakpoint::new(breakpoint.clone()));
                }
            }
            BreakpointEditAction::EditLogMessage(log_message) => {
                if !log_message.is_empty() {
                    let found_bp = breakpoint_set.breakpoints.iter_mut().find_map(|bp| {
                        if breakpoint.position == *bp.position() {
                            Some(&mut bp.bp.bp)
                        } else {
                            None
                        }
                    });

                    if let Some(found_bp) = found_bp {
                        found_bp.message = Some(log_message);
                    } else {
                        breakpoint.bp.message = Some(log_message);
                        // We did not remove any breakpoint, hence let's toggle one.
                        breakpoint_set
                            .breakpoints
                            .push(StatefulBreakpoint::new(breakpoint.clone()));
                    }
                } else if breakpoint.bp.message.is_some() {
                    if let Some(position) = breakpoint_set
                        .breakpoints
                        .iter()
                        .find_position(|other| breakpoint == other.bp)
                        .map(|res| res.0)
                    {
                        breakpoint_set.breakpoints.remove(position);
                    } else {
                        log::error!("Failed to find position of breakpoint to delete")
                    }
                }
            }
            BreakpointEditAction::EditHitCondition(hit_condition) => {
                if !hit_condition.is_empty() {
                    let found_bp = breakpoint_set.breakpoints.iter_mut().find_map(|other| {
                        if breakpoint.position == *other.position() {
                            Some(&mut other.bp.bp)
                        } else {
                            None
                        }
                    });

                    if let Some(found_bp) = found_bp {
                        found_bp.hit_condition = Some(hit_condition);
                    } else {
                        breakpoint.bp.hit_condition = Some(hit_condition);
                        // We did not remove any breakpoint, hence let's toggle one.
                        breakpoint_set
                            .breakpoints
                            .push(StatefulBreakpoint::new(breakpoint.clone()))
                    }
                } else if breakpoint.bp.hit_condition.is_some() {
                    if let Some(position) = breakpoint_set
                        .breakpoints
                        .iter()
                        .find_position(|bp| breakpoint == bp.bp)
                        .map(|res| res.0)
                    {
                        breakpoint_set.breakpoints.remove(position);
                    } else {
                        log::error!("Failed to find position of breakpoint to delete")
                    }
                }
            }
            BreakpointEditAction::EditCondition(condition) => {
                if !condition.is_empty() {
                    let found_bp = breakpoint_set.breakpoints.iter_mut().find_map(|other| {
                        if breakpoint.position == *other.position() {
                            Some(&mut other.bp.bp)
                        } else {
                            None
                        }
                    });

                    if let Some(found_bp) = found_bp {
                        found_bp.condition = Some(condition);
                    } else {
                        breakpoint.bp.condition = Some(condition);
                        // We did not remove any breakpoint, hence let's toggle one.
                        breakpoint_set
                            .breakpoints
                            .push(StatefulBreakpoint::new(breakpoint.clone()));
                    }
                } else if breakpoint.bp.condition.is_some() {
                    if let Some(position) = breakpoint_set
                        .breakpoints
                        .iter()
                        .find_position(|bp| breakpoint == bp.bp)
                        .map(|res| res.0)
                    {
                        breakpoint_set.breakpoints.remove(position);
                    } else {
                        log::error!("Failed to find position of breakpoint to delete")
                    }
                }
            }
        }

        if breakpoint_set.breakpoints.is_empty() {
            self.breakpoints.remove(&abs_path);
        }
        self.sync_file_breakpoints(&abs_path, &previous_breakpoints, cx);

        cx.emit(BreakpointStoreEvent::BreakpointsUpdated(
            abs_path,
            BreakpointUpdatedReason::Toggled,
        ));
        cx.notify();
    }

    fn file_breakpoints_for_buffer(
        &mut self,
        abs_path: &Arc<Path>,
        buffer: Entity<Buffer>,
        cx: &mut Context<Self>,
    ) -> &mut BreakpointsInFile {
        let breakpoint_set = self
            .breakpoints
            .entry(abs_path.clone())
            .or_insert_with(|| BreakpointsInFile::new(buffer.clone(), cx));

        // Buffers changed for the file, migrate breakpoints to the new buffer
        if breakpoint_set.buffer != buffer {
            let old_snapshot = breakpoint_set.buffer.read(cx).snapshot();
            let new_snapshot = buffer.read(cx).snapshot();
            let breakpoints = breakpoint_set
                .breakpoints
                .drain(..)
                .map(|mut breakpoint| {
                    let old_position =
                        old_snapshot.summary_for_anchor::<PointUtf16>(breakpoint.position());
                    let new_position = PointUtf16::new(old_position.row, 0);
                    let new_position =
                        new_snapshot.clip_point_utf16(Unclipped(new_position), Bias::Left);
                    breakpoint.bp.position = new_snapshot.anchor_after(new_position);
                    breakpoint
                })
                .collect();
            *breakpoint_set = BreakpointsInFile::new(buffer, cx);
            breakpoint_set.breakpoints = breakpoints;
        }
        breakpoint_set
    }

    fn apply_upstream_edit(
        &mut self,
        buffer: Entity<Buffer>,
        breakpoint: BreakpointWithPosition,
        keep: bool,
        cx: &mut Context<Self>,
    ) {
        let Some(abs_path) = Self::abs_path_from_buffer(&buffer, cx) else {
            return;
        };
        let row = buffer
            .read(cx)
            .summary_for_anchor::<PointUtf16>(&breakpoint.position)
            .row;
        self.forget_pending_restored(&abs_path, row);

        let breakpoint_set = self.file_breakpoints_for_buffer(&abs_path, buffer, cx);
        let previous_breakpoints = breakpoint_positions(&breakpoint_set.breakpoints);
        let existing = breakpoint_set
            .breakpoints
            .iter()
            .position(|existing| existing.bp == breakpoint)
            .or_else(|| {
                breakpoint_set
                    .breakpoints
                    .iter()
                    .position(|existing| *existing.position() == breakpoint.position)
            });
        match (existing, keep) {
            (Some(index), true) => {
                if let Some(existing) = breakpoint_set.breakpoints.get_mut(index) {
                    existing.bp = breakpoint;
                }
            }
            (None, true) => breakpoint_set
                .breakpoints
                .push(StatefulBreakpoint::new(breakpoint)),
            (Some(index), false) => {
                breakpoint_set.breakpoints.remove(index);
            }
            (None, false) => {}
        }
        let changed = breakpoint_set
            .breakpoints
            .iter()
            .map(|breakpoint| &breakpoint.bp)
            .ne(previous_breakpoints.iter());
        if breakpoint_set.breakpoints.is_empty() {
            self.breakpoints.remove(&abs_path);
        }
        self.sync_file_breakpoints(&abs_path, &previous_breakpoints, cx);
        if !changed {
            return;
        }
        cx.emit(BreakpointStoreEvent::BreakpointsUpdated(
            abs_path,
            BreakpointUpdatedReason::Toggled,
        ));
        cx.notify();
    }

    fn sync_file_breakpoints(
        &mut self,
        abs_path: &Arc<Path>,
        previous_breakpoints: &[BreakpointWithPosition],
        cx: &mut Context<Self>,
    ) {
        if let BreakpointStoreMode::Remote(remote) = &self.mode {
            let upstream_client = remote.upstream_client.clone();
            let current_breakpoints = self
                .breakpoints
                .get(abs_path)
                .map(|file_breakpoints| file_breakpoints.breakpoints.as_slice())
                .unwrap_or_default();
            let upstream_requests = changed_breakpoints(previous_breakpoints, current_breakpoints)
                .into_iter()
                .flat_map(|(previous, resulting)| upstream_edits(previous, resulting))
                .filter_map(|(breakpoint, edit)| {
                    Self::upstream_request(remote, abs_path, breakpoint, edit)
                })
                .collect::<Vec<_>>();
            for upstream_request in upstream_requests {
                self.send_upstream(upstream_client.clone(), upstream_request, cx);
            }
        }
        self.send_breakpoints_downstream(abs_path);
    }

    fn upstream_request(
        remote: &RemoteBreakpointStore,
        abs_path: &Path,
        breakpoint: &BreakpointWithPosition,
        edit: proto::BreakpointEdit,
    ) -> Option<proto::ToggleBreakpoint> {
        let breakpoint =
            breakpoint
                .bp
                .to_proto(abs_path, &breakpoint.position, &HashMap::default())?;
        Some(proto::ToggleBreakpoint {
            project_id: remote.upstream_project_id,
            path: abs_path.to_string_lossy().into_owned(),
            breakpoint: Some(breakpoint),
            edit: i32::from(edit),
        })
    }

    fn send_upstream(
        &mut self,
        upstream_client: AnyProtoClient,
        request: proto::ToggleBreakpoint,
        cx: &mut Context<Self>,
    ) {
        let (upstream_requests, _) = self.upstream_requests.get_or_insert_with(|| {
            let (upstream_requests, mut queued_requests) = mpsc::unbounded();
            let task = cx.background_spawn(async move {
                while let Some(request) = queued_requests.next().await {
                    upstream_client.request(request).await.log_err();
                }
            });
            (upstream_requests, task)
        });
        upstream_requests.unbounded_send(request).log_err();
    }

    fn remove_breakpoints_of_buffer(&mut self, buffer_id: EntityId, cx: &mut Context<Self>) {
        let removed = self
            .breakpoints
            .iter()
            .filter(|(_, breakpoints_in_file)| breakpoints_in_file.buffer.entity_id() == buffer_id)
            .map(|(path, _)| path.clone())
            .collect::<Vec<_>>();
        if removed.is_empty() {
            return;
        }
        for path in &removed {
            self.breakpoints.remove(path);
            self.send_breakpoints_downstream(path);
        }
        cx.emit(BreakpointStoreEvent::BreakpointsCleared(removed));
        cx.notify();
    }

    fn send_breakpoints_downstream(&self, abs_path: &Arc<Path>) {
        let Some((client, project_id)) = &self.downstream_client else {
            return;
        };
        let breakpoints = self
            .breakpoints
            .get(abs_path)
            .map(|breakpoint_set| {
                breakpoint_set
                    .breakpoints
                    .iter()
                    .filter_map(|bp| {
                        bp.bp
                            .bp
                            .to_proto(abs_path, bp.position(), &bp.session_state)
                    })
                    .collect()
            })
            .unwrap_or_default();

        let version = self.downstream_version.get() + 1;
        self.downstream_version.set(version);
        client
            .send(proto::BreakpointsForFile {
                project_id: *project_id,
                path: abs_path.to_string_lossy().into_owned(),
                breakpoints,
                version,
            })
            .log_err();
    }

    pub fn on_file_rename(
        &mut self,
        old_path: Arc<Path>,
        new_path: Arc<Path>,
        cx: &mut Context<Self>,
    ) {
        if old_path == new_path {
            return;
        }
        let Some(breakpoints) = self.breakpoints.remove(&old_path) else {
            return;
        };
        self.breakpoints.insert(new_path.clone(), breakpoints);
        self.send_breakpoints_downstream(&old_path);
        self.send_breakpoints_downstream(&new_path);
        cx.emit(BreakpointStoreEvent::BreakpointsCleared(vec![old_path]));
        cx.emit(BreakpointStoreEvent::BreakpointsUpdated(
            new_path,
            BreakpointUpdatedReason::Toggled,
        ));
        cx.notify();
    }

    pub fn clear_breakpoints(&mut self, cx: &mut Context<Self>) {
        let cleared = std::mem::take(&mut self.breakpoints);
        for pending in self.pending_restored.values_mut() {
            pending.clear();
        }
        for (path, breakpoints_in_file) in &cleared {
            let previous_breakpoints = breakpoint_positions(&breakpoints_in_file.breakpoints);
            self.sync_file_breakpoints(path, &previous_breakpoints, cx);
        }
        cx.emit(BreakpointStoreEvent::BreakpointsCleared(
            cleared.into_keys().collect(),
        ));
        cx.notify();
    }

    pub fn breakpoints<'a>(
        &'a self,
        buffer: &'a Entity<Buffer>,
        range: Option<Range<text::Anchor>>,
        buffer_snapshot: &'a BufferSnapshot,
        cx: &App,
    ) -> impl Iterator<Item = (&'a BreakpointWithPosition, Option<BreakpointSessionState>)> + 'a
    {
        let abs_path = Self::abs_path_from_buffer(buffer, cx);
        let active_session_id = self
            .active_stack_frame
            .as_ref()
            .map(|frame| frame.session_id);
        abs_path
            .and_then(|path| self.breakpoints.get(&path))
            .into_iter()
            .flat_map(move |file_breakpoints| {
                file_breakpoints.breakpoints.iter().filter_map({
                    let range = range.clone();
                    move |bp| {
                        if !buffer_snapshot.can_resolve(bp.position()) {
                            return None;
                        }

                        if let Some(range) = &range
                            && (bp.position().cmp(&range.start, buffer_snapshot).is_lt()
                                || bp.position().cmp(&range.end, buffer_snapshot).is_gt())
                        {
                            return None;
                        }
                        let session_state = active_session_id
                            .and_then(|id| bp.session_state.get(&id))
                            .copied();
                        Some((&bp.bp, session_state))
                    }
                })
            })
    }

    pub fn active_position(&self) -> Option<&ActiveStackFrame> {
        self.active_stack_frame.as_ref()
    }

    pub fn active_debug_line_pane_id(&self) -> Option<EntityId> {
        self.active_debug_line_pane_id
    }

    pub fn set_active_debug_pane_id(&mut self, pane_id: EntityId) {
        self.active_debug_line_pane_id = Some(pane_id);
    }

    pub fn remove_active_position(
        &mut self,
        session_id: Option<SessionId>,
        cx: &mut Context<Self>,
    ) {
        if let Some(session_id) = session_id {
            if self
                .active_stack_frame
                .take_if(|active_stack_frame| active_stack_frame.session_id == session_id)
                .is_some()
            {
                self.active_debug_line_pane_id = None;
            }
        } else {
            self.active_stack_frame.take();
            self.active_debug_line_pane_id = None;
        }

        cx.emit(BreakpointStoreEvent::ClearDebugLines);
        cx.notify();
    }

    pub fn set_active_position(&mut self, position: ActiveStackFrame, cx: &mut Context<Self>) {
        if self
            .active_stack_frame
            .as_ref()
            .is_some_and(|active_position| active_position == &position)
        {
            cx.emit(BreakpointStoreEvent::SetDebugLine);
            return;
        }

        if self.active_stack_frame.is_some() {
            cx.emit(BreakpointStoreEvent::ClearDebugLines);
        }

        self.active_stack_frame = Some(position);

        cx.emit(BreakpointStoreEvent::SetDebugLine);
        cx.notify();
    }

    pub fn breakpoint_at_row(
        &self,
        path: &Path,
        row: u32,
        cx: &App,
    ) -> Option<(Entity<Buffer>, BreakpointWithPosition)> {
        self.breakpoints.get(path).and_then(|breakpoints| {
            let snapshot = breakpoints.buffer.read(cx).text_snapshot();

            breakpoints
                .breakpoints
                .iter()
                .find(|bp| bp.position().summary::<Point>(&snapshot).row == row)
                .map(|breakpoint| (breakpoints.buffer.clone(), breakpoint.bp.clone()))
        })
    }

    pub fn breakpoints_from_path(&self, path: &Arc<Path>) -> Vec<BreakpointWithPosition> {
        self.breakpoints
            .get(path)
            .map(|bp| bp.breakpoints.iter().map(|bp| bp.bp.clone()).collect())
            .unwrap_or_default()
    }

    pub fn source_breakpoints_from_path(
        &self,
        path: &Arc<Path>,
        cx: &App,
    ) -> Vec<SourceBreakpoint> {
        self.breakpoints
            .get(path)
            .map(|bp| {
                let snapshot = bp.buffer.read(cx).snapshot();
                bp.breakpoints
                    .iter()
                    .map(|bp| {
                        let position = snapshot.summary_for_anchor::<PointUtf16>(bp.position()).row;
                        let bp = &bp.bp;
                        SourceBreakpoint {
                            row: position,
                            path: path.clone(),
                            state: bp.bp.state,
                            message: bp.bp.message.clone(),
                            condition: bp.bp.condition.clone(),
                            hit_condition: bp.bp.hit_condition.clone(),
                        }
                    })
                    .collect()
            })
            .unwrap_or_default()
    }

    pub fn all_breakpoints(&self) -> BTreeMap<Arc<Path>, Vec<BreakpointWithPosition>> {
        self.breakpoints
            .iter()
            .map(|(path, bp)| {
                (
                    path.clone(),
                    bp.breakpoints.iter().map(|bp| bp.bp.clone()).collect(),
                )
            })
            .collect()
    }
    pub fn all_source_breakpoints(&self, cx: &App) -> BTreeMap<Arc<Path>, Vec<SourceBreakpoint>> {
        self.breakpoints
            .iter()
            .map(|(path, bp)| {
                let snapshot = bp.buffer.read(cx).snapshot();
                (
                    path.clone(),
                    bp.breakpoints
                        .iter()
                        .map(|breakpoint| {
                            let position = snapshot
                                .summary_for_anchor::<PointUtf16>(breakpoint.position())
                                .row;
                            let breakpoint = &breakpoint.bp;
                            SourceBreakpoint {
                                row: position,
                                path: path.clone(),
                                message: breakpoint.bp.message.clone(),
                                state: breakpoint.bp.state,
                                hit_condition: breakpoint.bp.hit_condition.clone(),
                                condition: breakpoint.bp.condition.clone(),
                            }
                        })
                        .collect(),
                )
            })
            .collect()
    }

    pub fn begin_restoring(&mut self, breakpoints: BTreeMap<Arc<Path>, Vec<SourceBreakpoint>>) {
        if !self.restores_saved_breakpoints() {
            return;
        }
        for (path, restored) in breakpoints {
            if restored.is_empty() || self.restoring_paths.contains(&path) {
                continue;
            }
            self.restoring_paths.insert(path.clone());
            let pending = self.pending_restored.entry(path).or_default();
            for breakpoint in restored {
                if !pending.iter().any(|pending| pending.row == breakpoint.row) {
                    pending.push(breakpoint);
                }
            }
        }
    }

    pub fn source_breakpoints_to_persist(
        &self,
        cx: &App,
    ) -> BTreeMap<Arc<Path>, Vec<SourceBreakpoint>> {
        let mut breakpoints = self.all_source_breakpoints(cx);
        for (path, pending) in &self.pending_restored {
            let live_rows = breakpoints
                .get(path)
                .map(|live| {
                    live.iter()
                        .map(|breakpoint| breakpoint.row)
                        .collect::<collections::HashSet<_>>()
                })
                .unwrap_or_default();
            let restored = pending
                .iter()
                .filter(|breakpoint| !live_rows.contains(&breakpoint.row))
                .cloned()
                .collect::<Vec<_>>();
            if !restored.is_empty() {
                breakpoints
                    .entry(path.clone())
                    .or_default()
                    .extend(restored);
            }
        }
        breakpoints
    }

    pub fn with_serialized_breakpoints(
        &mut self,
        breakpoints: BTreeMap<Arc<Path>, Vec<SourceBreakpoint>>,
        cx: &mut Context<BreakpointStore>,
    ) -> Task<Result<()>> {
        self.begin_restoring(breakpoints);
        self.finish_restoring(cx)
    }

    pub fn restore_pending_for_paths(
        &mut self,
        project_paths: impl IntoIterator<Item = ProjectPath>,
        cx: &mut Context<Self>,
    ) {
        if self.pending_restored.is_empty() {
            return;
        }
        let buffers = project_paths
            .into_iter()
            .filter_map(|project_path| self.buffer_store.read(cx).get_by_path(&project_path))
            .collect::<Vec<_>>();
        for buffer in buffers {
            self.restore_pending_in_buffer(&buffer, cx);
        }
    }

    pub fn finish_restoring(&mut self, cx: &mut Context<BreakpointStore>) -> Task<Result<()>> {
        if !self.restores_saved_breakpoints() {
            return Task::ready(Ok(()));
        }
        let open_buffers = self
            .pending_restored
            .keys()
            .filter_map(|path| {
                let project_path = self
                    .worktree_store
                    .read(cx)
                    .project_path_for_absolute_path(path, cx)?;
                self.buffer_store.read(cx).get_by_path(&project_path)
            })
            .collect::<Vec<_>>();
        for buffer in open_buffers {
            self.restore_pending_in_buffer(&buffer, cx);
        }
        if self.pending_restored.is_empty() {
            return Task::ready(Ok(()));
        }
        self.pending_restored_buffers = Some(cx.subscribe(
            &self.buffer_store,
            |breakpoint_store, _, event, cx| {
                if let BufferStoreEvent::BufferAdded(buffer) = event {
                    breakpoint_store.restore_pending_in_buffer(buffer, cx);
                }
            },
        ));
        let paths = self.pending_restored.keys().cloned().collect::<Vec<_>>();
        let worktree_store = self.worktree_store.downgrade();
        let buffer_store = self.buffer_store.downgrade();
        cx.spawn(async move |this, cx| {
            for path in paths {
                if !this.read_with(cx, |this, _| this.pending_restored.contains_key(&path))? {
                    continue;
                }
                let buffer = async {
                    let (worktree, relative_path) = worktree_store
                        .update(cx, |this, cx| {
                            this.find_or_create_worktree(&path, false, cx)
                        })?
                        .await?;
                    buffer_store
                        .update(cx, |this, cx| {
                            let path = ProjectPath {
                                worktree_id: worktree.read(cx).id(),
                                path: relative_path,
                            };
                            this.open_buffer(path, cx)
                        })?
                        .await
                }
                .await;
                this.update(cx, |this, cx| match buffer {
                    Ok(buffer) => this.restore_pending_in_buffer(&buffer, cx),
                    Err(error) => {
                        if let Some(pending) = this.pending_restored.get(&path) {
                            log::warn!(
                                "Keeping {} breakpoints of {path:?} until it can be opened: {error:#}",
                                pending.len()
                            );
                        }
                    }
                })?;
            }
            this.update(cx, |this, _| {
                if this.pending_restored.is_empty() {
                    this.pending_restored_buffers = None;
                }
            })
        })
    }

    fn restore_pending_in_buffer(&mut self, buffer: &Entity<Buffer>, cx: &mut Context<Self>) {
        let Some(path) = Self::abs_path_from_buffer(buffer, cx) else {
            return;
        };
        let Some(pending) = self.pending_restored.remove(&path) else {
            return;
        };
        self.restoring_paths.remove(&path);
        let snapshot = buffer.read(cx).snapshot();
        let max_point = snapshot.max_point_utf16();
        let mut restored = BreakpointsInFile::new(buffer.clone(), cx);
        for breakpoint in pending {
            let point = PointUtf16::new(breakpoint.row, 0);
            if point > max_point {
                log::error!("skipping a deserialized breakpoint that's out of range");
                continue;
            }
            restored
                .breakpoints
                .push(StatefulBreakpoint::new(BreakpointWithPosition {
                    position: snapshot.anchor_after(point),
                    bp: Breakpoint {
                        message: breakpoint.message,
                        state: breakpoint.state,
                        condition: breakpoint.condition,
                        hit_condition: breakpoint.hit_condition,
                    },
                }));
        }
        let previous_breakpoints = self
            .breakpoints
            .get(&path)
            .map(|live| breakpoint_positions(&live.breakpoints))
            .unwrap_or_default();
        let added = match self.breakpoints.get_mut(&path) {
            Some(live) => live.merge_restored(restored, cx),
            None => {
                let added = restored
                    .breakpoints
                    .iter()
                    .map(|breakpoint| *breakpoint.position())
                    .collect::<Vec<_>>();
                if !added.is_empty() {
                    self.breakpoints.insert(path.clone(), restored);
                }
                added
            }
        };
        if self.pending_restored.is_empty() {
            self.pending_restored_buffers = None;
        }
        if !added.is_empty() {
            self.sync_file_breakpoints(&path, &previous_breakpoints, cx);
            cx.emit(BreakpointStoreEvent::BreakpointsUpdated(
                path,
                BreakpointUpdatedReason::Toggled,
            ));
        }
        cx.notify();
    }

    fn restores_saved_breakpoints(&self) -> bool {
        match &self.mode {
            BreakpointStoreMode::Local => true,
            BreakpointStoreMode::Remote(remote) => !remote.upstream_client.is_via_collab(),
        }
    }

    fn forget_pending_restored(&mut self, path: &Path, row: u32) {
        if let Some(pending) = self.pending_restored.get_mut(path) {
            pending.retain(|breakpoint| breakpoint.row != row);
        }
    }

    #[cfg(any(test, feature = "test-support"))]
    pub(crate) fn breakpoint_paths(&self) -> Vec<Arc<Path>> {
        self.breakpoints.keys().cloned().collect()
    }

    #[cfg(any(test, feature = "test-support"))]
    pub fn pending_remote_edits(&self) -> (usize, usize) {
        (
            self.remote_edits.values().map(VecDeque::len).sum(),
            self.remote_edit_buffers.len(),
        )
    }
}

#[derive(Clone, Copy)]
pub enum BreakpointUpdatedReason {
    Toggled,
    FileSaved,
}

pub enum BreakpointStoreEvent {
    SetDebugLine,
    ClearDebugLines,
    BreakpointsUpdated(Arc<Path>, BreakpointUpdatedReason),
    BreakpointsCleared(Vec<Arc<Path>>),
}

impl EventEmitter<BreakpointStoreEvent> for BreakpointStore {}

type BreakpointMessage = Arc<str>;

#[derive(Clone, Debug)]
pub enum BreakpointEditAction {
    Toggle,
    InvertState,
    EditLogMessage(BreakpointMessage),
    EditCondition(BreakpointMessage),
    EditHitCondition(BreakpointMessage),
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub enum BreakpointState {
    Enabled,
    Disabled,
}

impl BreakpointState {
    #[inline]
    pub fn is_enabled(&self) -> bool {
        matches!(self, BreakpointState::Enabled)
    }

    #[inline]
    pub fn is_disabled(&self) -> bool {
        matches!(self, BreakpointState::Disabled)
    }

    #[inline]
    pub fn to_int(self) -> i32 {
        match self {
            BreakpointState::Enabled => 0,
            BreakpointState::Disabled => 1,
        }
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct Breakpoint {
    pub message: Option<BreakpointMessage>,
    /// How many times do we hit the breakpoint until we actually stop at it e.g. (2 = 2 times of the breakpoint action)
    pub hit_condition: Option<Arc<str>>,
    pub condition: Option<BreakpointMessage>,
    pub state: BreakpointState,
}

impl Breakpoint {
    pub fn new_standard() -> Self {
        Self {
            state: BreakpointState::Enabled,
            hit_condition: None,
            condition: None,
            message: None,
        }
    }

    pub fn new_condition(hit_condition: &str) -> Self {
        Self {
            state: BreakpointState::Enabled,
            condition: None,
            hit_condition: Some(hit_condition.into()),
            message: None,
        }
    }

    pub fn new_log(log_message: &str) -> Self {
        Self {
            state: BreakpointState::Enabled,
            hit_condition: None,
            condition: None,
            message: Some(log_message.into()),
        }
    }

    fn to_proto(
        &self,
        _path: &Path,
        position: &text::Anchor,
        session_states: &HashMap<SessionId, BreakpointSessionState>,
    ) -> Option<client::proto::Breakpoint> {
        Some(client::proto::Breakpoint {
            position: Some(serialize_text_anchor(position)),
            state: match self.state {
                BreakpointState::Enabled => proto::BreakpointState::Enabled.into(),
                BreakpointState::Disabled => proto::BreakpointState::Disabled.into(),
            },
            message: self.message.as_ref().map(|s| String::from(s.as_ref())),
            condition: self.condition.as_ref().map(|s| String::from(s.as_ref())),
            hit_condition: self
                .hit_condition
                .as_ref()
                .map(|s| String::from(s.as_ref())),
            session_state: session_states
                .iter()
                .map(|(session_id, state)| {
                    (
                        session_id.to_proto(),
                        proto::BreakpointSessionState {
                            id: state.id,
                            verified: state.verified,
                        },
                    )
                })
                .collect(),
        })
    }

    fn from_proto(breakpoint: client::proto::Breakpoint) -> Option<Self> {
        Some(Self {
            state: match proto::BreakpointState::try_from(breakpoint.state).ok() {
                Some(proto::BreakpointState::Disabled) => BreakpointState::Disabled,
                None | Some(proto::BreakpointState::Enabled) => BreakpointState::Enabled,
            },
            message: breakpoint.message.map(Into::into),
            condition: breakpoint.condition.map(Into::into),
            hit_condition: breakpoint.hit_condition.map(Into::into),
        })
    }

    #[inline]
    pub fn is_enabled(&self) -> bool {
        self.state.is_enabled()
    }

    #[inline]
    pub fn is_disabled(&self) -> bool {
        self.state.is_disabled()
    }
}

/// Breakpoint for location within source code.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct SourceBreakpoint {
    pub row: u32,
    pub path: Arc<Path>,
    pub message: Option<Arc<str>>,
    pub condition: Option<Arc<str>>,
    pub hit_condition: Option<Arc<str>>,
    pub state: BreakpointState,
}

impl From<SourceBreakpoint> for dap::SourceBreakpoint {
    fn from(bp: SourceBreakpoint) -> Self {
        Self {
            line: bp.row as u64 + 1,
            column: None,
            condition: bp
                .condition
                .map(|condition| String::from(condition.as_ref())),
            hit_condition: bp
                .hit_condition
                .map(|hit_condition| String::from(hit_condition.as_ref())),
            log_message: bp.message.map(|message| String::from(message.as_ref())),
            mode: None,
        }
    }
}

fn upstream_edits<'a>(
    previous: Option<&'a BreakpointWithPosition>,
    resulting: Option<&'a BreakpointWithPosition>,
) -> Vec<(&'a BreakpointWithPosition, proto::BreakpointEdit)> {
    match (previous, resulting) {
        (None, None) => Vec::new(),
        (Some(previous), Some(resulting)) if previous == resulting => Vec::new(),
        (None, Some(resulting)) => Vec::from([(resulting, proto::BreakpointEdit::Set)]),
        (Some(previous), None) => Vec::from([(previous, proto::BreakpointEdit::Remove)]),
        (Some(previous), Some(resulting)) => Vec::from([
            (previous, proto::BreakpointEdit::Superseded),
            (resulting, proto::BreakpointEdit::Set),
        ]),
    }
}

fn breakpoint_positions(breakpoints: &[StatefulBreakpoint]) -> Vec<BreakpointWithPosition> {
    breakpoints
        .iter()
        .map(|breakpoint| breakpoint.bp.clone())
        .collect()
}

fn changed_breakpoints<'a>(
    previous: &'a [BreakpointWithPosition],
    current: &'a [StatefulBreakpoint],
) -> Vec<(
    Option<&'a BreakpointWithPosition>,
    Option<&'a BreakpointWithPosition>,
)> {
    let mut unmatched = current
        .iter()
        .map(|breakpoint| &breakpoint.bp)
        .collect::<Vec<_>>();
    let mut changes = previous
        .iter()
        .map(|previous| {
            let resulting = unmatched
                .iter()
                .position(|current| *current == previous)
                .or_else(|| {
                    unmatched
                        .iter()
                        .position(|current| current.position == previous.position)
                })
                .map(|index| unmatched.remove(index));
            (Some(previous), resulting)
        })
        .collect::<Vec<_>>();
    changes.extend(unmatched.into_iter().map(|current| (None, Some(current))));
    changes
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Project;
    use fs::FakeFs;
    use gpui::TestAppContext;
    use serde_json::json;
    use settings::SettingsStore;
    use util::{path, rel_path::rel_path};

    #[gpui::test]
    async fn test_toggle_breakpoint_requests_are_gated_by_collaborators(cx: &mut TestAppContext) {
        cx.update(|cx| {
            let settings_store = SettingsStore::test(cx);
            cx.set_global(settings_store);
        });
        let fs = FakeFs::new(cx.executor());
        fs.insert_tree(path!("/a"), json!({ "test.txt": "one\ntwo" }))
            .await;
        let project = Project::test(fs, [Path::new(path!("/a"))], cx).await;
        let worktree_id = project.read_with(cx, |project, cx| {
            project.worktrees(cx).next().unwrap().read(cx).id()
        });
        let buffer = project
            .update(cx, |project, cx| {
                project.open_buffer((worktree_id, rel_path("test.txt")), cx)
            })
            .await
            .unwrap();
        let breakpoint_store = project.read_with(cx, |project, _| project.breakpoint_store());
        let guest = proto::PeerId { owner_id: 1, id: 7 };
        let not_a_collaborator = format!("Peer {guest} is not a collaborator of this project");

        let before_joining = toggle_breakpoint_from(&breakpoint_store, &buffer, guest, cx).await;
        breakpoint_store.update(cx, |breakpoint_store, _| {
            breakpoint_store.collaborator_added(guest)
        });
        let after_joining = toggle_breakpoint_from(&breakpoint_store, &buffer, guest, cx).await;
        breakpoint_store.update(cx, |breakpoint_store, _| {
            breakpoint_store.collaborator_removed(guest)
        });
        let after_leaving = toggle_breakpoint_from(&breakpoint_store, &buffer, guest, cx).await;

        assert_eq!(
            (
                before_joining,
                after_joining,
                after_leaving,
                breakpoint_store.read_with(cx, |breakpoint_store, cx| {
                    breakpoint_store
                        .all_source_breakpoints(cx)
                        .into_values()
                        .flatten()
                        .map(|breakpoint| breakpoint.row)
                        .collect::<Vec<_>>()
                }),
            ),
            (
                Err(not_a_collaborator.clone()),
                Ok(proto::Ack {}),
                Err(not_a_collaborator),
                Vec::from([1]),
            )
        );
    }

    #[gpui::test]
    async fn test_upstream_edits_converge_on_hosts_that_only_toggle(cx: &mut TestAppContext) {
        cx.update(|cx| {
            let settings_store = SettingsStore::test(cx);
            cx.set_global(settings_store);
        });
        let mut histories = Vec::new();
        for host_only_toggles in [true, false] {
            let fs = FakeFs::new(cx.executor());
            fs.insert_tree(path!("/a"), json!({ "test.txt": "one\ntwo" }))
                .await;
            let project = Project::test(fs, [Path::new(path!("/a"))], cx).await;
            let buffer = project
                .update(cx, |project, cx| {
                    project.open_local_buffer(path!("/a/test.txt"), cx)
                })
                .await
                .unwrap();
            let breakpoint_store = project.read_with(cx, |project, _| project.breakpoint_store());
            let enabled = BreakpointWithPosition {
                position: buffer.read_with(cx, |buffer, _| buffer.anchor_before(Point::new(1, 0))),
                bp: Breakpoint::new_standard(),
            };
            let disabled = BreakpointWithPosition {
                bp: Breakpoint {
                    state: BreakpointState::Disabled,
                    ..enabled.bp.clone()
                },
                ..enabled.clone()
            };
            let mut history = Vec::new();
            for (previous, resulting) in [
                (None, Some(&enabled)),
                (Some(&enabled), Some(&disabled)),
                (Some(&disabled), Some(&disabled)),
                (Some(&disabled), None),
            ] {
                for (breakpoint, edit) in upstream_edits(previous, resulting) {
                    if host_only_toggles {
                        breakpoint_store.update(cx, |breakpoint_store, cx| {
                            breakpoint_store.toggle_breakpoint(
                                buffer.clone(),
                                breakpoint.clone(),
                                BreakpointEditAction::Toggle,
                                cx,
                            )
                        });
                    } else {
                        send_upstream_edit(&breakpoint_store, breakpoint, edit, cx)
                            .await
                            .unwrap();
                    }
                }
                history.push(breakpoint_store.read_with(cx, |breakpoint_store, cx| {
                    breakpoint_store
                        .all_source_breakpoints(cx)
                        .into_values()
                        .flatten()
                        .map(|breakpoint| (breakpoint.row, breakpoint.state))
                        .collect::<Vec<_>>()
                }));
            }
            histories.push(history);
        }

        let expected = Vec::from([
            Vec::from([(1, BreakpointState::Enabled)]),
            Vec::from([(1, BreakpointState::Disabled)]),
            Vec::from([(1, BreakpointState::Disabled)]),
            Vec::new(),
        ]);
        assert_eq!(histories, Vec::from([expected.clone(), expected]));
    }

    #[gpui::test]
    async fn test_upstream_edits_keep_other_breakpoints_on_a_joined_row(cx: &mut TestAppContext) {
        cx.update(|cx| {
            let settings_store = SettingsStore::test(cx);
            cx.set_global(settings_store);
        });
        let fs = FakeFs::new(cx.executor());
        fs.insert_tree(path!("/a"), json!({ "test.txt": "aaa\nbbb\n" }))
            .await;
        let project = Project::test(fs, [Path::new(path!("/a"))], cx).await;
        let buffer = project
            .update(cx, |project, cx| {
                project.open_local_buffer(path!("/a/test.txt"), cx)
            })
            .await
            .unwrap();
        let breakpoint_store = project.read_with(cx, |project, _| project.breakpoint_store());
        let [first, second] = [0, 1].map(|row| BreakpointWithPosition {
            position: buffer.read_with(cx, |buffer, _| buffer.anchor_after(Point::new(row, 0))),
            bp: Breakpoint::new_standard(),
        });
        for breakpoint in [&first, &second] {
            breakpoint_store.update(cx, |breakpoint_store, cx| {
                breakpoint_store.toggle_breakpoint(
                    buffer.clone(),
                    breakpoint.clone(),
                    BreakpointEditAction::Toggle,
                    cx,
                )
            });
        }
        buffer.update(cx, |buffer, cx| {
            buffer.edit([(Point::new(0, 3)..Point::new(1, 0), "")], None, cx)
        });

        let disabled_first = BreakpointWithPosition {
            bp: Breakpoint {
                state: BreakpointState::Disabled,
                ..first.bp.clone()
            },
            ..first.clone()
        };
        let previous = [second.clone(), first];
        let current = [second, disabled_first].map(StatefulBreakpoint::new);
        let edits = changed_breakpoints(&previous, &current)
            .into_iter()
            .flat_map(|(previous, resulting)| upstream_edits(previous, resulting))
            .map(|(breakpoint, edit)| (breakpoint.clone(), edit))
            .collect::<Vec<_>>();
        for (breakpoint, edit) in &edits {
            send_upstream_edit(&breakpoint_store, breakpoint, *edit, cx)
                .await
                .unwrap();
        }
        buffer.update(cx, |buffer, cx| buffer.undo(cx));

        assert_eq!(
            (
                edits.into_iter().map(|(_, edit)| edit).collect::<Vec<_>>(),
                breakpoint_store.read_with(cx, |breakpoint_store, cx| {
                    breakpoint_store
                        .all_source_breakpoints(cx)
                        .into_values()
                        .flatten()
                        .map(|breakpoint| (breakpoint.row, breakpoint.state))
                        .sorted_by_key(|(row, _)| *row)
                        .collect::<Vec<_>>()
                }),
            ),
            (
                Vec::from([
                    proto::BreakpointEdit::Superseded,
                    proto::BreakpointEdit::Set
                ]),
                Vec::from([
                    (0, BreakpointState::Disabled),
                    (1, BreakpointState::Enabled)
                ]),
            )
        );
    }

    async fn send_upstream_edit(
        breakpoint_store: &Entity<BreakpointStore>,
        breakpoint: &BreakpointWithPosition,
        edit: proto::BreakpointEdit,
        cx: &mut TestAppContext,
    ) -> Result<proto::Ack> {
        let envelope = TypedEnvelope {
            sender_id: proto::PeerId { owner_id: 0, id: 0 },
            original_sender_id: None,
            message_id: 0,
            payload: proto::ToggleBreakpoint {
                project_id: 0,
                path: String::from(path!("/a/test.txt")),
                breakpoint: breakpoint.bp.to_proto(
                    Path::new(path!("/a/test.txt")),
                    &breakpoint.position,
                    &HashMap::default(),
                ),
                edit: i32::from(edit),
            },
            received_at: std::time::Instant::now(),
        };
        BreakpointStore::handle_toggle_breakpoint(breakpoint_store.clone(), envelope, cx.to_async())
            .await
    }

    async fn toggle_breakpoint_from(
        breakpoint_store: &Entity<BreakpointStore>,
        buffer: &Entity<Buffer>,
        sender: proto::PeerId,
        cx: &mut TestAppContext,
    ) -> Result<proto::Ack, String> {
        let position = buffer.read_with(cx, |buffer, _| buffer.anchor_before(Point::new(1, 0)));
        let envelope = TypedEnvelope {
            sender_id: proto::PeerId { owner_id: 0, id: 0 },
            original_sender_id: Some(sender),
            message_id: 0,
            payload: proto::ToggleBreakpoint {
                project_id: 0,
                path: String::from(path!("/a/test.txt")),
                breakpoint: Breakpoint::new_standard().to_proto(
                    Path::new(path!("/a/test.txt")),
                    &position,
                    &HashMap::default(),
                ),
                edit: i32::from(proto::BreakpointEdit::Set),
            },
            received_at: std::time::Instant::now(),
        };
        BreakpointStore::handle_toggle_breakpoint(breakpoint_store.clone(), envelope, cx.to_async())
            .await
            .map_err(|error| error.to_string())
    }
}
