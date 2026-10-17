pub mod model;

use std::{
    borrow::Cow,
    collections::BTreeMap,
    ffi::OsStr,
    path::{Path, PathBuf},
    str::FromStr,
    sync::Arc,
};

use chrono::{DateTime, NaiveDateTime, Utc};
use fs::Fs;

use anyhow::{Context as _, Result, bail};
use collections::{HashMap, HashSet, IndexSet};
use db::{
    kvp::KeyValueStore,
    query,
    sqlez::{connection::Connection, domain::Domain},
    sqlez_macros::sql,
};
use futures::future::Shared;
use gpui::{
    AppContext as _, Axis, Bounds, Entity, EntityId, Global, Task, WindowBounds, WindowId, point,
    size,
};
use parking_lot::Mutex;
use project::{
    ProjectGroupKey,
    bookmark_store::SerializedBookmark,
    debugger::breakpoint_store::{BreakpointState, SourceBreakpoint},
    trusted_worktrees::{DbTrustedPaths, RemoteHostLocation},
};

use language::{LanguageName, Toolchain, ToolchainScope};
use remote::{
    DockerConnectionOptions, RemoteConnectionIdentity, RemoteConnectionOptions,
    RemoteConnectionTarget, SshConnectionOptions, WslConnectionOptions, remote_connection_identity,
};
use serde::{Deserialize, Serialize};
use sqlez::{
    bindable::{Bind, Column, StaticColumnCount},
    statement::Statement,
    thread_safe_connection::ThreadSafeConnection,
};

use ui::{App, SharedString, px};
use util::{ResultExt, maybe, rel_path::RelPath};
use uuid::Uuid;

use crate::{
    WorkspaceId,
    path_list::{PathList, SerializedPathList},
    persistence::model::RemoteConnectionKind,
};

use model::{
    GroupId, ItemId, Lenient, PaneId, RemoteConnectionId, SerializedItem, SerializedPane,
    SerializedPaneGroup, SerializedWorkspace, UnserializedRootFiles,
};

use self::model::{
    DockStructure, SerializedWorkspaceLocation, SessionBinding, SessionWindow, SessionWorkspace,
};

// https://www.sqlite.org/limits.html
// > <..> the maximum value of a host parameter number is SQLITE_MAX_VARIABLE_NUMBER,
// > which defaults to <..> 32766 for SQLite versions after 3.32.0.
const MAX_QUERY_PLACEHOLDERS: usize = 32000;

fn parse_timestamp(text: &str) -> DateTime<Utc> {
    NaiveDateTime::parse_from_str(text, "%Y-%m-%d %H:%M:%S")
        .map(|naive| naive.and_utc())
        .unwrap_or_else(|_| Utc::now())
}

pub(crate) async fn is_git_message_file(path: &Path, fs: &dyn Fs) -> bool {
    if !has_git_message_file_name(path) {
        return false;
    }
    let Some(mut git_directory) = path.parent() else {
        return false;
    };
    if git_directory.file_name().is_some_and(|name| {
        name == OsStr::new("rebase-merge") || name == OsStr::new("rebase-apply")
    }) && let Some(parent) = git_directory.parent()
    {
        git_directory = parent;
    }
    fs.is_file(&git_directory.join("HEAD")).await
        && (fs.is_dir(&git_directory.join("objects")).await
            || fs.is_file(&git_directory.join("commondir")).await)
}

pub(crate) fn has_git_message_file_name(path: &Path) -> bool {
    const GIT_MESSAGE_FILES: [&str; 8] = [
        "COMMIT_EDITMSG",
        "MERGE_MSG",
        "SQUASH_MSG",
        "TAG_EDITMSG",
        "NOTES_EDITMSG",
        "EDIT_DESCRIPTION",
        "git-rebase-todo",
        "addp-hunk-edit.diff",
    ];
    path.file_name()
        .and_then(|file_name| file_name.to_str())
        .is_some_and(|file_name| GIT_MESSAGE_FILES.contains(&file_name))
}

struct WindowMember {
    workspace_id: WorkspaceId,
    location: SerializedWorkspaceLocation,
    restorable_paths: PathList,
    has_items: bool,
}

fn restores_in_own_window(sibling: &WindowMember, members: &[WindowMember]) -> bool {
    sibling.has_items
        && (sibling.restorable_paths.is_empty()
            || members.iter().any(|member| {
                member.workspace_id != sibling.workspace_id
                    && member.location == sibling.location
                    && member.restorable_paths.paths() == sibling.restorable_paths.paths()
            }))
}

const CONFIGURED_SSH_CONNECTIONS_KEY: &str = "configured_connections";
const SSH_ARGUMENT_RENAMES_KEY: &str = "argument_renames";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SshArgumentRenames {
    Keep,
    Discard,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConfiguredSshConnection {
    pub host: String,
    pub username: Option<String>,
    pub port: Option<u16>,
    pub args: Vec<String>,
}

impl ConfiguredSshConnection {
    fn target(&self) -> SshTarget {
        SshTarget {
            host: self.host.clone(),
            username: self.username.clone(),
            port: self.port,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct SshTarget {
    host: String,
    username: Option<String>,
    port: Option<u16>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct SshArgumentsRename {
    target: SshTarget,
    from: Vec<String>,
    to: Vec<String>,
}

fn ssh_argument_edits(
    previous: &[ConfiguredSshConnection],
    configured: &[ConfiguredSshConnection],
) -> Vec<SshArgumentsRename> {
    let removed = previous
        .iter()
        .filter(|connection| !configured.contains(connection))
        .collect::<Vec<_>>();
    let added = configured
        .iter()
        .filter(|connection| !previous.contains(connection))
        .collect::<Vec<_>>();
    removed
        .iter()
        .filter_map(|removed_connection| {
            let target = removed_connection.target();
            let removed_for_target = removed
                .iter()
                .filter(|connection| connection.target() == target)
                .count();
            let mut added_for_target = added
                .iter()
                .filter(|connection| connection.target() == target);
            let added_connection = added_for_target.next()?;
            (removed_for_target == 1 && added_for_target.next().is_none()).then(|| {
                SshArgumentsRename {
                    target,
                    from: removed_connection.args.clone(),
                    to: added_connection.args.clone(),
                }
            })
        })
        .collect()
}

fn compose_ssh_argument_renames(
    mut renames: Vec<SshArgumentsRename>,
    edits: &[SshArgumentsRename],
    configured: &[ConfiguredSshConnection],
) -> Vec<SshArgumentsRename> {
    for edit in edits {
        for existing in &mut renames {
            if existing.target == edit.target && existing.to == edit.from {
                existing.to = edit.to.clone();
            }
        }
        renames.retain(|existing| existing.target != edit.target || existing.from != edit.from);
        renames.push(edit.clone());
    }
    renames.retain(|rename| {
        rename.from != rename.to
            && !configured.iter().any(|connection| {
                connection.target() == rename.target && connection.args == rename.from
            })
    });
    renames
}

fn renamed_ssh_arguments(
    renames: &[SshArgumentsRename],
    target: &SshTarget,
    args: &[String],
) -> Option<Vec<String>> {
    renames
        .iter()
        .find(|rename| rename.target == *target && rename.from == args)
        .map(|rename| rename.to.clone())
}

fn contains_wsl_path(paths: &PathList) -> bool {
    cfg!(windows)
        && paths
            .paths()
            .iter()
            .any(|path| util::paths::WslPath::from_path(path).is_some())
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub(crate) struct SerializedAxis(pub(crate) gpui::Axis);
impl sqlez::bindable::StaticColumnCount for SerializedAxis {}
impl sqlez::bindable::Bind for SerializedAxis {
    fn bind(
        &self,
        statement: &sqlez::statement::Statement,
        start_index: i32,
    ) -> anyhow::Result<i32> {
        match self.0 {
            gpui::Axis::Horizontal => "Horizontal",
            gpui::Axis::Vertical => "Vertical",
        }
        .bind(statement, start_index)
    }
}

impl sqlez::bindable::Column for SerializedAxis {
    fn column(
        statement: &mut sqlez::statement::Statement,
        start_index: i32,
    ) -> anyhow::Result<(Self, i32)> {
        String::column(statement, start_index).and_then(|(axis_text, next_index)| {
            Ok((
                match axis_text.as_str() {
                    "Horizontal" => Self(Axis::Horizontal),
                    "Vertical" => Self(Axis::Vertical),
                    _ => anyhow::bail!("Stored serialized item kind is incorrect"),
                },
                next_index,
            ))
        })
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Default)]
pub(crate) struct SerializedWindowBounds(pub(crate) WindowBounds);

impl StaticColumnCount for SerializedWindowBounds {
    fn column_count() -> usize {
        5
    }
}

impl Bind for SerializedWindowBounds {
    fn bind(&self, statement: &Statement, start_index: i32) -> Result<i32> {
        match self.0 {
            WindowBounds::Windowed(bounds) => {
                let next_index = statement.bind(&"Windowed", start_index)?;
                statement.bind(
                    &(
                        SerializedPixels(bounds.origin.x),
                        SerializedPixels(bounds.origin.y),
                        SerializedPixels(bounds.size.width),
                        SerializedPixels(bounds.size.height),
                    ),
                    next_index,
                )
            }
            WindowBounds::Maximized(bounds) => {
                let next_index = statement.bind(&"Maximized", start_index)?;
                statement.bind(
                    &(
                        SerializedPixels(bounds.origin.x),
                        SerializedPixels(bounds.origin.y),
                        SerializedPixels(bounds.size.width),
                        SerializedPixels(bounds.size.height),
                    ),
                    next_index,
                )
            }
            WindowBounds::Fullscreen(bounds) => {
                let next_index = statement.bind(&"FullScreen", start_index)?;
                statement.bind(
                    &(
                        SerializedPixels(bounds.origin.x),
                        SerializedPixels(bounds.origin.y),
                        SerializedPixels(bounds.size.width),
                        SerializedPixels(bounds.size.height),
                    ),
                    next_index,
                )
            }
        }
    }
}

impl Column for SerializedWindowBounds {
    fn column(statement: &mut Statement, start_index: i32) -> Result<(Self, i32)> {
        let (window_state, next_index) = String::column(statement, start_index)?;
        let ((x, y, width, height), _): ((i32, i32, i32, i32), _) =
            Column::column(statement, next_index)?;
        let bounds = Bounds {
            origin: point(px(x as f32), px(y as f32)),
            size: size(px(width as f32), px(height as f32)),
        };

        let status = match window_state.as_str() {
            "Windowed" | "Fixed" => SerializedWindowBounds(WindowBounds::Windowed(bounds)),
            "Maximized" => SerializedWindowBounds(WindowBounds::Maximized(bounds)),
            "FullScreen" => SerializedWindowBounds(WindowBounds::Fullscreen(bounds)),
            _ => bail!("Window State did not have a valid string"),
        };

        Ok((status, next_index + 4))
    }
}

const DEFAULT_WINDOW_BOUNDS_KEY: &str = "default_window_bounds";

pub fn read_default_window_bounds(kvp: &KeyValueStore) -> Option<(Uuid, WindowBounds)> {
    let json_str = kvp
        .read_kvp(DEFAULT_WINDOW_BOUNDS_KEY)
        .log_err()
        .flatten()?;

    let (display_uuid, persisted) =
        serde_json::from_str::<(Uuid, WindowBoundsJson)>(&json_str).ok()?;
    Some((display_uuid, persisted.into()))
}

pub async fn write_default_window_bounds(
    kvp: &KeyValueStore,
    bounds: WindowBounds,
    display_uuid: Uuid,
) -> anyhow::Result<()> {
    let persisted = WindowBoundsJson::from(bounds);
    let json_str = serde_json::to_string(&(display_uuid, persisted))?;
    kvp.write_kvp(DEFAULT_WINDOW_BOUNDS_KEY.to_string(), json_str)
        .await?;
    Ok(())
}

#[derive(Serialize, Deserialize)]
pub enum WindowBoundsJson {
    Windowed {
        x: i32,
        y: i32,
        width: i32,
        height: i32,
    },
    Maximized {
        x: i32,
        y: i32,
        width: i32,
        height: i32,
    },
    Fullscreen {
        x: i32,
        y: i32,
        width: i32,
        height: i32,
    },
}

impl From<WindowBounds> for WindowBoundsJson {
    fn from(b: WindowBounds) -> Self {
        match b {
            WindowBounds::Windowed(bounds) => {
                let origin = bounds.origin;
                let size = bounds.size;
                WindowBoundsJson::Windowed {
                    x: f32::from(origin.x).round() as i32,
                    y: f32::from(origin.y).round() as i32,
                    width: f32::from(size.width).round() as i32,
                    height: f32::from(size.height).round() as i32,
                }
            }
            WindowBounds::Maximized(bounds) => {
                let origin = bounds.origin;
                let size = bounds.size;
                WindowBoundsJson::Maximized {
                    x: f32::from(origin.x).round() as i32,
                    y: f32::from(origin.y).round() as i32,
                    width: f32::from(size.width).round() as i32,
                    height: f32::from(size.height).round() as i32,
                }
            }
            WindowBounds::Fullscreen(bounds) => {
                let origin = bounds.origin;
                let size = bounds.size;
                WindowBoundsJson::Fullscreen {
                    x: f32::from(origin.x).round() as i32,
                    y: f32::from(origin.y).round() as i32,
                    width: f32::from(size.width).round() as i32,
                    height: f32::from(size.height).round() as i32,
                }
            }
        }
    }
}

impl From<WindowBoundsJson> for WindowBounds {
    fn from(n: WindowBoundsJson) -> Self {
        match n {
            WindowBoundsJson::Windowed {
                x,
                y,
                width,
                height,
            } => WindowBounds::Windowed(Bounds {
                origin: point(px(x as f32), px(y as f32)),
                size: size(px(width as f32), px(height as f32)),
            }),
            WindowBoundsJson::Maximized {
                x,
                y,
                width,
                height,
            } => WindowBounds::Maximized(Bounds {
                origin: point(px(x as f32), px(y as f32)),
                size: size(px(width as f32), px(height as f32)),
            }),
            WindowBoundsJson::Fullscreen {
                x,
                y,
                width,
                height,
            } => WindowBounds::Fullscreen(Bounds {
                origin: point(px(x as f32), px(y as f32)),
                size: size(px(width as f32), px(height as f32)),
            }),
        }
    }
}

const PERSISTENT_ITEM_ID_EPOCH_KEY: &str = "persistent_item_id_epoch";
const MAX_PERSISTENT_ITEM_ID_EPOCH: u32 = u32::MAX >> 1;

pub fn reserve_persistent_item_ids(cx: &mut App) {
    let kvp = KeyValueStore::global(cx);
    let ids = cx.default_global::<PersistentItemIds>();
    if ids.epoch.is_none() {
        ids.start_epoch(&kvp);
    }
}

pub fn persistent_item_id<T: 'static>(entity: &Entity<T>, cx: &mut App) -> ItemId {
    let entity_id = entity.entity_id();
    if let Some(item_id) = cx
        .try_global::<PersistentItemIds>()
        .and_then(|ids| ids.by_entity.get(&entity_id).copied())
    {
        return item_id;
    }
    let item_id = PersistentItemIds::allocate(cx);
    PersistentItemIds::track(entity, item_id, cx);
    item_id
}

pub(crate) fn claim_persistent_item_id<T: 'static>(
    entity: &Entity<T>,
    item_id: ItemId,
    cx: &mut App,
) -> ItemId {
    let ids = cx.default_global::<PersistentItemIds>();
    if let Some(existing_item_id) = ids.by_entity.get(&entity.entity_id()) {
        return *existing_item_id;
    }
    let item_id = if ids.by_item.contains_key(&item_id) {
        PersistentItemIds::allocate(cx)
    } else {
        item_id
    };
    PersistentItemIds::track(entity, item_id, cx);
    item_id
}

#[derive(Default)]
struct PersistentItemIds {
    epoch: Option<u32>,
    next_index: u32,
    by_entity: HashMap<EntityId, ItemId>,
    by_item: HashMap<ItemId, EntityId>,
    live: LiveItemIds,
}

impl Global for PersistentItemIds {}

#[derive(Clone, Default)]
struct LiveItemIds(Arc<Mutex<HashSet<ItemId>>>);

impl PersistentItemIds {
    fn track<T: 'static>(entity: &Entity<T>, item_id: ItemId, cx: &mut App) {
        let entity_id = entity.entity_id();
        let ids = cx.default_global::<Self>();
        ids.by_entity.insert(entity_id, item_id);
        ids.by_item.insert(item_id, entity_id);
        ids.live.0.lock().insert(item_id);
        cx.observe_release(entity, move |_, cx| {
            let ids = cx.default_global::<Self>();
            if let Some(item_id) = ids.by_entity.remove(&entity_id) {
                ids.by_item.remove(&item_id);
                ids.live.0.lock().remove(&item_id);
            }
        })
        .detach();
    }

    fn live_item_ids(cx: &mut App) -> LiveItemIds {
        cx.default_global::<Self>().live.clone()
    }

    fn allocate(cx: &mut App) -> ItemId {
        let kvp = KeyValueStore::global(cx);
        let ids = cx.default_global::<Self>();
        loop {
            let epoch = match ids.epoch.filter(|_| ids.next_index != u32::MAX) {
                Some(epoch) => epoch,
                None => ids.start_epoch(&kvp),
            };
            let item_id = (u64::from(epoch) << 33) | u64::from(ids.next_index);
            ids.next_index += 1;
            if !ids.by_item.contains_key(&item_id) {
                return item_id;
            }
        }
    }

    fn start_epoch(&mut self, kvp: &KeyValueStore) -> u32 {
        let epoch = gpui::block_on(kvp.next_counter_value(
            PERSISTENT_ITEM_ID_EPOCH_KEY.to_string(),
            MAX_PERSISTENT_ITEM_ID_EPOCH,
        ))
        .log_err()
        .unwrap_or_else(|| {
            let fallback_epochs = MAX_PERSISTENT_ITEM_ID_EPOCH >> 1;
            (Uuid::new_v4().as_u64_pair().0 as u32 & fallback_epochs) | (fallback_epochs + 1)
        })
        .clamp(1, MAX_PERSISTENT_ITEM_ID_EPOCH);
        self.epoch = Some(epoch);
        self.next_index = 0;
        epoch
    }
}

#[derive(Clone, Default)]
pub(crate) struct RestoringItems(Arc<Mutex<HashMap<(WorkspaceId, ItemId), usize>>>);

impl Global for RestoringItems {}

pub(crate) struct RestoringItemsLease {
    restoring_items: RestoringItems,
    keys: Vec<(WorkspaceId, ItemId)>,
}

impl RestoringItems {
    pub(crate) fn global(cx: &mut App) -> Self {
        cx.default_global::<Self>().clone()
    }

    pub(crate) fn lease(&self, workspace: &SerializedWorkspace) -> RestoringItemsLease {
        let keys = workspace
            .center_group
            .item_ids()
            .into_iter()
            .map(|item_id| (workspace.id, item_id))
            .collect::<Vec<_>>();
        let mut restoring = self.0.lock();
        for key in &keys {
            *restoring.entry(*key).or_default() += 1;
        }
        RestoringItemsLease {
            restoring_items: self.clone(),
            keys,
        }
    }

    fn item_ids(&self, workspace_id: WorkspaceId) -> Vec<ItemId> {
        self.0
            .lock()
            .keys()
            .filter(|(restoring_workspace_id, _)| *restoring_workspace_id == workspace_id)
            .map(|(_, item_id)| *item_id)
            .collect()
    }
}

impl Drop for RestoringItemsLease {
    fn drop(&mut self) {
        let mut restoring = self.restoring_items.0.lock();
        for key in &self.keys {
            if let Some(count) = restoring.get_mut(key) {
                *count -= 1;
                if *count == 0 {
                    restoring.remove(key);
                }
            }
        }
    }
}

#[derive(Clone, Default)]
pub struct WorkspaceIdClaims(Arc<Mutex<ClaimsState>>);

impl Global for WorkspaceIdClaims {}

#[derive(Default)]
struct ClaimsState {
    holders: HashMap<WorkspaceId, Holders>,
    last_changed_at: HashMap<WorkspaceId, u64>,
    generation: u64,
}

#[derive(Default)]
struct Holders {
    shared: usize,
    exclusive: bool,
}

impl ClaimsState {
    fn acquire(&mut self, workspace_id: WorkspaceId, exclusive: bool) {
        let holders = self.holders.entry(workspace_id).or_default();
        if exclusive {
            holders.exclusive = true;
        } else {
            holders.shared += 1;
        }
        self.touch(workspace_id);
    }

    fn release(&mut self, workspace_id: WorkspaceId, exclusive: bool) {
        if let Some(holders) = self.holders.get_mut(&workspace_id) {
            if exclusive {
                holders.exclusive = false;
            } else {
                holders.shared = holders.shared.saturating_sub(1);
            }
            if !holders.exclusive && holders.shared == 0 {
                self.holders.remove(&workspace_id);
            }
        }
        self.touch(workspace_id);
    }

    fn touch(&mut self, workspace_id: WorkspaceId) {
        self.generation += 1;
        self.last_changed_at.insert(workspace_id, self.generation);
    }
}

#[derive(Clone)]
pub struct ClaimsSnapshot {
    claims: WorkspaceIdClaims,
    generation: u64,
}

impl ClaimsSnapshot {
    pub(crate) fn protected(&self) -> ProtectedWorkspaces<'_> {
        ProtectedWorkspaces {
            state: self.claims.0.lock(),
            unchanged_since: Some(self.generation),
        }
    }
}

pub struct WorkspaceIdClaim {
    claims: WorkspaceIdClaims,
    workspace_id: WorkspaceId,
    exclusive: bool,
}

pub(crate) struct ProtectedWorkspaces<'a> {
    state: parking_lot::MutexGuard<'a, ClaimsState>,
    unchanged_since: Option<u64>,
}

impl ProtectedWorkspaces<'_> {
    pub(crate) fn contains(&self, workspace_id: WorkspaceId) -> bool {
        self.state.holders.contains_key(&workspace_id)
            || self.unchanged_since.is_some_and(|since| {
                self.state
                    .last_changed_at
                    .get(&workspace_id)
                    .is_some_and(|changed_at| *changed_at > since)
            })
    }
}

impl WorkspaceIdClaims {
    pub fn global(cx: &mut App) -> Self {
        cx.default_global::<Self>().clone()
    }

    pub fn current(cx: &App) -> Self {
        cx.try_global::<Self>().cloned().unwrap_or_default()
    }

    pub fn try_claim(&self, workspace_id: WorkspaceId) -> Option<WorkspaceIdClaim> {
        let mut state = self.0.lock();
        if state
            .holders
            .get(&workspace_id)
            .is_some_and(|holders| holders.exclusive)
        {
            return None;
        }
        state.acquire(workspace_id, true);
        Some(self.claim(workspace_id, true))
    }

    pub(crate) fn hold(&self, workspace_id: WorkspaceId) -> WorkspaceIdClaim {
        self.0.lock().acquire(workspace_id, false);
        self.claim(workspace_id, false)
    }

    pub(crate) fn claimed(&self) -> HashSet<WorkspaceId> {
        self.0.lock().holders.keys().copied().collect()
    }

    pub fn snapshot(&self) -> ClaimsSnapshot {
        ClaimsSnapshot {
            claims: self.clone(),
            generation: self.0.lock().generation,
        }
    }

    pub(crate) fn protected(&self) -> ProtectedWorkspaces<'_> {
        ProtectedWorkspaces {
            state: self.0.lock(),
            unchanged_since: None,
        }
    }

    fn claim(&self, workspace_id: WorkspaceId, exclusive: bool) -> WorkspaceIdClaim {
        WorkspaceIdClaim {
            claims: self.clone(),
            workspace_id,
            exclusive,
        }
    }
}

impl Drop for WorkspaceIdClaim {
    fn drop(&mut self) {
        self.claims
            .0
            .lock()
            .release(self.workspace_id, self.exclusive);
    }
}

#[derive(Clone, Default)]
pub(crate) struct WorkspaceWrites(Arc<Mutex<HashMap<WorkspaceId, Shared<Task<()>>>>>);

impl Global for WorkspaceWrites {}

impl WorkspaceWrites {
    pub(crate) fn global(cx: &mut App) -> Self {
        cx.default_global::<Self>().clone()
    }

    pub(crate) fn last(&self, workspace_id: WorkspaceId) -> Option<Shared<Task<()>>> {
        self.0
            .lock()
            .get(&workspace_id)
            .filter(|write| write.peek().is_none())
            .cloned()
    }

    pub(crate) fn record(&self, workspace_id: WorkspaceId, write: Shared<Task<()>>) {
        let mut writes = self.0.lock();
        writes.retain(|_, write| write.peek().is_none());
        writes.insert(workspace_id, write);
    }

    pub(crate) async fn settled(&self, workspace_id: WorkspaceId) {
        while let Some(write) = self.last(workspace_id) {
            write.await;
        }
    }

    pub(crate) async fn all_settled(&self) {
        loop {
            let pending = self
                .0
                .lock()
                .values()
                .filter(|write| write.peek().is_none())
                .cloned()
                .collect::<Vec<_>>();
            if pending.is_empty() {
                return;
            }
            futures::future::join_all(pending).await;
        }
    }
}

const MULTI_WORKSPACE_STATE_NAMESPACE: &str = "multi_workspace_state";

pub async fn write_multi_workspace_state(
    kvp: &KeyValueStore,
    session_id: &str,
    window_id: WindowId,
    state: model::MultiWorkspaceState,
) {
    if let Ok(json_str) = serde_json::to_string(&state) {
        kvp.scoped(MULTI_WORKSPACE_STATE_NAMESPACE)
            .write(multi_workspace_state_key(session_id, window_id), json_str)
            .await
            .log_err();
    }
}

pub async fn migrate_legacy_multi_workspace_states(
    kvp: &KeyValueStore,
    last_session_id: Option<&str>,
) {
    kvp.scoped(MULTI_WORKSPACE_STATE_NAMESPACE)
        .prefix_keys_without_separator(
            MULTI_WORKSPACE_STATE_KEY_SEPARATOR,
            last_session_id.map(multi_workspace_state_key_prefix),
        )
        .await
        .log_err();
}

fn read_multi_workspace_state(
    session_id: Option<&str>,
    window_id: WindowId,
    cx: &App,
) -> model::MultiWorkspaceState {
    let kvp = KeyValueStore::global(cx);
    let store = kvp.scoped(MULTI_WORKSPACE_STATE_NAMESPACE);
    session_id
        .and_then(|session_id| {
            store
                .read(&multi_workspace_state_key(session_id, window_id))
                .log_err()
                .flatten()
        })
        .and_then(|json| serde_json::from_str(&json).ok())
        .unwrap_or_default()
}

fn multi_workspace_state_key(session_id: &str, window_id: WindowId) -> String {
    format!(
        "{}{}",
        multi_workspace_state_key_prefix(session_id),
        window_id.as_u64()
    )
}

const MULTI_WORKSPACE_STATE_KEY_SEPARATOR: &str = ":";

const UNAVAILABLE_SESSION_WORKSPACE_RETENTION: chrono::Duration = chrono::Duration::days(7);
const MAX_RESTORE_ATTEMPTS: u32 = 2;
const LOCKED_RETRIES: usize = 100;
const LOCKED_RETRY_DELAY: std::time::Duration = std::time::Duration::from_millis(1);

fn parse_multi_workspace_state_key(key: &str) -> Option<(&str, u64)> {
    let (session_id, window_id) = key.rsplit_once(MULTI_WORKSPACE_STATE_KEY_SEPARATOR)?;
    Some((session_id, window_id.parse().ok()?))
}

fn retry_table_locks<T>(mut operation: impl FnMut() -> Result<T>) -> Result<T> {
    let mut attempt = 0;
    loop {
        match operation() {
            Err(error) if attempt < LOCKED_RETRIES && is_table_lock_error(&error) => {
                attempt += 1;
                std::thread::sleep(LOCKED_RETRY_DELAY);
            }
            result => return result,
        }
    }
}

fn is_table_lock_error(error: &anyhow::Error) -> bool {
    format!("{error:#}").contains("database table is locked")
}

fn lossy_text(bytes: Vec<u8>) -> String {
    String::from_utf8(bytes)
        .unwrap_or_else(|error| String::from_utf8_lossy(error.as_bytes()).into_owned())
}

fn multi_workspace_state_key_prefix(session_id: &str) -> String {
    format!("{session_id}{MULTI_WORKSPACE_STATE_KEY_SEPARATOR}")
}

pub fn read_serialized_multi_workspaces(
    session_workspaces: Vec<model::SessionWorkspace>,
    cx: &App,
) -> Task<Vec<model::SerializedMultiWorkspace>> {
    let db = WorkspaceDb::global(cx);
    let mut detached_from_windows = Vec::new();
    let mut window_groups: Vec<Vec<model::SessionWorkspace>> = Vec::new();
    let mut window_id_to_group: HashMap<(Option<String>, WindowId), usize> = HashMap::default();

    for session_workspace in session_workspaces {
        match session_workspace.window_id {
            Some(window_id) => {
                let group_index = *window_id_to_group
                    .entry((session_workspace.session_id.clone(), window_id))
                    .or_insert_with(|| {
                        window_groups.push(Vec::new());
                        window_groups.len() - 1
                    });
                window_groups[group_index].push(session_workspace);
            }
            None => {
                window_groups.push(vec![session_workspace]);
            }
        }
    }

    let windows = window_groups
        .into_iter()
        .flat_map(|group| {
            let state = group
                .first()
                .and_then(|session_workspace| {
                    Some(read_multi_workspace_state(
                        session_workspace.session_id.as_deref(),
                        session_workspace.window_id?,
                        cx,
                    ))
                })
                .unwrap_or_default();
            let active_index = state
                .active_workspace_id
                .and_then(|id| group.iter().position(|ws| ws.workspace_id == id))
                // If the persisted active workspace can't be matched (e.g. its
                // pointer was lost or its row was pruned), fall back to the
                // first workspace that actually has paths rather than blindly
                // taking index 0, so a stray scratch/empty workspace isn't
                // restored as the focused window. Only if none have paths do we
                // fall back to the first entry.
                .or_else(|| group.iter().position(|ws| !ws.paths.is_empty()))
                .unwrap_or(0);
            let members = group
                .iter()
                .map(|member| WindowMember {
                    workspace_id: member.workspace_id,
                    location: member.location.clone(),
                    restorable_paths: member.paths.clone(),
                    has_items: db
                        .workspace_has_items(member.workspace_id)
                        .log_err()
                        .flatten()
                        .unwrap_or(false),
                })
                .collect::<Vec<_>>();
            let mut windows = Vec::new();
            let mut active_workspace = None;
            for (index, (mut session_workspace, member)) in
                group.into_iter().zip(&members).enumerate()
            {
                if index == active_index {
                    active_workspace = Some(session_workspace);
                } else if restores_in_own_window(member, &members) {
                    if session_workspace.window_id.is_some() {
                        detached_from_windows
                            .push((session_workspace.workspace_id, session_workspace.binding()));
                        session_workspace.window_id = None;
                    }
                    windows.push(model::SerializedMultiWorkspace {
                        active_workspace: session_workspace,
                        state: model::MultiWorkspaceState::default(),
                    });
                }
            }
            windows.extend(active_workspace.map(|active_workspace| {
                model::SerializedMultiWorkspace {
                    active_workspace,
                    state,
                }
            }));
            windows
        })
        .collect::<Vec<_>>();
    cx.background_spawn(async move {
        if !detached_from_windows.is_empty() {
            db.detach_from_session_windows(detached_from_windows)
                .await
                .log_err();
        }
        windows
    })
}

const DEFAULT_DOCK_STATE_KEY: &str = "default_dock_state";

pub fn read_default_dock_state(kvp: &KeyValueStore) -> Option<DockStructure> {
    let json_str = kvp.read_kvp(DEFAULT_DOCK_STATE_KEY).log_err().flatten()?;

    serde_json::from_str::<DockStructure>(&json_str).ok()
}

pub async fn write_default_dock_state(
    kvp: &KeyValueStore,
    docks: DockStructure,
) -> anyhow::Result<()> {
    let json_str = serde_json::to_string(&docks)?;
    kvp.write_kvp(DEFAULT_DOCK_STATE_KEY.to_string(), json_str)
        .await?;
    Ok(())
}

#[derive(Debug)]
pub struct Bookmark {
    pub row: u32,
    pub label: String,
}

impl sqlez::bindable::StaticColumnCount for Bookmark {
    fn column_count() -> usize {
        // row, label
        2
    }
}

impl sqlez::bindable::Bind for Bookmark {
    fn bind(
        &self,
        statement: &sqlez::statement::Statement,
        start_index: i32,
    ) -> anyhow::Result<i32> {
        let next_index = statement.bind(&self.row, start_index)?;
        statement.bind(&self.label, next_index)
    }
}

impl Column for Bookmark {
    fn column(statement: &mut Statement, start_index: i32) -> Result<(Self, i32)> {
        let row = statement
            .column_int(start_index)
            .with_context(|| format!("Failed to read bookmark at index {start_index}"))?
            as u32;

        let (label, next_index) = String::column(statement, start_index + 1)?;

        Ok((Bookmark { row, label }, next_index))
    }
}

#[derive(Debug)]
pub struct Breakpoint {
    pub position: u32,
    pub message: Option<Arc<str>>,
    pub condition: Option<Arc<str>>,
    pub hit_condition: Option<Arc<str>>,
    pub state: BreakpointState,
}

/// Wrapper for DB type of a breakpoint
struct BreakpointStateWrapper<'a>(Cow<'a, BreakpointState>);

impl From<BreakpointState> for BreakpointStateWrapper<'static> {
    fn from(kind: BreakpointState) -> Self {
        BreakpointStateWrapper(Cow::Owned(kind))
    }
}

impl StaticColumnCount for BreakpointStateWrapper<'_> {
    fn column_count() -> usize {
        1
    }
}

impl Bind for BreakpointStateWrapper<'_> {
    fn bind(&self, statement: &Statement, start_index: i32) -> anyhow::Result<i32> {
        statement.bind(&self.0.to_int(), start_index)
    }
}

impl Column for BreakpointStateWrapper<'_> {
    fn column(statement: &mut Statement, start_index: i32) -> anyhow::Result<(Self, i32)> {
        let state = statement.column_int(start_index)?;

        match state {
            0 => Ok((BreakpointState::Enabled.into(), start_index + 1)),
            1 => Ok((BreakpointState::Disabled.into(), start_index + 1)),
            _ => anyhow::bail!("Invalid BreakpointState discriminant {state}"),
        }
    }
}

impl sqlez::bindable::StaticColumnCount for Breakpoint {
    fn column_count() -> usize {
        // Position, log message, condition message, and hit condition message
        4 + BreakpointStateWrapper::column_count()
    }
}

impl sqlez::bindable::Bind for Breakpoint {
    fn bind(
        &self,
        statement: &sqlez::statement::Statement,
        start_index: i32,
    ) -> anyhow::Result<i32> {
        let next_index = statement.bind(&self.position, start_index)?;
        let next_index = statement.bind(&self.message, next_index)?;
        let next_index = statement.bind(&self.condition, next_index)?;
        let next_index = statement.bind(&self.hit_condition, next_index)?;
        statement.bind(
            &BreakpointStateWrapper(Cow::Borrowed(&self.state)),
            next_index,
        )
    }
}

impl Column for Breakpoint {
    fn column(statement: &mut Statement, start_index: i32) -> Result<(Self, i32)> {
        let position = statement
            .column_int(start_index)
            .with_context(|| format!("Failed to read BreakPoint at index {start_index}"))?
            as u32;
        let (message, next_index) = Option::<String>::column(statement, start_index + 1)?;
        let (condition, next_index) = Option::<String>::column(statement, next_index)?;
        let (hit_condition, next_index) = Option::<String>::column(statement, next_index)?;
        let (state, next_index) = BreakpointStateWrapper::column(statement, next_index)?;

        Ok((
            Breakpoint {
                position,
                message: message.map(Arc::from),
                condition: condition.map(Arc::from),
                hit_condition: hit_condition.map(Arc::from),
                state: state.0.into_owned(),
            },
            next_index,
        ))
    }
}

#[derive(Clone, Debug, PartialEq)]
struct SerializedPixels(gpui::Pixels);
impl sqlez::bindable::StaticColumnCount for SerializedPixels {}

impl sqlez::bindable::Bind for SerializedPixels {
    fn bind(
        &self,
        statement: &sqlez::statement::Statement,
        start_index: i32,
    ) -> anyhow::Result<i32> {
        let this: i32 = u32::from(self.0) as _;
        this.bind(statement, start_index)
    }
}

pub struct WorkspaceDb(ThreadSafeConnection);

impl Domain for WorkspaceDb {
    const NAME: &str = stringify!(WorkspaceDb);

    const MIGRATIONS: &[&str] = &[
        sql!(
            CREATE TABLE workspaces(
                workspace_id INTEGER PRIMARY KEY,
                workspace_location BLOB UNIQUE,
                dock_visible INTEGER, // Deprecated. Preserving so users can downgrade Zed.
                dock_anchor TEXT, // Deprecated. Preserving so users can downgrade Zed.
                dock_pane INTEGER, // Deprecated.  Preserving so users can downgrade Zed.
                left_sidebar_open INTEGER, // Boolean
                timestamp TEXT DEFAULT CURRENT_TIMESTAMP NOT NULL,
                FOREIGN KEY(dock_pane) REFERENCES panes(pane_id)
            ) STRICT;

            CREATE TABLE pane_groups(
                group_id INTEGER PRIMARY KEY,
                workspace_id INTEGER NOT NULL,
                parent_group_id INTEGER, // NULL indicates that this is a root node
                position INTEGER, // NULL indicates that this is a root node
                axis TEXT NOT NULL, // Enum: 'Vertical' / 'Horizontal'
                FOREIGN KEY(workspace_id) REFERENCES workspaces(workspace_id)
                ON DELETE CASCADE
                ON UPDATE CASCADE,
                FOREIGN KEY(parent_group_id) REFERENCES pane_groups(group_id) ON DELETE CASCADE
            ) STRICT;

            CREATE TABLE panes(
                pane_id INTEGER PRIMARY KEY,
                workspace_id INTEGER NOT NULL,
                active INTEGER NOT NULL, // Boolean
                FOREIGN KEY(workspace_id) REFERENCES workspaces(workspace_id)
                ON DELETE CASCADE
                ON UPDATE CASCADE
            ) STRICT;

            CREATE TABLE center_panes(
                pane_id INTEGER PRIMARY KEY,
                parent_group_id INTEGER, // NULL means that this is a root pane
                position INTEGER, // NULL means that this is a root pane
                FOREIGN KEY(pane_id) REFERENCES panes(pane_id)
                ON DELETE CASCADE,
                FOREIGN KEY(parent_group_id) REFERENCES pane_groups(group_id) ON DELETE CASCADE
            ) STRICT;

            CREATE TABLE items(
                item_id INTEGER NOT NULL, // This is the item's view id, so this is not unique
                workspace_id INTEGER NOT NULL,
                pane_id INTEGER NOT NULL,
                kind TEXT NOT NULL,
                position INTEGER NOT NULL,
                active INTEGER NOT NULL,
                FOREIGN KEY(workspace_id) REFERENCES workspaces(workspace_id)
                ON DELETE CASCADE
                ON UPDATE CASCADE,
                FOREIGN KEY(pane_id) REFERENCES panes(pane_id)
                ON DELETE CASCADE,
                PRIMARY KEY(item_id, workspace_id)
            ) STRICT;
        ),
        sql!(
            ALTER TABLE workspaces ADD COLUMN window_state TEXT;
            ALTER TABLE workspaces ADD COLUMN window_x REAL;
            ALTER TABLE workspaces ADD COLUMN window_y REAL;
            ALTER TABLE workspaces ADD COLUMN window_width REAL;
            ALTER TABLE workspaces ADD COLUMN window_height REAL;
            ALTER TABLE workspaces ADD COLUMN display BLOB;
        ),
        // Drop foreign key constraint from workspaces.dock_pane to panes table.
        sql!(
            CREATE TABLE workspaces_2(
                workspace_id INTEGER PRIMARY KEY,
                workspace_location BLOB UNIQUE,
                dock_visible INTEGER, // Deprecated. Preserving so users can downgrade Zed.
                dock_anchor TEXT, // Deprecated. Preserving so users can downgrade Zed.
                dock_pane INTEGER, // Deprecated.  Preserving so users can downgrade Zed.
                left_sidebar_open INTEGER, // Boolean
                timestamp TEXT DEFAULT CURRENT_TIMESTAMP NOT NULL,
                window_state TEXT,
                window_x REAL,
                window_y REAL,
                window_width REAL,
                window_height REAL,
                display BLOB
            ) STRICT;
            INSERT INTO workspaces_2 SELECT * FROM workspaces;
            DROP TABLE workspaces;
            ALTER TABLE workspaces_2 RENAME TO workspaces;
        ),
        // Add panels related information
        sql!(
            ALTER TABLE workspaces ADD COLUMN left_dock_visible INTEGER; //bool
            ALTER TABLE workspaces ADD COLUMN left_dock_active_panel TEXT;
            ALTER TABLE workspaces ADD COLUMN right_dock_visible INTEGER; //bool
            ALTER TABLE workspaces ADD COLUMN right_dock_active_panel TEXT;
            ALTER TABLE workspaces ADD COLUMN bottom_dock_visible INTEGER; //bool
            ALTER TABLE workspaces ADD COLUMN bottom_dock_active_panel TEXT;
        ),
        // Add panel zoom persistence
        sql!(
            ALTER TABLE workspaces ADD COLUMN left_dock_zoom INTEGER; //bool
            ALTER TABLE workspaces ADD COLUMN right_dock_zoom INTEGER; //bool
            ALTER TABLE workspaces ADD COLUMN bottom_dock_zoom INTEGER; //bool
        ),
        // Add pane group flex data
        sql!(
            ALTER TABLE pane_groups ADD COLUMN flexes TEXT;
        ),
        // Add fullscreen field to workspace
        // Deprecated, `WindowBounds` holds the fullscreen state now.
        // Preserving so users can downgrade Zed.
        sql!(
            ALTER TABLE workspaces ADD COLUMN fullscreen INTEGER; //bool
        ),
        // Add preview field to items
        sql!(
            ALTER TABLE items ADD COLUMN preview INTEGER; //bool
        ),
        // Add centered_layout field to workspace
        sql!(
            ALTER TABLE workspaces ADD COLUMN centered_layout INTEGER; //bool
        ),
        sql!(
            CREATE TABLE remote_projects (
                remote_project_id INTEGER NOT NULL UNIQUE,
                path TEXT,
                dev_server_name TEXT
            );
            ALTER TABLE workspaces ADD COLUMN remote_project_id INTEGER;
            ALTER TABLE workspaces RENAME COLUMN workspace_location TO local_paths;
        ),
        sql!(
            DROP TABLE remote_projects;
            CREATE TABLE dev_server_projects (
                id INTEGER NOT NULL UNIQUE,
                path TEXT,
                dev_server_name TEXT
            );
            ALTER TABLE workspaces DROP COLUMN remote_project_id;
            ALTER TABLE workspaces ADD COLUMN dev_server_project_id INTEGER;
        ),
        sql!(
            ALTER TABLE workspaces ADD COLUMN local_paths_order BLOB;
        ),
        sql!(
            ALTER TABLE workspaces ADD COLUMN session_id TEXT DEFAULT NULL;
        ),
        sql!(
            ALTER TABLE workspaces ADD COLUMN window_id INTEGER DEFAULT NULL;
        ),
        sql!(
            ALTER TABLE panes ADD COLUMN pinned_count INTEGER DEFAULT 0;
        ),
        sql!(
            CREATE TABLE ssh_projects (
                id INTEGER PRIMARY KEY,
                host TEXT NOT NULL,
                port INTEGER,
                path TEXT NOT NULL,
                user TEXT
            );
            ALTER TABLE workspaces ADD COLUMN ssh_project_id INTEGER REFERENCES ssh_projects(id) ON DELETE CASCADE;
        ),
        sql!(
            ALTER TABLE ssh_projects RENAME COLUMN path TO paths;
        ),
        sql!(
            CREATE TABLE toolchains (
                workspace_id INTEGER,
                worktree_id INTEGER,
                language_name TEXT NOT NULL,
                name TEXT NOT NULL,
                path TEXT NOT NULL,
                PRIMARY KEY (workspace_id, worktree_id, language_name)
            );
        ),
        sql!(
            ALTER TABLE toolchains ADD COLUMN raw_json TEXT DEFAULT "{}";
        ),
        sql!(
            CREATE TABLE breakpoints (
                workspace_id INTEGER NOT NULL,
                path TEXT NOT NULL,
                breakpoint_location INTEGER NOT NULL,
                kind INTEGER NOT NULL,
                log_message TEXT,
                FOREIGN KEY(workspace_id) REFERENCES workspaces(workspace_id)
                ON DELETE CASCADE
                ON UPDATE CASCADE
            );
        ),
        sql!(
            ALTER TABLE workspaces ADD COLUMN local_paths_array TEXT;
            CREATE UNIQUE INDEX local_paths_array_uq ON workspaces(local_paths_array);
            ALTER TABLE workspaces ADD COLUMN local_paths_order_array TEXT;
        ),
        sql!(
            ALTER TABLE breakpoints ADD COLUMN state INTEGER DEFAULT(0) NOT NULL
        ),
        sql!(
            ALTER TABLE breakpoints DROP COLUMN kind
        ),
        sql!(ALTER TABLE toolchains ADD COLUMN relative_worktree_path TEXT DEFAULT "" NOT NULL),
        sql!(
            ALTER TABLE breakpoints ADD COLUMN condition TEXT;
            ALTER TABLE breakpoints ADD COLUMN hit_condition TEXT;
        ),
        sql!(CREATE TABLE toolchains2 (
            workspace_id INTEGER,
            worktree_id INTEGER,
            language_name TEXT NOT NULL,
            name TEXT NOT NULL,
            path TEXT NOT NULL,
            raw_json TEXT NOT NULL,
            relative_worktree_path TEXT NOT NULL,
            PRIMARY KEY (workspace_id, worktree_id, language_name, relative_worktree_path)) STRICT;
            INSERT INTO toolchains2
                SELECT * FROM toolchains;
            DROP TABLE toolchains;
            ALTER TABLE toolchains2 RENAME TO toolchains;
        ),
        sql!(
            CREATE TABLE ssh_connections (
                id INTEGER PRIMARY KEY,
                host TEXT NOT NULL,
                port INTEGER,
                user TEXT
            );

            INSERT INTO ssh_connections (host, port, user)
            SELECT DISTINCT host, port, user
            FROM ssh_projects;

            CREATE TABLE workspaces_2(
                workspace_id INTEGER PRIMARY KEY,
                paths TEXT,
                paths_order TEXT,
                ssh_connection_id INTEGER REFERENCES ssh_connections(id),
                timestamp TEXT DEFAULT CURRENT_TIMESTAMP NOT NULL,
                window_state TEXT,
                window_x REAL,
                window_y REAL,
                window_width REAL,
                window_height REAL,
                display BLOB,
                left_dock_visible INTEGER,
                left_dock_active_panel TEXT,
                right_dock_visible INTEGER,
                right_dock_active_panel TEXT,
                bottom_dock_visible INTEGER,
                bottom_dock_active_panel TEXT,
                left_dock_zoom INTEGER,
                right_dock_zoom INTEGER,
                bottom_dock_zoom INTEGER,
                fullscreen INTEGER,
                centered_layout INTEGER,
                session_id TEXT,
                window_id INTEGER
            ) STRICT;

            INSERT
            INTO workspaces_2
            SELECT
                workspaces.workspace_id,
                CASE
                    WHEN ssh_projects.id IS NOT NULL THEN ssh_projects.paths
                    ELSE
                        CASE
                            WHEN workspaces.local_paths_array IS NULL OR workspaces.local_paths_array = "" THEN
                                NULL
                            ELSE
                                replace(workspaces.local_paths_array, ',', CHAR(10))
                        END
                END as paths,

                CASE
                    WHEN ssh_projects.id IS NOT NULL THEN ""
                    ELSE workspaces.local_paths_order_array
                END as paths_order,

                CASE
                    WHEN ssh_projects.id IS NOT NULL THEN (
                        SELECT ssh_connections.id
                        FROM ssh_connections
                        WHERE
                            ssh_connections.host IS ssh_projects.host AND
                            ssh_connections.port IS ssh_projects.port AND
                            ssh_connections.user IS ssh_projects.user
                    )
                    ELSE NULL
                END as ssh_connection_id,

                workspaces.timestamp,
                workspaces.window_state,
                workspaces.window_x,
                workspaces.window_y,
                workspaces.window_width,
                workspaces.window_height,
                workspaces.display,
                workspaces.left_dock_visible,
                workspaces.left_dock_active_panel,
                workspaces.right_dock_visible,
                workspaces.right_dock_active_panel,
                workspaces.bottom_dock_visible,
                workspaces.bottom_dock_active_panel,
                workspaces.left_dock_zoom,
                workspaces.right_dock_zoom,
                workspaces.bottom_dock_zoom,
                workspaces.fullscreen,
                workspaces.centered_layout,
                workspaces.session_id,
                workspaces.window_id
            FROM
                workspaces LEFT JOIN
                ssh_projects ON
                workspaces.ssh_project_id = ssh_projects.id;

            DELETE FROM workspaces_2
            WHERE workspace_id NOT IN (
                SELECT MAX(workspace_id)
                FROM workspaces_2
                GROUP BY ssh_connection_id, paths
            );

            DROP TABLE ssh_projects;
            DROP TABLE workspaces;
            ALTER TABLE workspaces_2 RENAME TO workspaces;

            CREATE UNIQUE INDEX ix_workspaces_location ON workspaces(ssh_connection_id, paths);
        ),
        // Fix any data from when workspaces.paths were briefly encoded as JSON arrays
        sql!(
            UPDATE workspaces
            SET paths = CASE
                WHEN substr(paths, 1, 2) = '[' || '"' AND substr(paths, -2, 2) = '"' || ']' THEN
                    replace(
                        substr(paths, 3, length(paths) - 4),
                        '"' || ',' || '"',
                        CHAR(10)
                    )
                ELSE
                    replace(paths, ',', CHAR(10))
            END
            WHERE paths IS NOT NULL
        ),
        sql!(
            CREATE TABLE remote_connections(
                id INTEGER PRIMARY KEY,
                kind TEXT NOT NULL,
                host TEXT,
                port INTEGER,
                user TEXT,
                distro TEXT
            );

            CREATE TABLE workspaces_2(
                workspace_id INTEGER PRIMARY KEY,
                paths TEXT,
                paths_order TEXT,
                remote_connection_id INTEGER REFERENCES remote_connections(id),
                timestamp TEXT DEFAULT CURRENT_TIMESTAMP NOT NULL,
                window_state TEXT,
                window_x REAL,
                window_y REAL,
                window_width REAL,
                window_height REAL,
                display BLOB,
                left_dock_visible INTEGER,
                left_dock_active_panel TEXT,
                right_dock_visible INTEGER,
                right_dock_active_panel TEXT,
                bottom_dock_visible INTEGER,
                bottom_dock_active_panel TEXT,
                left_dock_zoom INTEGER,
                right_dock_zoom INTEGER,
                bottom_dock_zoom INTEGER,
                fullscreen INTEGER,
                centered_layout INTEGER,
                session_id TEXT,
                window_id INTEGER
            ) STRICT;

            INSERT INTO remote_connections
            SELECT
                id,
                "ssh" as kind,
                host,
                port,
                user,
                NULL as distro
            FROM ssh_connections;

            INSERT
            INTO workspaces_2
            SELECT
                workspace_id,
                paths,
                paths_order,
                ssh_connection_id as remote_connection_id,
                timestamp,
                window_state,
                window_x,
                window_y,
                window_width,
                window_height,
                display,
                left_dock_visible,
                left_dock_active_panel,
                right_dock_visible,
                right_dock_active_panel,
                bottom_dock_visible,
                bottom_dock_active_panel,
                left_dock_zoom,
                right_dock_zoom,
                bottom_dock_zoom,
                fullscreen,
                centered_layout,
                session_id,
                window_id
            FROM
                workspaces;

            DROP TABLE workspaces;
            ALTER TABLE workspaces_2 RENAME TO workspaces;

            CREATE UNIQUE INDEX ix_workspaces_location ON workspaces(remote_connection_id, paths);
        ),
        sql!(CREATE TABLE user_toolchains (
            remote_connection_id INTEGER,
            workspace_id INTEGER NOT NULL,
            worktree_id INTEGER NOT NULL,
            relative_worktree_path TEXT NOT NULL,
            language_name TEXT NOT NULL,
            name TEXT NOT NULL,
            path TEXT NOT NULL,
            raw_json TEXT NOT NULL,

            PRIMARY KEY (workspace_id, worktree_id, relative_worktree_path, language_name, name, path, raw_json)
        ) STRICT;),
        sql!(
            DROP TABLE ssh_connections;
        ),
        sql!(
            ALTER TABLE remote_connections ADD COLUMN name TEXT;
            ALTER TABLE remote_connections ADD COLUMN container_id TEXT;
        ),
        sql!(
            CREATE TABLE IF NOT EXISTS trusted_worktrees (
                trust_id INTEGER PRIMARY KEY AUTOINCREMENT,
                absolute_path TEXT,
                user_name TEXT,
                host_name TEXT
            ) STRICT;
        ),
        sql!(CREATE TABLE toolchains2 (
            workspace_id INTEGER,
            worktree_root_path TEXT NOT NULL,
            language_name TEXT NOT NULL,
            name TEXT NOT NULL,
            path TEXT NOT NULL,
            raw_json TEXT NOT NULL,
            relative_worktree_path TEXT NOT NULL,
            PRIMARY KEY (workspace_id, worktree_root_path, language_name, relative_worktree_path)) STRICT;
            INSERT OR REPLACE INTO toolchains2
                // The `instr(paths, '\n') = 0` part allows us to find all
                // workspaces that have a single worktree, as `\n` is used as a
                // separator when serializing the workspace paths, so if no `\n` is
                // found, we know we have a single worktree.
                SELECT toolchains.workspace_id, paths, language_name, name, path, raw_json, relative_worktree_path FROM toolchains INNER JOIN workspaces ON toolchains.workspace_id = workspaces.workspace_id AND instr(paths, '\n') = 0;
            DROP TABLE toolchains;
            ALTER TABLE toolchains2 RENAME TO toolchains;
        ),
        sql!(CREATE TABLE user_toolchains2 (
            remote_connection_id INTEGER,
            workspace_id INTEGER NOT NULL,
            worktree_root_path TEXT NOT NULL,
            relative_worktree_path TEXT NOT NULL,
            language_name TEXT NOT NULL,
            name TEXT NOT NULL,
            path TEXT NOT NULL,
            raw_json TEXT NOT NULL,

            PRIMARY KEY (workspace_id, worktree_root_path, relative_worktree_path, language_name, name, path, raw_json)) STRICT;
            INSERT OR REPLACE INTO user_toolchains2
                // The `instr(paths, '\n') = 0` part allows us to find all
                // workspaces that have a single worktree, as `\n` is used as a
                // separator when serializing the workspace paths, so if no `\n` is
                // found, we know we have a single worktree.
                SELECT user_toolchains.remote_connection_id, user_toolchains.workspace_id, paths, relative_worktree_path, language_name, name, path, raw_json  FROM user_toolchains INNER JOIN workspaces ON user_toolchains.workspace_id = workspaces.workspace_id AND instr(paths, '\n') = 0;
            DROP TABLE user_toolchains;
            ALTER TABLE user_toolchains2 RENAME TO user_toolchains;
        ),
        sql!(
            ALTER TABLE remote_connections ADD COLUMN use_podman BOOLEAN;
        ),
        sql!(
            ALTER TABLE remote_connections ADD COLUMN remote_env TEXT;
        ),
        sql!(
            CREATE TABLE bookmarks (
                workspace_id INTEGER NOT NULL,
                path TEXT NOT NULL,
                row INTEGER NOT NULL,
                FOREIGN KEY(workspace_id) REFERENCES workspaces(workspace_id)
                ON DELETE CASCADE
                ON UPDATE CASCADE
            );
        ),
        sql!(
            ALTER TABLE workspaces ADD COLUMN identity_paths TEXT;
            ALTER TABLE workspaces ADD COLUMN identity_paths_order TEXT;
        ),
        sql!(
            ALTER TABLE bookmarks ADD COLUMN label TEXT NOT NULL DEFAULT "";
        ),
        sql!(
            CREATE TABLE recent_navigation_history (
                workspace_id INTEGER NOT NULL,
                path BLOB NOT NULL,
                position INTEGER NOT NULL,
                PRIMARY KEY (workspace_id, path),
                FOREIGN KEY(workspace_id) REFERENCES workspaces(workspace_id)
                ON DELETE CASCADE
                ON UPDATE CASCADE
            ) STRICT;
        ),
        sql!(
            ALTER TABLE workspaces ADD COLUMN native_window_state BLOB;
        ),
        sql!(
            CREATE TABLE items_2(
                item_id INTEGER NOT NULL,
                workspace_id INTEGER NOT NULL,
                pane_id INTEGER NOT NULL,
                kind TEXT NOT NULL,
                position INTEGER NOT NULL,
                active INTEGER NOT NULL,
                preview INTEGER,
                FOREIGN KEY(workspace_id) REFERENCES workspaces(workspace_id)
                ON DELETE CASCADE
                ON UPDATE CASCADE,
                FOREIGN KEY(pane_id) REFERENCES panes(pane_id)
                ON DELETE CASCADE,
                PRIMARY KEY(item_id, workspace_id, kind)
            ) STRICT;
            INSERT INTO items_2(item_id, workspace_id, pane_id, kind, position, active, preview)
                SELECT item_id, workspace_id, pane_id, kind, position, active, preview FROM items;
            DROP TABLE items;
            ALTER TABLE items_2 RENAME TO items;
        ),
        sql!(
            ALTER TABLE workspaces ADD COLUMN unserialized_root_files TEXT;
        ),
        sql!(
            ALTER TABLE workspaces ADD COLUMN active_unserialized_root_file BLOB;
        ),
        sql!(
            DROP INDEX IF EXISTS ix_workspaces_location;
            CREATE INDEX ix_workspaces_location ON workspaces(remote_connection_id, paths);
        ),
        sql!(
            ALTER TABLE remote_connections ADD COLUMN args TEXT;
        ),
        sql!(
            ALTER TABLE items ADD COLUMN unrestored_since INTEGER;
        ),
        sql!(
            ALTER TABLE items DROP COLUMN unrestored_since;
            ALTER TABLE workspaces ADD COLUMN restore_failures INTEGER NOT NULL DEFAULT 0;
            ALTER TABLE workspaces ADD COLUMN roots_unavailable_since INTEGER;
        ),
        sql!(
            CREATE TABLE remote_unavailable_roots(
                workspace_id INTEGER NOT NULL,
                root BLOB NOT NULL,
                since INTEGER NOT NULL,
                PRIMARY KEY(workspace_id, root),
                FOREIGN KEY(workspace_id) REFERENCES workspaces(workspace_id)
                ON DELETE CASCADE
                ON UPDATE CASCADE
            ) STRICT;
        ),
        sql!(
            CREATE TABLE ssh_connection_settings(
                key TEXT PRIMARY KEY,
                value TEXT NOT NULL
            ) STRICT;
        ),
        sql!(
            ALTER TABLE remote_unavailable_roots RENAME TO unavailable_roots;
            WITH RECURSIVE split(workspace_id, since, root, rest) AS (
                SELECT workspace_id, roots_unavailable_since, NULL, paths || CHAR(10)
                FROM workspaces
                WHERE roots_unavailable_since IS NOT NULL
                    AND remote_connection_id IS NULL
                    AND (length(paths) > 0)
                UNION ALL
                SELECT
                    workspace_id,
                    since,
                    substr(rest, 1, instr(rest, CHAR(10)) - 1),
                    substr(rest, instr(rest, CHAR(10)) + 1)
                FROM split
                WHERE length(rest) > 0
            )
            INSERT OR IGNORE INTO unavailable_roots(workspace_id, root, since)
            SELECT workspace_id, CAST(root AS BLOB), since
            FROM split
            WHERE length(root) > 0;
            ALTER TABLE workspaces DROP COLUMN roots_unavailable_since;
        ),
    ];

    // Allow recovering from bad migration that was initially shipped to nightly
    // when introducing the ssh_connections table.
    fn should_allow_migration_change(_index: usize, old: &str, new: &str) -> bool {
        old.starts_with("CREATE TABLE ssh_connections")
            && new.starts_with("CREATE TABLE ssh_connections")
    }
}

db::static_connection!(WorkspaceDb, []);

impl WorkspaceDb {
    /// Returns a serialized workspace for the given worktree_roots. If the passed array
    /// is empty, the most recent workspace is returned instead. If no workspace for the
    /// passed roots is stored, returns none.
    #[cfg(test)]
    pub(crate) fn workspace_for_roots<P: AsRef<Path>>(
        &self,
        worktree_roots: &[P],
    ) -> Option<SerializedWorkspace> {
        self.workspace_for_roots_internal(worktree_roots, None)
    }

    pub(crate) fn remote_workspace_for_roots<P: AsRef<Path>>(
        &self,
        worktree_roots: &[P],
        remote_connection_ids: &[RemoteConnectionId],
    ) -> Option<SerializedWorkspace> {
        self.workspace_for_roots_internal(worktree_roots, Some(remote_connection_ids))
    }

    pub(crate) fn workspace_for_roots_internal<P: AsRef<Path>>(
        &self,
        worktree_roots: &[P],
        remote_connection_ids: Option<&[RemoteConnectionId]>,
    ) -> Option<SerializedWorkspace> {
        Self::workspace_ids_for_roots(self, &PathList::new(worktree_roots), remote_connection_ids)
            .log_err()
            .unwrap_or_default()
            .into_iter()
            .find_map(|workspace_id| self.workspace_for_id(workspace_id))
    }

    pub(crate) async fn claim_settled_workspace_for_roots<P: AsRef<Path>>(
        &self,
        worktree_roots: &[P],
        remote_connection_ids: Option<&[RemoteConnectionId]>,
        mut claim_unopened: impl FnMut(WorkspaceId) -> Option<WorkspaceIdClaim>,
        writes: &WorkspaceWrites,
    ) -> Result<Option<(SerializedWorkspace, WorkspaceIdClaim)>> {
        // paths are sorted before db interactions to ensure that the order of the paths
        // doesn't affect the workspace selection for existing workspaces
        let root_paths = PathList::new(worktree_roots);
        let workspace_ids = self
            .write({
                let root_paths = root_paths.clone();
                let remote_connection_ids = remote_connection_ids.map(<[_]>::to_vec);
                move |conn| {
                    retry_table_locks(|| {
                        Self::workspace_ids_for_roots(
                            conn,
                            &root_paths,
                            remote_connection_ids.as_deref(),
                        )
                    })
                }
            })
            .await?;
        for workspace_id in workspace_ids {
            let Some(claim) = claim_unopened(workspace_id) else {
                continue;
            };
            if let Some(workspace) = self
                .settled_workspace_for_id(workspace_id, writes)
                .await?
                .filter(|workspace| workspace.paths.paths() == root_paths.paths())
            {
                return Ok(Some((workspace, claim)));
            }
        }
        Ok(None)
    }

    pub(crate) async fn settled_workspace_for_id(
        &self,
        workspace_id: WorkspaceId,
        writes: &WorkspaceWrites,
    ) -> Result<Option<SerializedWorkspace>> {
        writes.settled(workspace_id).await;
        self.read_workspace_for_id(workspace_id).await
    }

    fn workspace_ids_for_roots(
        conn: &Connection,
        root_paths: &PathList,
        remote_connection_ids: Option<&[RemoteConnectionId]>,
    ) -> Result<Vec<WorkspaceId>> {
        // Empty workspaces cannot be matched by paths (all empty workspaces have paths = "").
        // They should only be restored via workspace_for_id during session restoration.
        if root_paths.is_empty() {
            return Ok(Vec::new());
        }

        maybe!({
            let remote_connection_ids = match remote_connection_ids {
                Some(remote_connection_ids) => {
                    remote_connection_ids.iter().copied().map(Some).collect()
                }
                None => vec![None],
            };
            let mut select_workspaces = conn
                .select_bound::<(String, Option<i32>), (WorkspaceId, Lenient<Option<String>>)>(
                    sql! {
                        SELECT workspace_id, timestamp
                        FROM workspaces
                        WHERE
                            paths IS ? AND
                            remote_connection_id IS ?
                    },
                )?;
            let mut workspaces = Vec::new();
            for remote_connection_id in remote_connection_ids {
                workspaces.extend(
                    select_workspaces((
                        root_paths.serialize().paths,
                        remote_connection_id.map(|id: RemoteConnectionId| id.0 as i32),
                    ))?
                    .into_iter()
                    .map(|(workspace_id, timestamp)| (workspace_id, timestamp.0.flatten())),
                );
            }
            workspaces.sort_by(|(left_id, left_timestamp), (right_id, right_timestamp)| {
                right_timestamp
                    .cmp(left_timestamp)
                    .then_with(|| i64::from(*right_id).cmp(&i64::from(*left_id)))
            });
            anyhow::Ok(
                workspaces
                    .into_iter()
                    .map(|(workspace_id, _)| workspace_id)
                    .collect(),
            )
        })
        .context("Looking up workspaces by roots")
    }

    /// Returns the workspace with the given ID, loading all associated data.
    pub(crate) fn workspace_for_id(
        &self,
        workspace_id: WorkspaceId,
    ) -> Option<SerializedWorkspace> {
        Self::read_workspace(self, workspace_id).log_err().flatten()
    }

    pub(crate) async fn read_workspace_for_id(
        &self,
        workspace_id: WorkspaceId,
    ) -> Result<Option<SerializedWorkspace>> {
        self.write(move |conn| retry_table_locks(|| Self::read_workspace(conn, workspace_id)))
            .await
    }

    fn read_workspace(
        conn: &Connection,
        workspace_id: WorkspaceId,
    ) -> Result<Option<SerializedWorkspace>> {
        let Some((
            paths,
            paths_order,
            identity_paths,
            identity_paths_order,
            window_bounds,
            display,
            centered_layout,
            docks,
            window_id,
            remote_connection_id,
        )) = conn
            .select_row_bound::<WorkspaceId, (
                Vec<u8>,
                Vec<u8>,
                Option<Vec<u8>>,
                Option<Vec<u8>>,
                Lenient<Option<SerializedWindowBounds>>,
                Lenient<Option<Uuid>>,
                Option<bool>,
                DockStructure,
                Option<u64>,
                Option<i32>,
            )>(sql! {
                SELECT
                    paths,
                    paths_order,
                    identity_paths,
                    identity_paths_order,
                    window_state,
                    window_x,
                    window_y,
                    window_width,
                    window_height,
                    display,
                    centered_layout,
                    left_dock_visible,
                    left_dock_active_panel,
                    left_dock_zoom,
                    right_dock_visible,
                    right_dock_active_panel,
                    right_dock_zoom,
                    bottom_dock_visible,
                    bottom_dock_active_panel,
                    bottom_dock_zoom,
                    window_id,
                    remote_connection_id
                FROM workspaces
                WHERE workspace_id = ?
            })
            .and_then(|mut prepared_statement| (prepared_statement)(workspace_id))
            .with_context(|| format!("Reading workspace {workspace_id:?}"))?
        else {
            return Ok(None);
        };

        let paths = PathList::deserialize(&SerializedPathList {
            paths: lossy_text(paths),
            order: lossy_text(paths_order),
        });
        let identity_paths = identity_paths.map(|paths| {
            PathList::deserialize(&SerializedPathList {
                paths: lossy_text(paths),
                order: identity_paths_order.map(lossy_text).unwrap_or_default(),
            })
        });

        let remote_connection_id = remote_connection_id.map(|id| RemoteConnectionId(id as u64));
        let location = match remote_connection_id {
            Some(remote_connection_id) => SerializedWorkspaceLocation::Remote(
                Self::read_remote_connection(conn, remote_connection_id).with_context(|| {
                    format!("Reading the remote connection of workspace {workspace_id:?}")
                })?,
            ),
            None => SerializedWorkspaceLocation::Local,
        };

        Ok(Some(SerializedWorkspace {
            id: workspace_id,
            location,
            paths,
            identity_paths,
            center_group: Self::get_center_pane_group(conn, workspace_id)
                .context("Getting center group")?,
            window_bounds: window_bounds.0.flatten(),
            centered_layout: centered_layout.unwrap_or(false),
            display: display.0.flatten(),
            docks,
            session_id: None,
            bookmarks: Self::bookmarks(conn, workspace_id)?,
            breakpoints: Self::breakpoints(conn, workspace_id)?,
            window_id,
            user_toolchains: Self::user_toolchains(conn, workspace_id, remote_connection_id)?,
            recent_navigation_history: Self::recent_navigation_history(conn, workspace_id)?,
            unserialized_root_files: Self::unserialized_root_files(conn, workspace_id)?,
        }))
    }

    fn unserialized_root_files(
        conn: &Connection,
        workspace_id: WorkspaceId,
    ) -> Result<Option<UnserializedRootFiles>> {
        let Some((paths, active)) = conn
            .select_row_bound::<WorkspaceId, (Lenient<Option<String>>, Lenient<Option<PathBuf>>)>(
                sql!(
                    SELECT unserialized_root_files, active_unserialized_root_file
                    FROM workspaces
                    WHERE workspace_id = ?
                ),
            )
            .and_then(|mut statement| statement(workspace_id))
            .context("Loading unserialized root files")?
        else {
            return Ok(None);
        };
        Ok(paths.0.flatten().map(|paths| UnserializedRootFiles {
            paths: PathList::deserialize(&SerializedPathList {
                paths,
                order: String::new(),
            }),
            active: active.0.flatten(),
        }))
    }

    fn recent_navigation_history(
        conn: &Connection,
        workspace_id: WorkspaceId,
    ) -> Result<Vec<PathBuf>> {
        Ok(conn
            .select_bound::<WorkspaceId, Lenient<PathBuf>>(sql!(
                SELECT path
                FROM recent_navigation_history
                WHERE workspace_id = ?
                ORDER BY position
            ))
            .and_then(|mut statement| statement(workspace_id))
            .context("Loading recent navigation history")?
            .into_iter()
            .filter_map(|path| path.0)
            .collect())
    }

    fn bookmarks(
        conn: &Connection,
        workspace_id: WorkspaceId,
    ) -> Result<BTreeMap<Arc<Path>, Vec<SerializedBookmark>>> {
        let bookmarks = conn
            .select_bound::<WorkspaceId, (Lenient<PathBuf>, Lenient<Bookmark>)>(sql! {
                SELECT path, row, label
                FROM bookmarks
                WHERE workspace_id = ?
                ORDER BY path, row
            })
            .and_then(|mut prepared_statement| (prepared_statement)(workspace_id))
            .context("Loading bookmarks")?;
        if bookmarks.is_empty() {
            log::debug!("Bookmarks are empty after querying database for them");
        }

        let mut map = BTreeMap::<Arc<Path>, Vec<SerializedBookmark>>::default();
        for (path, bookmark) in bookmarks {
            let (Some(path), Some(bookmark)) = (path.0, bookmark.0) else {
                continue;
            };
            map.entry(Arc::from(path))
                .or_default()
                .push(SerializedBookmark {
                    row: bookmark.row,
                    label: bookmark.label,
                });
        }
        Ok(map)
    }

    fn breakpoints(
        conn: &Connection,
        workspace_id: WorkspaceId,
    ) -> Result<BTreeMap<Arc<Path>, Vec<SourceBreakpoint>>> {
        let breakpoints = conn
            .select_bound::<WorkspaceId, (Lenient<PathBuf>, Lenient<Breakpoint>)>(sql! {
                SELECT path, breakpoint_location, log_message, condition, hit_condition, state
                FROM breakpoints
                WHERE workspace_id = ?
            })
            .and_then(|mut prepared_statement| (prepared_statement)(workspace_id))
            .context("Loading breakpoints")?;
        if breakpoints.is_empty() {
            log::debug!("Breakpoints are empty after querying database for them");
        }

        let mut map = BTreeMap::<Arc<Path>, Vec<SourceBreakpoint>>::default();
        for (path, breakpoint) in breakpoints {
            let (Some(path), Some(breakpoint)) = (path.0, breakpoint.0) else {
                continue;
            };
            let path = Arc::<Path>::from(path);
            map.entry(path.clone()).or_default().push(SourceBreakpoint {
                row: breakpoint.position,
                path,
                message: breakpoint.message,
                condition: breakpoint.condition,
                hit_condition: breakpoint.hit_condition,
                state: breakpoint.state,
            });
        }

        for (path, bps) in map.iter() {
            log::info!(
                "Got {} breakpoints from database at path: {}",
                bps.len(),
                path.to_string_lossy()
            );
        }

        Ok(map)
    }

    fn user_toolchains(
        conn: &Connection,
        workspace_id: WorkspaceId,
        remote_connection_id: Option<RemoteConnectionId>,
    ) -> Result<BTreeMap<ToolchainScope, IndexSet<Toolchain>>> {
        type RowKind = (WorkspaceId, String, String, String, String, String, String);

        let toolchains = conn
            .select_bound::<(Option<u64>, WorkspaceId), Lenient<RowKind>>(sql! {
                SELECT workspace_id, worktree_root_path, relative_worktree_path,
                language_name, name, path, raw_json
                FROM user_toolchains WHERE remote_connection_id IS ?1 AND (
                      workspace_id IN (0, ?2)
                )
            })
            .and_then(|mut statement| {
                (statement)((remote_connection_id.map(|id| id.0), workspace_id))
            })
            .context("Loading user toolchains")?;
        let mut ret = BTreeMap::<_, IndexSet<_>>::default();

        for (
            _workspace_id,
            worktree_root_path,
            relative_worktree_path,
            language_name,
            name,
            path,
            raw_json,
        ) in toolchains.into_iter().filter_map(|toolchain| toolchain.0)
        {
            // INTEGER's that are primary keys (like workspace ids, remote connection ids and such) start at 1, so we're safe to
            let scope = if _workspace_id == WorkspaceId(0) {
                debug_assert_eq!(worktree_root_path, String::default());
                debug_assert_eq!(relative_worktree_path, String::default());
                ToolchainScope::Global
            } else {
                debug_assert_eq!(workspace_id, _workspace_id);
                debug_assert_eq!(
                    worktree_root_path == String::default(),
                    relative_worktree_path == String::default()
                );

                let Some(relative_path) = RelPath::from_unix_str(&relative_worktree_path).log_err()
                else {
                    continue;
                };
                if worktree_root_path != String::default()
                    && relative_worktree_path != String::default()
                {
                    ToolchainScope::Subproject(
                        Arc::from(worktree_root_path.as_ref()),
                        relative_path.into(),
                    )
                } else {
                    ToolchainScope::Project
                }
            };
            let Ok(as_json) = serde_json::from_str(&raw_json) else {
                continue;
            };
            let toolchain = Toolchain {
                name: SharedString::from(name),
                path: SharedString::from(path),
                language_name: LanguageName::from_proto(language_name),
                as_json,
            };
            ret.entry(scope).or_default().insert(toolchain);
        }

        Ok(ret)
    }

    #[cfg(test)]
    pub(crate) async fn save_workspace(&self, workspace: SerializedWorkspace) {
        self.save_workspace_adopting(workspace, None, WorkspaceIdClaims::default())
            .await
            .log_err();
    }

    pub(crate) async fn save_workspace_adopting(
        &self,
        workspace: SerializedWorkspace,
        adopting: Option<SessionWindow>,
        claims: WorkspaceIdClaims,
    ) -> Result<()> {
        let paths = workspace.paths.serialize();
        let identity_paths = workspace.identity_paths.map(|paths| paths.serialize());
        log::debug!("Saving workspace at location: {:?}", workspace.location);
        self.write(move |conn| {
            let protected = claims.protected();
            conn.with_savepoint("update_worktrees", || {
                let remote_connection_id = match workspace.location.clone() {
                    SerializedWorkspaceLocation::Local => None,
                    SerializedWorkspaceLocation::Remote(connection_options) => {
                        Some(Self::get_or_create_remote_connection_internal(
                            conn,
                            connection_options
                        )?.0)
                    }
                };

                // Clear out panes and pane_groups
                conn.exec_bound(sql!(
                    DELETE FROM pane_groups WHERE workspace_id = ?1;
                    DELETE FROM panes WHERE workspace_id = ?1;))?(workspace.id)
                    .context("Clearing old panes")?;

                conn.exec_bound(
                    sql!(
                        DELETE FROM bookmarks WHERE workspace_id = ?1;
                    )
                )?(workspace.id).context("Clearing old bookmarks")?;

                for (path, bookmarks) in workspace.bookmarks {
                    for bookmark in bookmarks {
                        conn.exec_bound(sql!(
                            INSERT INTO bookmarks (workspace_id, path, row, label)
                            VALUES (?1, ?2, ?3, ?4);
                        ))?((workspace.id, path.as_ref(), bookmark.row, bookmark.label)).context("Inserting bookmark")?;
                    }
                }

                conn.exec_bound(
                    sql!(
                        DELETE FROM breakpoints WHERE workspace_id = ?1;
                    )
                )?(workspace.id).context("Clearing old breakpoints")?;

                for (path, breakpoints) in workspace.breakpoints {
                    for bp in breakpoints {
                        let state = BreakpointStateWrapper::from(bp.state);
                        match conn.exec_bound(sql!(
                            INSERT INTO breakpoints (workspace_id, path, breakpoint_location,  log_message, condition, hit_condition, state)
                            VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7);))?

                        ((
                            workspace.id,
                            path.as_ref(),
                            bp.row,
                            bp.message,
                            bp.condition,
                            bp.hit_condition,
                            state,
                        )) {
                            Ok(_) => {
                                log::debug!("Stored breakpoint at row: {} in path: {}", bp.row, path.to_string_lossy())
                            }
                            Err(err) => {
                                log::error!("{err}");
                                continue;
                            }
                        }
                    }
                }

                conn.exec_bound(
                    sql!(
                        DELETE FROM user_toolchains WHERE workspace_id = ?1;
                    )
                )?(workspace.id).context("Clearing old user toolchains")?;

                for (scope, toolchains) in workspace.user_toolchains {
                    for toolchain in toolchains {
                        let query = sql!(INSERT OR REPLACE INTO user_toolchains(remote_connection_id, workspace_id, worktree_root_path, relative_worktree_path, language_name, name, path, raw_json) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8));
                        let (workspace_id, worktree_root_path, relative_worktree_path) = match scope {
                            ToolchainScope::Subproject(ref worktree_root_path, ref path) => (Some(workspace.id), Some(worktree_root_path.to_string_lossy().into_owned()), Some(path.as_unix_str().to_owned())),
                            ToolchainScope::Project => (Some(workspace.id), None, None),
                            ToolchainScope::Global => (None, None, None),
                        };
                        let args = (remote_connection_id, workspace_id.unwrap_or(WorkspaceId(0)), worktree_root_path.unwrap_or_default(), relative_worktree_path.unwrap_or_default(),
                        toolchain.language_name.as_ref().to_owned(), toolchain.name.to_string(), toolchain.path.to_string(), toolchain.as_json.to_string());
                        if let Err(err) = conn.exec_bound(query)?(args) {
                            log::error!("{err}");
                            continue;
                        }
                    }
                }

                // Clear out old workspaces with the same paths.
                // Skip this for empty workspaces - they are identified by workspace_id, not paths.
                // Multiple empty workspaces with different content should coexist.
                if !paths.paths.is_empty() {
                    let stale_workspace_ids = conn.select_bound::<_, WorkspaceId>(sql!(
                        SELECT workspace_id
                        FROM workspaces
                        WHERE
                            workspace_id != ?1 AND
                            paths IS ?2 AND
                            remote_connection_id IS ?3 AND
                            session_id IS NULL AND
                            NOT EXISTS(
                                SELECT item_id FROM items
                                WHERE items.workspace_id = workspaces.workspace_id
                            )
                    ))?((
                        workspace.id,
                        paths.paths.clone(),
                        remote_connection_id,
                    ))
                    .context("finding old locations")?;
                    let mut delete_workspace = conn.exec_bound::<WorkspaceId>(sql!(
                        DELETE FROM workspaces WHERE workspace_id = ?
                    ))?;
                    for stale_workspace_id in stale_workspace_ids {
                        if !protected.contains(stale_workspace_id) {
                            delete_workspace(stale_workspace_id)
                                .context("clearing out old locations")?;
                        }
                    }
                }

                if let Some(origin) = &adopting
                    && let Some(session_id) = workspace.session_id.as_deref()
                    && let Some(window_id) = workspace.window_id
                {
                    Self::adopt_session_window(
                        conn,
                        workspace.id,
                        origin,
                        session_id,
                        window_id,
                        &protected,
                    )?;
                }

                // Upsert
                let query = sql!(
                    INSERT INTO workspaces(
                        workspace_id,
                        paths,
                        paths_order,
                        identity_paths,
                        identity_paths_order,
                        remote_connection_id,
                        left_dock_visible,
                        left_dock_active_panel,
                        left_dock_zoom,
                        right_dock_visible,
                        right_dock_active_panel,
                        right_dock_zoom,
                        bottom_dock_visible,
                        bottom_dock_active_panel,
                        bottom_dock_zoom,
                        session_id,
                        window_id,
                        unserialized_root_files,
                        active_unserialized_root_file,
                        timestamp
                    )
                    VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11, ?12, ?13, ?14, ?15, ?16, ?17, ?18, ?19, CURRENT_TIMESTAMP)
                    ON CONFLICT DO
                    UPDATE SET
                        paths = ?2,
                        paths_order = ?3,
                        identity_paths = ?4,
                        identity_paths_order = ?5,
                        remote_connection_id = ?6,
                        left_dock_visible = ?7,
                        left_dock_active_panel = ?8,
                        left_dock_zoom = ?9,
                        right_dock_visible = ?10,
                        right_dock_active_panel = ?11,
                        right_dock_zoom = ?12,
                        bottom_dock_visible = ?13,
                        bottom_dock_active_panel = ?14,
                        bottom_dock_zoom = ?15,
                        session_id = ?16,
                        window_id = ?17,
                        unserialized_root_files = ?18,
                        active_unserialized_root_file = ?19,
                        timestamp = CURRENT_TIMESTAMP
                );
                let mut prepared_query = conn.exec_bound(query)?;
                let args = (
                    workspace.id,
                    paths.paths.clone(),
                    paths.order.clone(),
                    identity_paths.as_ref().map(|paths| paths.paths.clone()),
                    identity_paths.as_ref().map(|paths| paths.order.clone()),
                    remote_connection_id,
                    workspace.docks,
                    workspace.session_id,
                    workspace.window_id,
                    workspace.unserialized_root_files.as_ref().map(|root_files| {
                        (
                            root_files.paths.serialize().paths,
                            root_files.active.as_deref(),
                        )
                    }),
                );

                prepared_query(args).context("Updating workspace")?;

                conn.exec_bound(sql!(
                    DELETE FROM recent_navigation_history WHERE workspace_id = ?;
                ))?(workspace.id)
                .context("Clearing recent navigation history")?;

                let mut insert_recent_path = conn.exec_bound(sql!(
                    INSERT INTO recent_navigation_history(workspace_id, path, position)
                    VALUES (?, ?, ?);
                ))?;
                for (position, path) in workspace.recent_navigation_history.iter().enumerate() {
                    insert_recent_path((workspace.id, path.as_path(), position))
                        .context("Inserting recent navigation history")?;
                }

                // Save center pane group
                Self::save_pane_group(conn, workspace.id, &workspace.center_group, None)
                    .context("save pane group in save workspace")?;

                Ok(())
            })
        })
        .await
    }

    #[cfg(test)]
    pub(crate) async fn get_or_create_remote_connection(
        &self,
        options: RemoteConnectionOptions,
    ) -> Result<RemoteConnectionId> {
        self.write(move |conn| Self::get_or_create_remote_connection_internal(conn, options))
            .await
    }

    pub(crate) async fn equivalent_remote_connections(
        &self,
        options: RemoteConnectionOptions,
    ) -> Result<Vec<RemoteConnectionId>> {
        self.write(move |conn| {
            retry_table_locks(|| {
                let remote_connection_id =
                    Self::get_or_create_remote_connection_internal(conn, options.clone())?;
                Self::equivalent_remote_connection_ids(conn, remote_connection_id)
            })
        })
        .await
    }

    fn get_or_create_remote_connection_internal(
        this: &Connection,
        options: RemoteConnectionOptions,
    ) -> Result<RemoteConnectionId> {
        let identity = remote_connection_identity(&options);
        let args = match &options {
            RemoteConnectionOptions::Ssh(ssh_options) => {
                let args = ssh_options.args.clone().unwrap_or_default();
                let target = SshTarget {
                    host: ssh_options.host.to_string(),
                    username: ssh_options.username.clone(),
                    port: ssh_options.port,
                };
                let args =
                    renamed_ssh_arguments(&Self::ssh_argument_renames(this)?, &target, &args)
                        .unwrap_or(args);
                Some(serde_json::to_string(&args)?)
            }
            _ => None,
        };
        let kind;
        let user: Option<String>;
        let mut host = None;
        let mut port = None;
        let mut distro = None;
        let mut name = None;
        let mut container_id = None;
        let mut use_podman = None;
        let mut remote_env = None;

        match identity {
            RemoteConnectionIdentity::Ssh {
                host: identity_host,
                username,
                port: identity_port,
            } => {
                kind = RemoteConnectionKind::Ssh;
                host = Some(identity_host);
                port = identity_port;
                user = username;
            }
            RemoteConnectionIdentity::Wsl {
                distro_name,
                user: identity_user,
            } => {
                kind = RemoteConnectionKind::Wsl;
                distro = Some(distro_name);
                user = identity_user;
            }
            RemoteConnectionIdentity::Docker {
                container_id: identity_container_id,
                name: identity_name,
                remote_user,
            } => {
                kind = RemoteConnectionKind::Docker;
                container_id = Some(identity_container_id);
                name = Some(identity_name);
                user = Some(remote_user);
            }
            #[cfg(any(test, feature = "test-support"))]
            RemoteConnectionIdentity::Mock { id } => {
                kind = RemoteConnectionKind::Mock;
                host = Some(id.to_string());
                user = None;
            }
        }

        if let RemoteConnectionOptions::Docker(options) = options {
            use_podman = Some(options.use_podman);
            remote_env = serde_json::to_string(&options.remote_env).ok();
        }

        Self::get_or_create_remote_connection_query(
            this,
            kind,
            host,
            port,
            user,
            distro,
            name,
            container_id,
            use_podman,
            remote_env,
            args,
        )
    }

    fn get_or_create_remote_connection_query(
        this: &Connection,
        kind: RemoteConnectionKind,
        host: Option<String>,
        port: Option<u16>,
        user: Option<String>,
        distro: Option<String>,
        name: Option<String>,
        container_id: Option<String>,
        use_podman: Option<bool>,
        remote_env: Option<String>,
        args: Option<String>,
    ) -> Result<RemoteConnectionId> {
        let existing = this.select_row_bound::<_, u64>(sql!(
            SELECT id
            FROM remote_connections
            WHERE
                kind IS ? AND
                host IS ? AND
                port IS ? AND
                user IS ? AND
                distro IS ? AND
                name IS ? AND
                container_id IS ? AND
                args IS ?
            ORDER BY id
            LIMIT 1
        ))?((
            kind.serialize(),
            host.clone(),
            port,
            user.clone(),
            distro.clone(),
            name.clone(),
            container_id.clone(),
            args.clone(),
        ))?;
        if let Some(id) = existing {
            return Ok(RemoteConnectionId(id));
        }
        let id = this.select_row_bound(sql!(
            INSERT INTO remote_connections (
                kind,
                host,
                port,
                user,
                distro,
                name,
                container_id,
                use_podman,
                remote_env,
                args
                ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10)
            RETURNING id
        ))?((
            kind.serialize(),
            host,
            port,
            user,
            distro,
            name,
            container_id,
            use_podman,
            remote_env,
            args,
        ))?
        .context("failed to insert remote project")?;
        Ok(RemoteConnectionId(id))
    }

    fn equivalent_remote_connection_ids(
        this: &Connection,
        remote_connection_id: RemoteConnectionId,
    ) -> Result<Vec<RemoteConnectionId>> {
        let connections = Self::remote_connection_rows(this)?;
        let Some(target) = connections
            .get(&remote_connection_id)
            .map(RemoteConnectionTarget::from)
        else {
            return Ok(vec![remote_connection_id]);
        };
        let mut equivalent_ids = connections
            .iter()
            .filter(|(id, options)| {
                **id != remote_connection_id && RemoteConnectionTarget::from(*options) == target
            })
            .map(|(id, _)| *id)
            .collect::<Vec<_>>();
        equivalent_ids.sort_by_key(|id| id.0);
        equivalent_ids.insert(0, remote_connection_id);
        Ok(equivalent_ids)
    }

    pub async fn sync_ssh_connections(
        &self,
        configured: Vec<ConfiguredSshConnection>,
        renames_from_previous_runs: SshArgumentRenames,
    ) -> Result<()> {
        self.write(move |conn| {
            conn.with_savepoint("sync_ssh_connections", || {
                let edits = Self::ssh_connection_setting(conn, CONFIGURED_SSH_CONNECTIONS_KEY)?
                    .and_then(|previous| {
                        serde_json::from_str::<Vec<ConfiguredSshConnection>>(&previous).log_err()
                    })
                    .map(|previous| ssh_argument_edits(&previous, &configured))
                    .unwrap_or_default();
                let renames = compose_ssh_argument_renames(
                    Self::ssh_argument_renames(conn)?,
                    &edits,
                    &configured,
                );
                let retained_renames = match renames_from_previous_runs {
                    SshArgumentRenames::Keep => renames.clone(),
                    SshArgumentRenames::Discard => {
                        compose_ssh_argument_renames(Vec::new(), &edits, &configured)
                    }
                };
                let connections = conn.select_bound::<&str, (
                    u64,
                    Option<String>,
                    Option<u16>,
                    Option<String>,
                    Option<String>,
                )>(sql!(
                    SELECT id, host, port, user, args
                    FROM remote_connections
                    WHERE kind IS ?
                ))?(RemoteConnectionKind::Ssh.serialize())?;
                let mut record_arguments = conn.exec_bound::<(String, u64)>(sql!(
                    UPDATE remote_connections SET args = ?1 WHERE id = ?2
                ))?;
                for (id, host, port, username, args) in connections {
                    let Some(host) = host else {
                        continue;
                    };
                    let target = SshTarget {
                        host,
                        username,
                        port,
                    };
                    let resolved = match args {
                        None => Some(
                            configured
                                .iter()
                                .find(|connection| connection.target() == target)
                                .map(|connection| connection.args.clone())
                                .unwrap_or_default(),
                        ),
                        Some(args) => serde_json::from_str::<Vec<String>>(&args)
                            .ok()
                            .and_then(|args| renamed_ssh_arguments(&renames, &target, &args)),
                    };
                    if let Some(resolved) = resolved {
                        record_arguments((serde_json::to_string(&resolved)?, id))?;
                    }
                }
                Self::rename_ssh_arguments_in_multi_workspace_states(conn, &renames)?;

                let mut write_setting = conn.exec_bound::<(&str, String)>(sql!(
                    INSERT OR REPLACE INTO ssh_connection_settings(key, value) VALUES (?1, ?2)
                ))?;
                write_setting((
                    CONFIGURED_SSH_CONNECTIONS_KEY,
                    serde_json::to_string(&configured)?,
                ))?;
                write_setting((
                    SSH_ARGUMENT_RENAMES_KEY,
                    serde_json::to_string(&retained_renames)?,
                ))
            })
        })
        .await
    }

    fn rename_ssh_arguments_in_multi_workspace_states(
        conn: &Connection,
        renames: &[SshArgumentsRename],
    ) -> Result<()> {
        if renames.is_empty() {
            return Ok(());
        }
        for (key, value) in db::kvp::read_scoped_values(conn, MULTI_WORKSPACE_STATE_NAMESPACE)? {
            let Some(mut state) =
                serde_json::from_str::<model::MultiWorkspaceState>(&value).log_err()
            else {
                continue;
            };
            let mut renamed = false;
            for group in &mut state.project_groups {
                let SerializedWorkspaceLocation::Remote(RemoteConnectionOptions::Ssh(options)) =
                    &mut group.location
                else {
                    continue;
                };
                let target = SshTarget {
                    host: options.host.to_string(),
                    username: options.username.clone(),
                    port: options.port,
                };
                if let Some(args) = options
                    .args
                    .as_deref()
                    .and_then(|args| renamed_ssh_arguments(renames, &target, args))
                {
                    options.args = Some(args);
                    renamed = true;
                }
            }
            if renamed {
                db::kvp::write_scoped_value(
                    conn,
                    MULTI_WORKSPACE_STATE_NAMESPACE,
                    &key,
                    &serde_json::to_string(&state)?,
                )?;
            }
        }
        Ok(())
    }

    fn ssh_connection_setting(conn: &Connection, key: &str) -> Result<Option<String>> {
        conn.select_row_bound::<&str, String>(sql!(
            SELECT value FROM ssh_connection_settings WHERE key = ?
        ))?(key)
    }

    fn ssh_argument_renames(conn: &Connection) -> Result<Vec<SshArgumentsRename>> {
        Ok(
            Self::ssh_connection_setting(conn, SSH_ARGUMENT_RENAMES_KEY)?
                .and_then(|renames| serde_json::from_str(&renames).log_err())
                .unwrap_or_default(),
        )
    }

    pub async fn next_id(&self) -> Result<WorkspaceId> {
        self.write(|conn| {
            retry_table_locks(|| {
                conn.select_row::<WorkspaceId>(sql!(
                    INSERT INTO workspaces DEFAULT VALUES RETURNING workspace_id
                ))?()?
                .context("Inserting a workspace returned no id")
            })
            .context("Allocating a workspace id")
        })
        .await
    }

    fn recent_workspaces(
        &self,
    ) -> Result<
        Vec<(
            WorkspaceId,
            PathList,
            Option<PathList>,
            Option<RemoteConnectionId>,
            Option<String>,
            DateTime<Utc>,
        )>,
    > {
        Ok(self
            .recent_workspaces_query()?
            .into_iter()
            .filter_map(|row| row.0)
            .map(
                |(
                    id,
                    paths,
                    order,
                    identity_paths,
                    identity_paths_order,
                    remote_connection_id,
                    session_id,
                    timestamp,
                )| {
                    (
                        id,
                        PathList::deserialize(&SerializedPathList { paths, order }),
                        identity_paths.map(|paths| {
                            PathList::deserialize(&SerializedPathList {
                                paths,
                                order: identity_paths_order.unwrap_or_default(),
                            })
                        }),
                        remote_connection_id.map(RemoteConnectionId),
                        session_id,
                        parse_timestamp(&timestamp),
                    )
                },
            )
            .collect())
    }

    fn recent_workspaces_query(
        &self,
    ) -> Result<
        Vec<
            Lenient<(
                WorkspaceId,
                String,
                String,
                Option<String>,
                Option<String>,
                Option<u64>,
                Option<String>,
                String,
            )>,
        >,
    > {
        self.select(sql!(
            SELECT workspace_id, paths, paths_order, identity_paths, identity_paths_order, remote_connection_id, session_id, timestamp
            FROM workspaces
            WHERE
                paths IS NOT NULL OR
                remote_connection_id IS NOT NULL
            ORDER BY timestamp DESC
        ))?()
    }

    fn session_workspaces(
        &self,
        session_id: String,
    ) -> Result<
        Vec<(
            WorkspaceId,
            PathList,
            Option<u64>,
            Option<RemoteConnectionId>,
        )>,
    > {
        Ok(self
            .session_workspaces_query(session_id)?
            .into_iter()
            .map(
                |(workspace_id, paths, order, window_id, remote_connection_id)| {
                    (
                        WorkspaceId(workspace_id),
                        PathList::deserialize(&SerializedPathList {
                            paths: lossy_text(paths),
                            order: lossy_text(order),
                        }),
                        window_id,
                        remote_connection_id.map(RemoteConnectionId),
                    )
                },
            )
            .collect())
    }

    query! {
        fn session_workspaces_query(session_id: String) -> Result<Vec<(i64, Vec<u8>, Vec<u8>, Option<u64>, Option<u64>)>> {
            SELECT workspace_id, paths, paths_order, window_id, remote_connection_id
            FROM workspaces
            WHERE session_id = ?1
            ORDER BY timestamp DESC
        }
    }

    query! {
        pub fn breakpoints_for_file(workspace_id: WorkspaceId, file_path: &Path) -> Result<Vec<Breakpoint>> {
            SELECT breakpoint_location
            FROM breakpoints
            WHERE  workspace_id= ?1 AND path = ?2
        }
    }

    query! {
        pub fn clear_breakpoints(file_path: &Path) -> Result<()> {
            DELETE FROM breakpoints
            WHERE file_path = ?2
        }
    }

    fn remote_connections(&self) -> Result<HashMap<RemoteConnectionId, RemoteConnectionOptions>> {
        Self::remote_connection_rows(self)
    }

    fn remote_connection_rows(
        this: &Connection,
    ) -> Result<HashMap<RemoteConnectionId, RemoteConnectionOptions>> {
        Ok(this.select(sql!(
            SELECT
                id, kind, host, port, user, distro, container_id, name, use_podman, remote_env, args
            FROM
                remote_connections
        ))?()?
        .into_iter()
        .filter_map(
            |(
                id,
                (kind, host, port, user, distro, container_id, name, use_podman, remote_env, args),
            )| {
                Some((
                    RemoteConnectionId(id),
                    Self::remote_connection_from_row(
                        kind,
                        host,
                        port,
                        user,
                        distro,
                        container_id,
                        name,
                        use_podman,
                        remote_env,
                        args,
                    )?,
                ))
            },
        )
        .collect())
    }

    fn remote_connection_ids(&self) -> Result<HashSet<RemoteConnectionId>> {
        Ok(self.select::<u64>(sql!(
            SELECT id FROM remote_connections
        ))?()?
        .into_iter()
        .map(RemoteConnectionId)
        .collect())
    }

    pub(crate) fn remote_connection(
        &self,
        id: RemoteConnectionId,
    ) -> Result<RemoteConnectionOptions> {
        Self::read_remote_connection(self, id)
    }

    fn read_remote_connection(
        conn: &Connection,
        id: RemoteConnectionId,
    ) -> Result<RemoteConnectionOptions> {
        let (kind, host, port, user, distro, container_id, name, use_podman, remote_env, args) =
            conn.select_row_bound(sql!(
                SELECT kind, host, port, user, distro, container_id, name, use_podman, remote_env, args
                FROM remote_connections
                WHERE id = ?
            ))?(id.0)?
            .context("no such remote connection")?;
        Self::remote_connection_from_row(
            kind,
            host,
            port,
            user,
            distro,
            container_id,
            name,
            use_podman,
            remote_env,
            args,
        )
        .context("invalid remote_connection row")
    }

    fn remote_connection_from_row(
        kind: String,
        host: Option<String>,
        port: Option<u16>,
        user: Option<String>,
        distro: Option<String>,
        container_id: Option<String>,
        name: Option<String>,
        use_podman: Option<bool>,
        remote_env: Option<String>,
        args: Option<String>,
    ) -> Option<RemoteConnectionOptions> {
        match RemoteConnectionKind::deserialize(&kind)? {
            RemoteConnectionKind::Wsl => Some(RemoteConnectionOptions::Wsl(WslConnectionOptions {
                distro_name: distro?,
                user: user,
            })),
            RemoteConnectionKind::Ssh => Some(RemoteConnectionOptions::Ssh(SshConnectionOptions {
                host: host?.into(),
                port,
                username: user,
                args: match args {
                    Some(args) => Some(serde_json::from_str(&args).ok()?),
                    None => None,
                },
                ..Default::default()
            })),
            RemoteConnectionKind::Docker => {
                let remote_env: BTreeMap<String, String> = match remote_env {
                    Some(remote_env) => serde_json::from_str(&remote_env).ok()?,
                    None => BTreeMap::default(),
                };
                Some(RemoteConnectionOptions::Docker(DockerConnectionOptions {
                    container_id: container_id?,
                    name: name?,
                    remote_user: user?,
                    upload_binary_over_docker_exec: false,
                    use_podman: use_podman.unwrap_or(false),
                    remote_env,
                }))
            }
            #[cfg(any(test, feature = "test-support"))]
            RemoteConnectionKind::Mock => Some(RemoteConnectionOptions::Mock(
                remote::MockConnectionOptions {
                    id: host?.parse().ok()?,
                },
            )),
        }
    }

    pub async fn delete_unclaimed_workspaces(
        &self,
        workspace_ids: Vec<WorkspaceId>,
        claims: WorkspaceIdClaims,
    ) -> Result<Vec<WorkspaceId>> {
        self.write(move |conn| {
            let mut delete = conn.exec_bound::<WorkspaceId>(sql!(
                DELETE FROM workspaces WHERE workspace_id = ?
            ))?;
            let mut deleted = Vec::with_capacity(workspace_ids.len());
            for workspace_id in workspace_ids {
                let protected = claims.protected();
                if !protected.contains(workspace_id) {
                    delete(workspace_id)?;
                    deleted.push(workspace_id);
                }
            }
            anyhow::Ok(deleted)
        })
        .await
    }

    async fn session_restore_paths(
        &self,
        workspace_id: WorkspaceId,
        paths: &PathList,
        has_unsaved_contents: bool,
        fs: &dyn Fs,
    ) -> Option<PathList> {
        if paths.is_empty() {
            return Some(paths.clone());
        }
        let mut restorable_paths = Vec::new();
        let mut any_missing = false;
        for path in paths.ordered_paths() {
            if fs.metadata(path).await.ok().flatten().is_none() {
                any_missing = true;
            } else if !is_git_message_file(path, fs).await {
                restorable_paths.push(path.clone());
            }
        }
        if !restorable_paths.is_empty() {
            return Some(PathList::new(&restorable_paths));
        }
        let has_items = self
            .workspace_has_items(workspace_id)
            .log_err()
            .flatten()
            .unwrap_or(false);
        (has_items && (!any_missing || has_unsaved_contents)).then(PathList::default)
    }

    query! {
        fn workspace_has_items(workspace_id: WorkspaceId) -> Result<Option<bool>> {
            SELECT EXISTS(SELECT item_id FROM items WHERE workspace_id = ?)
        }
    }

    async fn all_paths_exist_with_a_directory(paths: &[PathBuf], fs: &dyn Fs) -> bool {
        Self::existing_paths_include_a_directory(paths, fs).await == Some(true)
    }

    async fn existing_paths_include_a_directory(paths: &[PathBuf], fs: &dyn Fs) -> Option<bool> {
        let mut any_dir = false;
        for path in paths {
            any_dir |= fs.metadata(path).await.ok().flatten()?.is_dir;
        }
        Some(any_dir)
    }

    // Returns the raw recent workspace history. Scratch workspaces (no paths) are filtered
    // out because they are restored separately by `last_session_workspace_locations`.
    pub async fn recent_project_workspaces_ungrouped(
        &self,
        fs: &dyn Fs,
    ) -> Result<Vec<RecentWorkspace>> {
        let remote_connections = self.remote_connections()?;
        let mut result = Vec::new();
        for (id, paths, identity_paths_hint, remote_connection_id, _session_id, timestamp) in
            self.recent_workspaces()?
        {
            if let Some(remote_connection_id) = remote_connection_id {
                if let Some(connection_options) = remote_connections.get(&remote_connection_id) {
                    result.push(RecentWorkspace {
                        workspace_id: id,
                        location: SerializedWorkspaceLocation::Remote(connection_options.clone()),
                        paths: paths.clone(),
                        identity_paths: identity_paths_hint.unwrap_or(paths),
                        timestamp,
                    });
                }
                continue;
            }

            if paths.paths().is_empty() || contains_wsl_path(&paths) {
                continue;
            }

            if Self::all_paths_exist_with_a_directory(paths.paths(), fs).await {
                let identity_paths = resolve_local_workspace_identity(fs, &paths)
                    .await
                    .or(identity_paths_hint)
                    .unwrap_or_else(|| paths.clone());
                result.push(RecentWorkspace {
                    workspace_id: id,
                    location: SerializedWorkspaceLocation::Local,
                    paths,
                    identity_paths,
                    timestamp,
                });
            }
        }

        Ok(result)
    }

    // Returns the recent project workspaces suitable for recent-project UIs.
    // Entries are deduplicated by git worktree identity, but preserve the original
    // serialized paths for reopening.
    pub async fn recent_project_workspaces(&self, fs: &dyn Fs) -> Result<Vec<RecentWorkspace>> {
        Ok(dedupe_recent_workspaces(
            self.recent_project_workspaces_ungrouped(fs).await?,
        ))
    }

    pub async fn delete_recent_workspace_group(
        &self,
        target: &RecentWorkspace,
        claims: WorkspaceIdClaims,
    ) -> Result<Vec<WorkspaceId>> {
        let target_paths = &target.identity_paths;
        let target_remote_connection = match &target.location {
            SerializedWorkspaceLocation::Local => None,
            SerializedWorkspaceLocation::Remote(connection) => {
                Some(RemoteConnectionTarget::from(connection))
            }
        };

        let remote_connections = self.remote_connections()?;

        let mut workspace_ids = Vec::new();
        for (workspace_id, paths, identity_paths, remote_connection_id, _, _) in
            self.recent_workspaces()?
        {
            let remote_connection = if let Some(id) = remote_connection_id {
                let Some(connection_options) = remote_connections.get(&id) else {
                    continue;
                };
                Some(RemoteConnectionTarget::from(connection_options))
            } else {
                None
            };
            if remote_connection == target_remote_connection
                && &identity_paths.unwrap_or(paths) == target_paths
            {
                workspace_ids.push(workspace_id);
            }
        }

        self.delete_unclaimed_workspaces(workspace_ids, claims)
            .await
    }

    // Deletes workspace rows that can no longer be restored from. Remote workspaces whose
    // connection was removed, and (on Windows) workspaces pointing at WSL paths, are cleaned
    // up immediately. Local workspaces with no valid paths on disk are kept for seven days
    // after going stale.
    pub async fn garbage_collect_workspaces(
        &self,
        fs: &dyn Fs,
        current_session_id: &str,
        workspaces_with_unsaved_contents: &HashSet<WorkspaceId>,
        claims: ClaimsSnapshot,
    ) -> Result<()> {
        let claimed_workspace_ids = claims.claims.claimed();
        let remote_connection_ids = self.remote_connection_ids()?;
        let persisted_project_groups = self.persisted_local_project_groups()?;
        let tracked_unavailable_roots = self.tracked_unavailable_roots()?;
        let now = Utc::now();
        let mut workspaces_to_delete = Vec::new();
        let mut local_workspace_ids = Vec::new();
        let mut still_unavailable =
            HashMap::<WorkspaceId, Vec<(PathBuf, DateTime<Utc>)>>::default();
        for (id, paths, identity_paths_hint, remote_connection_id, session_id, timestamp) in
            self.recent_workspaces()?
        {
            let is_live = session_id.as_deref() == Some(current_session_id)
                || claimed_workspace_ids.contains(&id)
                || workspaces_with_unsaved_contents.contains(&id);

            if let Some(remote_connection_id) = remote_connection_id {
                if !is_live && !remote_connection_ids.contains(&remote_connection_id) {
                    workspaces_to_delete.push(id);
                }
                continue;
            }
            local_workspace_ids.push(id);

            // Delete the workspace if any of the paths are WSL paths. If a
            // local workspace points to WSL, attempting to read its metadata
            // will wait for the WSL VM and file server to boot up. This can
            // block for many seconds. Supported scenarios use remote
            // workspaces.
            if contains_wsl_path(&paths) {
                if !is_live {
                    workspaces_to_delete.push(id);
                }
                continue;
            }

            let directory_roots = Self::existing_paths_include_a_directory(paths.paths(), fs).await;
            let mut missing_roots = Vec::new();
            let mut any_root_inaccessible = false;
            if directory_roots.is_none() {
                for root in paths.paths() {
                    match fs.metadata(root).await {
                        Ok(Some(_)) => {}
                        Ok(None) => missing_roots.push(root),
                        Err(_) => any_root_inaccessible = true,
                    }
                }
            }
            let mut unavailable_roots = Vec::new();
            if session_id.is_some() {
                for root in missing_roots {
                    let since = tracked_unavailable_roots
                        .get(&id)
                        .and_then(|tracked| tracked.get(root))
                        .copied()
                        .unwrap_or(now);
                    unavailable_roots.push((root.clone(), since));
                }
            }
            let unavailable_root_in_grace_period = unavailable_roots
                .iter()
                .any(|(_, since)| now - *since < UNAVAILABLE_SESSION_WORKSPACE_RETENTION);
            if !unavailable_roots.is_empty() {
                still_unavailable.insert(id, unavailable_roots);
            }
            if is_live {
                continue;
            }

            let referenced_by_window = persisted_project_groups.contains(&paths)
                || identity_paths_hint.as_ref().is_some_and(|identity_paths| {
                    persisted_project_groups.contains(identity_paths)
                });
            if referenced_by_window {
                continue;
            }

            if session_id.is_some() {
                if self
                    .session_restore_paths(id, &paths, false, fs)
                    .await
                    .is_some()
                {
                    continue;
                }
                if unavailable_root_in_grace_period {
                    continue;
                }
            }

            if !any_root_inaccessible
                && directory_roots != Some(true)
                && now - timestamp >= chrono::Duration::days(7)
            {
                workspaces_to_delete.push(id);
            }
        }

        self.write(move |conn| {
            conn.with_savepoint("record_unavailable_workspaces", || {
                let mut forget = conn.exec_bound::<WorkspaceId>(sql!(
                    DELETE FROM unavailable_roots WHERE workspace_id = ?
                ))?;
                for id in &local_workspace_ids {
                    forget(*id)?;
                }
                let mut track = conn.exec_bound::<(WorkspaceId, &Path, i64)>(sql!(
                    INSERT OR REPLACE INTO unavailable_roots(workspace_id, root, since)
                    VALUES (?1, ?2, ?3)
                ))?;
                for (id, roots) in &still_unavailable {
                    for (root, since) in roots {
                        track((*id, root.as_path(), since.timestamp()))?;
                    }
                }
                Ok(())
            })
        })
        .await
        .log_err();

        let current_session_id = current_session_id.to_owned();
        self.write(move |conn| {
            let mut delete = conn.exec_bound::<(WorkspaceId, &str)>(sql!(
                DELETE FROM workspaces WHERE workspace_id = ?1 AND session_id IS NOT ?2
            ))?;
            for id in workspaces_to_delete {
                let protected = claims.protected();
                if !protected.contains(id) {
                    delete((id, current_session_id.as_str()))?;
                }
            }
            anyhow::Ok(())
        })
        .await
    }

    pub(crate) async fn record_unavailable_roots(
        &self,
        workspace_id: WorkspaceId,
        unavailable_roots: Vec<PathBuf>,
    ) -> Result<Vec<PathBuf>> {
        let now = Utc::now();
        self.write(move |conn| {
            conn.with_savepoint("record_unavailable_roots", || {
                let tracked = conn.select_bound::<WorkspaceId, (PathBuf, i64)>(sql!(
                    SELECT root, since FROM unavailable_roots WHERE workspace_id = ?
                ))?(workspace_id)?;
                let mut forget = conn.exec_bound::<(WorkspaceId, &Path)>(sql!(
                    DELETE FROM unavailable_roots WHERE workspace_id = ?1 AND root = ?2
                ))?;
                let mut expired = Vec::new();
                for (root, since) in &tracked {
                    if !unavailable_roots.contains(root) {
                        forget((workspace_id, root.as_path()))?;
                    } else if DateTime::from_timestamp(*since, 0)
                        .is_none_or(|since| now - since >= UNAVAILABLE_SESSION_WORKSPACE_RETENTION)
                    {
                        expired.push(root.clone());
                    }
                }
                let mut track = conn.exec_bound::<(WorkspaceId, &Path, i64)>(sql!(
                    INSERT OR IGNORE INTO unavailable_roots(workspace_id, root, since)
                    VALUES (?1, ?2, ?3)
                ))?;
                for root in &unavailable_roots {
                    track((workspace_id, root.as_path(), now.timestamp()))?;
                }
                Ok(expired)
            })
        })
        .await
    }

    fn tracked_unavailable_roots(
        &self,
    ) -> Result<HashMap<WorkspaceId, HashMap<PathBuf, DateTime<Utc>>>> {
        let mut tracked = HashMap::<WorkspaceId, HashMap<PathBuf, DateTime<Utc>>>::default();
        for (id, root, since) in self.select::<(WorkspaceId, PathBuf, i64)>(sql!(
            SELECT workspace_id, root, since FROM unavailable_roots
        ))?()? {
            if let Some(since) = DateTime::from_timestamp(since, 0) {
                tracked.entry(id).or_default().insert(root, since);
            }
        }
        Ok(tracked)
    }

    pub async fn last_workspace(&self, fs: &dyn Fs) -> Result<Option<RecentWorkspace>> {
        Ok(self.recent_project_workspaces(fs).await?.into_iter().next())
    }

    // Returns the locations of the workspaces that were still opened when the last
    // session was closed (i.e. when Zed was quit).
    // If `last_session_window_order` is provided, the returned locations are ordered
    // according to that.
    pub async fn last_session_workspace_locations(
        &self,
        last_session_id: &str,
        last_session_window_stack: Option<Vec<WindowId>>,
        fs: &dyn Fs,
    ) -> Result<Vec<SessionWorkspace>> {
        self.restorable_session_workspace_locations(
            &[last_session_id.to_owned()],
            last_session_window_stack.map(|stack| (last_session_id.to_owned(), stack)),
            &HashSet::default(),
            fs,
        )
        .await
    }

    pub async fn restorable_session_workspace_locations(
        &self,
        last_session_ids: &[String],
        last_session_window_stack: Option<(String, Vec<WindowId>)>,
        workspaces_with_unsaved_contents: &HashSet<WorkspaceId>,
        fs: &dyn Fs,
    ) -> Result<Vec<SessionWorkspace>> {
        let mut workspaces = Vec::new();
        let mut session_workspaces = Vec::new();
        for last_session_id in last_session_ids {
            session_workspaces.extend(
                self.session_workspaces(last_session_id.clone())?
                    .into_iter()
                    .map(|session_workspace| (last_session_id, session_workspace)),
            );
        }

        for (session_id, (workspace_id, mut paths, window_id, remote_connection_id)) in
            session_workspaces
        {
            let window_id = window_id.map(WindowId::from);

            let location = match remote_connection_id {
                Some(remote_connection_id) => {
                    match self
                        .remote_connection(remote_connection_id)
                        .with_context(|| {
                            format!("reading the remote connection of workspace {workspace_id:?}")
                        })
                        .log_err()
                    {
                        Some(connection_options) => {
                            SerializedWorkspaceLocation::Remote(connection_options)
                        }
                        None => continue,
                    }
                }
                None => {
                    let Some(restore_paths) = self
                        .session_restore_paths(
                            workspace_id,
                            &paths,
                            workspaces_with_unsaved_contents.contains(&workspace_id),
                            fs,
                        )
                        .await
                    else {
                        continue;
                    };
                    paths = restore_paths;
                    SerializedWorkspaceLocation::Local
                }
            };
            workspaces.push(SessionWorkspace {
                workspace_id,
                location,
                paths,
                session_id: Some(session_id.clone()),
                window_id,
            });
        }

        if let Some((stack_session_id, stack)) = last_session_window_stack {
            workspaces.sort_by_key(|workspace| {
                workspace
                    .window_id
                    .filter(|_| workspace.session_id.as_ref() == Some(&stack_session_id))
                    .and_then(|id| stack.iter().position(|&order_id| order_id == id))
                    .unwrap_or(usize::MAX)
            });
        }

        Ok(workspaces)
    }

    fn get_center_pane_group(
        conn: &Connection,
        workspace_id: WorkspaceId,
    ) -> Result<SerializedPaneGroup> {
        Ok(Self::get_pane_group(conn, workspace_id, None)?
            .into_iter()
            .next()
            .unwrap_or_else(|| {
                SerializedPaneGroup::Pane(SerializedPane {
                    active: true,
                    children: vec![],
                    pinned_count: 0,
                })
            }))
    }

    fn get_pane_group(
        conn: &Connection,
        workspace_id: WorkspaceId,
        group_id: Option<GroupId>,
    ) -> Result<Vec<SerializedPaneGroup>> {
        type GroupKey = (Option<GroupId>, WorkspaceId);
        type GroupOrPane = (
            Option<GroupId>,
            Lenient<Option<SerializedAxis>>,
            Option<PaneId>,
            Option<bool>,
            Option<usize>,
            Lenient<Option<String>>,
        );
        let rows = conn.select_bound::<GroupKey, GroupOrPane>(sql!(
            SELECT group_id, axis, pane_id, active, pinned_count, flexes
                FROM (SELECT
                        group_id,
                        axis,
                        NULL as pane_id,
                        NULL as active,
                        NULL as pinned_count,
                        position,
                        parent_group_id,
                        workspace_id,
                        flexes
                      FROM pane_groups
                    UNION
                      SELECT
                        NULL,
                        NULL,
                        center_panes.pane_id,
                        panes.active as active,
                        pinned_count,
                        position,
                        parent_group_id,
                        panes.workspace_id as workspace_id,
                        NULL
                      FROM center_panes
                      JOIN panes ON center_panes.pane_id = panes.pane_id)
                WHERE parent_group_id IS ? AND workspace_id = ?
                ORDER BY position
        ))?((group_id, workspace_id))?;
        let mut pane_groups = Vec::with_capacity(rows.len());
        for (child_group_id, axis, pane_id, active, pinned_count, flexes) in rows {
            let pane_group = if let Some(child_group_id) = child_group_id {
                SerializedPaneGroup::Group {
                    axis: axis.0.flatten().unwrap_or(SerializedAxis(Axis::Horizontal)),
                    children: Self::get_pane_group(conn, workspace_id, Some(child_group_id))?,
                    flexes: flexes.0.flatten().and_then(|flexes| {
                        serde_json::from_str::<Vec<f32>>(&flexes)
                            .with_context(|| {
                                format!("Decoding pane group flexes of workspace {workspace_id:?}")
                            })
                            .log_err()
                    }),
                }
            } else if let Some(pane_id) = pane_id {
                SerializedPaneGroup::Pane(SerializedPane::new(
                    Self::get_items(conn, pane_id)?,
                    active.unwrap_or(false),
                    pinned_count.unwrap_or(0),
                ))
            } else {
                log::warn!(
                    "Skipping a pane group child of workspace {workspace_id:?} that is neither a group nor a pane"
                );
                continue;
            };
            // Filter out panes and pane groups which don't have any children or items
            let has_children = match &pane_group {
                SerializedPaneGroup::Group { children, .. } => !children.is_empty(),
                SerializedPaneGroup::Pane(pane) => !pane.children.is_empty(),
            };
            if has_children {
                pane_groups.push(pane_group);
            }
        }
        Ok(pane_groups)
    }

    fn save_pane_group(
        conn: &Connection,
        workspace_id: WorkspaceId,
        pane_group: &SerializedPaneGroup,
        parent: Option<(GroupId, usize)>,
    ) -> Result<()> {
        if parent.is_none() {
            log::debug!("Saving a pane group for workspace {workspace_id:?}");
        }
        match pane_group {
            SerializedPaneGroup::Group {
                axis,
                children,
                flexes,
            } => {
                let (parent_id, position) = parent.unzip();

                let flex_string = flexes
                    .as_ref()
                    .map(|flexes| serde_json::json!(flexes).to_string());

                let group_id = conn.select_row_bound::<_, i64>(sql!(
                    INSERT INTO pane_groups(
                        workspace_id,
                        parent_group_id,
                        position,
                        axis,
                        flexes
                    )
                    VALUES (?, ?, ?, ?, ?)
                    RETURNING group_id
                ))?((
                    workspace_id,
                    parent_id,
                    position,
                    *axis,
                    flex_string,
                ))?
                .context("Couldn't retrieve group_id from inserted pane_group")?;

                for (position, group) in children.iter().enumerate() {
                    Self::save_pane_group(conn, workspace_id, group, Some((group_id, position)))?
                }

                Ok(())
            }
            SerializedPaneGroup::Pane(pane) => {
                Self::save_pane(conn, workspace_id, pane, parent)?;
                Ok(())
            }
        }
    }

    fn save_pane(
        conn: &Connection,
        workspace_id: WorkspaceId,
        pane: &SerializedPane,
        parent: Option<(GroupId, usize)>,
    ) -> Result<PaneId> {
        let pane_id = conn.select_row_bound::<_, i64>(sql!(
            INSERT INTO panes(workspace_id, active, pinned_count)
            VALUES (?, ?, ?)
            RETURNING pane_id
        ))?((workspace_id, pane.active, pane.pinned_count))?
        .context("Could not retrieve inserted pane_id")?;

        let (parent_id, order) = parent.unzip();
        conn.exec_bound(sql!(
            INSERT INTO center_panes(pane_id, parent_group_id, position)
            VALUES (?, ?, ?)
        ))?((pane_id, parent_id, order))?;

        Self::save_items(conn, workspace_id, pane_id, &pane.children).context("Saving items")?;

        Ok(pane_id)
    }

    fn get_items(conn: &Connection, pane_id: PaneId) -> Result<Vec<SerializedItem>> {
        Ok(
            conn.select_bound::<PaneId, (Vec<u8>, Lenient<ItemId>, Lenient<bool>, Lenient<bool>)>(
                sql!(
                    SELECT CAST(kind AS BLOB), item_id, active, preview FROM items
                    WHERE pane_id = ?
                        ORDER BY position
                ),
            )?(pane_id)?
            .into_iter()
            .filter_map(|(kind, item_id, active, preview)| {
                Some(SerializedItem {
                    kind: Arc::from(String::from_utf8_lossy(&kind).as_ref()),
                    item_id: item_id.0?,
                    active: active.0.unwrap_or(false),
                    preview: preview.0.unwrap_or(false),
                })
            })
            .collect(),
        )
    }

    fn save_items(
        conn: &Connection,
        workspace_id: WorkspaceId,
        pane_id: PaneId,
        items: &[SerializedItem],
    ) -> Result<()> {
        let mut insert = conn.exec_bound(sql!(
            INSERT INTO items(workspace_id, pane_id, position, kind, item_id, active, preview) VALUES (?, ?, ?, ?, ?, ?, ?)
        )).context("Preparing insertion")?;
        for (position, item) in items.iter().enumerate() {
            insert((workspace_id, pane_id, position, item))?;
        }

        Ok(())
    }

    query! {
        pub async fn update_timestamp(workspace_id: WorkspaceId) -> Result<()> {
            UPDATE workspaces
            SET timestamp = CURRENT_TIMESTAMP
            WHERE workspace_id = ?
        }
    }

    #[cfg(test)]
    query! {
        pub(crate) async fn set_timestamp_for_tests(workspace_id: WorkspaceId, timestamp: String) -> Result<()> {
            UPDATE workspaces
            SET timestamp = ?2
            WHERE workspace_id = ?1
        }
    }

    #[cfg(test)]
    query! {
        pub(crate) async fn set_root_unavailable_since_for_tests(workspace_id: WorkspaceId, root: PathBuf, since: i64) -> Result<()> {
            INSERT OR REPLACE INTO unavailable_roots(workspace_id, root, since)
            VALUES (?1, ?2, ?3)
        }
    }

    query! {
        pub(crate) async fn set_window_open_status(workspace_id: WorkspaceId, bounds: SerializedWindowBounds, display: Uuid, native_window_state: Option<Vec<u8>>) -> Result<()> {
            UPDATE workspaces
            SET window_state = ?2,
                window_x = ?3,
                window_y = ?4,
                window_width = ?5,
                window_height = ?6,
                display = ?7,
                native_window_state = ?8
            WHERE workspace_id = ?1
        }
    }

    query! {
        pub(crate) fn native_window_state(workspace_id: WorkspaceId) -> Result<Option<(Option<Uuid>, Option<Vec<u8>>)>> {
            SELECT display, native_window_state
            FROM workspaces
            WHERE workspace_id = ?
        }
    }

    query! {
        pub(crate) async fn set_centered_layout(workspace_id: WorkspaceId, centered_layout: bool) -> Result<()> {
            UPDATE workspaces
            SET centered_layout = ?2
            WHERE workspace_id = ?1
        }
    }

    query! {
        pub async fn set_session_binding(workspace_id: WorkspaceId, session_id: Option<String>, window_id: Option<u64>) -> Result<()> {
            UPDATE workspaces
            SET session_id = ?2, window_id = ?3
            WHERE workspace_id = ?1
        }
    }

    pub async fn release_restored_workspace(
        &self,
        workspace_id: WorkspaceId,
        original: SessionBinding,
        adopted: Option<SessionWindow>,
        claims: WorkspaceIdClaims,
    ) -> Result<()> {
        self.write(move |conn| {
            let protected = claims.protected();
            conn.with_savepoint("release_restored_workspace", || {
                Self::release_restored_rows(
                    conn,
                    workspace_id,
                    &original,
                    &HashSet::default(),
                    &protected,
                )?;
                if let Some(adopted) = adopted {
                    Self::release_row_if_bound(
                        conn,
                        workspace_id,
                        &SessionBinding {
                            session_id: Some(adopted.session_id),
                            window_id: Some(adopted.window_id),
                        },
                    )?;
                }
                Ok(())
            })
        })
        .await
    }

    pub async fn record_restore_failure(
        &self,
        workspace_id: WorkspaceId,
        original: SessionBinding,
        workspaces_with_unsaved_contents: HashSet<WorkspaceId>,
        claims: WorkspaceIdClaims,
    ) -> Result<bool> {
        self.write(move |conn| {
            let protected = claims.protected();
            conn.with_savepoint("record_restore_failure", || {
                let Some(failures) = conn.select_row_bound::<WorkspaceId, u32>(sql!(
                    UPDATE workspaces
                    SET restore_failures = (restore_failures + 1)
                    WHERE workspace_id = ?
                    RETURNING restore_failures
                ))?(workspace_id)?
                else {
                    return Ok(false);
                };
                if failures < MAX_RESTORE_ATTEMPTS {
                    return Ok(false);
                }
                Self::reset_restore_failures(conn, workspace_id)?;
                Self::release_restored_rows(
                    conn,
                    workspace_id,
                    &original,
                    &workspaces_with_unsaved_contents,
                    &protected,
                )?;
                Ok(true)
            })
        })
        .await
    }

    pub async fn clear_restore_failures(&self, workspace_ids: Vec<WorkspaceId>) -> Result<()> {
        self.write(move |conn| {
            conn.with_savepoint("clear_restore_failures", || {
                for workspace_id in workspace_ids {
                    Self::reset_restore_failures(conn, workspace_id)?;
                }
                Ok(())
            })
        })
        .await
    }

    fn reset_restore_failures(conn: &Connection, workspace_id: WorkspaceId) -> Result<()> {
        conn.exec_bound::<WorkspaceId>(sql!(
            UPDATE workspaces SET restore_failures = (0) WHERE workspace_id = ?
        ))?(workspace_id)
    }

    pub async fn release_sessions_except(
        &self,
        current_session_id: String,
        restorable_session_ids: Vec<String>,
    ) -> Result<()> {
        self.write(move |conn| {
            conn.with_savepoint("release_sessions_except", || {
                let retained_session_ids = serde_json::to_string(
                    &std::iter::once(&current_session_id)
                        .chain(&restorable_session_ids)
                        .collect::<Vec<_>>(),
                )?;
                conn.exec_bound::<String>(sql!(
                    UPDATE workspaces SET session_id = NULL, window_id = NULL
                    WHERE session_id IS NOT NULL
                        AND session_id NOT IN (SELECT value FROM json_each(?))
                ))?(retained_session_ids)?;

                let bound_session_ids = conn.select::<String>(sql!(
                    SELECT DISTINCT session_id FROM workspaces WHERE session_id IS NOT NULL
                ))?()?
                .into_iter()
                .collect::<HashSet<_>>();
                let still_restorable = std::iter::once(&current_session_id)
                    .chain(
                        restorable_session_ids
                            .iter()
                            .filter(|session_id| bound_session_ids.contains(*session_id)),
                    )
                    .cloned()
                    .collect::<Vec<_>>();
                db::kvp::write_value(
                    conn,
                    session::RESTORABLE_SESSION_IDS_KEY,
                    &session::serialize_restorable_session_ids(&still_restorable),
                )
            })
        })
        .await
    }

    pub async fn retain_bound_multi_workspace_states(
        &self,
        current_session_id: String,
    ) -> Result<()> {
        self.write(move |conn| {
            conn.with_savepoint("retain_bound_multi_workspace_states", || {
                let mut window_is_bound = conn.select_bound::<(String, u64), i64>(sql!(
                    SELECT workspace_id FROM workspaces WHERE session_id = ?1 AND window_id = ?2 LIMIT 1
                ))?;
                for (key, _) in db::kvp::read_scoped_values(conn, MULTI_WORKSPACE_STATE_NAMESPACE)?
                {
                    let retained = match parse_multi_workspace_state_key(&key) {
                        Some((session_id, _)) if session_id == current_session_id => true,
                        Some((session_id, window_id)) => {
                            !window_is_bound((session_id.to_owned(), window_id))?.is_empty()
                        }
                        None => false,
                    };
                    if !retained {
                        db::kvp::delete_scoped_value(conn, MULTI_WORKSPACE_STATE_NAMESPACE, &key)?;
                    }
                }
                Ok(())
            })
        })
        .await
    }

    async fn detach_from_session_windows(
        &self,
        workspaces: Vec<(WorkspaceId, SessionBinding)>,
    ) -> Result<()> {
        self.write(move |conn| {
            conn.with_savepoint("detach_from_session_windows", || {
                let mut detach =
                    conn.exec_bound::<(WorkspaceId, Option<&str>, Option<u64>)>(sql!(
                        UPDATE workspaces
                        SET window_id = NULL
                        WHERE workspace_id = ?1 AND session_id IS ?2 AND window_id IS ?3
                    ))?;
                for (workspace_id, binding) in &workspaces {
                    detach((
                        *workspace_id,
                        binding.session_id.as_deref(),
                        binding.window_id,
                    ))?;
                }
                Ok(())
            })
        })
        .await
    }

    pub(crate) async fn adopt_restored_workspace(
        &self,
        workspace_id: WorkspaceId,
        original: SessionBinding,
        adopted: SessionWindow,
        state: Option<String>,
        claims: WorkspaceIdClaims,
    ) -> Result<()> {
        self.write(move |conn| {
            let protected = claims.protected();
            conn.with_savepoint("adopt_restored_workspace", || {
                if let Some(state) = &state {
                    db::kvp::insert_scoped_value_if_absent(
                        conn,
                        MULTI_WORKSPACE_STATE_NAMESPACE,
                        &multi_workspace_state_key(
                            &adopted.session_id,
                            WindowId::from(adopted.window_id),
                        ),
                        state,
                    )?;
                }
                if let Some(origin) = original.window() {
                    Self::adopt_session_window(
                        conn,
                        workspace_id,
                        &origin,
                        &adopted.session_id,
                        adopted.window_id,
                        &protected,
                    )?;
                }
                conn.exec_bound(sql!(
                    UPDATE workspaces
                    SET session_id = ?2, window_id = ?3
                    WHERE workspace_id = ?1 AND session_id IS ?4 AND window_id IS ?5
                ))?((
                    workspace_id,
                    adopted.session_id.as_str(),
                    adopted.window_id,
                    original.session_id.as_deref(),
                    original.window_id,
                ))
            })
        })
        .await
    }

    fn persisted_local_project_groups(&self) -> Result<HashSet<PathList>> {
        Ok(
            db::kvp::read_scoped_values(self, MULTI_WORKSPACE_STATE_NAMESPACE)?
                .into_iter()
                .filter_map(|(_, state)| {
                    serde_json::from_str::<model::MultiWorkspaceState>(&state).ok()
                })
                .flat_map(|state| state.project_groups)
                .filter(|group| group.location == SerializedWorkspaceLocation::Local)
                .map(|group| PathList::deserialize(&group.path_list))
                .filter(|paths| !paths.is_empty())
                .collect(),
        )
    }

    fn release_restored_rows(
        conn: &Connection,
        workspace_id: WorkspaceId,
        binding: &SessionBinding,
        workspaces_with_unsaved_contents: &HashSet<WorkspaceId>,
        protected: &ProtectedWorkspaces,
    ) -> Result<()> {
        if let Some(origin) = binding.window() {
            Self::release_session_window_rows(
                conn,
                &origin,
                None,
                workspaces_with_unsaved_contents,
                protected,
            )?;
        }
        if workspaces_with_unsaved_contents.contains(&workspace_id) {
            Self::detach_row_if_bound(conn, workspace_id, binding)
        } else {
            Self::release_row_if_bound(conn, workspace_id, binding)
        }
    }

    fn detach_row_if_bound(
        conn: &Connection,
        workspace_id: WorkspaceId,
        binding: &SessionBinding,
    ) -> Result<()> {
        conn.exec_bound(sql!(
            UPDATE workspaces
            SET window_id = NULL
            WHERE workspace_id = ?1 AND session_id IS ?2 AND window_id IS ?3
        ))?((
            workspace_id,
            binding.session_id.as_deref(),
            binding.window_id,
        ))
        .context("detaching the restored workspace")
    }

    fn release_row_if_bound(
        conn: &Connection,
        workspace_id: WorkspaceId,
        binding: &SessionBinding,
    ) -> Result<()> {
        conn.exec_bound(sql!(
            UPDATE workspaces
            SET session_id = NULL, window_id = NULL
            WHERE workspace_id = ?1 AND session_id IS ?2 AND window_id IS ?3
        ))?((
            workspace_id,
            binding.session_id.as_deref(),
            binding.window_id,
        ))
        .context("releasing the restored workspace")
    }

    fn adopt_session_window(
        conn: &Connection,
        workspace_id: WorkspaceId,
        origin: &SessionWindow,
        session_id: &str,
        window_id: u64,
        protected: &ProtectedWorkspaces,
    ) -> Result<()> {
        if origin.session_id == session_id {
            return Ok(());
        }
        let origin_state = db::kvp::read_scoped_value(
            conn,
            MULTI_WORKSPACE_STATE_NAMESPACE,
            &multi_workspace_state_key(&origin.session_id, WindowId::from(origin.window_id)),
        )?;
        if let Some(origin_state) = origin_state {
            db::kvp::insert_scoped_value_if_absent(
                conn,
                MULTI_WORKSPACE_STATE_NAMESPACE,
                &multi_workspace_state_key(session_id, WindowId::from(window_id)),
                &origin_state,
            )?;
        }
        Self::release_session_window_rows(
            conn,
            origin,
            Some(workspace_id),
            &HashSet::default(),
            protected,
        )
    }

    pub(crate) async fn release_session_window(
        &self,
        origin: SessionWindow,
        claims: WorkspaceIdClaims,
    ) -> Result<()> {
        self.write(move |conn| {
            let protected = claims.protected();
            Self::release_session_window_rows(conn, &origin, None, &HashSet::default(), &protected)
        })
        .await
    }

    fn release_session_window_rows(
        conn: &Connection,
        origin: &SessionWindow,
        adopting_workspace_id: Option<WorkspaceId>,
        workspaces_with_unsaved_contents: &HashSet<WorkspaceId>,
        protected: &ProtectedWorkspaces,
    ) -> Result<()> {
        let remote_connections = Self::remote_connection_rows(conn)?;
        let members = conn.select_bound::<(&str, u64), (
            WorkspaceId,
            Option<String>,
            Option<String>,
            Option<u64>,
            bool,
        )>(sql!(
            SELECT
                workspace_id,
                paths,
                paths_order,
                remote_connection_id,
                EXISTS(SELECT item_id FROM items WHERE items.workspace_id = workspaces.workspace_id)
            FROM workspaces
            WHERE session_id = ?1 AND window_id = ?2
        ))?((origin.session_id.as_str(), origin.window_id))
        .context("reading the session window")?
        .into_iter()
        .map(
            |(workspace_id, paths, paths_order, remote_connection_id, has_items)| {
                let paths = PathList::deserialize(&SerializedPathList {
                    paths: paths.unwrap_or_default(),
                    order: paths_order.unwrap_or_default(),
                });
                let location = match remote_connection_id {
                    Some(id) => remote_connections
                        .get(&RemoteConnectionId(id))
                        .cloned()
                        .map(SerializedWorkspaceLocation::Remote),
                    None => Some(SerializedWorkspaceLocation::Local),
                };
                (workspace_id, location, paths, has_items)
            },
        )
        .collect::<Vec<_>>();
        let window_members = members
            .iter()
            .filter_map(|(workspace_id, location, restorable_paths, has_items)| {
                Some(WindowMember {
                    workspace_id: *workspace_id,
                    location: location.clone()?,
                    restorable_paths: restorable_paths.clone(),
                    has_items: *has_items,
                })
            })
            .collect::<Vec<_>>();
        let mut release_workspace = conn.exec_bound::<WorkspaceId>(sql!(
            UPDATE workspaces SET session_id = NULL, window_id = NULL WHERE workspace_id = ?
        ))?;
        let mut detach_workspace = conn.exec_bound::<WorkspaceId>(sql!(
            UPDATE workspaces SET window_id = NULL WHERE workspace_id = ?
        ))?;
        for (workspace_id, ..) in &members {
            if Some(*workspace_id) == adopting_workspace_id || protected.contains(*workspace_id) {
                continue;
            }
            let restores_alone = workspaces_with_unsaved_contents.contains(workspace_id)
                || window_members
                    .iter()
                    .find(|member| member.workspace_id == *workspace_id)
                    .is_some_and(|member| restores_in_own_window(member, &window_members));
            if restores_alone {
                detach_workspace(*workspace_id).context("detaching from the session window")?;
            } else {
                release_workspace(*workspace_id).context("releasing the session window")?;
            }
        }
        db::kvp::delete_scoped_value(
            conn,
            MULTI_WORKSPACE_STATE_NAMESPACE,
            &multi_workspace_state_key(&origin.session_id, WindowId::from(origin.window_id)),
        )
    }

    pub(crate) async fn toolchains(
        &self,
        workspace_id: WorkspaceId,
    ) -> Result<Vec<(Toolchain, Arc<Path>, Arc<RelPath>)>> {
        self.write(move |this| {
            let mut select = this
                .select_bound(sql!(
                    SELECT
                        name, path, worktree_root_path, relative_worktree_path, language_name, raw_json
                    FROM toolchains
                    WHERE workspace_id = ?
                ))
                .context("select toolchains")?;

            let toolchain: Vec<(String, String, String, String, String, String)> =
                select(workspace_id)?;

            Ok(toolchain
                .into_iter()
                .filter_map(
                    |(name, path, worktree_root_path, relative_worktree_path, language, json)| {
                        Some((
                            Toolchain {
                                name: name.into(),
                                path: path.into(),
                                language_name: LanguageName::new(&language),
                                as_json: serde_json::Value::from_str(&json).ok()?,
                            },
                           Arc::from(worktree_root_path.as_ref()),
                            RelPath::from_unix_str(&relative_worktree_path).log_err()?.into(),
                        ))
                    },
                )
                .collect())
        })
        .await
    }

    pub async fn set_toolchain(
        &self,
        workspace_id: WorkspaceId,
        worktree_root_path: Arc<Path>,
        relative_worktree_path: Arc<RelPath>,
        toolchain: Toolchain,
    ) -> Result<()> {
        log::debug!(
            "Setting toolchain for workspace, worktree: {worktree_root_path:?}, relative path: {relative_worktree_path:?}, toolchain: {}",
            toolchain.name
        );
        self.write(move |conn| {
            let mut insert = conn
                .exec_bound(sql!(
                    INSERT INTO toolchains(workspace_id, worktree_root_path, relative_worktree_path, language_name, name, path, raw_json) VALUES (?, ?, ?, ?, ?,  ?, ?)
                    ON CONFLICT DO
                    UPDATE SET
                        name = ?5,
                        path = ?6,
                        raw_json = ?7
                ))
                .context("Preparing insertion")?;

            insert((
                workspace_id,
                worktree_root_path.to_string_lossy().into_owned(),
                relative_worktree_path.as_unix_str(),
                toolchain.language_name.as_ref(),
                toolchain.name.as_ref(),
                toolchain.path.as_ref(),
                toolchain.as_json.to_string(),
            ))?;

            Ok(())
        }).await
    }

    pub(crate) async fn save_trusted_worktrees(
        &self,
        trusted_worktrees: HashMap<Option<RemoteHostLocation>, HashSet<PathBuf>>,
    ) -> anyhow::Result<()> {
        use anyhow::Context as _;
        use db::sqlez::statement::Statement;
        use itertools::Itertools as _;

        self.clear_trusted_worktrees()
            .await
            .context("clearing previous trust state")?;

        let trusted_worktrees = trusted_worktrees
            .into_iter()
            .flat_map(|(host, abs_paths)| {
                abs_paths
                    .into_iter()
                    .map(move |abs_path| (Some(abs_path), host.clone()))
            })
            .collect::<Vec<_>>();
        let mut first_worktree;
        let mut last_worktree = 0_usize;
        for (count, placeholders) in std::iter::once("(?, ?, ?)")
            .cycle()
            .take(trusted_worktrees.len())
            .chunks(MAX_QUERY_PLACEHOLDERS / 3)
            .into_iter()
            .map(|chunk| {
                let mut count = 0;
                let placeholders = chunk
                    .inspect(|_| {
                        count += 1;
                    })
                    .join(", ");
                (count, placeholders)
            })
            .collect::<Vec<_>>()
        {
            first_worktree = last_worktree;
            last_worktree = last_worktree + count;
            let query = format!(
                r#"INSERT INTO trusted_worktrees(absolute_path, user_name, host_name)
VALUES {placeholders};"#
            );

            let trusted_worktrees = trusted_worktrees[first_worktree..last_worktree].to_vec();
            self.write(move |conn| {
                let mut statement = Statement::prepare(conn, query)?;
                let mut next_index = 1;
                for (abs_path, host) in trusted_worktrees {
                    let abs_path = abs_path.as_ref().map(|abs_path| abs_path.to_string_lossy());
                    next_index = statement.bind(
                        &abs_path.as_ref().map(|abs_path| abs_path.as_ref()),
                        next_index,
                    )?;
                    next_index = statement.bind(
                        &host
                            .as_ref()
                            .and_then(|host| Some(host.user_name.as_ref()?.as_str())),
                        next_index,
                    )?;
                    next_index = statement.bind(
                        &host.as_ref().map(|host| host.host_identifier.as_str()),
                        next_index,
                    )?;
                }
                statement.exec()
            })
            .await
            .context("inserting new trusted state")?;
        }
        Ok(())
    }

    pub fn fetch_trusted_worktrees(&self) -> Result<DbTrustedPaths> {
        let trusted_worktrees = self.trusted_worktrees()?;
        Ok(trusted_worktrees
            .into_iter()
            .filter_map(|(abs_path, user_name, host_name)| {
                let db_host = match (user_name, host_name) {
                    (None, Some(host_name)) => Some(RemoteHostLocation {
                        user_name: None,
                        host_identifier: SharedString::new(host_name),
                    }),
                    (Some(user_name), Some(host_name)) => Some(RemoteHostLocation {
                        user_name: Some(SharedString::new(user_name)),
                        host_identifier: SharedString::new(host_name),
                    }),
                    _ => None,
                };
                Some((db_host, abs_path?))
            })
            .fold(HashMap::default(), |mut acc, (remote_host, abs_path)| {
                acc.entry(remote_host)
                    .or_insert_with(HashSet::default)
                    .insert(abs_path);
                acc
            }))
    }

    query! {
        fn trusted_worktrees() -> Result<Vec<(Option<PathBuf>, Option<String>, Option<String>)>> {
            SELECT absolute_path, user_name, host_name
            FROM trusted_worktrees
        }
    }

    query! {
        pub async fn clear_trusted_worktrees() -> Result<()> {
            DELETE FROM trusted_worktrees
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct RecentWorkspace {
    pub workspace_id: WorkspaceId,
    pub location: SerializedWorkspaceLocation,
    pub paths: PathList,
    pub identity_paths: PathList,
    pub timestamp: DateTime<Utc>,
}

impl RecentWorkspace {
    pub fn project_group_key(&self) -> ProjectGroupKey {
        let host = match &self.location {
            SerializedWorkspaceLocation::Local => None,
            SerializedWorkspaceLocation::Remote(options) => Some(options.clone()),
        };
        ProjectGroupKey::new(host, self.identity_paths.clone())
    }
}

async fn resolve_local_workspace_identity(fs: &dyn Fs, paths: &PathList) -> Option<PathList> {
    let raw_paths = paths.paths();
    let resolved_paths = futures::future::join_all(
        raw_paths
            .iter()
            .map(|path| project::git_store::resolve_git_worktree_to_main_repo(fs, path)),
    )
    .await;

    if resolved_paths.iter().all(|resolved| resolved.is_none()) {
        return None;
    }

    let resolved_paths: Vec<PathBuf> = raw_paths
        .iter()
        .zip(resolved_paths.iter())
        .map(|(original, resolved)| {
            resolved
                .as_ref()
                .cloned()
                .unwrap_or_else(|| original.clone())
        })
        .collect();
    let resolved_path_refs: Vec<&Path> = resolved_paths.iter().map(PathBuf::as_path).collect();
    Some(PathList::new(&resolved_path_refs))
}

fn dedupe_recent_workspaces(
    workspaces: impl IntoIterator<Item = RecentWorkspace>,
) -> Vec<RecentWorkspace> {
    let mut indices_by_key: HashMap<(Option<RemoteConnectionTarget>, Vec<PathBuf>), usize> =
        HashMap::default();
    let mut result: Vec<RecentWorkspace> = Vec::new();
    for workspace in workspaces {
        let location_identity = match &workspace.location {
            SerializedWorkspaceLocation::Local => None,
            SerializedWorkspaceLocation::Remote(connection) => {
                Some(RemoteConnectionTarget::from(connection))
            }
        };
        let key = (location_identity, workspace.identity_paths.paths().to_vec());
        if let Some(&existing_index) = indices_by_key.get(&key) {
            if workspace.timestamp > result[existing_index].timestamp {
                result[existing_index] = workspace;
            }
        } else {
            indices_by_key.insert(key, result.len());
            result.push(workspace);
        }
    }

    result
}

pub fn delete_unloaded_items(
    alive_items: Vec<ItemId>,
    workspace_id: WorkspaceId,
    table: &'static str,
    db: &ThreadSafeConnection,
    cx: &mut App,
) -> Task<Result<()>> {
    delete_unloaded_items_keeping(
        alive_items,
        workspace_id,
        table,
        db,
        |_, _| Ok(Vec::new()),
        cx,
    )
}

pub fn delete_unloaded_items_keeping(
    alive_items: Vec<ItemId>,
    workspace_id: WorkspaceId,
    table: &'static str,
    db: &ThreadSafeConnection,
    persisted_references: impl FnOnce(&Connection, WorkspaceId) -> Result<Vec<ItemId>> + Send + 'static,
    cx: &mut App,
) -> Task<Result<()>> {
    let db = db.clone();
    let restoring_items = RestoringItems::global(cx);
    let live_items = PersistentItemIds::live_item_ids(cx);
    cx.spawn(async move |_| {
        db.write(move |conn| {
            let mut kept_items = alive_items.into_iter().collect::<HashSet<_>>();
            kept_items.extend(restoring_items.item_ids(workspace_id));
            kept_items.extend(live_items.0.lock().iter().copied());
            kept_items.extend(conn.select_bound::<WorkspaceId, ItemId>(sql!(
                SELECT item_id FROM items WHERE workspace_id = ?
            ))?(workspace_id)?);
            kept_items.extend(persisted_references(conn, workspace_id)?);
            let stored_items = conn.select_bound::<WorkspaceId, ItemId>(&format!(
                "SELECT item_id FROM {table} WHERE workspace_id = ?"
            ))?(workspace_id)?;
            let mut delete_item = conn.exec_bound::<(WorkspaceId, ItemId)>(&format!(
                "DELETE FROM {table} WHERE workspace_id = ? AND item_id = ?"
            ))?;
            for item_id in stored_items {
                if !kept_items.contains(&item_id) {
                    delete_item((workspace_id, item_id))?;
                }
            }
            Ok(())
        })
        .await
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::PathList;
    use crate::ProjectGroupKey;
    use crate::RemovalIntent;
    use crate::{
        item::test::TestItem,
        multi_workspace::MultiWorkspace,
        persistence::{
            model::{
                SerializedItem, SerializedPane, SerializedPaneGroup, SerializedWorkspace,
                SessionWorkspace,
            },
            read_multi_workspace_state,
        },
    };
    use futures::{FutureExt as _, channel::oneshot};
    use gpui::TaskExt;

    use pretty_assertions::assert_eq;
    use project::Project;
    use remote::SshConnectionOptions;
    use serde_json::json;
    use session::Session;
    use std::{thread, time::Duration};

    /// Creates a unique directory in a FakeFs, returning the path.
    /// Uses a UUID suffix to avoid collisions with other tests sharing the global DB.
    async fn unique_test_dir(fs: &fs::FakeFs, prefix: &str) -> PathBuf {
        let dir = PathBuf::from(format!("/test-dirs/{}-{}", prefix, uuid::Uuid::new_v4()));
        fs.insert_tree(&dir, json!({})).await;
        dir
    }

    #[gpui::test]
    async fn test_multi_workspace_serializes_on_add_and_remove(cx: &mut gpui::TestAppContext) {
        crate::tests::init_test(cx);

        let fs = fs::FakeFs::new(cx.executor());
        let project1 = Project::test(fs.clone(), [], cx).await;
        let project2 = Project::test(fs.clone(), [], cx).await;

        let (multi_workspace, cx) =
            cx.add_window_view(|window, cx| MultiWorkspace::test_new(project1.clone(), window, cx));

        multi_workspace.update(cx, |mw, cx| {
            mw.open_sidebar(cx);
        });

        multi_workspace.update_in(cx, |mw, _, cx| {
            mw.set_random_database_id(cx);
        });

        let window_id =
            multi_workspace.update_in(cx, |_, window, _cx| window.window_handle().window_id());
        let read_state = |cx: &mut gpui::VisualTestContext| {
            let session_id =
                multi_workspace.read_with(cx, |mw, cx| mw.workspace().read(cx).session_id());
            cx.update(|_, cx| read_multi_workspace_state(session_id.as_deref(), window_id, cx))
        };

        // --- Add a second workspace ---
        let workspace2 = multi_workspace.update_in(cx, |mw, window, cx| {
            let workspace = cx.new(|cx| crate::Workspace::test_new(project2.clone(), window, cx));
            workspace.update(cx, |ws, _cx| ws.set_random_database_id());
            mw.activate(workspace.clone(), None, window, cx);
            workspace
        });

        // Run background tasks so serialize has a chance to flush.
        cx.run_until_parked();

        // Read back the persisted state and check that the active workspace ID was written.
        let state_after_add = read_state(cx);
        let active_workspace2_db_id = workspace2.read_with(cx, |ws, _| ws.database_id());
        assert_eq!(
            state_after_add.active_workspace_id, active_workspace2_db_id,
            "After adding a second workspace, the serialized active_workspace_id should match \
             the newly activated workspace's database id"
        );

        // --- Remove the non-active workspace ---
        multi_workspace.update_in(cx, |mw, _window, cx| {
            let active = mw.workspace().clone();
            let ws = mw
                .workspaces()
                .find(|ws| *ws != &active)
                .expect("should have a non-active workspace");
            mw.remove([ws.clone()], RemovalIntent::CloseProject, _window, cx)
                .detach_and_log_err(cx);
        });

        cx.run_until_parked();

        let state_after_remove = read_state(cx);
        let remaining_db_id =
            multi_workspace.read_with(cx, |mw, cx| mw.workspace().read(cx).database_id());
        assert_eq!(
            state_after_remove.active_workspace_id, remaining_db_id,
            "After removing a workspace, the serialized active_workspace_id should match \
             the remaining active workspace's database id"
        );
    }

    #[gpui::test]
    async fn test_breakpoints() {
        zlog::init_test();

        let db = WorkspaceDb::open_test_db("test_breakpoints").await;
        let id = db.next_id().await.unwrap();

        let path = Path::new("/tmp/test.rs");

        let breakpoint = Breakpoint {
            position: 123,
            message: None,
            state: BreakpointState::Enabled,
            condition: None,
            hit_condition: None,
        };

        let log_breakpoint = Breakpoint {
            position: 456,
            message: Some("Test log message".into()),
            state: BreakpointState::Enabled,
            condition: None,
            hit_condition: None,
        };

        let disable_breakpoint = Breakpoint {
            position: 578,
            message: None,
            state: BreakpointState::Disabled,
            condition: None,
            hit_condition: None,
        };

        let condition_breakpoint = Breakpoint {
            position: 789,
            message: None,
            state: BreakpointState::Enabled,
            condition: Some("x > 5".into()),
            hit_condition: None,
        };

        let hit_condition_breakpoint = Breakpoint {
            position: 999,
            message: None,
            state: BreakpointState::Enabled,
            condition: None,
            hit_condition: Some(">= 3".into()),
        };

        let workspace = SerializedWorkspace {
            id,
            paths: PathList::new(&["/tmp"]),
            identity_paths: None,
            location: SerializedWorkspaceLocation::Local,
            center_group: Default::default(),
            window_bounds: Default::default(),
            display: Default::default(),
            docks: Default::default(),
            centered_layout: false,
            bookmarks: Default::default(),
            breakpoints: {
                let mut map = collections::BTreeMap::default();
                map.insert(
                    Arc::from(path),
                    vec![
                        SourceBreakpoint {
                            row: breakpoint.position,
                            path: Arc::from(path),
                            message: breakpoint.message.clone(),
                            state: breakpoint.state,
                            condition: breakpoint.condition.clone(),
                            hit_condition: breakpoint.hit_condition.clone(),
                        },
                        SourceBreakpoint {
                            row: log_breakpoint.position,
                            path: Arc::from(path),
                            message: log_breakpoint.message.clone(),
                            state: log_breakpoint.state,
                            condition: log_breakpoint.condition.clone(),
                            hit_condition: log_breakpoint.hit_condition.clone(),
                        },
                        SourceBreakpoint {
                            row: disable_breakpoint.position,
                            path: Arc::from(path),
                            message: disable_breakpoint.message.clone(),
                            state: disable_breakpoint.state,
                            condition: disable_breakpoint.condition.clone(),
                            hit_condition: disable_breakpoint.hit_condition.clone(),
                        },
                        SourceBreakpoint {
                            row: condition_breakpoint.position,
                            path: Arc::from(path),
                            message: condition_breakpoint.message.clone(),
                            state: condition_breakpoint.state,
                            condition: condition_breakpoint.condition.clone(),
                            hit_condition: condition_breakpoint.hit_condition.clone(),
                        },
                        SourceBreakpoint {
                            row: hit_condition_breakpoint.position,
                            path: Arc::from(path),
                            message: hit_condition_breakpoint.message.clone(),
                            state: hit_condition_breakpoint.state,
                            condition: hit_condition_breakpoint.condition.clone(),
                            hit_condition: hit_condition_breakpoint.hit_condition.clone(),
                        },
                    ],
                );
                map
            },
            session_id: None,
            window_id: None,
            user_toolchains: Default::default(),
            recent_navigation_history: Default::default(),
            unserialized_root_files: None,
        };

        db.save_workspace(workspace.clone()).await;

        let loaded = db.workspace_for_roots(&["/tmp"]).unwrap();
        let loaded_breakpoints = loaded.breakpoints.get(&Arc::from(path)).unwrap();

        assert_eq!(loaded_breakpoints.len(), 5);

        // normal breakpoint
        assert_eq!(loaded_breakpoints[0].row, breakpoint.position);
        assert_eq!(loaded_breakpoints[0].message, breakpoint.message);
        assert_eq!(loaded_breakpoints[0].condition, breakpoint.condition);
        assert_eq!(
            loaded_breakpoints[0].hit_condition,
            breakpoint.hit_condition
        );
        assert_eq!(loaded_breakpoints[0].state, breakpoint.state);
        assert_eq!(loaded_breakpoints[0].path, Arc::from(path));

        // enabled breakpoint
        assert_eq!(loaded_breakpoints[1].row, log_breakpoint.position);
        assert_eq!(loaded_breakpoints[1].message, log_breakpoint.message);
        assert_eq!(loaded_breakpoints[1].condition, log_breakpoint.condition);
        assert_eq!(
            loaded_breakpoints[1].hit_condition,
            log_breakpoint.hit_condition
        );
        assert_eq!(loaded_breakpoints[1].state, log_breakpoint.state);
        assert_eq!(loaded_breakpoints[1].path, Arc::from(path));

        // disable breakpoint
        assert_eq!(loaded_breakpoints[2].row, disable_breakpoint.position);
        assert_eq!(loaded_breakpoints[2].message, disable_breakpoint.message);
        assert_eq!(
            loaded_breakpoints[2].condition,
            disable_breakpoint.condition
        );
        assert_eq!(
            loaded_breakpoints[2].hit_condition,
            disable_breakpoint.hit_condition
        );
        assert_eq!(loaded_breakpoints[2].state, disable_breakpoint.state);
        assert_eq!(loaded_breakpoints[2].path, Arc::from(path));

        // condition breakpoint
        assert_eq!(loaded_breakpoints[3].row, condition_breakpoint.position);
        assert_eq!(loaded_breakpoints[3].message, condition_breakpoint.message);
        assert_eq!(
            loaded_breakpoints[3].condition,
            condition_breakpoint.condition
        );
        assert_eq!(
            loaded_breakpoints[3].hit_condition,
            condition_breakpoint.hit_condition
        );
        assert_eq!(loaded_breakpoints[3].state, condition_breakpoint.state);
        assert_eq!(loaded_breakpoints[3].path, Arc::from(path));

        // hit condition breakpoint
        assert_eq!(loaded_breakpoints[4].row, hit_condition_breakpoint.position);
        assert_eq!(
            loaded_breakpoints[4].message,
            hit_condition_breakpoint.message
        );
        assert_eq!(
            loaded_breakpoints[4].condition,
            hit_condition_breakpoint.condition
        );
        assert_eq!(
            loaded_breakpoints[4].hit_condition,
            hit_condition_breakpoint.hit_condition
        );
        assert_eq!(loaded_breakpoints[4].state, hit_condition_breakpoint.state);
        assert_eq!(loaded_breakpoints[4].path, Arc::from(path));
    }

    #[gpui::test]
    async fn test_remove_last_breakpoint() {
        zlog::init_test();

        let db = WorkspaceDb::open_test_db("test_remove_last_breakpoint").await;
        let id = db.next_id().await.unwrap();

        let singular_path = Path::new("/tmp/test_remove_last_breakpoint.rs");

        let breakpoint_to_remove = Breakpoint {
            position: 100,
            message: None,
            state: BreakpointState::Enabled,
            condition: None,
            hit_condition: None,
        };

        let workspace = SerializedWorkspace {
            id,
            paths: PathList::new(&["/tmp"]),
            identity_paths: None,
            location: SerializedWorkspaceLocation::Local,
            center_group: Default::default(),
            window_bounds: Default::default(),
            display: Default::default(),
            docks: Default::default(),
            centered_layout: false,
            bookmarks: Default::default(),
            breakpoints: {
                let mut map = collections::BTreeMap::default();
                map.insert(
                    Arc::from(singular_path),
                    vec![SourceBreakpoint {
                        row: breakpoint_to_remove.position,
                        path: Arc::from(singular_path),
                        message: None,
                        state: BreakpointState::Enabled,
                        condition: None,
                        hit_condition: None,
                    }],
                );
                map
            },
            session_id: None,
            window_id: None,
            user_toolchains: Default::default(),
            recent_navigation_history: Default::default(),
            unserialized_root_files: None,
        };

        db.save_workspace(workspace.clone()).await;

        let loaded = db.workspace_for_roots(&["/tmp"]).unwrap();
        let loaded_breakpoints = loaded.breakpoints.get(&Arc::from(singular_path)).unwrap();

        assert_eq!(loaded_breakpoints.len(), 1);
        assert_eq!(loaded_breakpoints[0].row, breakpoint_to_remove.position);
        assert_eq!(loaded_breakpoints[0].message, breakpoint_to_remove.message);
        assert_eq!(
            loaded_breakpoints[0].condition,
            breakpoint_to_remove.condition
        );
        assert_eq!(
            loaded_breakpoints[0].hit_condition,
            breakpoint_to_remove.hit_condition
        );
        assert_eq!(loaded_breakpoints[0].state, breakpoint_to_remove.state);
        assert_eq!(loaded_breakpoints[0].path, Arc::from(singular_path));

        let workspace_without_breakpoint = SerializedWorkspace {
            id,
            paths: PathList::new(&["/tmp"]),
            identity_paths: None,
            location: SerializedWorkspaceLocation::Local,
            center_group: Default::default(),
            window_bounds: Default::default(),
            display: Default::default(),
            docks: Default::default(),
            centered_layout: false,
            bookmarks: Default::default(),
            breakpoints: collections::BTreeMap::default(),
            session_id: None,
            window_id: None,
            user_toolchains: Default::default(),
            recent_navigation_history: Default::default(),
            unserialized_root_files: None,
        };

        db.save_workspace(workspace_without_breakpoint.clone())
            .await;

        let loaded_after_remove = db.workspace_for_roots(&["/tmp"]).unwrap();
        let empty_breakpoints = loaded_after_remove
            .breakpoints
            .get(&Arc::from(singular_path));

        assert!(empty_breakpoints.is_none());
    }

    #[gpui::test]
    async fn test_next_id_stability() {
        zlog::init_test();

        let db = WorkspaceDb::open_test_db("test_next_id_stability").await;

        db.write(|conn| {
            conn.migrate(
                "test_table",
                &[sql!(
                    CREATE TABLE test_table(
                        text TEXT,
                        workspace_id INTEGER,
                        FOREIGN KEY(workspace_id) REFERENCES workspaces(workspace_id)
                        ON DELETE CASCADE
                    ) STRICT;
                )],
                &mut |_, _, _| false,
            )
            .unwrap();
        })
        .await;

        let id = db.next_id().await.unwrap();
        // Assert the empty row got inserted
        assert_eq!(
            Some(id),
            db.select_row_bound::<WorkspaceId, WorkspaceId>(sql!(
                SELECT workspace_id FROM workspaces WHERE workspace_id = ?
            ))
            .unwrap()(id)
            .unwrap()
        );

        db.write(move |conn| {
            conn.exec_bound(sql!(INSERT INTO test_table(text, workspace_id) VALUES (?, ?)))
                .unwrap()(("test-text-1", id))
            .unwrap()
        })
        .await;

        let test_text_1 = db
            .select_row_bound::<_, String>(sql!(SELECT text FROM test_table WHERE workspace_id = ?))
            .unwrap()(1)
        .unwrap()
        .unwrap();
        assert_eq!(test_text_1, "test-text-1");
    }

    #[gpui::test]
    async fn test_native_window_state_round_trip() {
        zlog::init_test();

        let db = WorkspaceDb::open_test_db("test_native_window_state_round_trip").await;
        let id = db.next_id().await.unwrap();
        let paths = &["/tmp/native-window-state"];
        let display_uuid = Uuid::new_v4();
        let window_bounds = SerializedWindowBounds(WindowBounds::Windowed(Bounds {
            origin: point(px(100.0), px(200.0)),
            size: size(px(800.0), px(600.0)),
        }));

        db.save_workspace(SerializedWorkspace {
            id,
            paths: PathList::new(paths),
            identity_paths: None,
            location: SerializedWorkspaceLocation::Local,
            center_group: Default::default(),
            window_bounds: None,
            display: None,
            docks: Default::default(),
            bookmarks: Default::default(),
            breakpoints: Default::default(),
            centered_layout: false,
            session_id: None,
            window_id: None,
            user_toolchains: Default::default(),
            recent_navigation_history: Default::default(),
            unserialized_root_files: None,
        })
        .await;
        assert_eq!(db.native_window_state(id).unwrap(), Some((None, None)));
        assert_eq!(
            db.native_window_state(WorkspaceId::from_i64(i64::MAX))
                .unwrap(),
            None
        );

        let state = vec![0u8, 1, 2, 3, 250, 251, 252];
        db.set_window_open_status(id, window_bounds, display_uuid, Some(state.clone()))
            .await
            .unwrap();
        assert_eq!(
            db.native_window_state(id).unwrap(),
            Some((Some(display_uuid), Some(state)))
        );
        let restored = db.workspace_for_roots(paths).unwrap();
        assert_eq!(restored.window_bounds, Some(window_bounds));
        assert_eq!(restored.display, Some(display_uuid));

        let new_state = vec![9u8, 8, 7];
        db.set_window_open_status(id, window_bounds, display_uuid, Some(new_state.clone()))
            .await
            .unwrap();
        assert_eq!(
            db.native_window_state(id).unwrap(),
            Some((Some(display_uuid), Some(new_state)))
        );

        db.set_window_open_status(id, window_bounds, display_uuid, None)
            .await
            .unwrap();
        assert_eq!(
            db.native_window_state(id).unwrap(),
            Some((Some(display_uuid), None))
        );
        assert_eq!(
            db.workspace_for_roots(paths).unwrap().window_bounds,
            Some(window_bounds)
        );
    }

    #[gpui::test]
    async fn test_workspace_id_stability() {
        zlog::init_test();

        let db = WorkspaceDb::open_test_db("test_workspace_id_stability").await;

        db.write(|conn| {
            conn.migrate(
                "test_table",
                &[sql!(
                        CREATE TABLE test_table(
                            text TEXT,
                            workspace_id INTEGER,
                            FOREIGN KEY(workspace_id)
                                REFERENCES workspaces(workspace_id)
                            ON DELETE CASCADE
                        ) STRICT;)],
                &mut |_, _, _| false,
            )
        })
        .await
        .unwrap();

        let mut workspace_1 = SerializedWorkspace {
            id: WorkspaceId(1),
            paths: PathList::new(&["/tmp", "/tmp2"]),
            identity_paths: None,
            location: SerializedWorkspaceLocation::Local,
            center_group: Default::default(),
            window_bounds: Default::default(),
            display: Default::default(),
            docks: Default::default(),
            centered_layout: false,
            bookmarks: Default::default(),
            breakpoints: Default::default(),
            session_id: None,
            window_id: None,
            user_toolchains: Default::default(),
            recent_navigation_history: Default::default(),
            unserialized_root_files: None,
        };

        let workspace_2 = SerializedWorkspace {
            id: WorkspaceId(2),
            paths: PathList::new(&["/tmp"]),
            identity_paths: None,
            location: SerializedWorkspaceLocation::Local,
            center_group: Default::default(),
            window_bounds: Default::default(),
            display: Default::default(),
            docks: Default::default(),
            centered_layout: false,
            bookmarks: Default::default(),
            breakpoints: Default::default(),
            session_id: None,
            window_id: None,
            user_toolchains: Default::default(),
            recent_navigation_history: Default::default(),
            unserialized_root_files: None,
        };

        db.save_workspace(workspace_1.clone()).await;

        db.write(|conn| {
            conn.exec_bound(sql!(INSERT INTO test_table(text, workspace_id) VALUES (?, ?)))
                .unwrap()(("test-text-1", 1))
            .unwrap();
        })
        .await;

        db.save_workspace(workspace_2.clone()).await;

        db.write(|conn| {
            conn.exec_bound(sql!(INSERT INTO test_table(text, workspace_id) VALUES (?, ?)))
                .unwrap()(("test-text-2", 2))
            .unwrap();
        })
        .await;

        workspace_1.paths = PathList::new(&["/tmp", "/tmp3"]);
        db.save_workspace(workspace_1.clone()).await;
        db.save_workspace(workspace_1).await;
        db.save_workspace(workspace_2).await;

        let test_text_2 = db
            .select_row_bound::<_, String>(sql!(SELECT text FROM test_table WHERE workspace_id = ?))
            .unwrap()(2)
        .unwrap()
        .unwrap();
        assert_eq!(test_text_2, "test-text-2");

        let test_text_1 = db
            .select_row_bound::<_, String>(sql!(SELECT text FROM test_table WHERE workspace_id = ?))
            .unwrap()(1)
        .unwrap()
        .unwrap();
        assert_eq!(test_text_1, "test-text-1");
    }

    fn group(axis: Axis, children: Vec<SerializedPaneGroup>) -> SerializedPaneGroup {
        SerializedPaneGroup::Group {
            axis: SerializedAxis(axis),
            flexes: None,
            children,
        }
    }

    #[gpui::test]
    async fn test_full_workspace_serialization() {
        zlog::init_test();

        let db = WorkspaceDb::open_test_db("test_full_workspace_serialization").await;

        //  -----------------
        //  | 1,2   | 5,6   |
        //  | - - - |       |
        //  | 3,4   |       |
        //  -----------------
        let center_group = group(
            Axis::Horizontal,
            vec![
                group(
                    Axis::Vertical,
                    vec![
                        SerializedPaneGroup::Pane(SerializedPane::new(
                            vec![
                                SerializedItem::new("Terminal", 5, false, false),
                                SerializedItem::new("Terminal", 6, true, false),
                            ],
                            false,
                            0,
                        )),
                        SerializedPaneGroup::Pane(SerializedPane::new(
                            vec![
                                SerializedItem::new("Terminal", 7, true, false),
                                SerializedItem::new("Terminal", 8, false, false),
                            ],
                            false,
                            0,
                        )),
                    ],
                ),
                SerializedPaneGroup::Pane(SerializedPane::new(
                    vec![
                        SerializedItem::new("Terminal", 9, false, false),
                        SerializedItem::new("Terminal", 10, true, false),
                    ],
                    false,
                    0,
                )),
            ],
        );

        let workspace = SerializedWorkspace {
            id: WorkspaceId(5),
            paths: PathList::new(&["/tmp", "/tmp2"]),
            identity_paths: None,
            location: SerializedWorkspaceLocation::Local,
            center_group,
            window_bounds: Default::default(),
            bookmarks: Default::default(),
            breakpoints: Default::default(),
            display: Default::default(),
            docks: Default::default(),
            centered_layout: false,
            session_id: None,
            window_id: Some(999),
            user_toolchains: Default::default(),
            recent_navigation_history: (0..20)
                .map(|index| PathBuf::from(format!("/tmp2/src/{index}.rs")))
                .collect(),
            unserialized_root_files: Some(UnserializedRootFiles {
                paths: PathList::new(&["/tmp3/one.png", "/tmp4/two.png"]),
                active: Some(PathBuf::from("/tmp4/two.png")),
            }),
        };

        db.save_workspace(workspace.clone()).await;

        let round_trip_workspace = db.workspace_for_roots(&["/tmp2", "/tmp"]);
        assert_eq!(workspace, round_trip_workspace.unwrap());

        // Test guaranteed duplicate IDs
        db.save_workspace(workspace.clone()).await;
        db.save_workspace(workspace.clone()).await;

        let round_trip_workspace = db.workspace_for_roots(&["/tmp", "/tmp2"]);
        assert_eq!(workspace, round_trip_workspace.unwrap());

        assert!(
            db.delete_unclaimed_workspaces(vec![workspace.id], WorkspaceIdClaims::default())
                .await
                .is_ok()
        );
        assert!(
            WorkspaceDb::recent_navigation_history(&db, workspace.id)
                .unwrap()
                .is_empty()
        );
    }

    #[gpui::test]
    async fn test_workspace_assignment() {
        zlog::init_test();

        let db = WorkspaceDb::open_test_db("test_basic_functionality").await;

        let workspace_1 = SerializedWorkspace {
            id: WorkspaceId(1),
            paths: PathList::new(&["/tmp", "/tmp2"]),
            identity_paths: None,
            location: SerializedWorkspaceLocation::Local,
            center_group: Default::default(),
            window_bounds: Default::default(),
            bookmarks: Default::default(),
            breakpoints: Default::default(),
            display: Default::default(),
            docks: Default::default(),
            centered_layout: false,
            session_id: None,
            window_id: Some(1),
            user_toolchains: Default::default(),
            recent_navigation_history: Default::default(),
            unserialized_root_files: None,
        };

        let mut workspace_2 = SerializedWorkspace {
            id: WorkspaceId(2),
            paths: PathList::new(&["/tmp"]),
            identity_paths: None,
            location: SerializedWorkspaceLocation::Local,
            center_group: Default::default(),
            window_bounds: Default::default(),
            display: Default::default(),
            docks: Default::default(),
            centered_layout: false,
            bookmarks: Default::default(),
            breakpoints: Default::default(),
            session_id: None,
            window_id: Some(2),
            user_toolchains: Default::default(),
            recent_navigation_history: Default::default(),
            unserialized_root_files: None,
        };

        db.save_workspace(workspace_1.clone()).await;
        db.save_workspace(workspace_2.clone()).await;

        // Test that paths are treated as a set
        assert_eq!(
            db.workspace_for_roots(&["/tmp", "/tmp2"]).unwrap(),
            workspace_1
        );
        assert_eq!(
            db.workspace_for_roots(&["/tmp2", "/tmp"]).unwrap(),
            workspace_1
        );

        // Make sure that other keys work
        assert_eq!(db.workspace_for_roots(&["/tmp"]).unwrap(), workspace_2);
        assert_eq!(db.workspace_for_roots(&["/tmp3", "/tmp2", "/tmp4"]), None);

        // Test 'mutate' case of updating a pre-existing id
        workspace_2.paths = PathList::new(&["/tmp", "/tmp2"]);

        db.save_workspace(workspace_2.clone()).await;
        assert_eq!(
            db.workspace_for_roots(&["/tmp", "/tmp2"]).unwrap(),
            workspace_2
        );

        // Test other mechanism for mutating
        let mut workspace_3 = SerializedWorkspace {
            id: WorkspaceId(3),
            paths: PathList::new(&["/tmp2", "/tmp"]),
            identity_paths: None,
            location: SerializedWorkspaceLocation::Local,
            center_group: Default::default(),
            window_bounds: Default::default(),
            bookmarks: Default::default(),
            breakpoints: Default::default(),
            display: Default::default(),
            docks: Default::default(),
            centered_layout: false,
            session_id: None,
            window_id: Some(3),
            user_toolchains: Default::default(),
            recent_navigation_history: Default::default(),
            unserialized_root_files: None,
        };

        db.save_workspace(workspace_3.clone()).await;
        assert_eq!(
            db.workspace_for_roots(&["/tmp", "/tmp2"]).unwrap(),
            workspace_3
        );

        // Make sure that updating paths differently also works
        workspace_3.paths = PathList::new(&["/tmp3", "/tmp4", "/tmp2"]);
        db.save_workspace(workspace_3.clone()).await;
        assert_eq!(db.workspace_for_roots(&["/tmp2", "tmp"]), None);
        assert_eq!(
            db.workspace_for_roots(&["/tmp2", "/tmp3", "/tmp4"])
                .unwrap(),
            workspace_3
        );
    }

    #[gpui::test]
    async fn test_session_workspaces() {
        zlog::init_test();

        let db = WorkspaceDb::open_test_db("test_serializing_workspaces_session_id").await;

        let workspace_1 = SerializedWorkspace {
            id: WorkspaceId(1),
            paths: PathList::new(&["/tmp1"]),
            identity_paths: None,
            location: SerializedWorkspaceLocation::Local,
            center_group: Default::default(),
            window_bounds: Default::default(),
            display: Default::default(),
            docks: Default::default(),
            centered_layout: false,
            bookmarks: Default::default(),
            breakpoints: Default::default(),
            session_id: Some("session-id-1".to_owned()),
            window_id: Some(10),
            user_toolchains: Default::default(),
            recent_navigation_history: Default::default(),
            unserialized_root_files: None,
        };

        let workspace_2 = SerializedWorkspace {
            id: WorkspaceId(2),
            paths: PathList::new(&["/tmp2"]),
            identity_paths: None,
            location: SerializedWorkspaceLocation::Local,
            center_group: Default::default(),
            window_bounds: Default::default(),
            display: Default::default(),
            docks: Default::default(),
            centered_layout: false,
            bookmarks: Default::default(),
            breakpoints: Default::default(),
            session_id: Some("session-id-1".to_owned()),
            window_id: Some(20),
            user_toolchains: Default::default(),
            recent_navigation_history: Default::default(),
            unserialized_root_files: None,
        };

        let workspace_3 = SerializedWorkspace {
            id: WorkspaceId(3),
            paths: PathList::new(&["/tmp3"]),
            identity_paths: None,
            location: SerializedWorkspaceLocation::Local,
            center_group: Default::default(),
            window_bounds: Default::default(),
            display: Default::default(),
            docks: Default::default(),
            centered_layout: false,
            bookmarks: Default::default(),
            breakpoints: Default::default(),
            session_id: Some("session-id-2".to_owned()),
            window_id: Some(30),
            user_toolchains: Default::default(),
            recent_navigation_history: Default::default(),
            unserialized_root_files: None,
        };

        let workspace_4 = SerializedWorkspace {
            id: WorkspaceId(4),
            paths: PathList::new(&["/tmp4"]),
            identity_paths: None,
            location: SerializedWorkspaceLocation::Local,
            center_group: Default::default(),
            window_bounds: Default::default(),
            display: Default::default(),
            docks: Default::default(),
            centered_layout: false,
            bookmarks: Default::default(),
            breakpoints: Default::default(),
            session_id: None,
            window_id: None,
            user_toolchains: Default::default(),
            recent_navigation_history: Default::default(),
            unserialized_root_files: None,
        };

        let connection_id = db
            .get_or_create_remote_connection(RemoteConnectionOptions::Ssh(SshConnectionOptions {
                host: "my-host".into(),
                port: Some(1234),
                ..Default::default()
            }))
            .await
            .unwrap();

        let workspace_5 = SerializedWorkspace {
            id: WorkspaceId(5),
            paths: PathList::default(),
            identity_paths: None,
            location: SerializedWorkspaceLocation::Remote(
                db.remote_connection(connection_id).unwrap(),
            ),
            center_group: Default::default(),
            window_bounds: Default::default(),
            display: Default::default(),
            docks: Default::default(),
            centered_layout: false,
            bookmarks: Default::default(),
            breakpoints: Default::default(),
            session_id: Some("session-id-2".to_owned()),
            window_id: Some(50),
            user_toolchains: Default::default(),
            recent_navigation_history: Default::default(),
            unserialized_root_files: None,
        };

        let workspace_6 = SerializedWorkspace {
            id: WorkspaceId(6),
            paths: PathList::new(&["/tmp6c", "/tmp6b", "/tmp6a"]),
            identity_paths: None,
            location: SerializedWorkspaceLocation::Local,
            center_group: Default::default(),
            window_bounds: Default::default(),
            bookmarks: Default::default(),
            breakpoints: Default::default(),
            display: Default::default(),
            docks: Default::default(),
            centered_layout: false,
            session_id: Some("session-id-3".to_owned()),
            window_id: Some(60),
            user_toolchains: Default::default(),
            recent_navigation_history: Default::default(),
            unserialized_root_files: None,
        };

        db.save_workspace(workspace_1.clone()).await;
        thread::sleep(Duration::from_millis(1000)); // Force timestamps to increment
        db.save_workspace(workspace_2.clone()).await;
        db.save_workspace(workspace_3.clone()).await;
        thread::sleep(Duration::from_millis(1000)); // Force timestamps to increment
        db.save_workspace(workspace_4.clone()).await;
        db.save_workspace(workspace_5.clone()).await;
        db.save_workspace(workspace_6.clone()).await;

        let locations = db.session_workspaces("session-id-1".to_owned()).unwrap();
        assert_eq!(locations.len(), 2);
        assert_eq!(locations[0].0, WorkspaceId(2));
        assert_eq!(locations[0].1, PathList::new(&["/tmp2"]));
        assert_eq!(locations[0].2, Some(20));
        assert_eq!(locations[1].0, WorkspaceId(1));
        assert_eq!(locations[1].1, PathList::new(&["/tmp1"]));
        assert_eq!(locations[1].2, Some(10));

        let locations = db.session_workspaces("session-id-2".to_owned()).unwrap();
        assert_eq!(locations.len(), 2);
        assert_eq!(locations[0].0, WorkspaceId(5));
        assert_eq!(locations[0].1, PathList::default());
        assert_eq!(locations[0].2, Some(50));
        assert_eq!(locations[0].3, Some(connection_id));
        assert_eq!(locations[1].0, WorkspaceId(3));
        assert_eq!(locations[1].1, PathList::new(&["/tmp3"]));
        assert_eq!(locations[1].2, Some(30));

        let locations = db.session_workspaces("session-id-3".to_owned()).unwrap();
        assert_eq!(locations.len(), 1);
        assert_eq!(locations[0].0, WorkspaceId(6));
        assert_eq!(
            locations[0].1,
            PathList::new(&["/tmp6c", "/tmp6b", "/tmp6a"]),
        );
        assert_eq!(locations[0].2, Some(60));
    }

    fn default_workspace<P: AsRef<Path>>(
        paths: &[P],
        center_group: &SerializedPaneGroup,
    ) -> SerializedWorkspace {
        SerializedWorkspace {
            id: WorkspaceId(4),
            paths: PathList::new(paths),
            identity_paths: None,
            location: SerializedWorkspaceLocation::Local,
            center_group: center_group.clone(),
            window_bounds: Default::default(),
            display: Default::default(),
            docks: Default::default(),
            bookmarks: Default::default(),
            breakpoints: Default::default(),
            centered_layout: false,
            session_id: None,
            window_id: None,
            user_toolchains: Default::default(),
            recent_navigation_history: Default::default(),
            unserialized_root_files: None,
        }
    }

    #[gpui::test]
    async fn test_last_session_workspace_locations(cx: &mut gpui::TestAppContext) {
        let dir1 = tempfile::TempDir::with_prefix("dir1").unwrap();
        let dir2 = tempfile::TempDir::with_prefix("dir2").unwrap();
        let dir3 = tempfile::TempDir::with_prefix("dir3").unwrap();
        let dir4 = tempfile::TempDir::with_prefix("dir4").unwrap();

        let fs = fs::FakeFs::new(cx.executor());
        fs.insert_tree(dir1.path(), json!({})).await;
        fs.insert_tree(dir2.path(), json!({})).await;
        fs.insert_tree(dir3.path(), json!({})).await;
        fs.insert_tree(dir4.path(), json!({})).await;

        let db =
            WorkspaceDb::open_test_db("test_serializing_workspaces_last_session_workspaces").await;

        let workspaces = [
            (1, vec![dir1.path()], 9),
            (2, vec![dir2.path()], 5),
            (3, vec![dir3.path()], 8),
            (4, vec![dir4.path()], 2),
            (5, vec![dir1.path(), dir2.path(), dir3.path()], 3),
            (6, vec![dir4.path(), dir3.path(), dir2.path()], 4),
        ]
        .into_iter()
        .map(|(id, paths, window_id)| SerializedWorkspace {
            id: WorkspaceId(id),
            paths: PathList::new(paths.as_slice()),
            identity_paths: None,
            location: SerializedWorkspaceLocation::Local,
            center_group: Default::default(),
            window_bounds: Default::default(),
            display: Default::default(),
            docks: Default::default(),
            centered_layout: false,
            session_id: Some("one-session".to_owned()),
            bookmarks: Default::default(),
            breakpoints: Default::default(),
            window_id: Some(window_id),
            user_toolchains: Default::default(),
            recent_navigation_history: Default::default(),
            unserialized_root_files: None,
        })
        .collect::<Vec<_>>();

        for workspace in workspaces.iter() {
            db.save_workspace(workspace.clone()).await;
        }

        let stack = Some(Vec::from([
            WindowId::from(2), // Top
            WindowId::from(8),
            WindowId::from(5),
            WindowId::from(9),
            WindowId::from(3),
            WindowId::from(4), // Bottom
        ]));

        let locations = db
            .last_session_workspace_locations("one-session", stack, fs.as_ref())
            .await
            .unwrap();
        assert_eq!(
            locations,
            [
                SessionWorkspace {
                    workspace_id: WorkspaceId(4),
                    location: SerializedWorkspaceLocation::Local,
                    paths: PathList::new(&[dir4.path()]),
                    session_id: Some("one-session".to_owned()),
                    window_id: Some(WindowId::from(2u64)),
                },
                SessionWorkspace {
                    workspace_id: WorkspaceId(3),
                    location: SerializedWorkspaceLocation::Local,
                    paths: PathList::new(&[dir3.path()]),
                    session_id: Some("one-session".to_owned()),
                    window_id: Some(WindowId::from(8u64)),
                },
                SessionWorkspace {
                    workspace_id: WorkspaceId(2),
                    location: SerializedWorkspaceLocation::Local,
                    paths: PathList::new(&[dir2.path()]),
                    session_id: Some("one-session".to_owned()),
                    window_id: Some(WindowId::from(5u64)),
                },
                SessionWorkspace {
                    workspace_id: WorkspaceId(1),
                    location: SerializedWorkspaceLocation::Local,
                    paths: PathList::new(&[dir1.path()]),
                    session_id: Some("one-session".to_owned()),
                    window_id: Some(WindowId::from(9u64)),
                },
                SessionWorkspace {
                    workspace_id: WorkspaceId(5),
                    location: SerializedWorkspaceLocation::Local,
                    paths: PathList::new(&[dir1.path(), dir2.path(), dir3.path()]),
                    session_id: Some("one-session".to_owned()),
                    window_id: Some(WindowId::from(3u64)),
                },
                SessionWorkspace {
                    workspace_id: WorkspaceId(6),
                    location: SerializedWorkspaceLocation::Local,
                    paths: PathList::new(&[dir4.path(), dir3.path(), dir2.path()]),
                    session_id: Some("one-session".to_owned()),
                    window_id: Some(WindowId::from(4u64)),
                },
            ]
        );
    }

    fn pane_with_items(item_ids: &[ItemId]) -> SerializedPaneGroup {
        SerializedPaneGroup::Pane(SerializedPane::new(
            item_ids
                .iter()
                .map(|id| SerializedItem::new("Terminal", *id, true, false))
                .collect(),
            true,
            0,
        ))
    }

    fn empty_pane_group() -> SerializedPaneGroup {
        SerializedPaneGroup::Pane(SerializedPane::default())
    }

    fn workspace_with(
        id: u64,
        paths: &[&Path],
        center_group: SerializedPaneGroup,
        session_id: Option<&str>,
    ) -> SerializedWorkspace {
        SerializedWorkspace {
            id: WorkspaceId(id as i64),
            paths: PathList::new(paths),
            identity_paths: None,
            location: SerializedWorkspaceLocation::Local,
            center_group,
            window_bounds: Default::default(),
            display: Default::default(),
            docks: Default::default(),
            bookmarks: Default::default(),
            breakpoints: Default::default(),
            centered_layout: false,
            session_id: session_id.map(|s| s.to_owned()),
            window_id: Some(id),
            user_toolchains: Default::default(),
            recent_navigation_history: Default::default(),
            unserialized_root_files: None,
        }
    }

    fn remote_workspace_with(id: u64, host: &str, paths: &[&Path]) -> SerializedWorkspace {
        SerializedWorkspace {
            id: WorkspaceId(id as i64),
            paths: PathList::new(paths),
            identity_paths: None,
            location: SerializedWorkspaceLocation::Remote(RemoteConnectionOptions::Ssh(
                SshConnectionOptions {
                    host: host.into(),
                    ..Default::default()
                },
            )),
            center_group: empty_pane_group(),
            window_bounds: Default::default(),
            display: Default::default(),
            docks: Default::default(),
            bookmarks: Default::default(),
            breakpoints: Default::default(),
            centered_layout: false,
            session_id: None,
            window_id: Some(id),
            user_toolchains: Default::default(),
            recent_navigation_history: Default::default(),
            unserialized_root_files: None,
        }
    }

    async fn local_recent_workspace(
        workspace_id: WorkspaceId,
        paths: PathList,
        timestamp: DateTime<Utc>,
        fs: &dyn Fs,
    ) -> RecentWorkspace {
        let identity_paths = resolve_local_workspace_identity(fs, &paths)
            .await
            .unwrap_or_else(|| paths.clone());
        RecentWorkspace {
            workspace_id,
            location: SerializedWorkspaceLocation::Local,
            paths,
            identity_paths,
            timestamp,
        }
    }

    #[gpui::test]
    async fn test_scratch_only_workspace_restores_from_last_session(cx: &mut gpui::TestAppContext) {
        let fs = fs::FakeFs::new(cx.executor());
        let db =
            WorkspaceDb::open_test_db("test_scratch_only_workspace_restores_from_last_session")
                .await;

        db.save_workspace(workspace_with(1, &[], pane_with_items(&[100]), Some("s1")))
            .await;

        let sessions = db
            .last_session_workspace_locations("s1", None, fs.as_ref())
            .await
            .unwrap();
        assert_eq!(sessions.len(), 1);
        assert_eq!(sessions[0].workspace_id, WorkspaceId(1));
        assert!(sessions[0].paths.is_empty());

        let recents = db.recent_project_workspaces(fs.as_ref()).await.unwrap();
        assert!(
            recents
                .iter()
                .all(|workspace| workspace.workspace_id != WorkspaceId(1)),
            "scratch-only workspace must not appear in the recent-projects UI"
        );
    }

    #[gpui::test]
    async fn test_gc_preserves_scratch_inside_window(cx: &mut gpui::TestAppContext) {
        let fs = fs::FakeFs::new(cx.executor());
        let db = WorkspaceDb(db::AppDatabase::test_new().0);

        db.save_workspace(workspace_with(1, &[], empty_pane_group(), None))
            .await;

        db.garbage_collect_workspaces(
            fs.as_ref(),
            "current",
            &HashSet::default(),
            WorkspaceIdClaims::default().snapshot(),
        )
        .await
        .unwrap();
        assert!(
            db.workspace_for_id(WorkspaceId(1)).is_some(),
            "fresh stale workspace must not be deleted before the 7-day window"
        );
    }

    #[gpui::test]
    async fn test_gc_deletes_stale_outside_window(cx: &mut gpui::TestAppContext) {
        let fs = fs::FakeFs::new(cx.executor());
        let db = WorkspaceDb(db::AppDatabase::test_new().0);

        db.save_workspace(workspace_with(1, &[], empty_pane_group(), None))
            .await;
        db.set_timestamp_for_tests(WorkspaceId(1), "2000-01-01 00:00:00".to_owned())
            .await
            .unwrap();

        db.garbage_collect_workspaces(
            fs.as_ref(),
            "current",
            &HashSet::default(),
            WorkspaceIdClaims::default().snapshot(),
        )
        .await
        .unwrap();
        assert!(
            db.workspace_for_id(WorkspaceId(1)).is_none(),
            "stale empty workspace older than the retention window must be deleted"
        );
    }

    #[gpui::test]
    async fn test_gc_keeps_stale_workspaces_whose_roots_are_inaccessible(
        cx: &mut gpui::TestAppContext,
    ) {
        let fs = fs::FakeFs::new(cx.executor());
        fs.insert_tree("/locked", json!({})).await;
        fs.set_path_error("/locked", Some(std::io::ErrorKind::PermissionDenied));
        let db = WorkspaceDb(db::AppDatabase::test_new().0);
        for (workspace_id, root) in [(1, "/locked"), (2, "/gone")] {
            db.save_workspace(workspace_with(
                workspace_id,
                &[Path::new(root)],
                empty_pane_group(),
                None,
            ))
            .await;
            db.set_timestamp_for_tests(
                WorkspaceId(workspace_id as i64),
                "2000-01-01 00:00:00".to_owned(),
            )
            .await
            .unwrap();
        }

        db.garbage_collect_workspaces(
            fs.as_ref(),
            "current",
            &HashSet::default(),
            WorkspaceIdClaims::default().snapshot(),
        )
        .await
        .unwrap();

        assert_eq!(
            [1, 2].map(|id| db.workspace_for_id(WorkspaceId(id)).is_some()),
            [true, false]
        );
    }

    #[gpui::test]
    async fn test_unavailable_remote_roots_expire_independently() {
        let db =
            WorkspaceDb::open_test_db("test_unavailable_remote_roots_expire_independently").await;
        db.save_workspace(remote_workspace_with(
            1,
            "host",
            &[Path::new("/a"), Path::new("/b"), Path::new("/c")],
        ))
        .await;
        let workspace_id = WorkspaceId(1);
        let roots = |roots: &[&str]| roots.iter().map(PathBuf::from).collect::<Vec<_>>();

        let mut expired = Vec::new();
        expired.push(
            db.record_unavailable_roots(workspace_id, roots(&["/b"]))
                .await
                .unwrap(),
        );
        let eight_days_ago = (Utc::now() - chrono::Duration::days(8)).timestamp();
        db.write(move |conn| {
            conn.exec_bound::<i64>(sql!(UPDATE unavailable_roots SET since = ?))?(eight_days_ago)
        })
        .await
        .unwrap();
        for unavailable in [&["/b", "/c"][..], &["/c"], &[]] {
            expired.push(
                db.record_unavailable_roots(workspace_id, roots(unavailable))
                    .await
                    .unwrap(),
            );
        }
        let tracked = db
            .select::<PathBuf>(sql!(SELECT root FROM unavailable_roots))
            .unwrap()()
        .unwrap();

        assert_eq!(
            (expired, tracked),
            (
                vec![Vec::new(), roots(&["/b"]), Vec::new(), Vec::new()],
                Vec::new()
            )
        );
    }

    #[gpui::test]
    async fn test_unavailable_local_roots_expire_independently(cx: &mut gpui::TestAppContext) {
        cx.update(|cx| cx.set_global(db::AppDatabase::test_new()));
        let fs = fs::FakeFs::new(cx.executor());
        let db = cx.update(|cx| WorkspaceDb::global(cx));
        let (root_a, root_b) = (Path::new("/a"), Path::new("/b"));
        db.save_workspace(workspace_with(
            1,
            &[root_a, root_b],
            empty_pane_group(),
            Some("previous"),
        ))
        .await;
        db.set_timestamp_for_tests(WorkspaceId(1), "2000-01-01 00:00:00".to_owned())
            .await
            .unwrap();
        db.set_root_unavailable_since_for_tests(
            WorkspaceId(1),
            root_a.to_path_buf(),
            (Utc::now() - chrono::Duration::days(8)).timestamp(),
        )
        .await
        .unwrap();

        let restored_before_gc = restored_unavailable_roots(&db, WorkspaceId(1), fs.as_ref()).await;
        db.garbage_collect_workspaces(
            fs.as_ref(),
            "current",
            &HashSet::default(),
            WorkspaceIdClaims::default().snapshot(),
        )
        .await
        .unwrap();
        let restored_after_gc = restored_unavailable_roots(&db, WorkspaceId(1), fs.as_ref()).await;

        assert_eq!(
            (restored_before_gc, restored_after_gc),
            (
                Some(vec![root_b.to_path_buf()]),
                Some(vec![root_b.to_path_buf()])
            )
        );
    }

    #[gpui::test]
    async fn test_migration_preserves_local_unavailable_root_timers(cx: &mut gpui::TestAppContext) {
        let name = "test_migration_preserves_local_unavailable_root_timers";
        let legacy = Connection::open_memory(Some(name));
        let migrations = WorkspaceDb::MIGRATIONS;
        legacy
            .migrate(
                WorkspaceDb::NAME,
                &migrations[..migrations.len() - 1],
                &mut |_, _, _| false,
            )
            .unwrap();
        let eight_days_ago = (Utc::now() - chrono::Duration::days(8)).timestamp();
        legacy
            .exec_bound::<(&str, i64)>(
                "INSERT INTO workspaces(workspace_id, paths, paths_order, session_id, timestamp, roots_unavailable_since) \
                VALUES (1, ?1, '0,1', 'previous', '2000-01-01 00:00:00', ?2)",
            )
            .unwrap()(("/available\n/missing", eight_days_ago))
            .unwrap();
        let db = WorkspaceDb(db::open_test_db::<db::AppMigrator>(name).await);
        let fs = fs::FakeFs::new(cx.executor());
        fs.insert_tree("/available", json!({})).await;
        let tracked_roots = |db: &WorkspaceDb| {
            db.select::<(PathBuf, i64)>("SELECT root, since FROM unavailable_roots ORDER BY root")
                .unwrap()()
            .unwrap()
        };

        let after_migration = tracked_roots(&db);
        db.garbage_collect_workspaces(
            fs.as_ref(),
            "current",
            &HashSet::default(),
            WorkspaceIdClaims::default().snapshot(),
        )
        .await
        .unwrap();
        let after_gc = tracked_roots(&db);

        let (available, missing) = (PathBuf::from("/available"), PathBuf::from("/missing"));
        assert_eq!(
            (after_migration, after_gc),
            (
                vec![
                    (available, eight_days_ago),
                    (missing.clone(), eight_days_ago)
                ],
                vec![(missing, eight_days_ago)]
            )
        );
    }

    #[gpui::test]
    async fn test_deletions_respect_claims_taken_before_they_execute(
        cx: &mut gpui::TestAppContext,
    ) {
        let fs = fs::FakeFs::new(cx.executor());
        let db = WorkspaceDb(db::AppDatabase::test_new().0);
        let claims = WorkspaceIdClaims::default();
        let exists = |id: i64| db.workspace_for_id(WorkspaceId(id)).is_some();

        db.save_workspace(workspace_with(1, &[], empty_pane_group(), None))
            .await;
        db.set_timestamp_for_tests(WorkspaceId(1), "2000-01-01 00:00:00".to_owned())
            .await
            .unwrap();
        let snapshot_before_reopening = claims.snapshot();
        drop(claims.try_claim(WorkspaceId(1)));
        db.garbage_collect_workspaces(
            fs.as_ref(),
            "current",
            &HashSet::default(),
            snapshot_before_reopening,
        )
        .await
        .unwrap();
        let kept_after_reopening = exists(1);
        db.garbage_collect_workspaces(
            fs.as_ref(),
            "current",
            &HashSet::default(),
            claims.snapshot(),
        )
        .await
        .unwrap();
        let kept_after_fresh_snapshot = exists(1);

        let project = Path::new("/project");
        db.save_workspace(workspace_with(2, &[project], empty_pane_group(), None))
            .await;
        let restoring = claims.try_claim(WorkspaceId(2));
        db.save_workspace_adopting(
            workspace_with(3, &[project], empty_pane_group(), None),
            None,
            claims.clone(),
        )
        .await
        .unwrap();
        let kept_while_claimed = exists(2);
        drop(restoring);
        db.save_workspace_adopting(
            workspace_with(3, &[project], empty_pane_group(), None),
            None,
            claims.clone(),
        )
        .await
        .unwrap();

        assert_eq!(
            (
                kept_after_reopening,
                kept_after_fresh_snapshot,
                kept_while_claimed,
                exists(2)
            ),
            (true, false, true, false)
        );
    }

    #[gpui::test]
    async fn test_gc_preserves_directory_workspace_with_missing_path(
        cx: &mut gpui::TestAppContext,
    ) {
        let fs = fs::FakeFs::new(cx.executor());
        let db = WorkspaceDb(db::AppDatabase::test_new().0);

        let missing_dir = PathBuf::from("/missing-project-dir");
        db.save_workspace(workspace_with(
            1,
            &[missing_dir.as_path()],
            empty_pane_group(),
            None,
        ))
        .await;

        db.garbage_collect_workspaces(
            fs.as_ref(),
            "current",
            &HashSet::default(),
            WorkspaceIdClaims::default().snapshot(),
        )
        .await
        .unwrap();
        assert!(
            db.workspace_for_id(WorkspaceId(1)).is_some(),
            "a stale workspace within the retention window must be kept"
        );

        db.set_timestamp_for_tests(WorkspaceId(1), "2000-01-01 00:00:00".to_owned())
            .await
            .unwrap();
        db.garbage_collect_workspaces(
            fs.as_ref(),
            "current",
            &HashSet::default(),
            WorkspaceIdClaims::default().snapshot(),
        )
        .await
        .unwrap();
        assert!(
            db.workspace_for_id(WorkspaceId(1)).is_none(),
            "a stale workspace past the retention window must be deleted"
        );
    }

    #[gpui::test]
    async fn test_gc_preserves_reachable_workspaces(cx: &mut gpui::TestAppContext) {
        cx.update(|cx| cx.set_global(db::AppDatabase::test_new()));
        let fs = fs::FakeFs::new(cx.executor());
        fs.insert_tree("/project", json!({ "notes.txt": "" })).await;
        let (db, kvp) = cx.update(|cx| (WorkspaceDb::global(cx), KeyValueStore::global(cx)));
        let notes = Path::new("/project/notes.txt");
        let docker = |name: &str| {
            RemoteConnectionOptions::Docker(DockerConnectionOptions {
                name: name.to_owned(),
                container_id: name.to_owned(),
                remote_user: "user".to_owned(),
                upload_binary_over_docker_exec: false,
                use_podman: false,
                remote_env: BTreeMap::default(),
            })
        };
        let remote = |id, name| SerializedWorkspace {
            location: SerializedWorkspaceLocation::Remote(docker(name)),
            ..workspace_with(
                id,
                &[Path::new("/remote")],
                empty_pane_group(),
                Some("previous"),
            )
        };
        for workspace in [
            workspace_with(1, &[], empty_pane_group(), Some("current")),
            workspace_with(2, &[], empty_pane_group(), Some("unadopted")),
            workspace_with(3, &[notes], empty_pane_group(), None),
            workspace_with(4, &[], empty_pane_group(), None),
            workspace_with(
                5,
                &[Path::new("/unmounted-volume/project")],
                empty_pane_group(),
                Some("previous"),
            ),
            remote(6, "legacy"),
            remote(7, "corrupt"),
        ] {
            let workspace_id = workspace.id;
            db.save_workspace(workspace).await;
            db.set_timestamp_for_tests(workspace_id, "2000-01-01 00:00:00".to_owned())
                .await
                .unwrap();
        }
        db.write(|conn| {
            conn.exec(
                "UPDATE remote_connections SET remote_env = NULL, use_podman = NULL WHERE name = 'legacy'",
            )?()?;
            conn.exec("UPDATE remote_connections SET remote_env = 'corrupt' WHERE name = 'corrupt'")?()
        })
        .await
        .unwrap();
        write_multi_workspace_state(
            &kvp,
            "current",
            WindowId::from(7u64),
            model::MultiWorkspaceState {
                project_groups: vec![model::SerializedProjectGroup::from_group(
                    &ProjectGroupKey::new(None, PathList::new(&[notes])),
                    true,
                )],
                ..model::MultiWorkspaceState::default()
            },
        )
        .await;
        let workspace_exists = |id: i64| {
            db.select_row_bound::<i64, i64>(
                "SELECT workspace_id FROM workspaces WHERE workspace_id = ?",
            )
            .unwrap()(id)
            .unwrap()
            .is_some()
        };

        let mut kept = Vec::new();
        for unavailable_days_ago in [None, Some(6), Some(7)] {
            if let Some(days) = unavailable_days_ago {
                let since = (Utc::now() - chrono::Duration::days(days)).timestamp();
                db.set_root_unavailable_since_for_tests(
                    WorkspaceId(5),
                    PathBuf::from("/unmounted-volume/project"),
                    since,
                )
                .await
                .unwrap();
            }
            db.garbage_collect_workspaces(
                fs.as_ref(),
                "current",
                &HashSet::default(),
                WorkspaceIdClaims::default().snapshot(),
            )
            .await
            .unwrap();
            kept.push((1..=7).map(workspace_exists).collect::<Vec<_>>());
        }

        assert_eq!(
            (
                kept,
                db.workspace_for_id(WorkspaceId(6))
                    .map(|workspace| workspace.location)
            ),
            (
                vec![
                    vec![true, true, true, false, true, true, true],
                    vec![true, true, true, false, true, true, true],
                    vec![true, true, true, false, false, true, true],
                ],
                Some(SerializedWorkspaceLocation::Remote(docker("legacy")))
            )
        );
    }

    #[gpui::test]
    async fn test_gc_deletes_empty_workspace_with_items(cx: &mut gpui::TestAppContext) {
        let fs = fs::FakeFs::new(cx.executor());
        let db = WorkspaceDb(db::AppDatabase::test_new().0);

        db.save_workspace(workspace_with(1, &[], pane_with_items(&[100]), None))
            .await;
        db.set_timestamp_for_tests(WorkspaceId(1), "2000-01-01 00:00:00".to_owned())
            .await
            .unwrap();

        db.garbage_collect_workspaces(
            fs.as_ref(),
            "current",
            &HashSet::default(),
            WorkspaceIdClaims::default().snapshot(),
        )
        .await
        .unwrap();
        assert!(
            db.workspace_for_id(WorkspaceId(1)).is_none(),
            "a stale empty-path workspace must be deleted regardless of its items"
        );
    }

    #[gpui::test]
    async fn test_interrupted_launches_never_make_historical_sessions_restorable(
        cx: &mut gpui::TestAppContext,
    ) {
        cx.update(|cx| cx.set_global(db::AppDatabase::test_new()));
        let (db, kvp) = cx.update(|cx| (WorkspaceDb::global(cx), KeyValueStore::global(cx)));
        for (id, session_id) in [(1, "historical"), (2, "last")] {
            db.save_workspace(workspace_with(
                id,
                &[],
                empty_pane_group(),
                Some(session_id),
            ))
            .await;
        }
        for session_id in ["last", "interrupted"] {
            Session::new(session_id.to_owned(), kvp.clone()).await;
        }
        let next_restorable = Session::new("next".to_owned(), kvp.clone())
            .await
            .restorable_session_ids()
            .to_vec();
        db.release_sessions_except("next".to_owned(), next_restorable.clone())
            .await
            .unwrap();
        let after_restorable = Session::new("after".to_owned(), kvp)
            .await
            .restorable_session_ids()
            .to_vec();

        assert_eq!(
            (
                next_restorable,
                [1, 2].map(|id| session_binding(&db, WorkspaceId(id)).0),
                after_restorable,
            ),
            (
                vec!["interrupted".to_owned(), "last".to_owned()],
                [None, Some("last".to_owned())],
                vec!["next".to_owned(), "last".to_owned()],
            )
        );
    }

    #[gpui::test]
    async fn test_last_session_restores_workspace_with_missing_paths(
        cx: &mut gpui::TestAppContext,
    ) {
        let fs = fs::FakeFs::new(cx.executor());
        let db =
            WorkspaceDb::open_test_db("test_last_session_restores_workspace_with_missing_paths")
                .await;

        let missing = PathBuf::from("/gone/file.rs");
        db.save_workspace(workspace_with(
            1,
            &[missing.as_path()],
            empty_pane_group(),
            Some("s"),
        ))
        .await;

        let sessions = db
            .last_session_workspace_locations("s", None, fs.as_ref())
            .await
            .unwrap();
        assert!(
            sessions.is_empty(),
            "workspaces whose paths no longer exist on disk must not restore"
        );
    }

    #[gpui::test]
    async fn test_session_restore_skips_unrestorable_roots_and_connections(
        cx: &mut gpui::TestAppContext,
    ) {
        let fs = fs::FakeFs::new(cx.executor());
        fs.insert_tree(
            "/repo",
            json!({
                "note.txt": "",
                ".git": {
                    "HEAD": "ref: refs/heads/main\n",
                    "objects": {},
                    "config": "",
                    "COMMIT_EDITMSG": "",
                    "worktrees": {
                        "feature": {
                            "HEAD": "ref: refs/heads/feature\n",
                            "commondir": "../..\n",
                            "MERGE_MSG": "",
                        },
                    },
                },
            }),
        )
        .await;
        fs.insert_tree(
            "/bare.git",
            json!({ "HEAD": "ref: refs/heads/main\n", "objects": {}, "COMMIT_EDITMSG": "" }),
        )
        .await;
        fs.insert_tree("/notes", json!({ "MERGE_MSG": "" })).await;
        fs.insert_tree("/fixture.git", json!({ "COMMIT_EDITMSG": "" }))
            .await;
        let db = WorkspaceDb::open_test_db(
            "test_session_restore_skips_unrestorable_roots_and_connections",
        )
        .await;
        let note = Path::new("/repo/note.txt");
        let config = Path::new("/repo/.git/config");
        let commit_message = Path::new("/repo/.git/COMMIT_EDITMSG");
        let non_git_message = Path::new("/notes/MERGE_MSG");
        let headless_git_message = Path::new("/fixture.git/COMMIT_EDITMSG");
        let missing = Path::new("/gone/deleted.txt");
        let workspaces = [
            (vec![note], empty_pane_group(), Some(vec![note])),
            (vec![config], empty_pane_group(), Some(vec![config])),
            (
                vec![Path::new("/repo"), commit_message],
                empty_pane_group(),
                Some(vec![Path::new("/repo")]),
            ),
            (vec![commit_message], empty_pane_group(), None),
            (
                vec![Path::new("/repo/.git/worktrees/feature/MERGE_MSG")],
                empty_pane_group(),
                None,
            ),
            (
                vec![Path::new("/bare.git/COMMIT_EDITMSG")],
                empty_pane_group(),
                None,
            ),
            (
                vec![non_git_message],
                empty_pane_group(),
                Some(vec![non_git_message]),
            ),
            (
                vec![headless_git_message],
                empty_pane_group(),
                Some(vec![headless_git_message]),
            ),
            (
                vec![commit_message],
                pane_with_items(&[1]),
                Some(Vec::new()),
            ),
            (vec![commit_message, missing], pane_with_items(&[2]), None),
            (vec![note, missing], pane_with_items(&[3]), Some(vec![note])),
            (
                vec![note, Path::new("/gone/other.txt")],
                empty_pane_group(),
                Some(vec![note]),
            ),
            (vec![missing], pane_with_items(&[4]), None),
        ];
        let mut expected = Vec::new();
        for (id, (paths, center_group, restored_paths)) in (1..).zip(workspaces) {
            db.save_workspace(workspace_with(id, &paths, center_group, Some("s")))
                .await;
            if let Some(restored_paths) = restored_paths {
                expected.push((WorkspaceId(id as i64), PathList::new(&restored_paths)));
            }
        }
        db.save_workspace(SerializedWorkspace {
            session_id: Some("s".to_owned()),
            ..remote_workspace_with(100, "host", &[Path::new("/remote")])
        })
        .await;
        db.write(|conn| conn.exec("UPDATE remote_connections SET kind = 'unknown'")?())
            .await
            .unwrap();

        let mut restored = db
            .last_session_workspace_locations("s", None, fs.as_ref())
            .await
            .unwrap()
            .into_iter()
            .map(|session| (session.workspace_id, session.paths))
            .collect::<Vec<_>>();
        restored.sort_by_key(|(workspace_id, _)| *workspace_id);
        assert_eq!(restored, expected);
    }

    #[gpui::test]
    async fn test_session_windows_stay_scoped_to_their_session(cx: &mut gpui::TestAppContext) {
        cx.update(|cx| cx.set_global(db::AppDatabase::test_new()));
        let fs = fs::FakeFs::new(cx.executor());
        let (db, kvp) = cx.update(|cx| (WorkspaceDb::global(cx), KeyValueStore::global(cx)));
        let window_id = WindowId::from(7u64);
        for (id, session_id) in [(1, "newest"), (2, "older"), (3, "older")] {
            db.save_workspace(SerializedWorkspace {
                window_id: Some(window_id.as_u64()),
                ..workspace_with(id, &[], empty_pane_group(), Some(session_id))
            })
            .await;
        }
        for (session_id, window_id, active_workspace_id) in
            [("newest", window_id, 1), ("older", window_id, 3)]
        {
            write_multi_workspace_state(
                &kvp,
                session_id,
                window_id,
                model::MultiWorkspaceState {
                    active_workspace_id: Some(WorkspaceId(active_workspace_id)),
                    ..model::MultiWorkspaceState::default()
                },
            )
            .await;
        }

        let windows_before_adoption = restorable_windows(&db, fs.as_ref(), cx).await;
        db.set_session_binding(WorkspaceId(2), Some("current".to_owned()), Some(5))
            .await
            .unwrap();
        let windows_after_manual_move = restorable_windows(&db, fs.as_ref(), cx).await;
        db.adopt_restored_workspace(
            WorkspaceId(3),
            SessionBinding {
                session_id: Some("older".to_owned()),
                window_id: Some(window_id.as_u64()),
            },
            SessionWindow {
                session_id: "current".to_owned(),
                window_id: 9,
            },
            None,
            WorkspaceIdClaims::default(),
        )
        .await
        .unwrap();
        let windows_after_adoption = restorable_windows(&db, fs.as_ref(), cx).await;
        db.retain_bound_multi_workspace_states("current".to_owned())
            .await
            .unwrap();
        let retained_states = cx.update(|cx| {
            [
                ("newest", window_id),
                ("older", window_id),
                ("current", WindowId::from(9u64)),
            ]
            .map(|(session_id, window_id)| {
                read_multi_workspace_state(Some(session_id), window_id, cx).active_workspace_id
            })
        });

        let restorable_before_adoption = vec![
            (
                Some("newest".to_owned()),
                WorkspaceId(1),
                Some(WorkspaceId(1)),
            ),
            (
                Some("older".to_owned()),
                WorkspaceId(3),
                Some(WorkspaceId(3)),
            ),
        ];
        assert_eq!(
            (
                windows_before_adoption,
                windows_after_manual_move,
                windows_after_adoption,
                retained_states
            ),
            (
                restorable_before_adoption.clone(),
                restorable_before_adoption,
                vec![(
                    Some("newest".to_owned()),
                    WorkspaceId(1),
                    Some(WorkspaceId(1))
                )],
                [Some(WorkspaceId(1)), None, Some(WorkspaceId(3))],
            )
        );
    }

    #[gpui::test]
    async fn test_window_persists_restored_state_until_it_is_applied(
        cx: &mut gpui::TestAppContext,
    ) {
        crate::tests::init_test(cx);
        let fs = fs::FakeFs::new(cx.executor());
        let project = Project::test(fs, [], cx).await;
        let (multi_workspace, cx) =
            cx.add_window_view(|window, cx| MultiWorkspace::test_new(project, window, cx));
        multi_workspace.update_in(cx, |mw, _, cx| mw.set_random_database_id(cx));
        let restored_group = ProjectGroupKey::new(None, PathList::new(&[Path::new("/restored")]));
        let (session_id, window_id) = multi_workspace.update_in(cx, |mw, window, cx| {
            mw.begin_restoring_state(model::MultiWorkspaceState {
                active_workspace_id: None,
                sidebar_open: true,
                project_groups: vec![model::SerializedProjectGroup::from_group(
                    &restored_group,
                    false,
                )],
                sidebar_state: Some("restored sidebar".to_owned()),
            });
            mw.serialize(cx);
            (
                mw.workspace().read(cx).session_id().unwrap(),
                window.window_handle().window_id(),
            )
        });
        let persisted = |cx: &mut gpui::VisualTestContext| {
            cx.run_until_parked();
            let state =
                cx.update(|_, cx| read_multi_workspace_state(Some(&session_id), window_id, cx));
            (
                state
                    .project_groups
                    .into_iter()
                    .map(ProjectGroupKey::from)
                    .collect::<Vec<_>>(),
                state.sidebar_open,
                state.sidebar_state,
            )
        };
        let while_restoring = persisted(cx);
        multi_workspace.update(cx, |mw, cx| mw.finish_restoring_state(cx));
        let after_restoring = persisted(cx);

        assert_eq!(
            (while_restoring, after_restoring),
            (
                (
                    vec![restored_group],
                    true,
                    Some("restored sidebar".to_owned())
                ),
                (Vec::new(), false, None),
            )
        );
    }

    #[gpui::test]
    async fn test_siblings_restored_in_their_own_windows_survive_adoption(
        cx: &mut gpui::TestAppContext,
    ) {
        cx.update(|cx| cx.set_global(db::AppDatabase::test_new()));
        let fs = fs::FakeFs::new(cx.executor());
        fs.insert_tree(
            "/",
            json!({
                "project": {},
                "other": {},
                "restoring": {},
                "notes": { "MERGE_MSG": {} },
                "repo": {
                    ".git": { "HEAD": "ref: refs/heads/main", "objects": {}, "COMMIT_EDITMSG": "" },
                },
            }),
        )
        .await;
        let db = cx.update(|cx| WorkspaceDb::global(cx));
        let kvp = cx.update(|cx| KeyValueStore::global(cx));
        let origin_window = WindowId::from(7u64);
        for (id, paths, center_group) in [
            (1, vec![Path::new("/project")], empty_pane_group()),
            (2, Vec::new(), pane_with_items(&[1])),
            (3, Vec::new(), empty_pane_group()),
            (
                4,
                vec![Path::new("/repo/.git/COMMIT_EDITMSG")],
                pane_with_items(&[2]),
            ),
            (5, vec![Path::new("/other")], pane_with_items(&[3])),
            (6, vec![Path::new("/project")], pane_with_items(&[4])),
            (7, vec![Path::new("/restoring")], pane_with_items(&[5])),
            (
                9,
                vec![Path::new("/notes/MERGE_MSG")],
                pane_with_items(&[7]),
            ),
            (10, vec![Path::new("/unmounted")], pane_with_items(&[8])),
            (11, vec![Path::new("/unmounted")], pane_with_items(&[9])),
        ] {
            db.save_workspace(SerializedWorkspace {
                window_id: Some(origin_window.as_u64()),
                ..workspace_with(id, &paths, center_group, Some("previous"))
            })
            .await;
        }
        db.save_workspace(SerializedWorkspace {
            session_id: Some("previous".to_owned()),
            window_id: Some(origin_window.as_u64()),
            center_group: pane_with_items(&[6]),
            ..remote_workspace_with(8, "host", &[])
        })
        .await;
        let claims = WorkspaceIdClaims::default();
        let _restoring = claims.try_claim(WorkspaceId(7));
        write_multi_workspace_state(
            &kvp,
            "previous",
            origin_window,
            model::MultiWorkspaceState {
                active_workspace_id: Some(WorkspaceId(1)),
                ..model::MultiWorkspaceState::default()
            },
        )
        .await;
        let original = SessionBinding {
            session_id: Some("previous".to_owned()),
            window_id: Some(origin_window.as_u64()),
        };
        let adopted = SessionWindow {
            session_id: "current".to_owned(),
            window_id: 9,
        };
        let bindings =
            || [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11].map(|id| session_binding(&db, WorkspaceId(id)));

        let locations = db
            .restorable_session_workspace_locations(
                &["previous".to_owned()],
                None,
                &HashSet::default(),
                fs.as_ref(),
            )
            .await
            .unwrap();
        let mut planned_windows = cx
            .update(|cx| read_serialized_multi_workspaces(locations, cx))
            .await
            .into_iter()
            .map(|window| {
                (
                    window.active_workspace.workspace_id,
                    window.active_workspace.window_id,
                )
            })
            .collect::<Vec<_>>();
        planned_windows.sort_by_key(|(workspace_id, _)| *workspace_id);
        let bindings_after_planning = bindings();
        db.adopt_restored_workspace(
            WorkspaceId(1),
            original.clone(),
            adopted.clone(),
            None,
            claims.clone(),
        )
        .await
        .unwrap();
        let bindings_after_adoption = bindings();
        let origin_state = cx.update(|cx| {
            read_multi_workspace_state(Some("previous"), origin_window, cx).active_workspace_id
        });
        db.release_restored_workspace(WorkspaceId(1), original, Some(adopted), claims)
            .await
            .unwrap();

        let in_window = || (Some("previous".to_owned()), Some(origin_window.as_u64()));
        let own_window = || (Some("previous".to_owned()), None);
        let released = || (None, None);
        assert_eq!(
            (
                planned_windows,
                bindings_after_planning,
                bindings_after_adoption,
                origin_state,
                bindings()
            ),
            (
                vec![
                    (WorkspaceId(1), Some(origin_window)),
                    (WorkspaceId(2), None),
                    (WorkspaceId(4), None),
                    (WorkspaceId(6), None),
                    (WorkspaceId(8), None),
                ],
                [
                    in_window(),
                    own_window(),
                    in_window(),
                    own_window(),
                    in_window(),
                    own_window(),
                    in_window(),
                    own_window(),
                    in_window(),
                    in_window(),
                    in_window(),
                ],
                [
                    (Some("current".to_owned()), Some(9)),
                    own_window(),
                    released(),
                    own_window(),
                    released(),
                    own_window(),
                    in_window(),
                    own_window(),
                    released(),
                    own_window(),
                    own_window(),
                ],
                None,
                [
                    released(),
                    own_window(),
                    released(),
                    own_window(),
                    released(),
                    own_window(),
                    in_window(),
                    own_window(),
                    released(),
                    own_window(),
                    own_window(),
                ],
            )
        );
    }

    #[gpui::test]
    async fn test_remote_window_position_follows_the_restored_workspace(
        cx: &mut gpui::TestAppContext,
    ) {
        cx.update(|cx| cx.set_global(db::AppDatabase::test_new()));
        let db = cx.update(|cx| WorkspaceDb::global(cx));
        let display = Uuid::new_v4();
        let bounds = |x: f32| {
            WindowBounds::Windowed(Bounds::new(point(px(x), px(0.)), size(px(800.), px(600.))))
        };
        for (id, x) in [(1, 10.), (2, 20.)] {
            db.save_workspace(SerializedWorkspace {
                session_id: Some("session".to_owned()),
                ..remote_workspace_with(id, "host", &[Path::new("/repo")])
            })
            .await;
            db.set_window_open_status(
                WorkspaceId(id as i64),
                SerializedWindowBounds(bounds(x)),
                display,
                None,
            )
            .await
            .unwrap();
        }
        let connection = RemoteConnectionOptions::Ssh(SshConnectionOptions {
            host: "host".into(),
            ..Default::default()
        });

        let mut positions = Vec::new();
        for workspace_id in [WorkspaceId(1), WorkspaceId(2)] {
            let position = cx
                .update(|cx| {
                    crate::remote_workspace_position_from_db(
                        connection.clone(),
                        &[PathBuf::from("/repo")],
                        Some(workspace_id),
                        cx,
                    )
                })
                .await
                .unwrap();
            positions.push(position.window_bounds);
        }

        assert_eq!(positions, vec![Some(bounds(10.)), Some(bounds(20.))]);
    }

    #[gpui::test]
    async fn test_failed_restoration_is_retried_once_per_workspace_lifetime(
        cx: &mut gpui::TestAppContext,
    ) {
        cx.update(|cx| cx.set_global(db::AppDatabase::test_new()));
        let db = cx.update(|cx| WorkspaceDb::global(cx));
        let original = SessionBinding {
            session_id: Some("previous".to_owned()),
            window_id: Some(7),
        };
        let save_workspace = || {
            db.save_workspace(SerializedWorkspace {
                window_id: original.window_id,
                ..workspace_with(1, &[], empty_pane_group(), Some("previous"))
            })
        };
        save_workspace().await;

        let mut outcomes = Vec::new();
        for reuse_workspace_id in [false, true, false] {
            if reuse_workspace_id {
                db.delete_unclaimed_workspaces(vec![WorkspaceId(1)], WorkspaceIdClaims::default())
                    .await
                    .unwrap();
                save_workspace().await;
            }
            let released = db
                .record_restore_failure(
                    WorkspaceId(1),
                    original.clone(),
                    HashSet::default(),
                    WorkspaceIdClaims::default(),
                )
                .await
                .unwrap();
            outcomes.push((released, session_binding(&db, WorkspaceId(1))));
        }

        let bound = (Some("previous".to_owned()), original.window_id);
        assert_eq!(
            outcomes,
            vec![(false, bound.clone()), (false, bound), (true, (None, None))]
        );
    }

    #[gpui::test]
    async fn test_exhausted_restore_attempts_keep_unsaved_workspaces_restorable(
        cx: &mut gpui::TestAppContext,
    ) {
        cx.update(|cx| cx.set_global(db::AppDatabase::test_new()));
        let db = cx.update(|cx| WorkspaceDb::global(cx));
        let original = SessionBinding {
            session_id: Some("previous".to_owned()),
            window_id: Some(7),
        };
        for workspace in [
            workspace_with(1, &[], pane_with_items(&[100]), Some("previous")),
            workspace_with(
                2,
                &[Path::new("/gone")],
                pane_with_items(&[200]),
                Some("previous"),
            ),
            workspace_with(
                3,
                &[Path::new("/saved")],
                pane_with_items(&[300]),
                Some("previous"),
            ),
        ] {
            db.save_workspace(SerializedWorkspace {
                window_id: original.window_id,
                ..workspace
            })
            .await;
        }
        let claims = WorkspaceIdClaims::default();
        let _restoration_claim = claims.try_claim(WorkspaceId(1));
        let workspaces_with_unsaved_contents = [WorkspaceId(1), WorkspaceId(2)]
            .into_iter()
            .collect::<HashSet<_>>();

        let mut released = Vec::new();
        for _ in 0..MAX_RESTORE_ATTEMPTS {
            released.push(
                db.record_restore_failure(
                    WorkspaceId(1),
                    original.clone(),
                    workspaces_with_unsaved_contents.clone(),
                    claims.clone(),
                )
                .await
                .unwrap(),
            );
        }

        let detached = (Some("previous".to_owned()), None);
        assert_eq!(
            (
                released,
                [1, 2, 3].map(|id| session_binding(&db, WorkspaceId(id)))
            ),
            (
                vec![false, true],
                [detached.clone(), detached, (None, None)]
            )
        );
    }

    #[gpui::test]
    async fn test_workspace_reads_distinguish_missing_from_unreadable() {
        let db =
            WorkspaceDb::open_test_db("test_workspace_reads_distinguish_missing_from_unreadable")
                .await;
        db.save_workspace(workspace_with(
            1,
            &[Path::new("/project")],
            empty_pane_group(),
            None,
        ))
        .await;
        db.save_workspace(remote_workspace_with(2, "host", &[Path::new("/remote")]))
            .await;
        let location = |workspace_id: i64| {
            WorkspaceDb::read_workspace(&db, WorkspaceId(workspace_id))
                .map(|workspace| workspace.map(|workspace| workspace.location))
                .ok()
        };

        db.write(|conn| conn.exec("UPDATE remote_connections SET kind = 'bogus'")?())
            .await
            .unwrap();
        let with_unknown_remote_connection = (location(1), location(2), location(99));
        db.write(|conn| conn.exec("DROP TABLE bookmarks")?())
            .await
            .unwrap();
        let claimed_by_roots = db
            .claim_settled_workspace_for_roots(
                &[Path::new("/project")],
                None,
                |workspace_id| WorkspaceIdClaims::default().try_claim(workspace_id),
                &WorkspaceWrites::default(),
            )
            .await;
        let with_unreadable_bookmarks = (location(1), claimed_by_roots.is_err());

        assert_eq!(
            (with_unknown_remote_connection, with_unreadable_bookmarks),
            (
                (
                    Some(Some(SerializedWorkspaceLocation::Local)),
                    None,
                    Some(None)
                ),
                (None, true)
            )
        );
    }

    #[gpui::test]
    async fn test_unreadable_saved_workspace_is_never_opened_fresh(cx: &mut gpui::TestAppContext) {
        crate::tests::init_test(cx);
        cx.update(|cx| cx.set_global(db::AppDatabase::test_new()));
        let app_state = cx.update(crate::AppState::test);
        app_state
            .fs
            .as_fake()
            .insert_tree("/project", json!({}))
            .await;
        let db = cx.update(|cx| WorkspaceDb::global(cx));
        db.save_workspace(workspace_with(
            1,
            &[Path::new("/project")],
            pane_with_items(&[100]),
            None,
        ))
        .await;
        db.write(|conn| conn.exec("DROP TABLE bookmarks")?())
            .await
            .unwrap();

        let opened = cx
            .update(|cx| {
                crate::Workspace::new_local(
                    vec![PathBuf::from("/project")],
                    app_state.clone(),
                    None,
                    None,
                    None,
                    crate::OpenMode::NewWindow,
                    cx,
                )
            })
            .await;
        cx.run_until_parked();

        assert_eq!((opened.is_err(), cx.windows().len()), (true, 0));
    }

    #[gpui::test]
    async fn test_corrupt_rows_do_not_fail_recent_workspaces_or_gc(cx: &mut gpui::TestAppContext) {
        cx.update(|cx| cx.set_global(db::AppDatabase::test_new()));
        let fs = fs::FakeFs::new(cx.executor());
        let db = cx.update(|cx| WorkspaceDb::global(cx));
        for id in [1, 2] {
            db.save_workspace(workspace_with(
                id,
                &[Path::new("/project")],
                empty_pane_group(),
                Some("previous"),
            ))
            .await;
        }
        db.write(|conn| {
            conn.exec("UPDATE workspaces SET paths = CAST(X'FF' AS TEXT) WHERE workspace_id = 2")?()
        })
        .await
        .unwrap();

        let recent_ids = db
            .recent_workspaces()
            .map(|rows| rows.into_iter().map(|row| row.0).collect::<Vec<_>>())
            .ok();
        let collected = db
            .garbage_collect_workspaces(
                fs.as_ref(),
                "current",
                &HashSet::default(),
                WorkspaceIdClaims::default().snapshot(),
            )
            .await
            .is_ok();

        assert_eq!((recent_ids, collected), (Some(vec![WorkspaceId(1)]), true));
    }

    #[gpui::test]
    async fn test_undecodable_layout_metadata_degrades_instead_of_failing_restoration() {
        let db = WorkspaceDb::open_test_db(
            "test_undecodable_layout_metadata_degrades_instead_of_failing_restoration",
        )
        .await;
        db.save_workspace(workspace_with(
            1,
            &[],
            SerializedPaneGroup::Group {
                axis: SerializedAxis(Axis::Vertical),
                flexes: Some(vec![1., 1.]),
                children: vec![pane_with_items(&[1, 2]), pane_with_items(&[3])],
            },
            Some("previous"),
        ))
        .await;
        db.write(|conn| {
            conn.exec("UPDATE pane_groups SET axis = 'Diagonal', flexes = 'not json'")?()?;
            conn.exec("UPDATE items SET kind = CAST(X'FF' AS TEXT) WHERE item_id = 2")?()?;
            conn.exec(
                "UPDATE workspaces SET window_state = 'Bogus', display = X'0102', \
                left_dock_active_panel = CAST(X'FF' AS TEXT)",
            )?()
        })
        .await
        .unwrap();

        let restored = db.workspace_for_id(WorkspaceId(1)).map(|workspace| {
            (
                workspace.center_group,
                workspace.window_bounds,
                workspace.display,
                workspace.docks,
            )
        });

        assert_eq!(
            restored,
            Some((
                SerializedPaneGroup::Group {
                    axis: SerializedAxis(Axis::Horizontal),
                    flexes: None,
                    children: vec![
                        SerializedPaneGroup::Pane(SerializedPane::new(
                            vec![
                                SerializedItem::new("Terminal", 1, true, false),
                                SerializedItem::new("\u{FFFD}", 2, true, false),
                            ],
                            true,
                            0,
                        )),
                        pane_with_items(&[3]),
                    ],
                },
                None,
                None,
                DockStructure::default(),
            ))
        );
    }

    #[gpui::test]
    async fn test_persistent_item_ids_are_unique_across_live_items_and_processes(
        cx: &mut gpui::TestAppContext,
    ) {
        cx.update(|cx| cx.set_global(db::AppDatabase::test_new()));
        let (first, second, third) = (cx.new(|_| ()), cx.new(|_| ()), cx.new(|_| ()));
        let claims = cx.update(|cx| {
            [
                claim_persistent_item_id(&first, 7, cx),
                claim_persistent_item_id(&first, 9, cx),
                persistent_item_id(&first, cx),
                claim_persistent_item_id(&second, 7, cx),
                persistent_item_id(&third, cx),
                persistent_item_id(&second, cx),
            ]
        });
        drop(first);
        cx.run_until_parked();
        let fourth = cx.new(|_| ());
        let after_release = cx.update(|cx| {
            let reclaimed = claim_persistent_item_id(&fourth, 7, cx);
            cx.remove_global::<PersistentItemIds>();
            [reclaimed, persistent_item_id(&fourth, cx)]
        });

        assert_eq!(
            (claims, after_release),
            ([7, 7, 7, 1 << 33, (1 << 33) | 1, 1 << 33], [7, 2 << 33])
        );
    }

    #[gpui::test]
    async fn test_closing_restored_workspace_before_first_save_releases_its_session_window(
        cx: &mut gpui::TestAppContext,
    ) {
        crate::tests::init_test(cx);
        let fs = fs::FakeFs::new(cx.executor());
        let project = Project::test(fs, [], cx).await;
        let (multi_workspace, cx) =
            cx.add_window_view(|window, cx| MultiWorkspace::test_new(project, window, cx));
        let workspace = multi_workspace.read_with(cx, |mw, _| mw.workspace().clone());
        let db = cx.update(|_, cx| WorkspaceDb::global(cx));
        for id in [101, 102] {
            db.save_workspace(SerializedWorkspace {
                window_id: Some(7),
                ..workspace_with(id, &[], empty_pane_group(), Some("previous"))
            })
            .await;
        }
        workspace.update(cx, |workspace, _| {
            workspace.set_database_id(WorkspaceId(101));
            *workspace.adopted_session_window.lock() = Some(SessionWindow {
                session_id: "previous".to_owned(),
                window_id: 7,
            });
        });

        workspace
            .update_in(cx, |workspace, window, cx| {
                workspace.leave_session(window, cx)
            })
            .await;

        let previous_session_workspaces = db
            .session_workspaces("previous".to_owned())
            .unwrap()
            .into_iter()
            .map(|(workspace_id, ..)| workspace_id)
            .collect::<Vec<_>>();
        assert_eq!(previous_session_workspaces, Vec::new());
    }

    #[gpui::test]
    async fn test_legacy_multi_workspace_states_move_to_last_session(
        cx: &mut gpui::TestAppContext,
    ) {
        cx.update(|cx| cx.set_global(db::AppDatabase::test_new()));
        let kvp = cx.update(|cx| KeyValueStore::global(cx));
        let state = |active_workspace_id| {
            serde_json::to_string(&model::MultiWorkspaceState {
                active_workspace_id: Some(WorkspaceId(active_workspace_id)),
                ..model::MultiWorkspaceState::default()
            })
            .unwrap()
        };
        let store = kvp.scoped(MULTI_WORKSPACE_STATE_NAMESPACE);
        let [first_window, second_window] = [11u64, 12].map(WindowId::from);
        let legacy_key = |window_id: WindowId| window_id.as_u64().to_string();
        for (key, active_workspace_id) in [
            (legacy_key(first_window), 4),
            (multi_workspace_state_key("last", second_window), 5),
            (legacy_key(second_window), 6),
        ] {
            store.write(key, state(active_workspace_id)).await.unwrap();
        }

        migrate_legacy_multi_workspace_states(&kvp, Some("last")).await;

        let states = cx.update(|cx| {
            [first_window, second_window].map(|window_id| {
                read_multi_workspace_state(Some("last"), window_id, cx).active_workspace_id
            })
        });
        assert_eq!(
            (
                states,
                store.read(&legacy_key(first_window)).unwrap(),
                store.read(&legacy_key(second_window)).unwrap()
            ),
            ([Some(WorkspaceId(4)), Some(WorkspaceId(5))], None, None)
        );
    }

    #[gpui::test]
    async fn test_last_session_workspace_locations_remote(cx: &mut gpui::TestAppContext) {
        let fs = fs::FakeFs::new(cx.executor());
        let db =
            WorkspaceDb::open_test_db("test_serializing_workspaces_last_session_workspaces_remote")
                .await;

        let remote_connections = [
            ("host-1", "my-user-1"),
            ("host-2", "my-user-2"),
            ("host-3", "my-user-3"),
            ("host-4", "my-user-4"),
        ]
        .into_iter()
        .map(|(host, user)| async {
            let options = RemoteConnectionOptions::Ssh(SshConnectionOptions {
                host: host.into(),
                username: Some(user.to_string()),
                args: Some(Vec::new()),
                ..Default::default()
            });
            db.get_or_create_remote_connection(options.clone())
                .await
                .unwrap();
            options
        })
        .collect::<Vec<_>>();

        let remote_connections = futures::future::join_all(remote_connections).await;

        let workspaces = [
            (1, remote_connections[0].clone(), 9),
            (2, remote_connections[1].clone(), 5),
            (3, remote_connections[2].clone(), 8),
            (4, remote_connections[3].clone(), 2),
        ]
        .into_iter()
        .map(|(id, remote_connection, window_id)| SerializedWorkspace {
            id: WorkspaceId(id),
            paths: PathList::default(),
            identity_paths: None,
            location: SerializedWorkspaceLocation::Remote(remote_connection),
            center_group: Default::default(),
            window_bounds: Default::default(),
            display: Default::default(),
            docks: Default::default(),
            centered_layout: false,
            session_id: Some("one-session".to_owned()),
            bookmarks: Default::default(),
            breakpoints: Default::default(),
            window_id: Some(window_id),
            user_toolchains: Default::default(),
            recent_navigation_history: Default::default(),
            unserialized_root_files: None,
        })
        .collect::<Vec<_>>();

        for workspace in workspaces.iter() {
            db.save_workspace(workspace.clone()).await;
        }

        let stack = Some(Vec::from([
            WindowId::from(2), // Top
            WindowId::from(8),
            WindowId::from(5),
            WindowId::from(9), // Bottom
        ]));

        let have = db
            .last_session_workspace_locations("one-session", stack, fs.as_ref())
            .await
            .unwrap();
        assert_eq!(have.len(), 4);
        assert_eq!(
            have[0],
            SessionWorkspace {
                workspace_id: WorkspaceId(4),
                location: SerializedWorkspaceLocation::Remote(remote_connections[3].clone()),
                paths: PathList::default(),
                session_id: Some("one-session".to_owned()),
                window_id: Some(WindowId::from(2u64)),
            }
        );
        assert_eq!(
            have[1],
            SessionWorkspace {
                workspace_id: WorkspaceId(3),
                location: SerializedWorkspaceLocation::Remote(remote_connections[2].clone()),
                paths: PathList::default(),
                session_id: Some("one-session".to_owned()),
                window_id: Some(WindowId::from(8u64)),
            }
        );
        assert_eq!(
            have[2],
            SessionWorkspace {
                workspace_id: WorkspaceId(2),
                location: SerializedWorkspaceLocation::Remote(remote_connections[1].clone()),
                paths: PathList::default(),
                session_id: Some("one-session".to_owned()),
                window_id: Some(WindowId::from(5u64)),
            }
        );
        assert_eq!(
            have[3],
            SessionWorkspace {
                workspace_id: WorkspaceId(1),
                location: SerializedWorkspaceLocation::Remote(remote_connections[0].clone()),
                paths: PathList::default(),
                session_id: Some("one-session".to_owned()),
                window_id: Some(WindowId::from(9u64)),
            }
        );
    }

    #[gpui::test]
    async fn test_get_or_create_ssh_project() {
        let db = WorkspaceDb::open_test_db("test_get_or_create_ssh_project").await;

        let host = "example.com".to_string();
        let port = Some(22_u16);
        let user = Some("user".to_string());

        let connection_id = db
            .get_or_create_remote_connection(RemoteConnectionOptions::Ssh(SshConnectionOptions {
                host: host.clone().into(),
                port,
                username: user.clone(),
                ..Default::default()
            }))
            .await
            .unwrap();

        // Test that calling the function again with the same parameters returns the same project
        let same_connection = db
            .get_or_create_remote_connection(RemoteConnectionOptions::Ssh(SshConnectionOptions {
                host: host.clone().into(),
                port,
                username: user.clone(),
                ..Default::default()
            }))
            .await
            .unwrap();

        assert_eq!(connection_id, same_connection);

        // Test with different parameters
        let host2 = "otherexample.com".to_string();
        let port2 = None;
        let user2 = Some("otheruser".to_string());

        let different_connection = db
            .get_or_create_remote_connection(RemoteConnectionOptions::Ssh(SshConnectionOptions {
                host: host2.clone().into(),
                port: port2,
                username: user2.clone(),
                ..Default::default()
            }))
            .await
            .unwrap();

        assert_ne!(connection_id, different_connection);
    }

    #[gpui::test]
    async fn test_get_or_create_ssh_project_with_null_user() {
        let db = WorkspaceDb::open_test_db("test_get_or_create_ssh_project_with_null_user").await;

        let (host, port, user) = ("example.com".to_string(), None, None);

        let connection_id = db
            .get_or_create_remote_connection(RemoteConnectionOptions::Ssh(SshConnectionOptions {
                host: host.clone().into(),
                port,
                username: None,
                ..Default::default()
            }))
            .await
            .unwrap();

        let same_connection_id = db
            .get_or_create_remote_connection(RemoteConnectionOptions::Ssh(SshConnectionOptions {
                host: host.clone().into(),
                port,
                username: user.clone(),
                ..Default::default()
            }))
            .await
            .unwrap();

        assert_eq!(connection_id, same_connection_id);
    }

    #[gpui::test]
    async fn test_get_remote_connections() {
        let db = WorkspaceDb::open_test_db("test_get_remote_connections").await;

        let connections = [
            ("example.com".to_string(), None, None),
            (
                "anotherexample.com".to_string(),
                Some(123_u16),
                Some("user2".to_string()),
            ),
            ("yetanother.com".to_string(), Some(345_u16), None),
        ];

        let mut ids = Vec::new();
        for (host, port, user) in connections.iter() {
            ids.push(
                db.get_or_create_remote_connection(RemoteConnectionOptions::Ssh(
                    SshConnectionOptions {
                        host: host.clone().into(),
                        port: *port,
                        username: user.clone(),
                        ..Default::default()
                    },
                ))
                .await
                .unwrap(),
            );
        }

        let stored_connections = db.remote_connections().unwrap();
        assert_eq!(
            stored_connections,
            [
                (
                    ids[0],
                    RemoteConnectionOptions::Ssh(SshConnectionOptions {
                        host: "example.com".into(),
                        port: None,
                        username: None,
                        args: Some(Vec::new()),
                        ..Default::default()
                    }),
                ),
                (
                    ids[1],
                    RemoteConnectionOptions::Ssh(SshConnectionOptions {
                        host: "anotherexample.com".into(),
                        port: Some(123),
                        username: Some("user2".into()),
                        args: Some(Vec::new()),
                        ..Default::default()
                    }),
                ),
                (
                    ids[2],
                    RemoteConnectionOptions::Ssh(SshConnectionOptions {
                        host: "yetanother.com".into(),
                        port: Some(345),
                        username: None,
                        args: Some(Vec::new()),
                        ..Default::default()
                    }),
                ),
            ]
            .into_iter()
            .collect::<HashMap<_, _>>(),
        );
    }

    #[gpui::test]
    async fn test_ssh_connection_arguments_separate_remote_connections() {
        let db =
            WorkspaceDb::open_test_db("test_ssh_connection_arguments_separate_remote_connections")
                .await;
        db.write(|conn| {
            conn.exec("INSERT INTO remote_connections (kind, host) VALUES ('ssh', 'host')")?()?;
            conn.exec(
                "INSERT INTO workspaces (workspace_id, paths, remote_connection_id) VALUES (41, '/legacy', 1)",
            )?()
        })
        .await
        .unwrap();
        let ssh = |target: &str, key: &str| {
            RemoteConnectionOptions::Ssh(SshConnectionOptions {
                host: "host".into(),
                args: Some(vec![
                    "-i".to_string(),
                    key.to_string(),
                    "-o".to_string(),
                    format!("Hostname={target}"),
                ]),
                ..Default::default()
            })
        };
        let legacy = RemoteConnectionOptions::Ssh(SshConnectionOptions {
            host: "host".into(),
            ..Default::default()
        });

        let find_workspace = async |root: &str, target: &str, key: &str| {
            let connections = db
                .equivalent_remote_connections(ssh(target, key))
                .await
                .unwrap();
            db.remote_workspace_for_roots(&[Path::new(root)], &connections)
                .map(|workspace| workspace.id)
        };

        let mut ids = Vec::new();
        for (target, key) in [
            ("host-a", "/keys/a"),
            ("host-b", "/keys/b"),
            ("host-a", "/keys/rotated"),
            ("host-a", "/keys/a"),
        ] {
            ids.push(
                db.get_or_create_remote_connection(ssh(target, key))
                    .await
                    .unwrap(),
            );
        }
        db.save_workspace(SerializedWorkspace {
            location: SerializedWorkspaceLocation::Remote(ssh("host-a", "/keys/a")),
            ..remote_workspace_with(7, "host", &[Path::new("/repo")])
        })
        .await;
        let found_after_rotation = find_workspace("/repo", "host-a", "/keys/rotated").await;
        let found_on_other_target = find_workspace("/repo", "host-b", "/keys/b").await;
        let legacy_before_resolution = db.remote_connection(RemoteConnectionId(1)).unwrap();

        db.sync_ssh_connections(
            vec![ConfiguredSshConnection {
                host: "host".to_string(),
                username: None,
                port: None,
                args: vec![
                    "-i".to_string(),
                    "/keys/b".to_string(),
                    "-o".to_string(),
                    "Hostname=host-b".to_string(),
                ],
            }],
            SshArgumentRenames::Keep,
        )
        .await
        .unwrap();
        let legacy_found_on_resolved_target = find_workspace("/legacy", "host-b", "/keys/b").await;

        assert_eq!(
            (
                ids,
                found_after_rotation,
                found_on_other_target,
                legacy_before_resolution,
                legacy_found_on_resolved_target,
            ),
            (
                vec![
                    RemoteConnectionId(2),
                    RemoteConnectionId(3),
                    RemoteConnectionId(4),
                    RemoteConnectionId(2),
                ],
                None,
                None,
                legacy,
                Some(WorkspaceId(41)),
            )
        );
    }

    #[gpui::test]
    async fn test_workspace_reads_wait_for_queued_writes_to_that_workspace(
        cx: &mut gpui::TestAppContext,
    ) {
        let db = WorkspaceDb::open_test_db(
            "test_workspace_reads_wait_for_queued_writes_to_that_workspace",
        )
        .await;
        let root = [Path::new("/root")];
        db.save_workspace(workspace_with(1, &root, pane_with_items(&[1]), None))
            .await;
        let writes = WorkspaceWrites::default();
        let (release_tx, release_rx) = futures::channel::oneshot::channel::<()>();
        let queued_write = cx.background_spawn({
            let db = db.clone();
            async move {
                release_rx.await.ok();
                db.save_workspace(workspace_with(1, &root, pane_with_items(&[1, 2]), None))
                    .await;
            }
        });
        writes.record(WorkspaceId(1), queued_write.shared());
        let read = cx.background_spawn({
            let db = db.clone();
            let writes = writes.clone();
            async move {
                db.claim_settled_workspace_for_roots(
                    &root,
                    None,
                    |workspace_id| WorkspaceIdClaims::default().try_claim(workspace_id),
                    &writes,
                )
                .await
                .unwrap()
                .map(|(workspace, _)| workspace.center_group.item_ids())
            }
        });
        cx.run_until_parked();
        release_tx.send(()).ok();

        assert_eq!(read.await, Some(vec![1, 2]));
    }

    #[gpui::test]
    async fn test_saved_ssh_sessions_follow_edited_settings_entries() {
        let db = WorkspaceDb(db::AppDatabase::test_new().0);
        let configured = |host: &str, key: &str| ConfiguredSshConnection {
            host: host.to_string(),
            username: None,
            port: None,
            args: vec!["-i".to_string(), key.to_string()],
        };
        let ssh = |host: &str, key: &str| {
            RemoteConnectionOptions::Ssh(SshConnectionOptions {
                host: host.into(),
                args: Some(vec!["-i".to_string(), key.to_string()]),
                ..Default::default()
            })
        };
        let find_workspace = async |host: &str, key: &str| {
            let connections = db
                .equivalent_remote_connections(ssh(host, key))
                .await
                .unwrap();
            db.remote_workspace_for_roots(&[Path::new("/repo")], &connections)
                .map(|workspace| workspace.id)
        };

        db.sync_ssh_connections(
            vec![
                configured("edited", "/old"),
                configured("shared", "/a"),
                configured("shared", "/b"),
            ],
            SshArgumentRenames::Keep,
        )
        .await
        .unwrap();
        for (id, host, key) in [(1, "edited", "/old"), (2, "shared", "/b")] {
            db.save_workspace(SerializedWorkspace {
                location: SerializedWorkspaceLocation::Remote(ssh(host, key)),
                ..remote_workspace_with(id, host, &[Path::new("/repo")])
            })
            .await;
        }
        db.sync_ssh_connections(
            vec![configured("edited", "/new"), configured("shared", "/a")],
            SshArgumentRenames::Keep,
        )
        .await
        .unwrap();
        let after_edit = [
            find_workspace("edited", "/new").await,
            find_workspace("edited", "/old").await,
            find_workspace("shared", "/a").await,
            find_workspace("shared", "/b").await,
        ];
        db.sync_ssh_connections(
            vec![
                configured("edited", "/new"),
                configured("edited", "/old"),
                configured("shared", "/a"),
            ],
            SshArgumentRenames::Keep,
        )
        .await
        .unwrap();
        let after_readding_old = find_workspace("edited", "/old").await;

        assert_eq!(
            (after_edit, after_readding_old),
            (
                [
                    Some(WorkspaceId(1)),
                    Some(WorkspaceId(1)),
                    None,
                    Some(WorkspaceId(2)),
                ],
                None,
            )
        );
    }

    #[gpui::test]
    async fn test_stale_ssh_clients_keep_following_many_edited_entries() {
        let db = WorkspaceDb(db::AppDatabase::test_new().0);
        let hosts = (0..=64)
            .map(|index| format!("host-{index}"))
            .collect::<Vec<_>>();
        let configured = |key: &str| {
            hosts
                .iter()
                .map(|host| ConfiguredSshConnection {
                    host: host.clone(),
                    username: None,
                    port: None,
                    args: vec!["-i".to_string(), key.to_string()],
                })
                .collect::<Vec<_>>()
        };
        let ssh = |host: &str, key: &str| {
            RemoteConnectionOptions::Ssh(SshConnectionOptions {
                host: host.into(),
                args: Some(vec!["-i".to_string(), key.to_string()]),
                ..Default::default()
            })
        };

        let save_with_key = async |index: usize, key: &str| {
            db.save_workspace(SerializedWorkspace {
                location: SerializedWorkspaceLocation::Remote(ssh(&hosts[index], key)),
                ..remote_workspace_with(index as u64 + 1, &hosts[index], &[Path::new("/repo")])
            })
            .await;
        };
        let stale_hosts = || {
            hosts
                .iter()
                .enumerate()
                .filter(|(index, host)| {
                    db.workspace_for_id(WorkspaceId(*index as i64 + 1))
                        .map(|workspace| workspace.location)
                        != Some(SerializedWorkspaceLocation::Remote(ssh(host, "/new")))
                })
                .map(|(_, host)| host.clone())
                .collect::<Vec<_>>()
        };

        db.sync_ssh_connections(configured("/old"), SshArgumentRenames::Keep)
            .await
            .unwrap();
        for index in 0..hosts.len() {
            save_with_key(index, "/old").await;
        }
        db.sync_ssh_connections(configured("/new"), SshArgumentRenames::Keep)
            .await
            .unwrap();
        save_with_key(0, "/old").await;
        let after_stale_save = stale_hosts();
        db.sync_ssh_connections(configured("/new"), SshArgumentRenames::Discard)
            .await
            .unwrap();

        assert_eq!(
            (after_stale_save, stale_hosts()),
            (Vec::<String>::new(), Vec::<String>::new())
        );
    }

    #[gpui::test]
    async fn test_saved_project_groups_follow_edited_ssh_settings_across_restarts() {
        let db = WorkspaceDb(db::AppDatabase::test_new().0);
        let configured = |key: &str| {
            vec![ConfiguredSshConnection {
                host: "host".to_string(),
                username: None,
                port: None,
                args: vec!["-i".to_string(), key.to_string()],
            }]
        };
        let state_key = multi_workspace_state_key("session", WindowId::from(1u64));
        let write_state_with_key = async |key: &str| {
            let state = model::MultiWorkspaceState {
                project_groups: vec![model::SerializedProjectGroup {
                    path_list: PathList::new(&["/repo"]).serialize(),
                    location: SerializedWorkspaceLocation::Remote(RemoteConnectionOptions::Ssh(
                        SshConnectionOptions {
                            host: "host".into(),
                            args: Some(vec!["-i".to_string(), key.to_string()]),
                            ..Default::default()
                        },
                    )),
                    expanded: true,
                }],
                ..Default::default()
            };
            let state_key = state_key.clone();
            db.write(move |conn| {
                db::kvp::write_scoped_value(
                    conn,
                    MULTI_WORKSPACE_STATE_NAMESPACE,
                    &state_key,
                    &serde_json::to_string(&state).unwrap(),
                )
            })
            .await
            .unwrap();
        };
        let saved_group_arguments = async || {
            let state_key = state_key.clone();
            let state = db
                .write(move |conn| {
                    db::kvp::read_scoped_value(conn, MULTI_WORKSPACE_STATE_NAMESPACE, &state_key)
                })
                .await
                .unwrap()
                .unwrap();
            serde_json::from_str::<model::MultiWorkspaceState>(&state)
                .unwrap()
                .project_groups
                .into_iter()
                .map(|group| match group.location {
                    SerializedWorkspaceLocation::Remote(RemoteConnectionOptions::Ssh(options)) => {
                        options.args
                    }
                    _ => None,
                })
                .collect::<Vec<_>>()
        };

        db.sync_ssh_connections(configured("/old"), SshArgumentRenames::Discard)
            .await
            .unwrap();
        write_state_with_key("/old").await;
        db.sync_ssh_connections(configured("/new"), SshArgumentRenames::Keep)
            .await
            .unwrap();
        let after_edit = saved_group_arguments().await;
        write_state_with_key("/old").await;
        db.sync_ssh_connections(configured("/new"), SshArgumentRenames::Discard)
            .await
            .unwrap();

        let new_arguments = Some(vec!["-i".to_string(), "/new".to_string()]);
        assert_eq!(
            (after_edit, saved_group_arguments().await),
            (vec![new_arguments.clone()], vec![new_arguments])
        );
    }

    #[gpui::test]
    async fn test_session_bound_remote_workspaces_may_share_roots() {
        let db =
            WorkspaceDb::open_test_db("test_session_bound_remote_workspaces_may_share_roots").await;
        for workspace in [
            remote_workspace_with(1, "host", &[Path::new("/repo")]),
            remote_workspace_with(2, "host", &[Path::new("/other"), Path::new("/repo")]),
            remote_workspace_with(2, "host", &[Path::new("/repo")]),
        ] {
            db.save_workspace(SerializedWorkspace {
                session_id: Some("session".to_owned()),
                ..workspace
            })
            .await;
        }

        let mut workspaces = db
            .session_workspaces("session".to_owned())
            .unwrap()
            .into_iter()
            .map(|(workspace_id, paths, _, _)| (workspace_id, paths))
            .collect::<Vec<_>>();
        workspaces.sort_by_key(|(workspace_id, _)| i64::from(*workspace_id));
        assert_eq!(
            workspaces,
            vec![
                (WorkspaceId(1), PathList::new(&["/repo"])),
                (WorkspaceId(2), PathList::new(&["/repo"])),
            ]
        );
    }

    #[gpui::test]
    async fn test_saving_a_workspace_keeps_unbound_duplicates_that_hold_items() {
        let db = WorkspaceDb::open_test_db(
            "test_saving_a_workspace_keeps_unbound_duplicates_that_hold_items",
        )
        .await;
        let root = [Path::new("/shared")];
        for workspace in [
            workspace_with(1, &root, empty_pane_group(), None),
            workspace_with(2, &root, pane_with_items(&[1]), None),
            workspace_with(3, &root, empty_pane_group(), Some("session")),
        ] {
            db.save_workspace(workspace).await;
        }

        assert_eq!(
            [1, 2, 3].map(|id| db.workspace_for_id(WorkspaceId(id)).is_some()),
            [false, true, true]
        );
    }

    #[gpui::test]
    async fn test_simple_split() {
        zlog::init_test();

        let db = WorkspaceDb::open_test_db("simple_split").await;

        //  -----------------
        //  | 1,2   | 5,6   |
        //  | - - - |       |
        //  | 3,4   |       |
        //  -----------------
        let center_pane = group(
            Axis::Horizontal,
            vec![
                group(
                    Axis::Vertical,
                    vec![
                        SerializedPaneGroup::Pane(SerializedPane::new(
                            vec![
                                SerializedItem::new("Terminal", 1, false, false),
                                SerializedItem::new("Terminal", 2, true, false),
                            ],
                            false,
                            0,
                        )),
                        SerializedPaneGroup::Pane(SerializedPane::new(
                            vec![
                                SerializedItem::new("Terminal", 4, false, false),
                                SerializedItem::new("Terminal", 3, true, false),
                            ],
                            true,
                            0,
                        )),
                    ],
                ),
                SerializedPaneGroup::Pane(SerializedPane::new(
                    vec![
                        SerializedItem::new("Terminal", 5, true, false),
                        SerializedItem::new("Terminal", 6, false, false),
                    ],
                    false,
                    0,
                )),
            ],
        );

        let workspace = default_workspace(&["/tmp"], &center_pane);

        db.save_workspace(workspace.clone()).await;

        let new_workspace = db.workspace_for_roots(&["/tmp"]).unwrap();

        assert_eq!(workspace.center_group, new_workspace.center_group);
    }

    #[gpui::test]
    async fn test_cleanup_panes() {
        zlog::init_test();

        let db = WorkspaceDb::open_test_db("test_cleanup_panes").await;

        let center_pane = group(
            Axis::Horizontal,
            vec![
                group(
                    Axis::Vertical,
                    vec![
                        SerializedPaneGroup::Pane(SerializedPane::new(
                            vec![
                                SerializedItem::new("Terminal", 1, false, false),
                                SerializedItem::new("Terminal", 2, true, false),
                            ],
                            false,
                            0,
                        )),
                        SerializedPaneGroup::Pane(SerializedPane::new(
                            vec![
                                SerializedItem::new("Terminal", 4, false, false),
                                SerializedItem::new("Terminal", 3, true, false),
                            ],
                            true,
                            0,
                        )),
                    ],
                ),
                SerializedPaneGroup::Pane(SerializedPane::new(
                    vec![
                        SerializedItem::new("Terminal", 5, false, false),
                        SerializedItem::new("Terminal", 6, true, false),
                    ],
                    false,
                    0,
                )),
            ],
        );

        let id = &["/tmp"];

        let mut workspace = default_workspace(id, &center_pane);

        db.save_workspace(workspace.clone()).await;

        workspace.center_group = group(
            Axis::Vertical,
            vec![
                SerializedPaneGroup::Pane(SerializedPane::new(
                    vec![
                        SerializedItem::new("Terminal", 1, false, false),
                        SerializedItem::new("Terminal", 2, true, false),
                    ],
                    false,
                    0,
                )),
                SerializedPaneGroup::Pane(SerializedPane::new(
                    vec![
                        SerializedItem::new("Terminal", 4, true, false),
                        SerializedItem::new("Terminal", 3, false, false),
                    ],
                    true,
                    0,
                )),
            ],
        );

        db.save_workspace(workspace.clone()).await;

        let new_workspace = db.workspace_for_roots(id).unwrap();

        assert_eq!(workspace.center_group, new_workspace.center_group);
    }

    #[gpui::test]
    async fn test_empty_workspace_window_bounds() {
        zlog::init_test();

        let db = WorkspaceDb::open_test_db("test_empty_workspace_window_bounds").await;
        let id = db.next_id().await.unwrap();

        // Create a workspace with empty paths (empty workspace)
        let empty_paths: &[&str] = &[];
        let display_uuid = Uuid::new_v4();
        let window_bounds = SerializedWindowBounds(WindowBounds::Windowed(Bounds {
            origin: point(px(100.0), px(200.0)),
            size: size(px(800.0), px(600.0)),
        }));

        let workspace = SerializedWorkspace {
            id,
            paths: PathList::new(empty_paths),
            identity_paths: None,
            location: SerializedWorkspaceLocation::Local,
            center_group: Default::default(),
            window_bounds: None,
            display: None,
            docks: Default::default(),
            bookmarks: Default::default(),
            breakpoints: Default::default(),
            centered_layout: false,
            session_id: None,
            window_id: None,
            user_toolchains: Default::default(),
            recent_navigation_history: Default::default(),
            unserialized_root_files: None,
        };

        // Save the workspace (this creates the record with empty paths)
        db.save_workspace(workspace.clone()).await;

        // Save window bounds separately (as the actual code does via set_window_open_status)
        db.set_window_open_status(id, window_bounds, display_uuid, None)
            .await
            .unwrap();

        // Empty workspaces cannot be retrieved by paths (they'd all match).
        // They must be retrieved by workspace_id.
        assert!(db.workspace_for_roots(empty_paths).is_none());

        // Retrieve using workspace_for_id instead
        let retrieved = db.workspace_for_id(id).unwrap();

        // Verify window bounds were persisted
        assert_eq!(retrieved.id, id);
        assert!(retrieved.window_bounds.is_some());
        assert_eq!(retrieved.window_bounds.unwrap().0, window_bounds.0);
        assert!(retrieved.display.is_some());
        assert_eq!(retrieved.display.unwrap(), display_uuid);
    }

    #[gpui::test]
    async fn test_last_session_workspace_locations_groups_by_window_id(
        cx: &mut gpui::TestAppContext,
    ) {
        let dir1 = tempfile::TempDir::with_prefix("dir1").unwrap();
        let dir2 = tempfile::TempDir::with_prefix("dir2").unwrap();
        let dir3 = tempfile::TempDir::with_prefix("dir3").unwrap();
        let dir4 = tempfile::TempDir::with_prefix("dir4").unwrap();
        let dir5 = tempfile::TempDir::with_prefix("dir5").unwrap();

        let fs = fs::FakeFs::new(cx.executor());
        fs.insert_tree(dir1.path(), json!({})).await;
        fs.insert_tree(dir2.path(), json!({})).await;
        fs.insert_tree(dir3.path(), json!({})).await;
        fs.insert_tree(dir4.path(), json!({})).await;
        fs.insert_tree(dir5.path(), json!({})).await;

        let db =
            WorkspaceDb::open_test_db("test_last_session_workspace_locations_groups_by_window_id")
                .await;

        // Simulate two MultiWorkspace windows each containing two workspaces,
        // plus one single-workspace window:
        //   Window 10: workspace 1, workspace 2
        //   Window 20: workspace 3, workspace 4
        //   Window 30: workspace 5 (only one)
        //
        // On session restore, the caller should be able to group these by
        // window_id to reconstruct the MultiWorkspace windows.
        let workspaces_data: Vec<(i64, &Path, u64)> = vec![
            (1, dir1.path(), 10),
            (2, dir2.path(), 10),
            (3, dir3.path(), 20),
            (4, dir4.path(), 20),
            (5, dir5.path(), 30),
        ];

        for (id, dir, window_id) in &workspaces_data {
            db.save_workspace(SerializedWorkspace {
                id: WorkspaceId(*id),
                paths: PathList::new(&[*dir]),
                identity_paths: None,
                location: SerializedWorkspaceLocation::Local,
                center_group: Default::default(),
                window_bounds: Default::default(),
                display: Default::default(),
                docks: Default::default(),
                centered_layout: false,
                session_id: Some("test-session".to_owned()),
                bookmarks: Default::default(),
                breakpoints: Default::default(),
                window_id: Some(*window_id),
                user_toolchains: Default::default(),
                recent_navigation_history: Default::default(),
                unserialized_root_files: None,
            })
            .await;
        }

        let locations = db
            .last_session_workspace_locations("test-session", None, fs.as_ref())
            .await
            .unwrap();

        // All 5 workspaces should be returned with their window_ids.
        assert_eq!(locations.len(), 5);

        // Every entry should have a window_id so the caller can group them.
        for session_workspace in &locations {
            assert!(
                session_workspace.window_id.is_some(),
                "workspace {:?} missing window_id",
                session_workspace.workspace_id
            );
        }

        // Group by window_id, simulating what the restoration code should do.
        let mut by_window: HashMap<WindowId, Vec<WorkspaceId>> = HashMap::default();
        for session_workspace in &locations {
            if let Some(window_id) = session_workspace.window_id {
                by_window
                    .entry(window_id)
                    .or_default()
                    .push(session_workspace.workspace_id);
            }
        }

        // Should produce 3 windows, not 5.
        assert_eq!(
            by_window.len(),
            3,
            "Expected 3 window groups, got {}: {:?}",
            by_window.len(),
            by_window
        );

        // Window 10 should contain workspaces 1 and 2.
        let window_10 = by_window.get(&WindowId::from(10u64)).unwrap();
        assert_eq!(window_10.len(), 2);
        assert!(window_10.contains(&WorkspaceId(1)));
        assert!(window_10.contains(&WorkspaceId(2)));

        // Window 20 should contain workspaces 3 and 4.
        let window_20 = by_window.get(&WindowId::from(20u64)).unwrap();
        assert_eq!(window_20.len(), 2);
        assert!(window_20.contains(&WorkspaceId(3)));
        assert!(window_20.contains(&WorkspaceId(4)));

        // Window 30 should contain only workspace 5.
        let window_30 = by_window.get(&WindowId::from(30u64)).unwrap();
        assert_eq!(window_30.len(), 1);
        assert!(window_30.contains(&WorkspaceId(5)));
    }

    #[gpui::test]
    async fn test_read_serialized_multi_workspaces_with_state(cx: &mut gpui::TestAppContext) {
        use crate::persistence::model::MultiWorkspaceState;

        // Write multi-workspace state for two windows via the scoped KVP.
        let window_10 = WindowId::from(10u64);
        let window_20 = WindowId::from(20u64);

        let kvp = cx.update(|cx| KeyValueStore::global(cx));

        write_multi_workspace_state(
            &kvp,
            "session",
            window_10,
            MultiWorkspaceState {
                active_workspace_id: Some(WorkspaceId(2)),
                project_groups: vec![],
                sidebar_open: true,
                sidebar_state: None,
            },
        )
        .await;

        write_multi_workspace_state(
            &kvp,
            "session",
            window_20,
            MultiWorkspaceState {
                active_workspace_id: Some(WorkspaceId(3)),
                project_groups: vec![],
                sidebar_open: false,
                sidebar_state: None,
            },
        )
        .await;

        // Build session workspaces: two in window 10, one in window 20, one with no window.
        let session_workspaces = vec![
            SessionWorkspace {
                workspace_id: WorkspaceId(1),
                location: SerializedWorkspaceLocation::Local,
                paths: PathList::new(&["/a"]),
                session_id: Some("session".to_owned()),
                window_id: Some(window_10),
            },
            SessionWorkspace {
                workspace_id: WorkspaceId(2),
                location: SerializedWorkspaceLocation::Local,
                paths: PathList::new(&["/b"]),
                session_id: Some("session".to_owned()),
                window_id: Some(window_10),
            },
            SessionWorkspace {
                workspace_id: WorkspaceId(3),
                location: SerializedWorkspaceLocation::Local,
                paths: PathList::new(&["/c"]),
                session_id: Some("session".to_owned()),
                window_id: Some(window_20),
            },
            SessionWorkspace {
                workspace_id: WorkspaceId(4),
                location: SerializedWorkspaceLocation::Local,
                paths: PathList::new(&["/d"]),
                session_id: Some("session".to_owned()),
                window_id: None,
            },
        ];

        let results = cx
            .update(|cx| read_serialized_multi_workspaces(session_workspaces, cx))
            .await;

        // Should produce 3 results: window 10, window 20, and the orphan.
        assert_eq!(results.len(), 3);

        // Window 10: active_workspace_id = 2 picks workspace 2 (paths /b), sidebar open.
        let group_10 = &results[0];
        assert_eq!(group_10.active_workspace.workspace_id, WorkspaceId(2));
        assert_eq!(group_10.state.active_workspace_id, Some(WorkspaceId(2)));
        assert_eq!(group_10.state.sidebar_open, true);

        // Window 20: active_workspace_id = 3 picks workspace 3 (paths /c), sidebar closed.
        let group_20 = &results[1];
        assert_eq!(group_20.active_workspace.workspace_id, WorkspaceId(3));
        assert_eq!(group_20.state.active_workspace_id, Some(WorkspaceId(3)));
        assert_eq!(group_20.state.sidebar_open, false);

        // Orphan: no active_workspace_id, falls back to first workspace (id 4).
        let group_none = &results[2];
        assert_eq!(group_none.active_workspace.workspace_id, WorkspaceId(4));
        assert_eq!(group_none.state.active_workspace_id, None);
        assert_eq!(group_none.state.sidebar_open, false);
    }

    #[gpui::test]
    async fn test_flush_serialization_completes_before_quit(cx: &mut gpui::TestAppContext) {
        crate::tests::init_test(cx);

        let fs = fs::FakeFs::new(cx.executor());
        let project = Project::test(fs.clone(), [], cx).await;

        let (multi_workspace, cx) =
            cx.add_window_view(|window, cx| MultiWorkspace::test_new(project.clone(), window, cx));

        let workspace = multi_workspace.read_with(cx, |mw, _| mw.workspace().clone());

        let db = cx.update(|_, cx| WorkspaceDb::global(cx));

        // Assign a database_id so serialization will actually persist.
        let workspace_id = db.next_id().await.unwrap();
        workspace.update(cx, |ws, _cx| {
            ws.set_database_id(workspace_id);
        });

        // Mutate some workspace state.
        db.set_centered_layout(workspace_id, true).await.unwrap();

        // Call flush_serialization and await the returned task directly
        // (without run_until_parked — the point is that awaiting the task
        // alone is sufficient).
        let task = multi_workspace.update_in(cx, |mw, window, cx| {
            mw.workspace()
                .update(cx, |ws, cx| ws.flush_serialization(window, cx))
        });
        task.await;

        // Read the workspace back from the DB and verify serialization happened.
        let serialized = db.workspace_for_id(workspace_id);
        assert!(
            serialized.is_some(),
            "flush_serialization should have persisted the workspace to DB"
        );
    }

    #[gpui::test]
    async fn test_pending_serialization_flushed_on_shutdown(cx: &mut gpui::TestAppContext) {
        crate::tests::init_test(cx);

        let app_state = cx.update(crate::AppState::test);
        cx.update(|cx| crate::init(app_state.clone(), cx));

        let fs = fs::FakeFs::new(cx.executor());
        let dir = unique_test_dir(&fs, "shutdown-flush").await;
        let project = Project::test(fs.clone(), [dir.as_path()], cx).await;

        let (multi_workspace, vcx) =
            cx.add_window_view(|window, cx| MultiWorkspace::test_new(project.clone(), window, cx));

        let workspace = multi_workspace.read_with(vcx, |mw, _| mw.workspace().clone());

        let db = vcx.update(|_, cx| WorkspaceDb::global(cx));
        let workspace_id = db.next_id().await.unwrap();
        workspace.update(vcx, |ws, _cx| {
            ws.set_database_id(workspace_id);
        });

        multi_workspace.update_in(vcx, |multi_workspace, window, cx| {
            multi_workspace.workspace().update(cx, |workspace, cx| {
                workspace.serialize_workspace(window, cx)
            })
        });

        let serialized_paths = db
            .workspace_for_id(workspace_id)
            .expect("next_id should have reserved a row")
            .paths;
        assert_eq!(
            serialized_paths.paths().len(),
            0,
            "the debounced serialization must not have fired yet"
        );

        cx.update(|cx| cx.shutdown());

        let serialized_paths = db
            .workspace_for_id(workspace_id)
            .expect("the workspace row should still exist after shutdown")
            .paths;
        assert_eq!(
            serialized_paths.paths(),
            std::slice::from_ref(&dir),
            "shutdown should flush the pending workspace serialization"
        );
    }

    #[gpui::test]
    async fn test_restore_keeps_saved_layout_and_item_ids(cx: &mut gpui::TestAppContext) {
        crate::tests::init_test(cx);
        cx.update(crate::register_serializable_item::<TestItem>);

        let fs = fs::FakeFs::new(cx.executor());
        let project = Project::test(fs.clone(), [], cx).await;
        let (multi_workspace, cx) =
            cx.add_window_view(|window, cx| MultiWorkspace::test_new(project.clone(), window, cx));
        let workspace = multi_workspace.read_with(cx, |mw, _| mw.workspace().clone());

        let db = cx.update(|_, cx| WorkspaceDb::global(cx));
        let workspace_id = db.next_id().await.unwrap();
        workspace.update(cx, |workspace, _| workspace.set_database_id(workspace_id));

        let center_group = SerializedPaneGroup::Pane(SerializedPane::new(
            vec![SerializedItem::new("TestItem", 1, true, false)],
            true,
            0,
        ));
        let bookmarks = BTreeMap::from_iter([(
            Arc::<Path>::from(Path::new("/tmp/file.rs")),
            vec![SerializedBookmark {
                row: 3,
                label: "bookmark".to_owned(),
            }],
        )]);
        let serialized_workspace = SerializedWorkspace {
            id: workspace_id,
            bookmarks: bookmarks.clone(),
            ..default_workspace::<&Path>(&[], &center_group)
        };
        db.save_workspace(serialized_workspace.clone()).await;
        let (_unblock_deserialization, pending_deserialization) = oneshot::channel::<()>();
        cx.update(|_, cx| {
            cx.set_global(crate::item::test::PendingTestItemDeserialization(
                pending_deserialization.shared(),
            ))
        });

        let restore = workspace.update_in(cx, |workspace, window, cx| {
            crate::open_items(
                workspace,
                Some(serialized_workspace.clone()),
                Vec::new(),
                true,
                window,
                cx,
            )
        });
        let scratch_item = SerializedItem::new(
            "TestItem",
            workspace.update_in(cx, |workspace, window, cx| {
                let item = cx.new(TestItem::new);
                workspace.add_item_to_active_pane(Box::new(item.clone()), None, true, window, cx);
                persistent_item_id(&item, cx)
            }),
            true,
            false,
        );
        let flush = workspace.update_in(cx, |workspace, window, cx| {
            workspace.flush_serialization(window, cx)
        });
        drop(restore);
        flush.await;

        assert_eq!(
            db.workspace_for_id(workspace_id)
                .map(|workspace| (workspace.center_group, workspace.bookmarks)),
            Some((
                SerializedPaneGroup::Pane(SerializedPane::new(
                    vec![
                        SerializedItem::new("TestItem", 1, false, false),
                        scratch_item.clone(),
                    ],
                    true,
                    0,
                )),
                bookmarks
            ))
        );

        cx.run_until_parked();
        workspace
            .update_in(cx, |workspace, window, cx| {
                workspace.flush_serialization(window, cx)
            })
            .await;
        let Some(SerializedPaneGroup::Pane(pane)) = db
            .workspace_for_id(workspace_id)
            .map(|workspace| workspace.center_group)
        else {
            panic!("expected a single pane after the restore was dropped");
        };
        assert_eq!(pane.children, vec![scratch_item.clone()]);

        cx.update(|_, cx| cx.remove_global::<crate::item::test::PendingTestItemDeserialization>());
        workspace
            .update_in(cx, |workspace, window, cx| {
                crate::open_items(
                    workspace,
                    Some(serialized_workspace),
                    Vec::new(),
                    true,
                    window,
                    cx,
                )
            })
            .await
            .unwrap();
        cx.run_until_parked();
        workspace
            .update_in(cx, |workspace, window, cx| {
                workspace.flush_serialization(window, cx)
            })
            .await;
        let mut live_item_ids = workspace.update(cx, |workspace, cx| {
            workspace
                .items(cx)
                .filter_map(|item| item.to_serializable_item_handle(cx))
                .collect::<Vec<_>>()
                .into_iter()
                .map(|item| item.persistent_item_id(cx))
                .collect::<Vec<_>>()
        });
        live_item_ids.sort();
        let mut saved_item_ids = db
            .workspace_for_id(workspace_id)
            .map(|workspace| workspace.center_group.item_ids())
            .unwrap_or_default();
        saved_item_ids.sort();
        assert_eq!(
            (live_item_ids, saved_item_ids),
            (vec![1, scratch_item.item_id], vec![1, scratch_item.item_id])
        );
    }

    #[gpui::test]
    async fn test_restoring_snapshot_appends_only_unsaved_live_items() {
        let db =
            WorkspaceDb::open_test_db("test_restoring_snapshot_appends_only_unsaved_live_items")
                .await;
        let mut center_group = SerializedPaneGroup::Pane(SerializedPane::new(
            vec![
                SerializedItem::new("Editor", 1, false, false),
                SerializedItem::new("Editor", 7, false, false),
                SerializedItem::new("Terminal", 7, true, false),
            ],
            true,
            2,
        ));
        center_group.append_unrestored_items(vec![
            SerializedItem::new("Editor", 7, false, false),
            SerializedItem::new("Terminal", 1, true, false),
        ]);
        db.save_workspace(SerializedWorkspace {
            id: WorkspaceId(1),
            ..default_workspace::<&Path>(&[], &center_group)
        })
        .await;

        assert_eq!(
            db.workspace_for_id(WorkspaceId(1))
                .map(|workspace| workspace.center_group),
            Some(SerializedPaneGroup::Pane(SerializedPane::new(
                vec![
                    SerializedItem::new("Editor", 1, false, false),
                    SerializedItem::new("Editor", 7, false, false),
                    SerializedItem::new("Terminal", 7, false, false),
                    SerializedItem::new("Terminal", 1, true, false),
                ],
                true,
                2,
            )))
        );
    }

    #[gpui::test]
    async fn test_cleanup_keeps_saved_restoring_and_live_items(cx: &mut gpui::TestAppContext) {
        cx.update(|cx| cx.set_global(db::AppDatabase::test_new()));
        let db = cx.update(|cx| WorkspaceDb::global(cx));
        db.write(|conn| {
            conn.exec(sql!(
                CREATE TABLE cleanup_items_test(workspace_id INTEGER, item_id INTEGER);
            ))?()
        })
        .await
        .unwrap();
        let workspace_id = WorkspaceId(1);
        db.save_workspace(workspace_with(1, &[], pane_with_items(&[1]), None))
            .await;
        let live_item = cx.new(|_| ());
        let live_item_id = cx.update(|cx| persistent_item_id(&live_item, cx));
        for item_id in [1, 2, 3, live_item_id] {
            db.write(move |conn| {
                conn.exec_bound(sql!(
                    INSERT INTO cleanup_items_test(workspace_id, item_id) VALUES (?, ?);
                ))?((workspace_id, item_id))
            })
            .await
            .unwrap();
        }
        let remaining_items = || {
            db.select_bound::<WorkspaceId, ItemId>(sql!(
                SELECT item_id FROM cleanup_items_test WHERE workspace_id = ? ORDER BY item_id
            ))
            .unwrap()(workspace_id)
            .unwrap()
        };
        let restoring = cx.update(|cx| {
            RestoringItems::global(cx).lease(&workspace_with(1, &[], pane_with_items(&[2]), None))
        });

        cx.update(|cx| {
            delete_unloaded_items(Vec::new(), workspace_id, "cleanup_items_test", &db, cx)
        })
        .await
        .unwrap();
        let remaining_while_referenced = remaining_items();
        drop((restoring, live_item));
        cx.run_until_parked();
        cx.update(|cx| {
            delete_unloaded_items(Vec::new(), workspace_id, "cleanup_items_test", &db, cx)
        })
        .await
        .unwrap();

        assert_eq!(
            (remaining_while_referenced, remaining_items()),
            (vec![1, 2, live_item_id], vec![1])
        );
    }

    #[gpui::test]
    async fn test_create_workspace_serialization(cx: &mut gpui::TestAppContext) {
        crate::tests::init_test(cx);

        let fs = fs::FakeFs::new(cx.executor());
        let project = Project::test(fs.clone(), [], cx).await;

        let (multi_workspace, cx) =
            cx.add_window_view(|window, cx| MultiWorkspace::test_new(project.clone(), window, cx));

        // Give the first workspace a database_id.
        multi_workspace.update_in(cx, |mw, _, cx| {
            mw.set_random_database_id(cx);
        });

        let window_id =
            multi_workspace.update_in(cx, |_, window, _cx| window.window_handle().window_id());
        let session_id =
            multi_workspace.read_with(cx, |mw, cx| mw.workspace().read(cx).session_id());

        // Create a new workspace via the MultiWorkspace API (triggers next_id()).
        multi_workspace.update_in(cx, |mw, window, cx| {
            mw.create_test_workspace(window, cx).detach();
        });

        // Let the async next_id() and re-serialization tasks complete.
        cx.run_until_parked();

        // The new workspace should now have a database_id.
        let new_workspace_db_id =
            multi_workspace.read_with(cx, |mw, cx| mw.workspace().read(cx).database_id());
        assert!(
            new_workspace_db_id.is_some(),
            "New workspace should have a database_id after run_until_parked"
        );

        // The multi-workspace state should record it as the active workspace.
        let state =
            cx.update(|_, cx| read_multi_workspace_state(session_id.as_deref(), window_id, cx));
        assert_eq!(
            state.active_workspace_id, new_workspace_db_id,
            "Serialized active_workspace_id should match the new workspace's database_id"
        );

        // The individual workspace row should exist with real data
        // (not just the bare DEFAULT VALUES row from next_id).
        let workspace_id = new_workspace_db_id.unwrap();
        let db = cx.update(|_, cx| WorkspaceDb::global(cx));
        let serialized = db.workspace_for_id(workspace_id);
        assert!(
            serialized.is_some(),
            "Newly created workspace should be fully serialized in the DB after database_id assignment"
        );
    }

    #[gpui::test]
    async fn test_remove_workspace_clears_session_binding(cx: &mut gpui::TestAppContext) {
        crate::tests::init_test(cx);

        let fs = fs::FakeFs::new(cx.executor());
        let dir = unique_test_dir(&fs, "remove").await;
        let project1 = Project::test(fs.clone(), [], cx).await;
        let project2 = Project::test(fs.clone(), [], cx).await;

        let (multi_workspace, cx) =
            cx.add_window_view(|window, cx| MultiWorkspace::test_new(project1.clone(), window, cx));

        multi_workspace.update(cx, |mw, cx| {
            mw.open_sidebar(cx);
        });

        multi_workspace.update_in(cx, |mw, _, cx| {
            mw.set_random_database_id(cx);
        });

        let db = cx.update(|_, cx| WorkspaceDb::global(cx));

        // Get a real DB id for workspace2 so the row actually exists.
        let workspace2_db_id = db.next_id().await.unwrap();

        multi_workspace.update_in(cx, |mw, window, cx| {
            let workspace = cx.new(|cx| crate::Workspace::test_new(project2.clone(), window, cx));
            workspace.update(cx, |ws: &mut crate::Workspace, _cx| {
                ws.set_database_id(workspace2_db_id)
            });
            mw.add(workspace.clone(), window, cx);
        });

        // Save a full workspace row to the DB directly.
        let session_id = format!("remove-test-session-{}", Uuid::new_v4());
        db.save_workspace(SerializedWorkspace {
            id: workspace2_db_id,
            paths: PathList::new(&[&dir]),
            identity_paths: None,
            location: SerializedWorkspaceLocation::Local,
            center_group: Default::default(),
            window_bounds: Default::default(),
            display: Default::default(),
            docks: Default::default(),
            centered_layout: false,
            session_id: Some(session_id.clone()),
            bookmarks: Default::default(),
            breakpoints: Default::default(),
            window_id: Some(99),
            user_toolchains: Default::default(),
            recent_navigation_history: Default::default(),
            unserialized_root_files: None,
        })
        .await;

        assert!(
            db.workspace_for_id(workspace2_db_id).is_some(),
            "Workspace2 should exist in DB before removal"
        );

        // Remove workspace at index 1 (the second workspace).
        multi_workspace.update_in(cx, |mw, window, cx| {
            let ws = mw.workspaces().nth(1).unwrap().clone();
            mw.remove([ws], RemovalIntent::CloseProject, window, cx)
                .detach_and_log_err(cx);
        });

        cx.run_until_parked();

        // The row should still exist so it continues to appear in recent
        // projects, but the session binding should be cleared so it is not
        // restored as part of any future session.
        assert!(
            db.workspace_for_id(workspace2_db_id).is_some(),
            "Removed workspace's DB row should be preserved for recent projects"
        );

        let session_workspaces = db
            .last_session_workspace_locations("remove-test-session", None, fs.as_ref())
            .await
            .unwrap();
        let restored_ids: Vec<WorkspaceId> = session_workspaces
            .iter()
            .map(|sw| sw.workspace_id)
            .collect();
        assert!(
            !restored_ids.contains(&workspace2_db_id),
            "Removed workspace should not appear in session restoration"
        );
    }

    #[gpui::test]
    async fn test_remove_workspace_not_restored_as_zombie(cx: &mut gpui::TestAppContext) {
        crate::tests::init_test(cx);

        let fs = fs::FakeFs::new(cx.executor());
        let dir1 = tempfile::TempDir::with_prefix("zombie_test1").unwrap();
        let dir2 = tempfile::TempDir::with_prefix("zombie_test2").unwrap();
        fs.insert_tree(dir1.path(), json!({})).await;
        fs.insert_tree(dir2.path(), json!({})).await;

        let project1 = Project::test(fs.clone(), [], cx).await;
        let project2 = Project::test(fs.clone(), [], cx).await;

        let db = cx.update(|cx| WorkspaceDb::global(cx));

        // Get real DB ids so the rows actually exist.
        let ws1_id = db.next_id().await.unwrap();
        let ws2_id = db.next_id().await.unwrap();

        let (multi_workspace, cx) =
            cx.add_window_view(|window, cx| MultiWorkspace::test_new(project1.clone(), window, cx));

        multi_workspace.update(cx, |mw, cx| {
            mw.open_sidebar(cx);
        });

        multi_workspace.update_in(cx, |mw, _, cx| {
            mw.workspace().update(cx, |ws, _cx| {
                ws.set_database_id(ws1_id);
            });
        });

        multi_workspace.update_in(cx, |mw, window, cx| {
            let workspace = cx.new(|cx| crate::Workspace::test_new(project2.clone(), window, cx));
            workspace.update(cx, |ws: &mut crate::Workspace, _cx| {
                ws.set_database_id(ws2_id)
            });
            mw.add(workspace.clone(), window, cx);
        });

        let session_id = "test-zombie-session";
        let window_id_val: u64 = 42;

        db.save_workspace(SerializedWorkspace {
            id: ws1_id,
            paths: PathList::new(&[dir1.path()]),
            identity_paths: None,
            location: SerializedWorkspaceLocation::Local,
            center_group: Default::default(),
            window_bounds: Default::default(),
            display: Default::default(),
            docks: Default::default(),
            centered_layout: false,
            session_id: Some(session_id.to_owned()),
            bookmarks: Default::default(),
            breakpoints: Default::default(),
            window_id: Some(window_id_val),
            user_toolchains: Default::default(),
            recent_navigation_history: Default::default(),
            unserialized_root_files: None,
        })
        .await;

        db.save_workspace(SerializedWorkspace {
            id: ws2_id,
            paths: PathList::new(&[dir2.path()]),
            identity_paths: None,
            location: SerializedWorkspaceLocation::Local,
            center_group: Default::default(),
            window_bounds: Default::default(),
            display: Default::default(),
            docks: Default::default(),
            centered_layout: false,
            session_id: Some(session_id.to_owned()),
            bookmarks: Default::default(),
            breakpoints: Default::default(),
            window_id: Some(window_id_val),
            user_toolchains: Default::default(),
            recent_navigation_history: Default::default(),
            unserialized_root_files: None,
        })
        .await;

        // Remove workspace2 (index 1).
        multi_workspace.update_in(cx, |mw, window, cx| {
            let ws = mw.workspaces().nth(1).unwrap().clone();
            mw.remove([ws], RemovalIntent::CloseProject, window, cx)
                .detach_and_log_err(cx);
        });

        cx.run_until_parked();

        // The removed workspace should NOT appear in session restoration.
        let locations = db
            .last_session_workspace_locations(session_id, None, fs.as_ref())
            .await
            .unwrap();

        let restored_ids: Vec<WorkspaceId> = locations.iter().map(|sw| sw.workspace_id).collect();
        assert!(
            !restored_ids.contains(&ws2_id),
            "Removed workspace should not appear in session restoration list. Found: {:?}",
            restored_ids
        );
        assert!(
            restored_ids.contains(&ws1_id),
            "Remaining workspace should still appear in session restoration list"
        );
    }

    #[gpui::test]
    async fn test_pending_removal_tasks_drained_on_flush(cx: &mut gpui::TestAppContext) {
        crate::tests::init_test(cx);

        let fs = fs::FakeFs::new(cx.executor());
        let dir = unique_test_dir(&fs, "pending-removal").await;
        let project1 = Project::test(fs.clone(), [], cx).await;
        let project2 = Project::test(fs.clone(), [], cx).await;

        let db = cx.update(|cx| WorkspaceDb::global(cx));

        // Get a real DB id for workspace2 so the row actually exists.
        let workspace2_db_id = db.next_id().await.unwrap();

        let (multi_workspace, cx) =
            cx.add_window_view(|window, cx| MultiWorkspace::test_new(project1.clone(), window, cx));

        multi_workspace.update(cx, |mw, cx| {
            mw.open_sidebar(cx);
        });

        multi_workspace.update_in(cx, |mw, _, cx| {
            mw.set_random_database_id(cx);
        });

        multi_workspace.update_in(cx, |mw, window, cx| {
            let workspace = cx.new(|cx| crate::Workspace::test_new(project2.clone(), window, cx));
            workspace.update(cx, |ws: &mut crate::Workspace, _cx| {
                ws.set_database_id(workspace2_db_id)
            });
            mw.add(workspace.clone(), window, cx);
        });

        // Save a full workspace row to the DB directly and let it settle.
        let session_id = format!("pending-removal-session-{}", Uuid::new_v4());
        db.save_workspace(SerializedWorkspace {
            id: workspace2_db_id,
            paths: PathList::new(&[&dir]),
            identity_paths: None,
            location: SerializedWorkspaceLocation::Local,
            center_group: Default::default(),
            window_bounds: Default::default(),
            display: Default::default(),
            docks: Default::default(),
            centered_layout: false,
            session_id: Some(session_id.clone()),
            bookmarks: Default::default(),
            breakpoints: Default::default(),
            window_id: Some(88),
            user_toolchains: Default::default(),
            recent_navigation_history: Default::default(),
            unserialized_root_files: None,
        })
        .await;
        cx.run_until_parked();

        // Remove workspace2 — this pushes a task to pending_removal_tasks.
        multi_workspace.update_in(cx, |mw, window, cx| {
            let ws = mw.workspaces().nth(1).unwrap().clone();
            mw.remove([ws], RemovalIntent::CloseProject, window, cx)
                .detach_and_log_err(cx);
        });

        // Simulate the quit handler pattern: collect flush tasks + pending
        // removal tasks and await them all.
        let all_tasks = multi_workspace.update_in(cx, |mw, window, cx| {
            let mut tasks: Vec<Task<()>> = mw
                .workspaces()
                .map(|workspace| {
                    workspace.update(cx, |workspace, cx| {
                        workspace.flush_serialization(window, cx)
                    })
                })
                .collect();
            let mut removal_tasks = mw.take_pending_removal_tasks();
            // Note: removal_tasks may be empty if the background task already
            // completed (take_pending_removal_tasks filters out ready tasks).
            tasks.append(&mut removal_tasks);
            tasks.push(mw.flush_serialization(cx));
            tasks
        });
        futures::future::join_all(all_tasks).await;

        // The row should still exist (for recent projects), but the session
        // binding should have been cleared by the pending removal task.
        assert!(
            db.workspace_for_id(workspace2_db_id).is_some(),
            "Workspace row should be preserved for recent projects"
        );

        let session_workspaces = db
            .last_session_workspace_locations("pending-removal-session", None, fs.as_ref())
            .await
            .unwrap();
        let restored_ids: Vec<WorkspaceId> = session_workspaces
            .iter()
            .map(|sw| sw.workspace_id)
            .collect();
        assert!(
            !restored_ids.contains(&workspace2_db_id),
            "Pending removal task should have cleared the session binding"
        );
    }

    #[gpui::test]
    async fn test_detached_workspace_queued_writes_do_not_rebind_session(
        cx: &mut gpui::TestAppContext,
    ) {
        crate::tests::init_test(cx);

        let fs = fs::FakeFs::new(cx.executor());
        let project1 = Project::test(fs.clone(), [], cx).await;
        let project2 = Project::test(fs.clone(), [], cx).await;
        let db = cx.update(|cx| WorkspaceDb::global(cx));
        let workspace2_db_id = db.next_id().await.unwrap();

        let (multi_workspace, cx) =
            cx.add_window_view(|window, cx| MultiWorkspace::test_new(project1.clone(), window, cx));
        multi_workspace.update(cx, |mw, cx| mw.open_sidebar(cx));
        multi_workspace.update_in(cx, |mw, _, cx| mw.set_random_database_id(cx));
        let workspace2 = multi_workspace.update_in(cx, |mw, window, cx| {
            let workspace = cx.new(|cx| crate::Workspace::test_new(project2.clone(), window, cx));
            workspace.update(cx, |workspace, _| {
                workspace.set_database_id(workspace2_db_id)
            });
            mw.add(workspace.clone(), window, cx);
            workspace
        });
        let session_id = workspace2.read_with(cx, |workspace, _| workspace.session_id().unwrap());
        multi_workspace
            .update_in(cx, |_, window, cx| {
                workspace2.update(cx, |workspace, cx| {
                    workspace.flush_serialization(window, cx)
                })
            })
            .await;
        let bound_before_detach = session_binding(&db, workspace2_db_id).0;

        multi_workspace.update_in(cx, |_, window, cx| {
            workspace2.update(cx, |workspace, cx| {
                drop(workspace.serialize_workspace_internal(window, cx));
                drop(workspace.serialize_workspace_internal(window, cx));
            });
        });
        cx.update(|_, cx| {
            <project::DisableAiSettings as settings::Settings>::override_global(
                project::DisableAiSettings { disable_ai: true },
                cx,
            );
        });
        cx.run_until_parked();

        assert_eq!(
            (
                bound_before_detach,
                session_binding(&db, workspace2_db_id).0
            ),
            (Some(session_id), None)
        );
    }

    #[gpui::test]
    async fn test_replaced_workspace_does_not_persist_discarded_items(
        cx: &mut gpui::TestAppContext,
    ) {
        crate::tests::init_test(cx);
        cx.update(|cx| {
            crate::register_serializable_item::<TestItem>(cx);
            <project::DisableAiSettings as settings::Settings>::override_global(
                project::DisableAiSettings { disable_ai: true },
                cx,
            );
        });
        let fs = fs::FakeFs::new(cx.executor());
        let notes = unique_test_dir(&fs, "replaced-notes").await;
        let note = notes.join("note.txt");
        fs.insert_file(&note, Vec::new()).await;
        let other = unique_test_dir(&fs, "replacement").await;
        let project = Project::test(fs.clone(), [note.as_path()], cx).await;
        let db = cx.update(|cx| WorkspaceDb::global(cx));
        let workspace_id = db.next_id().await.unwrap();
        let (multi_workspace, cx) =
            cx.add_window_view(|window, cx| MultiWorkspace::test_new(project, window, cx));
        let workspace =
            multi_workspace.read_with(cx, |multi_workspace, _| multi_workspace.workspace().clone());
        let item = cx.new(|cx| {
            TestItem::new(cx)
                .with_dirty(true)
                .with_buffer_kind(crate::item::ItemBufferKind::Singleton)
                .with_serialize(|| Some(Task::ready(Ok(()))))
        });
        multi_workspace
            .update_in(cx, |_, window, cx| {
                workspace.update(cx, |workspace, cx| {
                    workspace.set_database_id(workspace_id);
                    workspace.add_item_to_active_pane(Box::new(item), None, true, window, cx);
                    workspace.flush_serialization(window, cx)
                })
            })
            .await;
        let saved_before = saved_center_item_count(&db, workspace_id);

        let open = multi_workspace.update_in(cx, |multi_workspace, window, cx| {
            multi_workspace.open_project(vec![other], crate::OpenMode::Activate, window, cx)
        });
        cx.run_until_parked();
        cx.simulate_prompt_answer("Don't Save");
        let opened = open.await.unwrap();
        cx.run_until_parked();

        assert_eq!(
            (
                saved_before,
                opened != workspace,
                saved_center_item_count(&db, workspace_id)
            ),
            (1, true, 0)
        );
    }

    #[gpui::test]
    async fn test_close_window_quit_app_preserves_all_sidebar_workspaces(
        cx: &mut gpui::TestAppContext,
    ) {
        crate::tests::init_test(cx);

        cx.update_global::<settings::SettingsStore, ()>(|store, cx| {
            store.update_user_settings(cx, |settings| {
                settings.workspace.on_last_window_closed =
                    Some(settings::OnLastWindowClosed::QuitApp);
            });
        });

        let fs = fs::FakeFs::new(cx.executor());
        let dir1 = unique_test_dir(&fs, "close-quit-a").await;
        let dir2 = unique_test_dir(&fs, "close-quit-b").await;
        let project1 = Project::test(fs.clone(), [dir1.as_path()], cx).await;
        let project2 = Project::test(fs.clone(), [dir2.as_path()], cx).await;

        let db = cx.update(|cx| WorkspaceDb::global(cx));
        let ws1_id = db.next_id().await.unwrap();
        let ws2_id = db.next_id().await.unwrap();

        let (multi_workspace, cx) =
            cx.add_window_view(|window, cx| MultiWorkspace::test_new(project1.clone(), window, cx));

        multi_workspace.update(cx, |mw, cx| {
            mw.open_sidebar(cx);
        });

        let session_id = format!("close-quit-session-{}", Uuid::new_v4());

        let workspace1 = multi_workspace.read_with(cx, |mw, _| mw.workspace().clone());
        workspace1.update(cx, |ws, _| {
            ws.set_database_id(ws1_id);
            ws.session_id = Some(session_id.clone());
        });

        let workspace2 = multi_workspace.update_in(cx, |mw, window, cx| {
            let workspace = cx.new(|cx| crate::Workspace::test_new(project2.clone(), window, cx));
            workspace.update(cx, |ws, _| {
                ws.set_database_id(ws2_id);
                ws.session_id = Some(session_id.clone());
            });
            mw.add(workspace.clone(), window, cx);
            workspace
        });

        multi_workspace.update_in(cx, |mw, window, cx| {
            mw.activate(workspace2.clone(), None, window, cx);
        });
        cx.run_until_parked();

        multi_workspace.update_in(cx, |mw, window, cx| {
            mw.close_window(&crate::CloseWindow, window, cx);
        });
        cx.run_until_parked();

        let mut restored_ids = db
            .last_session_workspace_locations(&session_id, None, fs.as_ref())
            .await
            .unwrap()
            .into_iter()
            .map(|workspace| workspace.workspace_id)
            .collect::<Vec<_>>();
        restored_ids.sort_by_key(|id| id.0);
        assert_eq!(restored_ids, vec![ws1_id, ws2_id]);
    }

    #[cfg(target_os = "macos")]
    #[gpui::test]
    async fn test_close_window_platform_default_still_removes_from_session(
        cx: &mut gpui::TestAppContext,
    ) {
        crate::tests::init_test(cx);

        let fs = fs::FakeFs::new(cx.executor());
        let dir1 = unique_test_dir(&fs, "close-default-a").await;
        let dir2 = unique_test_dir(&fs, "close-default-b").await;
        let project1 = Project::test(fs.clone(), [dir1.as_path()], cx).await;
        let project2 = Project::test(fs.clone(), [dir2.as_path()], cx).await;

        let db = cx.update(|cx| WorkspaceDb::global(cx));
        let ws1_id = db.next_id().await.unwrap();
        let ws2_id = db.next_id().await.unwrap();

        let (multi_workspace, cx) =
            cx.add_window_view(|window, cx| MultiWorkspace::test_new(project1.clone(), window, cx));

        multi_workspace.update(cx, |mw, cx| {
            mw.open_sidebar(cx);
        });

        let session_id = format!("close-default-session-{}", Uuid::new_v4());

        let workspace1 = multi_workspace.read_with(cx, |mw, _| mw.workspace().clone());
        workspace1.update(cx, |ws, _| {
            ws.set_database_id(ws1_id);
            ws.session_id = Some(session_id.clone());
        });

        let workspace2 = multi_workspace.update_in(cx, |mw, window, cx| {
            let workspace = cx.new(|cx| crate::Workspace::test_new(project2.clone(), window, cx));
            workspace.update(cx, |ws, _| {
                ws.set_database_id(ws2_id);
                ws.session_id = Some(session_id.clone());
            });
            mw.add(workspace.clone(), window, cx);
            workspace
        });

        multi_workspace.update_in(cx, |mw, window, cx| {
            mw.activate(workspace2.clone(), None, window, cx);
        });
        cx.run_until_parked();

        multi_workspace.update_in(cx, |mw, window, cx| {
            mw.close_window(&crate::CloseWindow, window, cx);
        });
        cx.run_until_parked();

        let restored_ids = db
            .last_session_workspace_locations(&session_id, None, fs.as_ref())
            .await
            .unwrap()
            .into_iter()
            .map(|workspace| workspace.workspace_id)
            .collect::<Vec<_>>();
        assert_eq!(restored_ids, Vec::new());
    }

    #[gpui::test]
    async fn test_create_workspace_bounds_observer_uses_fresh_id(cx: &mut gpui::TestAppContext) {
        crate::tests::init_test(cx);

        let fs = fs::FakeFs::new(cx.executor());
        let project = Project::test(fs.clone(), [], cx).await;

        let (multi_workspace, cx) =
            cx.add_window_view(|window, cx| MultiWorkspace::test_new(project.clone(), window, cx));

        multi_workspace.update_in(cx, |mw, _, cx| {
            mw.set_random_database_id(cx);
        });

        let task =
            multi_workspace.update_in(cx, |mw, window, cx| mw.create_test_workspace(window, cx));
        task.await;

        let new_workspace_db_id =
            multi_workspace.read_with(cx, |mw, cx| mw.workspace().read(cx).database_id());
        assert!(
            new_workspace_db_id.is_some(),
            "After run_until_parked, the workspace should have a database_id"
        );

        let workspace_id = new_workspace_db_id.unwrap();

        let db = cx.update(|_, cx| WorkspaceDb::global(cx));

        assert!(
            db.workspace_for_id(workspace_id).is_some(),
            "The workspace row should exist in the DB"
        );

        cx.simulate_resize(gpui::size(px(1024.0), px(768.0)));

        // Advance the clock past the 100ms debounce timer so the bounds
        // observer task fires
        cx.executor().advance_clock(Duration::from_millis(200));
        cx.run_until_parked();

        let serialized = db
            .workspace_for_id(workspace_id)
            .expect("workspace row should still exist");
        assert!(
            serialized.window_bounds.is_some(),
            "The bounds observer should write bounds for the workspace's real DB ID, \
             even when the workspace was created via create_workspace (where the ID \
             is assigned asynchronously after construction)."
        );
    }

    #[gpui::test]
    async fn test_flush_serialization_writes_bounds(cx: &mut gpui::TestAppContext) {
        crate::tests::init_test(cx);

        let fs = fs::FakeFs::new(cx.executor());
        let dir = tempfile::TempDir::with_prefix("flush_bounds_test").unwrap();
        fs.insert_tree(dir.path(), json!({})).await;

        let project = Project::test(fs.clone(), [dir.path()], cx).await;

        let (multi_workspace, cx) =
            cx.add_window_view(|window, cx| MultiWorkspace::test_new(project.clone(), window, cx));

        let db = cx.update(|_, cx| WorkspaceDb::global(cx));
        let workspace_id = db.next_id().await.unwrap();
        multi_workspace.update_in(cx, |mw, _, cx| {
            mw.workspace().update(cx, |ws, _cx| {
                ws.set_database_id(workspace_id);
            });
        });

        let task = multi_workspace.update_in(cx, |mw, window, cx| {
            mw.workspace()
                .update(cx, |ws, cx| ws.flush_serialization(window, cx))
        });
        task.await;

        let after = db
            .workspace_for_id(workspace_id)
            .expect("workspace row should exist after flush_serialization");
        assert!(
            !after.paths.is_empty(),
            "flush_serialization should have written paths via save_workspace"
        );
        assert!(
            after.window_bounds.is_some(),
            "flush_serialization should ensure window bounds are persisted to the DB \
             before the process exits."
        );
    }

    #[gpui::test]
    async fn test_empty_window_without_items_stays_in_session(cx: &mut gpui::TestAppContext) {
        crate::tests::init_test(cx);

        let fs = fs::FakeFs::new(cx.executor());
        let project = Project::test(fs.clone(), [], cx).await;
        let (multi_workspace, cx) =
            cx.add_window_view(|window, cx| MultiWorkspace::test_new(project.clone(), window, cx));

        let db = cx.update(|_, cx| WorkspaceDb::global(cx));
        let workspace_id = db.next_id().await.unwrap();
        let session_id = multi_workspace
            .update_in(cx, |multi_workspace, _, cx| {
                multi_workspace.workspace().update(cx, |workspace, _| {
                    workspace.set_database_id(workspace_id);
                    workspace.session_id()
                })
            })
            .unwrap();

        multi_workspace
            .update_in(cx, |multi_workspace, window, cx| {
                multi_workspace.workspace().update(cx, |workspace, cx| {
                    workspace.flush_serialization(window, cx)
                })
            })
            .await;

        let restored = db
            .last_session_workspace_locations(&session_id, None, fs.as_ref())
            .await
            .unwrap();
        assert_eq!(
            restored
                .iter()
                .map(|workspace| workspace.workspace_id)
                .collect::<Vec<_>>(),
            vec![workspace_id]
        );
    }

    #[gpui::test]
    async fn test_window_with_last_folder_removed_reopens_empty(cx: &mut gpui::TestAppContext) {
        crate::tests::init_test(cx);

        let fs = fs::FakeFs::new(cx.executor());
        fs.insert_tree("/project", json!({ "main.rs": "" })).await;
        let project = Project::test(fs.clone(), [Path::new("/project")], cx).await;
        let (multi_workspace, cx) =
            cx.add_window_view(|window, cx| MultiWorkspace::test_new(project.clone(), window, cx));

        let db = cx.update(|_, cx| WorkspaceDb::global(cx));
        let workspace_id = db.next_id().await.unwrap();
        let session_id = multi_workspace
            .update_in(cx, |multi_workspace, _, cx| {
                multi_workspace.workspace().update(cx, |workspace, _| {
                    workspace.set_database_id(workspace_id);
                    workspace.session_id()
                })
            })
            .unwrap();
        multi_workspace
            .update_in(cx, |multi_workspace, window, cx| {
                multi_workspace.workspace().update(cx, |workspace, cx| {
                    workspace.flush_serialization(window, cx)
                })
            })
            .await;
        assert_eq!(
            db.workspace_for_id(workspace_id).unwrap().paths,
            PathList::new(&[Path::new("/project")])
        );

        let worktree_id = project.read_with(cx, |project, cx| {
            project.worktrees(cx).next().unwrap().read(cx).id()
        });
        project.update(cx, |project, cx| project.remove_worktree(worktree_id, cx));
        multi_workspace
            .update_in(cx, |multi_workspace, window, cx| {
                multi_workspace.workspace().update(cx, |workspace, cx| {
                    workspace.flush_serialization(window, cx)
                })
            })
            .await;

        assert_eq!(
            db.workspace_for_id(workspace_id).unwrap().paths,
            PathList::default()
        );
        let restored = db
            .last_session_workspace_locations(&session_id, None, fs.as_ref())
            .await
            .unwrap();
        assert_eq!(
            restored
                .iter()
                .map(|workspace| (workspace.workspace_id, workspace.paths.clone()))
                .collect::<Vec<_>>(),
            vec![(workspace_id, PathList::default())]
        );
    }

    #[gpui::test]
    async fn test_recent_workspace_identity_deduplication(cx: &mut gpui::TestAppContext) {
        let fs = fs::FakeFs::new(cx.executor());

        // Main repo with a linked worktree entry
        fs.insert_tree(
            "/repo",
            json!({
                ".git": {
                    "worktrees": {
                        "feature": {
                            "commondir": "../../",
                            "HEAD": "ref: refs/heads/feature"
                        }
                    }
                },
                "src": { "main.rs": "" }
            }),
        )
        .await;

        // Linked worktree checkout pointing back to /repo
        fs.insert_tree(
            "/worktree",
            json!({
                ".git": "gitdir: /repo/.git/worktrees/feature",
                "src": { "main.rs": "" }
            }),
        )
        .await;

        // A plain non-git project
        fs.insert_tree(
            "/plain-project",
            json!({
                "src": { "main.rs": "" }
            }),
        )
        .await;

        // Another normal git repo (used in mixed-path entry)
        fs.insert_tree(
            "/other-repo",
            json!({
                ".git": {},
                "src": { "lib.rs": "" }
            }),
        )
        .await;

        let t0 = Utc::now() - chrono::Duration::hours(4);
        let t1 = Utc::now() - chrono::Duration::hours(3);
        let t2 = Utc::now() - chrono::Duration::hours(2);
        let t3 = Utc::now() - chrono::Duration::hours(1);

        let workspaces = vec![
            local_recent_workspace(WorkspaceId(1), PathList::new(&["/repo"]), t0, fs.as_ref())
                .await,
            local_recent_workspace(
                WorkspaceId(2),
                PathList::new(&["/worktree"]),
                t1,
                fs.as_ref(),
            )
            .await,
            local_recent_workspace(
                WorkspaceId(3),
                PathList::new(&["/other-repo", "/worktree"]),
                t2,
                fs.as_ref(),
            )
            .await,
            local_recent_workspace(
                WorkspaceId(4),
                PathList::new(&["/plain-project"]),
                t3,
                fs.as_ref(),
            )
            .await,
        ];

        let result = dedupe_recent_workspaces(workspaces);

        // Should have 3 entries: #1 and #2 deduped into one, plus #3 and #4.
        assert_eq!(result.len(), 3);

        // First entry: /repo — deduplicated from #1 and #2.
        // Keeps the position of #1 (first seen), but with #2's later timestamp.
        assert_eq!(result[0].identity_paths.paths(), &[PathBuf::from("/repo")]);
        assert_eq!(result[0].timestamp, t1);

        // Second entry: mixed-path workspace with worktree resolved.
        // /worktree → /repo, so paths become [/other-repo, /repo] (sorted).
        assert_eq!(
            result[1].identity_paths.paths(),
            &[PathBuf::from("/other-repo"), PathBuf::from("/repo")]
        );
        assert_eq!(result[1].workspace_id, WorkspaceId(3));

        // Third entry: non-git project, unchanged.
        assert_eq!(
            result[2].identity_paths.paths(),
            &[PathBuf::from("/plain-project")]
        );
        assert_eq!(result[2].workspace_id, WorkspaceId(4));
    }

    #[gpui::test]
    async fn test_recent_workspace_identity_for_bare_repo(cx: &mut gpui::TestAppContext) {
        let fs = fs::FakeFs::new(cx.executor());

        // Bare repo at /foo/.bare (commondir doesn't end with .git)
        fs.insert_tree(
            "/foo/.bare",
            json!({
                "worktrees": {
                    "my-feature": {
                        "commondir": "../../",
                        "HEAD": "ref: refs/heads/my-feature"
                    }
                }
            }),
        )
        .await;

        // Linked worktree whose commondir resolves to a bare repo (/foo/.bare)
        fs.insert_tree(
            "/foo/my-feature",
            json!({
                ".git": "gitdir: /foo/.bare/worktrees/my-feature",
                "src": { "main.rs": "" }
            }),
        )
        .await;

        let t0 = Utc::now();

        let result = local_recent_workspace(
            WorkspaceId(1),
            PathList::new(&["/foo/my-feature"]),
            t0,
            fs.as_ref(),
        )
        .await;

        // Bare-backed worktrees should resolve to the repo identity path, which
        // is the parent directory users think of as the project root.
        assert_eq!(result.identity_paths.paths(), &[PathBuf::from("/foo")]);
    }

    #[gpui::test]
    async fn test_recent_workspace_identity_for_submodule(cx: &mut gpui::TestAppContext) {
        let fs = fs::FakeFs::new(cx.executor());

        // Superproject `/Foo` with a submodule `Bar`. A submodule's `.git` is a
        // file pointing into the superproject's `.git/modules/<name>` directory,
        // structurally like a linked worktree's `.git` file.
        fs.insert_tree(
            "/Foo",
            json!({
                ".git": {
                    "modules": {
                        "Bar": {
                            "HEAD": "ref: refs/heads/main"
                        }
                    }
                },
                "Bar": {
                    ".git": "gitdir: ../.git/modules/Bar\n",
                    "src": { "main.rs": "" }
                },
                "src": { "lib.rs": "" }
            }),
        )
        .await;

        let t0 = Utc::now();

        let result = local_recent_workspace(
            WorkspaceId(1),
            PathList::new(&["/Foo/Bar"]),
            t0,
            fs.as_ref(),
        )
        .await;

        // Submodules are independent projects: their identity is their own
        // working directory, not the superproject's `.git/modules/<name>`.
        assert_eq!(result.identity_paths.paths(), &[PathBuf::from("/Foo/Bar")]);
    }

    #[gpui::test]
    async fn test_recent_workspace_identity_deduplicates_main_and_linked_worktree(
        cx: &mut gpui::TestAppContext,
    ) {
        let fs = fs::FakeFs::new(cx.executor());

        fs.insert_tree(
            "/the-project",
            json!({
                ".git": "gitdir: ./.bare\n",
                ".bare": {
                    "worktrees": {
                        "feature-a": {
                            "commondir": "../../",
                            "HEAD": "ref: refs/heads/feature-a"
                        }
                    }
                },
                "src": { "main.rs": "" }
            }),
        )
        .await;

        fs.insert_tree(
            "/the-project/feature-a",
            json!({
                ".git": "gitdir: ../.bare/worktrees/feature-a\n",
                "src": { "lib.rs": "" }
            }),
        )
        .await;

        let t0 = Utc::now() - chrono::Duration::hours(1);
        let t1 = Utc::now();
        let workspaces = vec![
            local_recent_workspace(
                WorkspaceId(1),
                PathList::new(&["/the-project"]),
                t0,
                fs.as_ref(),
            )
            .await,
            local_recent_workspace(
                WorkspaceId(2),
                PathList::new(&["/the-project/feature-a"]),
                t1,
                fs.as_ref(),
            )
            .await,
        ];

        let result = dedupe_recent_workspaces(workspaces);

        assert_eq!(result.len(), 1);
        assert_eq!(
            result[0].identity_paths.paths(),
            &[PathBuf::from("/the-project")]
        );
        assert_eq!(result[0].workspace_id, WorkspaceId(2));
        assert_eq!(result[0].timestamp, t1);
    }

    #[gpui::test]
    async fn test_recent_project_workspaces_preserve_reopen_paths(cx: &mut gpui::TestAppContext) {
        let fs = fs::FakeFs::new(cx.executor());
        let db =
            WorkspaceDb::open_test_db("test_recent_project_workspaces_preserve_reopen_paths").await;

        fs.insert_tree(
            "/the-project",
            json!({
                ".git": "gitdir: ./.bare\n",
                ".bare": {
                    "worktrees": {
                        "feature-a": {
                            "commondir": "../../",
                            "HEAD": "ref: refs/heads/feature-a"
                        }
                    }
                },
                "src": { "main.rs": "" }
            }),
        )
        .await;

        fs.insert_tree(
            "/the-project/feature-a",
            json!({
                ".git": "gitdir: ../.bare/worktrees/feature-a\n",
                "src": { "lib.rs": "" }
            }),
        )
        .await;

        db.save_workspace(workspace_with(
            1,
            &[Path::new("/the-project")],
            empty_pane_group(),
            None,
        ))
        .await;
        db.save_workspace(workspace_with(
            2,
            &[Path::new("/the-project/feature-a")],
            empty_pane_group(),
            None,
        ))
        .await;
        db.set_timestamp_for_tests(WorkspaceId(1), "2024-01-01 00:00:00".to_owned())
            .await
            .unwrap();
        db.set_timestamp_for_tests(WorkspaceId(2), "2024-01-01 00:00:01".to_owned())
            .await
            .unwrap();

        let recents = db.recent_project_workspaces(fs.as_ref()).await.unwrap();

        assert_eq!(recents.len(), 1);
        assert_eq!(recents[0].workspace_id, WorkspaceId(2));
        assert_eq!(
            recents[0].paths.paths(),
            &[PathBuf::from("/the-project/feature-a")]
        );
        assert_eq!(
            recents[0].identity_paths.paths(),
            &[PathBuf::from("/the-project")]
        );
    }

    #[gpui::test]
    async fn test_recent_project_workspaces_remote_identity_hint(cx: &mut gpui::TestAppContext) {
        let fs = fs::FakeFs::new(cx.executor());
        let db =
            WorkspaceDb::open_test_db("test_recent_project_workspaces_remote_identity_hint").await;

        let workspace = remote_workspace_with(1, "example.com", &[Path::new("/repo/feature-a")]);
        db.save_workspace(SerializedWorkspace {
            identity_paths: Some(PathList::new(&["/repo"])),
            ..workspace
        })
        .await;

        let recents = db.recent_project_workspaces(fs.as_ref()).await.unwrap();

        assert_eq!(recents.len(), 1);
        assert_eq!(
            recents[0].paths.paths(),
            &[PathBuf::from("/repo/feature-a")]
        );
        assert_eq!(recents[0].identity_paths.paths(), &[PathBuf::from("/repo")]);
    }

    #[gpui::test]
    async fn test_recent_project_workspaces_remote_paths_do_not_use_local_fs_identity(
        cx: &mut gpui::TestAppContext,
    ) {
        let fs = fs::FakeFs::new(cx.executor());
        let db = WorkspaceDb::open_test_db(
            "test_recent_project_workspaces_remote_paths_do_not_use_local_fs_identity",
        )
        .await;

        fs.insert_tree(
            "/repo",
            json!({
                ".git": "gitdir: ./.bare\n",
                ".bare": {
                    "worktrees": {
                        "feature-a": {
                            "commondir": "../../",
                            "HEAD": "ref: refs/heads/feature-a"
                        }
                    }
                },
                "src": { "main.rs": "" }
            }),
        )
        .await;
        fs.insert_tree(
            "/repo/feature-a",
            json!({
                ".git": "gitdir: ../.bare/worktrees/feature-a\n",
                "src": { "lib.rs": "" }
            }),
        )
        .await;

        db.save_workspace(remote_workspace_with(
            1,
            "example.com",
            &[Path::new("/repo/feature-a")],
        ))
        .await;

        let recents = db.recent_project_workspaces(fs.as_ref()).await.unwrap();

        assert_eq!(recents.len(), 1);
        assert_eq!(
            recents[0].identity_paths.paths(),
            &[PathBuf::from("/repo/feature-a")]
        );
    }

    #[gpui::test]
    async fn test_recent_project_workspaces_do_not_dedupe_remote_hosts(
        cx: &mut gpui::TestAppContext,
    ) {
        let fs = fs::FakeFs::new(cx.executor());
        let db =
            WorkspaceDb::open_test_db("test_recent_project_workspaces_do_not_dedupe_remote_hosts")
                .await;

        db.save_workspace(remote_workspace_with(1, "host-a", &[Path::new("/repo")]))
            .await;
        db.save_workspace(remote_workspace_with(2, "host-b", &[Path::new("/repo")]))
            .await;
        db.set_timestamp_for_tests(WorkspaceId(1), "2024-01-01 00:00:00".to_owned())
            .await
            .unwrap();
        db.set_timestamp_for_tests(WorkspaceId(2), "2024-01-01 00:00:01".to_owned())
            .await
            .unwrap();

        let recents = db.recent_project_workspaces(fs.as_ref()).await.unwrap();

        assert_eq!(recents.len(), 2);
        assert_eq!(recents[0].workspace_id, WorkspaceId(2));
        assert_eq!(recents[1].workspace_id, WorkspaceId(1));
    }

    #[gpui::test]
    async fn test_delete_recent_workspace_group_removes_all_matching_rows(
        cx: &mut gpui::TestAppContext,
    ) {
        let fs = fs::FakeFs::new(cx.executor());
        let db = WorkspaceDb::open_test_db(
            "test_delete_recent_workspace_group_removes_all_matching_rows",
        )
        .await;

        fs.insert_tree(
            "/the-group",
            json!({
                ".git": "gitdir: ./.bare\n",
                ".bare": {
                    "worktrees": {
                        "feature-a": {
                            "commondir": "../../",
                            "HEAD": "ref: refs/heads/feature-a"
                        }
                    }
                },
                "src": { "main.rs": "" }
            }),
        )
        .await;

        fs.insert_tree(
            "/the-group/feature-a",
            json!({
                ".git": "gitdir: ../.bare/worktrees/feature-a\n",
                "src": { "lib.rs": "" }
            }),
        )
        .await;

        db.save_workspace(SerializedWorkspace {
            identity_paths: Some(PathList::new(&["/the-group"])),
            ..workspace_with(1, &[Path::new("/the-group")], empty_pane_group(), None)
        })
        .await;
        db.save_workspace(SerializedWorkspace {
            identity_paths: Some(PathList::new(&["/the-group"])),
            ..workspace_with(
                2,
                &[Path::new("/the-group/feature-a")],
                empty_pane_group(),
                None,
            )
        })
        .await;
        db.set_timestamp_for_tests(WorkspaceId(1), "2024-01-01 00:00:00".to_owned())
            .await
            .unwrap();
        db.set_timestamp_for_tests(WorkspaceId(2), "2024-01-01 00:00:01".to_owned())
            .await
            .unwrap();

        let recents = db.recent_project_workspaces(fs.as_ref()).await.unwrap();
        assert_eq!(recents.len(), 1);

        let deleted = db
            .delete_recent_workspace_group(&recents[0], WorkspaceIdClaims::default())
            .await
            .unwrap();
        assert_eq!(deleted, vec![WorkspaceId(2), WorkspaceId(1)]);

        let recents = db.recent_project_workspaces(fs.as_ref()).await.unwrap();
        assert!(recents.is_empty());
    }

    #[gpui::test]
    async fn test_restore_window_with_linked_worktree_and_multiple_project_groups(
        cx: &mut gpui::TestAppContext,
    ) {
        crate::tests::init_test(cx);

        let fs = fs::FakeFs::new(cx.executor());

        // Main git repo at /repo
        fs.insert_tree(
            "/repo",
            json!({
                ".git": {
                    "HEAD": "ref: refs/heads/main",
                    "worktrees": {
                        "feature": {
                            "commondir": "../../",
                            "HEAD": "ref: refs/heads/feature"
                        }
                    }
                },
                "src": { "main.rs": "" }
            }),
        )
        .await;

        // Linked worktree checkout pointing back to /repo
        fs.insert_tree(
            "/worktree-feature",
            json!({
                ".git": "gitdir: /repo/.git/worktrees/feature",
                "src": { "lib.rs": "" }
            }),
        )
        .await;

        // --- Phase 1: Set up the original multi-workspace window ---

        let project_1 = Project::test(fs.clone(), ["/repo".as_ref()], cx).await;
        let project_1_linked_worktree =
            Project::test(fs.clone(), ["/worktree-feature".as_ref()], cx).await;

        // Wait for git discovery to finish.
        cx.run_until_parked();

        // Create a second, unrelated project so we have two distinct project groups.
        fs.insert_tree(
            "/other-project",
            json!({
                ".git": { "HEAD": "ref: refs/heads/main" },
                "readme.md": ""
            }),
        )
        .await;
        let project_2 = Project::test(fs.clone(), ["/other-project".as_ref()], cx).await;
        cx.run_until_parked();

        // Create the MultiWorkspace with project_2, then add the main repo
        // and its linked worktree. The linked worktree is added last and
        // becomes the active workspace.
        let (multi_workspace, cx) = cx
            .add_window_view(|window, cx| MultiWorkspace::test_new(project_2.clone(), window, cx));

        multi_workspace.update(cx, |mw, cx| {
            mw.open_sidebar(cx);
        });

        multi_workspace.update_in(cx, |mw, window, cx| {
            mw.test_add_workspace(project_1.clone(), window, cx);
        });

        let workspace_worktree = multi_workspace.update_in(cx, |mw, window, cx| {
            mw.test_add_workspace(project_1_linked_worktree.clone(), window, cx)
        });

        let tasks =
            multi_workspace.update_in(cx, |mw, window, cx| mw.flush_all_serialization(window, cx));
        cx.run_until_parked();
        for task in tasks {
            task.await;
        }
        cx.run_until_parked();

        let active_db_id = workspace_worktree.read_with(cx, |ws, _| ws.database_id());
        assert!(
            active_db_id.is_some(),
            "Active workspace should have a database ID"
        );

        // --- Phase 2: Read back and verify the serialized state ---

        let session_id = multi_workspace
            .read_with(cx, |mw, cx| mw.workspace().read(cx).session_id())
            .unwrap();
        let db = cx.update(|_, cx| WorkspaceDb::global(cx));
        let session_workspaces = db
            .last_session_workspace_locations(&session_id, None, fs.as_ref())
            .await
            .expect("should load session workspaces");
        assert!(
            !session_workspaces.is_empty(),
            "Should have at least one session workspace"
        );

        let multi_workspaces = cx
            .update(|_, cx| read_serialized_multi_workspaces(session_workspaces, cx))
            .await;
        assert_eq!(
            multi_workspaces.len(),
            1,
            "All workspaces share one window, so there should be exactly one multi-workspace"
        );

        let serialized = &multi_workspaces[0];
        assert_eq!(
            serialized.active_workspace.workspace_id,
            active_db_id.unwrap(),
        );
        assert_eq!(serialized.state.project_groups.len(), 2,);

        // Verify the serialized project group keys round-trip back to the
        // originals.
        let restored_keys: Vec<ProjectGroupKey> = serialized
            .state
            .project_groups
            .iter()
            .cloned()
            .map(Into::into)
            .collect();
        let expected_keys = vec![
            ProjectGroupKey::new(None, PathList::new(&["/repo"])),
            ProjectGroupKey::new(None, PathList::new(&["/other-project"])),
        ];
        assert_eq!(
            restored_keys, expected_keys,
            "Deserialized project group keys should match the originals"
        );

        // --- Phase 3: Restore the window and verify the result ---

        let app_state =
            multi_workspace.read_with(cx, |mw, cx| mw.workspace().read(cx).app_state().clone());

        let serialized_mw = multi_workspaces.into_iter().next().unwrap();
        let restored_handle: gpui::WindowHandle<MultiWorkspace> = cx
            .update(|_, cx| {
                cx.spawn(async move |mut cx| {
                    crate::restore_multiworkspace(serialized_mw, app_state, None, None, &mut cx)
                        .await
                })
            })
            .await
            .expect("restore_multiworkspace should succeed");

        cx.run_until_parked();

        // The restored window should have the same project group keys.
        let restored_keys: Vec<ProjectGroupKey> = restored_handle
            .read_with(cx, |mw: &MultiWorkspace, _cx| mw.project_group_keys())
            .unwrap();
        assert_eq!(
            restored_keys, expected_keys,
            "Restored window should have the same project group keys as the original"
        );

        // The active workspace in the restored window should have the linked
        // worktree paths.
        let active_paths: Vec<PathBuf> = restored_handle
            .read_with(cx, |mw: &MultiWorkspace, cx| {
                mw.workspace()
                    .read(cx)
                    .root_paths(cx)
                    .into_iter()
                    .map(|p: Arc<Path>| p.to_path_buf())
                    .collect()
            })
            .unwrap();
        assert_eq!(
            active_paths,
            vec![PathBuf::from("/worktree-feature")],
            "The restored active workspace should be the linked worktree project"
        );
    }

    #[gpui::test]
    async fn test_remove_project_group_falls_back_to_neighbor(cx: &mut gpui::TestAppContext) {
        crate::tests::init_test(cx);

        let fs = fs::FakeFs::new(cx.executor());
        let dir_a = unique_test_dir(&fs, "group-a").await;
        let dir_b = unique_test_dir(&fs, "group-b").await;
        let dir_c = unique_test_dir(&fs, "group-c").await;

        let project_a = Project::test(fs.clone(), [dir_a.as_path()], cx).await;
        let project_b = Project::test(fs.clone(), [dir_b.as_path()], cx).await;
        let project_c = Project::test(fs.clone(), [dir_c.as_path()], cx).await;

        // Create a multi-workspace with project A, then add B and C.
        // project_groups stores newest first: [C, B, A].
        // Sidebar displays in the same order: C (top), B (middle), A (bottom).
        let (multi_workspace, cx) = cx
            .add_window_view(|window, cx| MultiWorkspace::test_new(project_a.clone(), window, cx));

        multi_workspace.update(cx, |mw, cx| mw.open_sidebar(cx));

        let workspace_b = multi_workspace.update_in(cx, |mw, window, cx| {
            mw.test_add_workspace(project_b.clone(), window, cx)
        });
        let _workspace_c = multi_workspace.update_in(cx, |mw, window, cx| {
            mw.test_add_workspace(project_c.clone(), window, cx)
        });
        cx.run_until_parked();

        let key_a = project_a.read_with(cx, |p, cx| p.project_group_key(cx));
        let key_b = project_b.read_with(cx, |p, cx| p.project_group_key(cx));
        let key_c = project_c.read_with(cx, |p, cx| p.project_group_key(cx));

        // Activate workspace B so removing its group exercises the fallback.
        multi_workspace.update_in(cx, |mw, window, cx| {
            mw.activate(workspace_b.clone(), None, window, cx);
        });
        cx.run_until_parked();

        // --- Remove group B (the middle one). ---
        // In the sidebar [C, B, A], "below" B is A.
        multi_workspace.update_in(cx, |mw, window, cx| {
            mw.remove_project_group(&key_b, window, cx)
                .detach_and_log_err(cx);
        });
        cx.run_until_parked();

        let active_paths =
            multi_workspace.read_with(cx, |mw, cx| mw.workspace().read(cx).root_paths(cx));
        assert_eq!(
            active_paths
                .iter()
                .map(|p| p.to_path_buf())
                .collect::<Vec<_>>(),
            vec![dir_a.clone()],
            "After removing the middle group, should fall back to the group below (A)"
        );

        // After removing B, keys = [A, C], sidebar = [C, A].
        // Activate workspace A (the bottom) so removing it tests the
        // "fall back upward" path.
        let workspace_a =
            multi_workspace.read_with(cx, |mw, _cx| mw.workspaces().next().unwrap().clone());
        multi_workspace.update_in(cx, |mw, window, cx| {
            mw.activate(workspace_a.clone(), None, window, cx);
        });
        cx.run_until_parked();

        // --- Remove group A (the bottom one in sidebar). ---
        // Nothing below A, so should fall back upward to C.
        multi_workspace.update_in(cx, |mw, window, cx| {
            mw.remove_project_group(&key_a, window, cx)
                .detach_and_log_err(cx);
        });
        cx.run_until_parked();

        let active_paths =
            multi_workspace.read_with(cx, |mw, cx| mw.workspace().read(cx).root_paths(cx));
        assert_eq!(
            active_paths
                .iter()
                .map(|p| p.to_path_buf())
                .collect::<Vec<_>>(),
            vec![dir_c.clone()],
            "After removing the bottom group, should fall back to the group above (C)"
        );

        // --- Remove group C (the only one remaining). ---
        // Should create an empty workspace.
        multi_workspace.update_in(cx, |mw, window, cx| {
            mw.remove_project_group(&key_c, window, cx)
                .detach_and_log_err(cx);
        });
        cx.run_until_parked();

        let active_paths =
            multi_workspace.read_with(cx, |mw, cx| mw.workspace().read(cx).root_paths(cx));
        assert!(
            active_paths.is_empty(),
            "After removing the only remaining group, should have an empty workspace"
        );
    }

    /// Regression test for a crash where `find_or_create_local_workspace`
    /// returned a workspace that was about to be removed, hitting an assert
    /// in `MultiWorkspace::remove`.
    ///
    /// The scenario: two workspaces share the same root paths (e.g. due to
    /// a provisional key mismatch). When the first is removed and the
    /// fallback searches for the same paths, `workspace_for_paths` must
    /// skip the doomed workspace so the assert in `remove` is satisfied.
    #[gpui::test]
    async fn test_remove_fallback_skips_excluded_workspaces(cx: &mut gpui::TestAppContext) {
        crate::tests::init_test(cx);

        let fs = fs::FakeFs::new(cx.executor());
        let dir = unique_test_dir(&fs, "shared").await;

        // Two projects that open the same directory — this creates two
        // workspaces whose root_paths are identical.
        let project_a = Project::test(fs.clone(), [dir.as_path()], cx).await;
        let project_b = Project::test(fs.clone(), [dir.as_path()], cx).await;

        let (multi_workspace, cx) = cx
            .add_window_view(|window, cx| MultiWorkspace::test_new(project_a.clone(), window, cx));

        multi_workspace.update(cx, |mw, cx| mw.open_sidebar(cx));

        let workspace_b = multi_workspace.update_in(cx, |mw, window, cx| {
            mw.test_add_workspace(project_b.clone(), window, cx)
        });
        cx.run_until_parked();

        // workspace_a is first in the workspaces vec.
        let workspace_a =
            multi_workspace.read_with(cx, |mw, _| mw.workspaces().next().cloned().unwrap());
        assert_ne!(workspace_a, workspace_b);

        // Activate workspace_a so removing it triggers the fallback path.
        multi_workspace.update_in(cx, |mw, window, cx| {
            mw.activate(workspace_a.clone(), None, window, cx);
        });
        cx.run_until_parked();

        // Remove workspace_a. Its replacement is looked up by the same paths,
        // so workspace_a itself has to be skipped or it would be picked again.
        multi_workspace.update_in(cx, |mw, window, cx| {
            mw.remove(
                vec![workspace_a.clone()],
                RemovalIntent::CloseProject,
                window,
                cx,
            )
            .detach_and_log_err(cx);
        });
        cx.run_until_parked();

        // workspace_b should now be active — workspace_a was removed.
        multi_workspace.read_with(cx, |mw, _cx| {
            assert_eq!(
                mw.workspace(),
                &workspace_b,
                "fallback should have found workspace_b, not the excluded workspace_a"
            );
        });
    }

    async fn restorable_windows(
        db: &WorkspaceDb,
        fs: &dyn Fs,
        cx: &mut gpui::TestAppContext,
    ) -> Vec<(Option<String>, WorkspaceId, Option<WorkspaceId>)> {
        let locations = db
            .restorable_session_workspace_locations(
                &["newest".to_owned(), "older".to_owned()],
                None,
                &HashSet::default(),
                fs,
            )
            .await
            .unwrap();
        cx.update(|cx| read_serialized_multi_workspaces(locations, cx))
            .await
            .into_iter()
            .map(|window| {
                (
                    window.active_workspace.session_id,
                    window.active_workspace.workspace_id,
                    window.state.active_workspace_id,
                )
            })
            .collect()
    }

    fn session_binding(
        db: &WorkspaceDb,
        workspace_id: WorkspaceId,
    ) -> (Option<String>, Option<u64>) {
        db.select_row_bound::<WorkspaceId, (Option<String>, Option<u64>)>(
            "SELECT session_id, window_id FROM workspaces WHERE workspace_id = ?",
        )
        .unwrap()(workspace_id)
        .unwrap()
        .unwrap_or_default()
    }

    async fn restored_unavailable_roots(
        db: &WorkspaceDb,
        workspace_id: WorkspaceId,
        fs: &dyn Fs,
    ) -> Option<Vec<PathBuf>> {
        let serialized_workspace = db.workspace_for_id(workspace_id)?;
        Some(
            crate::UnavailableRestoredRoots::detect(&serialized_workspace, &[], fs, db)
                .await
                .roots,
        )
    }

    fn saved_center_item_count(db: &WorkspaceDb, workspace_id: WorkspaceId) -> usize {
        fn count(group: &SerializedPaneGroup) -> usize {
            match group {
                SerializedPaneGroup::Pane(pane) => pane.children.len(),
                SerializedPaneGroup::Group { children, .. } => children.iter().map(count).sum(),
            }
        }
        db.workspace_for_id(workspace_id)
            .map_or(0, |workspace| count(&workspace.center_group))
    }
}
