use super::{SerializedAxis, SerializedWindowBounds};
use crate::{
    Member, Pane, PaneAxis, SerializableItemRegistry, Workspace, WorkspaceId, item::ItemHandle,
    multi_workspace::SerializedProjectGroupState, path_list::PathList,
};
use anyhow::Result;
use collections::{HashSet, IndexSet};
use db::sqlez::{
    bindable::{Bind, Column, StaticColumnCount},
    statement::Statement,
};
use gpui::{App, Context, Entity, Task, WeakEntity, Window, WindowId};

use language::{Toolchain, ToolchainScope};
use project::{
    Project, ProjectGroupKey, bookmark_store::SerializedBookmark,
    debugger::breakpoint_store::SourceBreakpoint,
};
use remote::RemoteConnectionOptions;
use serde::{Deserialize, Serialize};
use std::{
    collections::BTreeMap,
    path::{Path, PathBuf},
    sync::Arc,
};
use util::path_list::SerializedPathList;
use uuid::Uuid;

#[derive(
    Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy, serde::Serialize, serde::Deserialize,
)]
pub(crate) struct RemoteConnectionId(pub u64);

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub(crate) enum RemoteConnectionKind {
    Ssh,
    Wsl,
    Docker,
    #[cfg(any(test, feature = "test-support"))]
    Mock,
}

#[derive(Debug, PartialEq, Clone, serde::Serialize, serde::Deserialize)]
pub enum SerializedWorkspaceLocation {
    Local,
    Remote(RemoteConnectionOptions),
}

impl SerializedWorkspaceLocation {
    /// Get sorted paths
    pub fn sorted_paths(&self) -> Arc<Vec<PathBuf>> {
        unimplemented!()
    }
}

/// A workspace entry from a previous session, containing all the info needed
/// to restore it including which window it belonged to (for MultiWorkspace grouping).
#[derive(Debug, PartialEq, Clone)]
pub struct SessionWorkspace {
    pub workspace_id: WorkspaceId,
    pub location: SerializedWorkspaceLocation,
    pub paths: PathList,
    pub session_id: Option<String>,
    pub window_id: Option<WindowId>,
}

impl SessionWorkspace {
    pub fn session_window(&self) -> Option<SessionWindow> {
        self.binding().window()
    }

    pub fn binding(&self) -> SessionBinding {
        SessionBinding {
            session_id: self.session_id.clone(),
            window_id: self.window_id.map(|window_id| window_id.as_u64()),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct SessionWindow {
    pub session_id: String,
    pub window_id: u64,
}

#[derive(Debug, PartialEq, Clone, Default)]
pub struct SessionBinding {
    pub session_id: Option<String>,
    pub window_id: Option<u64>,
}

impl SessionBinding {
    pub fn window(&self) -> Option<SessionWindow> {
        Some(SessionWindow {
            session_id: self.session_id.clone()?,
            window_id: self.window_id?,
        })
    }
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct SerializedProjectGroup {
    pub path_list: SerializedPathList,
    pub(crate) location: SerializedWorkspaceLocation,
    #[serde(default = "default_expanded")]
    pub expanded: bool,
}

fn default_expanded() -> bool {
    true
}

impl SerializedProjectGroup {
    pub fn from_group(key: &ProjectGroupKey, expanded: bool) -> Self {
        Self {
            path_list: key.path_list().serialize(),
            location: match key.host() {
                Some(host) => SerializedWorkspaceLocation::Remote(host),
                None => SerializedWorkspaceLocation::Local,
            },
            expanded,
        }
    }

    pub fn into_restored_state(self) -> SerializedProjectGroupState {
        let path_list = PathList::deserialize(&self.path_list);
        let host = match self.location {
            SerializedWorkspaceLocation::Local => None,
            SerializedWorkspaceLocation::Remote(opts) => Some(opts),
        };
        SerializedProjectGroupState {
            key: ProjectGroupKey::new(host, path_list),
            expanded: self.expanded,
        }
    }
}

impl From<SerializedProjectGroup> for ProjectGroupKey {
    fn from(value: SerializedProjectGroup) -> Self {
        value.into_restored_state().key
    }
}

/// Per-window state for a MultiWorkspace, persisted to KVP.
#[derive(Debug, Clone, Default, serde::Serialize, serde::Deserialize)]
pub struct MultiWorkspaceState {
    pub active_workspace_id: Option<WorkspaceId>,
    pub sidebar_open: bool,
    #[serde(alias = "project_group_keys")]
    pub project_groups: Vec<SerializedProjectGroup>,
    #[serde(default)]
    pub sidebar_state: Option<String>,
}

impl MultiWorkspaceState {
    pub(crate) fn preserving_restored(&self, live: MultiWorkspaceState) -> MultiWorkspaceState {
        let mut project_groups = self.project_groups.clone();
        for group in live.project_groups {
            let key = ProjectGroupKey::from(group.clone());
            if !project_groups
                .iter()
                .any(|restored| ProjectGroupKey::from(restored.clone()) == key)
            {
                project_groups.push(group);
            }
        }
        MultiWorkspaceState {
            active_workspace_id: live.active_workspace_id,
            sidebar_open: self.sidebar_open || live.sidebar_open,
            project_groups,
            sidebar_state: self.sidebar_state.clone().or(live.sidebar_state),
        }
    }
}

/// The serialized state of a single MultiWorkspace window from a previous session:
/// the active workspace to restore plus window-level state (project group keys,
/// sidebar).
#[derive(Debug, Clone)]
pub struct SerializedMultiWorkspace {
    pub active_workspace: SessionWorkspace,
    pub state: MultiWorkspaceState,
}

#[derive(Debug, PartialEq, Clone)]
pub(crate) struct SerializedWorkspace {
    pub(crate) id: WorkspaceId,
    pub(crate) location: SerializedWorkspaceLocation,
    pub(crate) paths: PathList,
    /// The workspace's main worktree paths at the time this workspace was saved.
    ///
    /// These paths are used for grouping, deduping, and display in recent-workspace
    /// UIs. They are not authoritative for reopening the workspace, because they may
    /// become stale if the repository layout changes after the save. Use `paths` when
    /// reopening the workspace.
    pub(crate) identity_paths: Option<PathList>,
    pub(crate) center_group: SerializedPaneGroup,
    pub(crate) window_bounds: Option<SerializedWindowBounds>,
    pub(crate) centered_layout: bool,
    pub(crate) display: Option<Uuid>,
    pub(crate) docks: DockStructure,
    pub(crate) session_id: Option<String>,
    pub(crate) bookmarks: BTreeMap<Arc<Path>, Vec<SerializedBookmark>>,
    pub(crate) breakpoints: BTreeMap<Arc<Path>, Vec<SourceBreakpoint>>,
    pub(crate) user_toolchains: BTreeMap<ToolchainScope, IndexSet<Toolchain>>,
    pub(crate) recent_navigation_history: Vec<PathBuf>,
    pub(crate) window_id: Option<u64>,
    pub(crate) unserialized_root_files: Option<UnserializedRootFiles>,
}

#[derive(Debug, PartialEq, Clone, Default)]
pub(crate) struct UnserializedRootFiles {
    pub(crate) paths: PathList,
    pub(crate) active: Option<PathBuf>,
}

pub(crate) struct Lenient<T>(pub(crate) Option<T>);

impl<T: StaticColumnCount> StaticColumnCount for Lenient<T> {
    fn column_count() -> usize {
        T::column_count()
    }
}

impl<T: Column + StaticColumnCount> Column for Lenient<T> {
    fn column(statement: &mut Statement, start_index: i32) -> Result<(Self, i32)> {
        let next_index = start_index + T::column_count() as i32;
        match T::column(statement, start_index) {
            Ok((value, _)) => Ok((Self(Some(value)), next_index)),
            Err(error) => {
                log::warn!(
                    "Ignoring an undecodable database value at column {start_index}: {error:#}"
                );
                Ok((Self(None), next_index))
            }
        }
    }
}

#[derive(Debug, PartialEq, Clone, Default, Serialize, Deserialize)]
pub struct DockStructure {
    pub left: DockData,
    pub right: DockData,
    pub bottom: DockData,
}

impl RemoteConnectionKind {
    pub(crate) fn serialize(&self) -> &'static str {
        match self {
            RemoteConnectionKind::Ssh => "ssh",
            RemoteConnectionKind::Wsl => "wsl",
            RemoteConnectionKind::Docker => "docker",
            #[cfg(any(test, feature = "test-support"))]
            RemoteConnectionKind::Mock => "mock",
        }
    }

    pub(crate) fn deserialize(text: &str) -> Option<Self> {
        match text {
            "ssh" => Some(Self::Ssh),
            "wsl" => Some(Self::Wsl),
            "docker" => Some(Self::Docker),
            #[cfg(any(test, feature = "test-support"))]
            "mock" => Some(Self::Mock),
            _ => None,
        }
    }
}

impl Column for DockStructure {
    fn column(statement: &mut Statement, start_index: i32) -> Result<(Self, i32)> {
        let (left, next_index) = DockData::column(statement, start_index)?;
        let (right, next_index) = DockData::column(statement, next_index)?;
        let (bottom, next_index) = DockData::column(statement, next_index)?;
        Ok((
            DockStructure {
                left,
                right,
                bottom,
            },
            next_index,
        ))
    }
}

impl Bind for DockStructure {
    fn bind(&self, statement: &Statement, start_index: i32) -> Result<i32> {
        let next_index = statement.bind(&self.left, start_index)?;
        let next_index = statement.bind(&self.right, next_index)?;
        statement.bind(&self.bottom, next_index)
    }
}

#[derive(Debug, PartialEq, Clone, Default, Serialize, Deserialize)]
pub struct DockData {
    pub visible: bool,
    pub active_panel: Option<String>,
    pub zoom: bool,
}

impl Column for DockData {
    fn column(statement: &mut Statement, start_index: i32) -> Result<(Self, i32)> {
        let (visible, next_index) = Option::<bool>::column(statement, start_index)?;
        let (active_panel, next_index) = Lenient::<Option<String>>::column(statement, next_index)?;
        let (zoom, next_index) = Option::<bool>::column(statement, next_index)?;
        Ok((
            DockData {
                visible: visible.unwrap_or(false),
                active_panel: active_panel.0.flatten(),
                zoom: zoom.unwrap_or(false),
            },
            next_index,
        ))
    }
}

impl Bind for DockData {
    fn bind(&self, statement: &Statement, start_index: i32) -> Result<i32> {
        let next_index = statement.bind(&self.visible, start_index)?;
        let next_index = statement.bind(&self.active_panel, next_index)?;
        statement.bind(&self.zoom, next_index)
    }
}

#[derive(Debug, PartialEq, Clone)]
pub(crate) enum SerializedPaneGroup {
    Group {
        axis: SerializedAxis,
        flexes: Option<Vec<f32>>,
        children: Vec<SerializedPaneGroup>,
    },
    Pane(SerializedPane),
}

#[cfg(test)]
impl Default for SerializedPaneGroup {
    fn default() -> Self {
        Self::Pane(SerializedPane {
            children: vec![SerializedItem::default()],
            active: false,
            pinned_count: 0,
        })
    }
}

impl SerializedPaneGroup {
    pub(crate) fn restorable_panes(&self) -> Vec<&SerializedPane> {
        self.panes()
            .into_iter()
            .filter(|pane| !pane.children.is_empty())
            .collect()
    }

    pub(crate) fn build_restored_member(
        &self,
        mut pane_for_leaf: impl FnMut(&SerializedPane) -> Entity<Pane>,
    ) -> Option<Member> {
        self.build_member(&mut pane_for_leaf)
    }

    fn build_member(
        &self,
        pane_for_leaf: &mut dyn FnMut(&SerializedPane) -> Entity<Pane>,
    ) -> Option<Member> {
        match self {
            SerializedPaneGroup::Group {
                axis,
                children,
                flexes,
            } => {
                let mut members = children
                    .iter()
                    .filter_map(|child| child.build_member(pane_for_leaf))
                    .collect::<Vec<_>>();
                match members.len() {
                    0 => None,
                    1 => members.pop(),
                    _ => Some(Member::Axis(PaneAxis::load(
                        axis.0,
                        members,
                        flexes.clone(),
                    ))),
                }
            }
            SerializedPaneGroup::Pane(serialized_pane) => (!serialized_pane.children.is_empty())
                .then(|| Member::Pane(pane_for_leaf(serialized_pane))),
        }
    }

    pub(crate) fn item_keys(&self) -> HashSet<(Arc<str>, ItemId)> {
        self.items().map(SerializedItem::key).collect()
    }

    pub(crate) fn item_ids(&self) -> Vec<ItemId> {
        self.items().map(|item| item.item_id).collect()
    }

    pub(crate) fn append_unrestored_items(&mut self, live_items: Vec<SerializedItem>) {
        let saved_keys = self.item_keys();
        let items = live_items
            .into_iter()
            .filter(|item| !saved_keys.contains(&item.key()))
            .collect::<Vec<_>>();
        if items.is_empty() {
            return;
        }
        let panes = self.panes_mut();
        let target_index = panes.iter().position(|pane| pane.active).unwrap_or(0);
        let Some(pane) = panes.into_iter().nth(target_index) else {
            return;
        };
        if items.iter().any(|item| item.active) {
            for child in &mut pane.children {
                child.active = false;
            }
        }
        pane.children.extend(items);
    }

    fn items(&self) -> impl Iterator<Item = &SerializedItem> {
        self.panes().into_iter().flat_map(|pane| &pane.children)
    }

    fn panes(&self) -> Vec<&SerializedPane> {
        match self {
            SerializedPaneGroup::Group { children, .. } => children
                .iter()
                .flat_map(SerializedPaneGroup::panes)
                .collect(),
            SerializedPaneGroup::Pane(serialized_pane) => vec![serialized_pane],
        }
    }

    fn panes_mut(&mut self) -> Vec<&mut SerializedPane> {
        match self {
            SerializedPaneGroup::Group { children, .. } => children
                .iter_mut()
                .flat_map(SerializedPaneGroup::panes_mut)
                .collect(),
            SerializedPaneGroup::Pane(serialized_pane) => vec![serialized_pane],
        }
    }
}

#[derive(Debug, PartialEq, Eq, Default, Clone)]
pub struct SerializedPane {
    pub(crate) active: bool,
    pub(crate) children: Vec<SerializedItem>,
    pub(crate) pinned_count: usize,
}

impl SerializedPane {
    pub fn new(children: Vec<SerializedItem>, active: bool, pinned_count: usize) -> Self {
        SerializedPane {
            children,
            active,
            pinned_count,
        }
    }

    pub(crate) fn deserialize_items(
        &self,
        project: &Entity<Project>,
        workspace: WeakEntity<Workspace>,
        workspace_id: WorkspaceId,
        window: &mut Window,
        cx: &mut App,
    ) -> Vec<Task<Result<Box<dyn ItemHandle>>>> {
        self.children
            .iter()
            .map(|item| {
                SerializableItemRegistry::deserialize(
                    &item.kind,
                    project.clone(),
                    workspace.clone(),
                    workspace_id,
                    item.item_id,
                    window,
                    cx,
                )
            })
            .collect()
    }

    pub(crate) fn place_restored_items(
        &self,
        pane: &mut Pane,
        items: &[Option<Box<dyn ItemHandle>>],
        window: &mut Window,
        cx: &mut Context<Pane>,
    ) -> Vec<Option<Box<dyn ItemHandle>>> {
        let pane_had_items = pane.items_len() > 0;
        let first_index = pane.pinned_count();
        let mut next_index = first_index;
        let mut restored_pinned_count = 0;
        let mut active_item = None;
        let mut preview_item = None;
        let mut adopted_items = Vec::new();
        let mut placed_items = Vec::with_capacity(items.len());
        for (child_index, (serialized_item, item)) in self.children.iter().zip(items).enumerate() {
            let Some(item) = item else {
                placed_items.push(None);
                continue;
            };
            let (item, inserted) = pane.insert_restored_item(item.boxed_clone(), next_index, cx);
            if inserted {
                next_index += 1;
                if child_index < self.pinned_count {
                    restored_pinned_count += 1;
                }
                if serialized_item.preview {
                    preview_item = Some(item.item_id());
                }
            } else {
                adopted_items.push((
                    item.item_id(),
                    child_index < self.pinned_count,
                    serialized_item.preview,
                ));
            }
            if serialized_item.active {
                active_item = Some(item.boxed_clone());
            }
            placed_items.push(Some(item));
        }

        if !pane_had_items
            && let Some(index) = active_item
                .as_ref()
                .and_then(|item| pane.index_for_item(item.as_ref()))
                .or_else(|| pane.items_len().checked_sub(1))
        {
            pane.activate_item(index, false, false, window, cx);
        }
        if let Some(preview_item) = preview_item
            && (!pane_had_items || pane.preview_item_id().is_none())
        {
            pane.set_preview_item_id(Some(preview_item), cx);
        }
        pane.set_pinned_count((first_index + restored_pinned_count).min(pane.items_len()));
        for (item_id, pinned, preview) in adopted_items {
            pane.adopt_tab_state(item_id, pinned, preview, cx);
        }
        if !pane_had_items {
            pane.enforce_tab_limit_keeping_active(window, cx);
        }
        placed_items
    }

    pub(crate) fn merge_pending(&mut self, pending: &SerializedPane) {
        let live_keys = self
            .children
            .iter()
            .map(SerializedItem::key)
            .collect::<HashSet<_>>();
        let live_has_active = self.children.iter().any(|item| item.active);
        let live_has_preview = self.children.iter().any(|item| item.preview);
        let insertion_index = self.pinned_count.min(self.children.len());
        let mut pending_pinned_count = 0;
        let pending_items = pending
            .children
            .iter()
            .enumerate()
            .filter(|(_, item)| !live_keys.contains(&item.key()))
            .map(|(index, item)| {
                if index < pending.pinned_count {
                    pending_pinned_count += 1;
                }
                SerializedItem {
                    active: item.active && !live_has_active,
                    preview: item.preview && !live_has_preview,
                    ..item.clone()
                }
            })
            .collect::<Vec<_>>();
        self.children
            .splice(insertion_index..insertion_index, pending_items);
        self.pinned_count = insertion_index + pending_pinned_count;
    }
}

pub type GroupId = i64;
pub type PaneId = i64;
pub type ItemId = u64;

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct SerializedItem {
    pub kind: Arc<str>,
    pub item_id: ItemId,
    pub active: bool,
    pub preview: bool,
}

impl SerializedItem {
    pub fn new(kind: impl AsRef<str>, item_id: ItemId, active: bool, preview: bool) -> Self {
        Self {
            kind: Arc::from(kind.as_ref()),
            item_id,
            active,
            preview,
        }
    }

    pub(crate) fn key(&self) -> (Arc<str>, ItemId) {
        (self.kind.clone(), self.item_id)
    }
}

#[cfg(test)]
impl Default for SerializedItem {
    fn default() -> Self {
        SerializedItem {
            kind: Arc::from("Terminal"),
            item_id: 100000,
            active: false,
            preview: false,
        }
    }
}

impl StaticColumnCount for SerializedItem {
    fn column_count() -> usize {
        4
    }
}
impl Bind for &SerializedItem {
    fn bind(&self, statement: &Statement, start_index: i32) -> Result<i32> {
        let next_index = statement.bind(&self.kind, start_index)?;
        let next_index = statement.bind(&self.item_id, next_index)?;
        let next_index = statement.bind(&self.active, next_index)?;
        statement.bind(&self.preview, next_index)
    }
}

impl Column for SerializedItem {
    fn column(statement: &mut Statement, start_index: i32) -> Result<(Self, i32)> {
        let (kind, next_index) = Arc::<str>::column(statement, start_index)?;
        let (item_id, next_index) = ItemId::column(statement, next_index)?;
        let (active, next_index) = bool::column(statement, next_index)?;
        let (preview, next_index) = bool::column(statement, next_index)?;
        Ok((
            SerializedItem {
                kind,
                item_id,
                active,
                preview,
            },
            next_index,
        ))
    }
}
