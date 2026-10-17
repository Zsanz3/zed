use crate::{
    ActiveDebugLine, Anchor, Autoscroll, BufferSerialization, Capability, Editor, EditorEvent,
    EditorSettings, ExcerptRange, FormatTarget, MultiBuffer, MultiBufferSnapshot, NavigationData,
    ReportEditorEvent, SelectionEffects, ToPoint as _,
    display_map::HighlightKey,
    editor_settings::SeedQuerySetting,
    persistence::{DeletedFile, EditorDb, SerializedEditor, TextFormat},
    scroll::{ScrollAnchor, ScrollOffset},
};
use anyhow::{Context as _, Result, anyhow};
use collections::{HashMap, HashSet};
use file_icons::FileIcons;
use fs::MTime;
use futures::{
    FutureExt as _,
    channel::oneshot,
    future::{Shared, try_join_all},
};
use git::status::GitSummary;
use gpui::{
    AnyElement, App, AsyncWindowContext, Context, Entity, EntityId, EventEmitter, Font, Global,
    IntoElement, ParentElement, Pixels, SharedString, Styled, Task, WeakEntity, Window, point,
};
use language::{
    Bias, Buffer, BufferRow, CharKind, CharScopeContext, DiskState, HighlightedText, Language,
    LocalFile, PLAIN_TEXT, Point, SelectionGoal,
    language_settings::{FormatOnSave, LanguageSettings},
    proto::serialize_anchor as serialize_text_anchor,
};
use lsp::DiagnosticSeverity;
use multi_buffer::{BufferOffset, MultiBufferOffset, MultiBufferRow, PathKey};
use project::{
    File, Project, ProjectItem as _, ProjectPath,
    git_store::GitStore,
    lsp_store::{FormatTrigger, LanguageServerShowDocumentRequest},
    project_settings::ProjectSettings,
    search::SearchQuery,
};
use rope::TextSummary;
use rpc::proto::{self, update_view};
use settings::Settings;
use std::{
    any::{Any, TypeId},
    borrow::Cow,
    cmp::{self, Ordering},
    num::NonZeroU32,
    ops::Range,
    path::{Path, PathBuf},
    sync::Arc,
};
use text::{BufferId, BufferSnapshot, OffsetRangeExt, Selection, ToPoint as _};
use ui::{IconDecorationKind, prelude::*};
use util::{
    ResultExt, TryFutureExt, debug_panic,
    paths::{PathExt, UrlExt as _},
    rel_path::RelPath,
};
use workspace::item::{Dedup, ItemSettings, SerializableItem, TabContentParams};
use workspace::{
    CollaboratorId, ItemId, ItemNavHistory, OpenOptions, OpenVisible, ToolbarItemLocation, ViewId,
    Workspace, WorkspaceId,
    invalid_item_view::InvalidItemView,
    item::{FollowableItem, Item, ItemBufferKind, ItemEvent, ProjectItem, SaveOptions},
    searchable::{
        Direction, FilteredSearchRange, SearchEvent, SearchToken, SearchableItem,
        SearchableItemHandle, SelectSearchOptions,
    },
    unrestored_item_view::RestorationFailure,
};
use workspace::{
    Pane, TabBarSettings, WorkspaceSettings,
    item::{FollowEvent, ProjectItemKind},
    searchable::SearchOptions,
};
use zed_actions::preview::{
    markdown::OpenPreview as OpenMarkdownPreview, svg::OpenPreview as OpenSvgPreview,
};

pub const MAX_TAB_TITLE_LEN: usize = 24;

impl FollowableItem for Editor {
    fn remote_id(&self) -> Option<ViewId> {
        self.remote_id
    }

    fn from_state_proto(
        workspace: Entity<Workspace>,
        remote_id: ViewId,
        state: &mut Option<proto::view::Variant>,
        window: &mut Window,
        cx: &mut App,
    ) -> Option<Task<Result<Entity<Self>>>> {
        let project = workspace.read(cx).project().to_owned();
        let Some(proto::view::Variant::Editor(_)) = state else {
            return None;
        };
        let Some(proto::view::Variant::Editor(state)) = state.take() else {
            unreachable!()
        };

        let buffer_ids = state
            .path_excerpts
            .iter()
            .map(|excerpt| excerpt.buffer_id)
            .collect::<HashSet<_>>();

        let buffers = project.update(cx, |project, cx| {
            buffer_ids
                .iter()
                .map(|id| BufferId::new(*id).map(|id| project.open_buffer_by_id(id, cx)))
                .collect::<Result<Vec<_>>>()
        });

        Some(window.spawn(cx, async move |cx| {
            let mut buffers = futures::future::try_join_all(buffers?)
                .await
                .debug_assert_ok("leaders don't share views for unshared buffers")?;

            let path_excerpts =
                deserialize_path_excerpts_and_wait_for_anchors(state.path_excerpts, &buffers, cx)
                    .await?;

            let editor = cx.update(|window, cx| {
                let multibuffer = cx.new(|cx| {
                    let mut multibuffer;
                    if state.singleton && buffers.len() == 1 {
                        multibuffer = MultiBuffer::singleton(buffers.pop().unwrap(), cx)
                    } else {
                        multibuffer = MultiBuffer::new(project.read(cx).capability());
                        for (path_key, buffer_id, ranges) in path_excerpts {
                            let Some(buffer) =
                                buffers.iter().find(|b| b.read(cx).remote_id() == buffer_id)
                            else {
                                continue;
                            };
                            let buffer_snapshot = buffer.read(cx).snapshot();
                            multibuffer.update_path_excerpts(
                                path_key,
                                buffer.clone(),
                                &buffer_snapshot,
                                &ranges,
                                cx,
                            );
                        }
                    };

                    if let Some(title) = &state.title {
                        multibuffer = multibuffer.with_title(title.clone())
                    }

                    multibuffer
                });

                cx.new(|cx| {
                    let mut editor =
                        Editor::for_multibuffer(multibuffer, Some(project.clone()), window, cx);
                    editor.remote_id = Some(remote_id);
                    editor
                })
            })?;

            editor.update(cx, |editor, cx| editor.text(cx));
            update_editor_from_message(
                editor.downgrade(),
                project,
                proto::update_view::Editor {
                    selections: state.selections,
                    pending_selection: state.pending_selection,
                    scroll_top_anchor: state.scroll_top_anchor,
                    scroll_x: state.scroll_x,
                    scroll_y: state.scroll_y,
                    ..Default::default()
                },
                cx,
            )
            .await?;

            Ok(editor)
        }))
    }

    fn set_leader_id(
        &mut self,
        leader_id: Option<CollaboratorId>,
        window: &mut Window,
        cx: &mut Context<Self>,
    ) {
        self.leader_id = leader_id;
        if self.leader_id.is_some() {
            self.buffer.update(cx, |buffer, cx| {
                buffer.remove_active_selections(cx);
            });
        } else if self.focus_handle.is_focused(window) {
            self.buffer.update(cx, |buffer, cx| {
                buffer.set_active_selections(
                    &self.selections.disjoint_anchors_arc(),
                    self.selections.line_mode(),
                    self.cursor_shape,
                    cx,
                );
            });
        }
        cx.notify();
    }

    fn to_state_proto(&self, _: &mut Window, cx: &mut App) -> Option<proto::view::Variant> {
        let is_private = self
            .buffer
            .read(cx)
            .as_singleton()
            .and_then(|buffer| buffer.read(cx).file())
            .is_some_and(|file| file.is_private());
        if is_private {
            return None;
        }

        let display_snapshot = self.display_map.update(cx, |map, cx| map.snapshot(cx));
        let scroll_anchor = self.scroll_manager.native_anchor(&display_snapshot, cx);
        let buffer = self.buffer.read(cx);
        let snapshot = buffer.snapshot(cx);
        let mut path_excerpts: Vec<proto::PathExcerpts> = Vec::new();
        for excerpt in snapshot.excerpts() {
            if let Some(prev_entry) = path_excerpts.last_mut()
                && prev_entry.buffer_id == excerpt.context.start.buffer_id.to_proto()
            {
                prev_entry.ranges.push(serialize_excerpt_range(excerpt));
            } else if let Some(path_key) = snapshot.path_for_buffer(excerpt.context.start.buffer_id)
            {
                path_excerpts.push(proto::PathExcerpts {
                    path_key: Some(serialize_path_key(path_key)),
                    buffer_id: excerpt.context.start.buffer_id.to_proto(),
                    ranges: vec![serialize_excerpt_range(excerpt)],
                });
            }
        }

        Some(proto::view::Variant::Editor(proto::view::Editor {
            singleton: buffer.is_singleton(),
            title: buffer.explicit_title().map(ToOwned::to_owned),
            excerpts: Vec::new(),
            scroll_top_anchor: Some(serialize_anchor(&scroll_anchor.anchor)),
            scroll_x: scroll_anchor.offset.x,
            scroll_y: scroll_anchor.offset.y,
            selections: self
                .selections
                .disjoint_anchors_arc()
                .iter()
                .map(serialize_selection)
                .collect(),
            pending_selection: self
                .selections
                .pending_anchor()
                .as_ref()
                .copied()
                .map(serialize_selection),
            path_excerpts,
        }))
    }

    fn to_follow_event(event: &EditorEvent) -> Option<workspace::item::FollowEvent> {
        match event {
            EditorEvent::Edited { .. } => Some(FollowEvent::Unfollow),
            EditorEvent::SelectionsChanged { local }
            | EditorEvent::ScrollPositionChanged { local, .. } => {
                if *local {
                    Some(FollowEvent::Unfollow)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn add_event_to_update_proto(
        &self,
        event: &EditorEvent,
        update: &mut Option<proto::update_view::Variant>,
        _: &mut Window,
        cx: &mut App,
    ) -> bool {
        let update =
            update.get_or_insert_with(|| proto::update_view::Variant::Editor(Default::default()));

        match update {
            proto::update_view::Variant::Editor(update) => match event {
                EditorEvent::BufferRangesUpdated {
                    buffer,
                    path_key,
                    ranges,
                } => {
                    let buffer_id = buffer.read(cx).remote_id().to_proto();
                    let path_key = serialize_path_key(path_key);
                    let ranges = ranges
                        .iter()
                        .cloned()
                        .map(serialize_excerpt_range)
                        .collect::<Vec<_>>();
                    update.updated_paths.push(proto::PathExcerpts {
                        path_key: Some(path_key),
                        buffer_id,
                        ranges,
                    });
                    true
                }
                EditorEvent::BuffersRemoved { removed_buffer_ids } => {
                    update
                        .deleted_buffers
                        .extend(removed_buffer_ids.iter().copied().map(BufferId::to_proto));
                    true
                }
                EditorEvent::ScrollPositionChanged { autoscroll, .. } if !autoscroll => {
                    let display_snapshot = self.display_map.update(cx, |map, cx| map.snapshot(cx));
                    let scroll_anchor = self.scroll_manager.native_anchor(&display_snapshot, cx);
                    update.scroll_top_anchor = Some(serialize_anchor(&scroll_anchor.anchor));
                    update.scroll_x = scroll_anchor.offset.x;
                    update.scroll_y = scroll_anchor.offset.y;
                    true
                }
                EditorEvent::SelectionsChanged { .. } => {
                    update.selections = self
                        .selections
                        .disjoint_anchors_arc()
                        .iter()
                        .map(serialize_selection)
                        .collect();
                    update.pending_selection = self
                        .selections
                        .pending_anchor()
                        .as_ref()
                        .copied()
                        .map(serialize_selection);
                    true
                }
                _ => false,
            },
        }
    }

    fn apply_update_proto(
        &mut self,
        project: &Entity<Project>,
        message: update_view::Variant,
        window: &mut Window,
        cx: &mut Context<Self>,
    ) -> Task<Result<()>> {
        let update_view::Variant::Editor(message) = message;
        let project = project.clone();
        cx.spawn_in(window, async move |this, cx| {
            update_editor_from_message(this, project, message, cx).await
        })
    }

    fn is_project_item(&self, _window: &Window, _cx: &App) -> bool {
        true
    }

    fn dedup(&self, existing: &Self, _: &Window, cx: &App) -> Option<Dedup> {
        let self_singleton = self.buffer.read(cx).as_singleton()?;
        let other_singleton = existing.buffer.read(cx).as_singleton()?;
        if self_singleton == other_singleton {
            Some(Dedup::KeepExisting)
        } else {
            None
        }
    }

    fn update_agent_location(
        &mut self,
        location: language::Anchor,
        window: &mut Window,
        cx: &mut Context<Self>,
    ) {
        let buffer = self.buffer.read(cx);
        let buffer = buffer.read(cx);
        let Some(position) = buffer.anchor_in_excerpt(location) else {
            return;
        };
        let selection = Selection {
            id: 0,
            reversed: false,
            start: position,
            end: position,
            goal: SelectionGoal::None,
        };
        drop(buffer);
        self.set_selections_from_remote(vec![selection], None, window, cx);
        self.request_autoscroll_remotely(Autoscroll::focused(), cx);
    }
}

async fn update_editor_from_message(
    this: WeakEntity<Editor>,
    project: Entity<Project>,
    message: proto::update_view::Editor,
    cx: &mut AsyncWindowContext,
) -> Result<()> {
    // Open all of the buffers of which excerpts were added to the editor.
    let inserted_excerpt_buffer_ids = message
        .updated_paths
        .iter()
        .map(|insertion| insertion.buffer_id)
        .collect::<HashSet<_>>();
    let inserted_excerpt_buffers = project.update(cx, |project, cx| {
        inserted_excerpt_buffer_ids
            .into_iter()
            .map(|id| BufferId::new(id).map(|id| project.open_buffer_by_id(id, cx)))
            .collect::<Result<Vec<_>>>()
    })?;
    let inserted_excerpt_buffers = try_join_all(inserted_excerpt_buffers).await?;

    let updated_paths = deserialize_path_excerpts_and_wait_for_anchors(
        message.updated_paths,
        &inserted_excerpt_buffers,
        cx,
    )
    .await?;

    // Update the editor's excerpts.
    let buffer_snapshot = this.update(cx, |editor, cx| {
        editor.buffer.update(cx, |multibuffer, cx| {
            for (path_key, buffer_id, ranges) in updated_paths {
                let Some(buffer) = project.read(cx).buffer_for_id(buffer_id, cx) else {
                    continue;
                };

                let buffer_snapshot = buffer.read(cx).snapshot();
                multibuffer.update_path_excerpts(path_key, buffer, &buffer_snapshot, &ranges, cx);
            }

            for buffer_id in message
                .deleted_buffers
                .into_iter()
                .filter_map(|buffer_id| BufferId::new(buffer_id).ok())
            {
                multibuffer.remove_excerpts_for_buffer(buffer_id, cx);
            }

            multibuffer.snapshot(cx)
        })
    })?;

    // Deserialize the editor state.
    let selections = message
        .selections
        .into_iter()
        .filter_map(|selection| deserialize_selection(selection, &buffer_snapshot))
        .collect::<Vec<_>>();
    let pending_selection = message
        .pending_selection
        .and_then(|selection| deserialize_selection(selection, &buffer_snapshot));
    let scroll_top_anchor = message
        .scroll_top_anchor
        .and_then(|selection| deserialize_anchor(selection, &buffer_snapshot));

    // Wait until the buffer has received all of the operations referenced by
    // the editor's new state.
    this.update(cx, |editor, cx| {
        editor.buffer.update(cx, |buffer, cx| {
            buffer.wait_for_anchors(
                selections
                    .iter()
                    .chain(pending_selection.as_ref())
                    .flat_map(|selection| [selection.start, selection.end])
                    .chain(scroll_top_anchor),
                cx,
            )
        })
    })?
    .await?;

    // Update the editor's state.
    this.update_in(cx, |editor, window, cx| {
        if !selections.is_empty() || pending_selection.is_some() {
            editor.set_selections_from_remote(selections, pending_selection, window, cx);
            editor.request_autoscroll_remotely(Autoscroll::newest(), cx);
        } else if let Some(scroll_top_anchor) = scroll_top_anchor {
            editor.set_scroll_anchor_remote(
                ScrollAnchor {
                    anchor: scroll_top_anchor,
                    offset: point(message.scroll_x, message.scroll_y),
                },
                window,
                cx,
            );
        }
    })?;
    Ok(())
}

fn serialize_selection(selection: &Selection<Anchor>) -> proto::Selection {
    proto::Selection {
        id: selection.id as u64,
        start: Some(serialize_anchor(&selection.start)),
        end: Some(serialize_anchor(&selection.end)),
        reversed: selection.reversed,
    }
}

fn serialize_anchor(anchor: &Anchor) -> proto::EditorAnchor {
    match anchor {
        Anchor::Min => proto::EditorAnchor {
            excerpt_id: None,
            anchor: Some(proto::Anchor {
                replica_id: 0,
                timestamp: 0,
                offset: 0,
                bias: proto::Bias::Left as i32,
                buffer_id: None,
            }),
        },
        Anchor::Excerpt(_) => proto::EditorAnchor {
            excerpt_id: None,
            anchor: anchor.raw_text_anchor().map(|a| serialize_text_anchor(&a)),
        },
        Anchor::Max => proto::EditorAnchor {
            excerpt_id: None,
            anchor: Some(proto::Anchor {
                replica_id: u32::MAX,
                timestamp: u32::MAX,
                offset: u64::MAX,
                bias: proto::Bias::Right as i32,
                buffer_id: None,
            }),
        },
    }
}

fn serialize_excerpt_range(range: ExcerptRange<language::Anchor>) -> proto::ExcerptRange {
    let context_start = language::proto::serialize_anchor(&range.context.start);
    let context_end = language::proto::serialize_anchor(&range.context.end);
    let primary_start = language::proto::serialize_anchor(&range.primary.start);
    let primary_end = language::proto::serialize_anchor(&range.primary.end);
    proto::ExcerptRange {
        context_start: Some(context_start),
        context_end: Some(context_end),
        primary_start: Some(primary_start),
        primary_end: Some(primary_end),
    }
}

async fn deserialize_path_excerpts_and_wait_for_anchors(
    path_excerpts: Vec<proto::PathExcerpts>,
    buffers: &[Entity<Buffer>],
    cx: &mut AsyncWindowContext,
) -> Result<Vec<(PathKey, BufferId, Vec<ExcerptRange<language::Anchor>>)>> {
    let path_excerpts = path_excerpts
        .into_iter()
        .filter_map(|path_with_ranges| {
            let path_key = path_with_ranges.path_key.and_then(deserialize_path_key)?;
            let buffer_id = BufferId::new(path_with_ranges.buffer_id).ok()?;
            let ranges = path_with_ranges
                .ranges
                .into_iter()
                .filter_map(deserialize_excerpt_range)
                .collect::<Vec<_>>();
            Some((path_key, buffer_id, ranges))
        })
        .collect::<Vec<_>>();

    let wait_for_anchors = cx.update(|_, cx| {
        buffers
            .iter()
            .map(|buffer| {
                let buffer_id = buffer.read(cx).remote_id();
                let anchors = path_excerpts
                    .iter()
                    .filter(|(_, id, _)| *id == buffer_id)
                    .flat_map(|(_, _, ranges)| {
                        ranges.iter().flat_map(|range| {
                            [
                                range.context.start,
                                range.context.end,
                                range.primary.start,
                                range.primary.end,
                            ]
                        })
                    })
                    .collect::<Vec<_>>();
                buffer.update(cx, |buffer, _| buffer.wait_for_anchors(anchors))
            })
            .collect::<Vec<_>>()
    })?;
    // Without this wait, resolving these anchors later can race ahead of the
    // leader's pending buffer ops and trip `panic_bad_anchor` on a stale
    // snapshot.
    try_join_all(wait_for_anchors).await?;

    Ok(path_excerpts)
}

fn deserialize_excerpt_range(
    excerpt_range: proto::ExcerptRange,
) -> Option<ExcerptRange<language::Anchor>> {
    let context = {
        let start = language::proto::deserialize_anchor(excerpt_range.context_start?)?;
        let end = language::proto::deserialize_anchor(excerpt_range.context_end?)?;
        start..end
    };
    let primary = excerpt_range
        .primary_start
        .zip(excerpt_range.primary_end)
        .and_then(|(start, end)| {
            let start = language::proto::deserialize_anchor(start)?;
            let end = language::proto::deserialize_anchor(end)?;
            Some(start..end)
        })
        .unwrap_or_else(|| context.clone());
    Some(ExcerptRange { context, primary })
}

fn deserialize_selection(
    selection: proto::Selection,
    buffer: &MultiBufferSnapshot,
) -> Option<Selection<Anchor>> {
    Some(Selection {
        id: selection.id as usize,
        start: deserialize_anchor(selection.start?, buffer)?,
        end: deserialize_anchor(selection.end?, buffer)?,
        reversed: selection.reversed,
        goal: SelectionGoal::None,
    })
}

fn deserialize_anchor(anchor: proto::EditorAnchor, buffer: &MultiBufferSnapshot) -> Option<Anchor> {
    let anchor = anchor.anchor?;
    if let Some(buffer_id) = anchor.buffer_id
        && BufferId::new(buffer_id).is_ok()
    {
        let text_anchor = language::proto::deserialize_anchor(anchor)?;
        buffer.anchor_in_buffer(text_anchor)
    } else {
        match proto::Bias::try_from(anchor.bias).ok()? {
            proto::Bias::Left => Some(Anchor::Min),
            proto::Bias::Right => Some(Anchor::Max),
        }
    }
}

impl Item for Editor {
    type Event = EditorEvent;

    fn act_as_type<'a>(
        &'a self,
        type_id: TypeId,
        self_handle: &'a Entity<Self>,
        cx: &'a App,
    ) -> Option<gpui::AnyEntity> {
        if TypeId::of::<Self>() == type_id {
            Some(self_handle.clone().into())
        } else if TypeId::of::<MultiBuffer>() == type_id {
            Some(self_handle.read(cx).buffer.clone().into())
        } else {
            None
        }
    }

    fn navigate(
        &mut self,
        data: Arc<dyn Any + Send>,
        window: &mut Window,
        cx: &mut Context<Self>,
    ) -> bool {
        if let Some(data) = data.downcast_ref::<NavigationData>() {
            let newest_selection = self.selections.newest::<Point>(&self.display_snapshot(cx));
            let buffer = self.buffer.read(cx).read(cx);
            let offset = if buffer.can_resolve(&data.cursor_anchor) {
                data.cursor_anchor.to_point(&buffer)
            } else {
                buffer.clip_point(data.cursor_position, Bias::Left)
            };

            let mut scroll_anchor = data.scroll_anchor;
            if !buffer.can_resolve(&scroll_anchor.anchor) {
                scroll_anchor.anchor = buffer.anchor_before(
                    buffer.clip_point(Point::new(data.scroll_top_row, 0), Bias::Left),
                );
            }

            drop(buffer);

            if newest_selection.head() == offset {
                false
            } else {
                self.set_scroll_anchor(scroll_anchor, window, cx);
                self.change_selections(
                    SelectionEffects::default().nav_history(false),
                    window,
                    cx,
                    |s| s.select_ranges([offset..offset]),
                );
                true
            }
        } else {
            false
        }
    }

    fn tab_tooltip_text(&self, cx: &App) -> Option<SharedString> {
        let multi_buffer = self.buffer().read(cx);
        if let Some(file) = multi_buffer
            .as_singleton()
            .and_then(|buffer| buffer.read(cx).file())
            .and_then(|file| File::from_dyn(Some(file)))
        {
            Some(
                file.worktree
                    .read(cx)
                    .absolutize(&file.path)
                    .compact()
                    .to_string_lossy()
                    .into_owned()
                    .into(),
            )
        } else if let Some(recovered_from) = recovered_source_path(self, cx) {
            Some(format!("{} (recovered)", recovered_from.compact().to_string_lossy()).into())
        } else {
            let title = multi_buffer.title(cx);
            (!title.is_empty()).then(|| title.to_string().into())
        }
    }

    fn telemetry_event_text(&self) -> Option<&'static str> {
        None
    }

    fn tab_content_text(&self, detail: usize, cx: &App) -> SharedString {
        if let Some(path) = path_for_buffer(&self.buffer, detail, true, cx) {
            path.to_string().into()
        } else {
            // Use the same logic as the displayed title for consistency
            tab_title(self, cx).to_string().into()
        }
    }

    fn suggested_filename(&self, cx: &App) -> SharedString {
        if let Some(file_name) = recovered_source_path(self, cx).and_then(|path| path.file_name()) {
            return file_name.to_string_lossy().into_owned().into();
        }
        let multi_buffer = self.buffer.read(cx);
        let title = multi_buffer.title(cx);
        if let Some(buffer) = multi_buffer.as_singleton() {
            let buffer = buffer.read(cx);
            if buffer.file().is_none()
                && let Some(language) = buffer.language()
                && *language != *PLAIN_TEXT
                && let Some(suffix) = language.path_suffixes().first()
                && !suffix.is_empty()
                && !title.ends_with(&format!(".{suffix}"))
            {
                return format!("{title}.{suffix}").into();
            }
        }

        title.to_string().into()
    }

    fn tab_icon(&self, _: &Window, cx: &App) -> Option<Icon> {
        ItemSettings::get_global(cx)
            .file_icons
            .then(|| {
                path_for_buffer(&self.buffer, 0, true, cx)
                    .and_then(|path| FileIcons::get_icon(Path::new(&*path), cx))
            })
            .flatten()
            .map(Icon::from_path)
    }

    fn tab_content(&self, params: TabContentParams, _: &Window, cx: &App) -> AnyElement {
        let label_color = if ItemSettings::get_global(cx).git_status {
            self.buffer()
                .read(cx)
                .as_singleton()
                .and_then(|buffer| {
                    let buffer = buffer.read(cx);
                    let path = buffer.project_path(cx)?;
                    let buffer_id = buffer.remote_id();
                    let project = self.project()?.read(cx);
                    let entry = project.entry_for_path(&path, cx)?;
                    let status = project
                        .git_store()
                        .read(cx)
                        .display_status_for_buffer_id(buffer_id, cx)?;

                    Some(entry_git_aware_label_color(
                        status.summary(),
                        entry.is_ignored,
                        params.selected,
                    ))
                })
                .unwrap_or_else(|| entry_label_color(params.selected))
        } else {
            entry_label_color(params.selected)
        };

        let description = params.detail.and_then(|detail| {
            let path = path_for_buffer(&self.buffer, detail, false, cx)?;
            let description = path.trim();

            if description.is_empty() {
                return None;
            }

            Some(util::truncate_and_trailoff(
                description,
                params.max_title_len.unwrap_or(MAX_TAB_TITLE_LEN),
            ))
        });

        // Whether the file was saved in the past but is now deleted.
        let was_deleted: bool = self
            .buffer()
            .read(cx)
            .as_singleton()
            .and_then(|buffer| buffer.read(cx).file())
            .is_some_and(|file| file.disk_state().is_deleted());

        h_flex()
            .gap_1()
            .when(!params.selected, |tab| tab.track_focus(&self.focus_handle))
            .when(params.truncate_title_middle, |this| {
                this.w_full().min_w_0().overflow_hidden()
            })
            .child(
                Label::new(if params.truncate_title_middle {
                    tab_title(self, cx).to_string()
                } else {
                    util::truncate_and_trailoff(
                        &tab_title(self, cx),
                        params.max_title_len.unwrap_or(MAX_TAB_TITLE_LEN),
                    )
                })
                .single_line()
                .color(label_color)
                .when(params.truncate_title_middle, |this| {
                    this.truncate_middle().flex_1()
                })
                .when(params.preview, |this| this.italic())
                .when(was_deleted, |this| this.strikethrough()),
            )
            .when_some(description, |this, description| {
                this.child(
                    Label::new(description)
                        .single_line()
                        .size(LabelSize::XSmall)
                        .when(params.truncate_title_middle, |this| {
                            this.truncate_start().flex_shrink()
                        })
                        .color(Color::Muted),
                )
            })
            .into_any_element()
    }

    fn for_each_project_item(
        &self,
        cx: &App,
        f: &mut dyn FnMut(EntityId, &dyn project::ProjectItem),
    ) {
        self.buffer
            .read(cx)
            .for_each_buffer(&mut |buffer| f(buffer.entity_id(), buffer.read(cx)));
    }

    fn buffer_kind(&self, cx: &App) -> ItemBufferKind {
        match self.buffer.read(cx).is_singleton() {
            true => ItemBufferKind::Singleton,
            false => ItemBufferKind::Multibuffer,
        }
    }

    fn active_project_path(&self, cx: &App) -> Option<ProjectPath> {
        self.active_buffer(cx)?.read(cx).project_path(cx)
    }

    fn can_save_as(&self, cx: &App) -> bool {
        self.buffer.read(cx).is_singleton()
    }

    fn can_split(&self) -> bool {
        true
    }

    fn clone_on_split(
        &self,
        _workspace_id: Option<WorkspaceId>,
        window: &mut Window,
        cx: &mut Context<Self>,
    ) -> Task<Option<Entity<Editor>>>
    where
        Self: Sized,
    {
        Task::ready(Some(cx.new(|cx| self.clone(window, cx))))
    }

    fn set_nav_history(
        &mut self,
        history: ItemNavHistory,
        _window: &mut Window,
        _: &mut Context<Self>,
    ) {
        self.nav_history = Some(history);
    }

    fn on_removed(&self, cx: &mut Context<Self>) {
        self.report_editor_event(ReportEditorEvent::Closed, None, cx);
    }

    fn deactivated(&mut self, _: &mut Window, cx: &mut Context<Self>) {
        let selection = self.selections.newest_anchor();
        self.push_to_nav_history(selection.head(), None, true, false, cx);
    }

    fn workspace_deactivated(&mut self, _: &mut Window, cx: &mut Context<Self>) {
        self.hide_hovered_link(cx);
    }

    fn is_dirty(&self, cx: &App) -> bool {
        self.buffer().read(cx).read(cx).is_dirty() || recovered_source_path(self, cx).is_some()
    }

    fn capability(&self, cx: &App) -> Capability {
        self.capability(cx)
    }

    // Note: this mirrors the logic in `Editor::toggle_read_only`, but is reachable
    // without relying on focus-based action dispatch.
    fn toggle_read_only(&mut self, window: &mut Window, cx: &mut Context<Self>) {
        if let Some(buffer) = self.buffer.read(cx).as_singleton() {
            buffer.update(cx, |buffer, cx| {
                buffer.set_capability(
                    match buffer.capability() {
                        Capability::ReadWrite => Capability::Read,
                        Capability::Read => Capability::ReadWrite,
                        Capability::ReadOnly => Capability::ReadOnly,
                    },
                    cx,
                );
            });
        }
        cx.notify();
        window.refresh();
    }

    fn has_deleted_file(&self, cx: &App) -> bool {
        self.buffer().read(cx).read(cx).has_deleted_file()
    }

    fn has_conflict(&self, cx: &App) -> bool {
        self.buffer().read(cx).read(cx).has_conflict()
    }

    fn can_save(&self, cx: &App) -> bool {
        if self.read_only(cx) {
            return false;
        }
        let buffer = &self.buffer().read(cx);
        if let Some(buffer) = buffer.as_singleton() {
            buffer.read(cx).project_path(cx).is_some()
        } else {
            true
        }
    }

    fn save(
        &mut self,
        options: SaveOptions,
        project: Entity<Project>,
        window: &mut Window,
        cx: &mut Context<Self>,
    ) -> Task<Result<()>> {
        if self.read_only(cx) {
            return Task::ready(Ok(()));
        }
        // Add meta data tracking # of auto saves
        if options.autosave {
            self.report_editor_event(ReportEditorEvent::Saved { auto_saved: true }, None, cx);
        } else {
            self.report_editor_event(ReportEditorEvent::Saved { auto_saved: false }, None, cx);
        }

        let buffers = self.buffer().clone().read(cx).all_buffers();
        let buffers = buffers
            .into_iter()
            .map(|handle| handle.read(cx).base_buffer().unwrap_or(handle.clone()))
            .collect::<HashSet<_>>();

        let buffers_to_save = if self.buffer.read(cx).is_singleton() && !options.autosave {
            buffers
        } else {
            buffers
                .into_iter()
                // Skip untitled buffers: a multi-buffer (e.g. project search results) can
                // excerpt a buffer with no file on disk, which can only be persisted via
                // `save_as`. Trying to save it here errors and aborts the whole save.
                .filter(|buffer| {
                    let buffer = buffer.read(cx);
                    buffer.is_dirty() && !buffer.read_only() && buffer.file().is_some()
                })
                .collect()
        };

        let format_trigger = if options.force_format {
            FormatTrigger::Manual
        } else {
            FormatTrigger::Save
        };

        cx.spawn_in(window, async move |this, cx| {
            if options.format {
                let format_task = this.update_in(cx, |editor, window, cx| {
                    let format_target = compute_format_target(
                        &buffers_to_save,
                        format_trigger,
                        editor.buffer(),
                        project.read(cx).git_store(),
                        cx,
                    );
                    format_target.map(|target| {
                        editor.perform_format(project.clone(), format_trigger, target, window, cx)
                    })
                })?;
                if let Some(format_task) = format_task {
                    format_task.await?;
                }
            }

            if !buffers_to_save.is_empty() {
                project
                    .update(cx, |project, cx| {
                        project.save_buffers(buffers_to_save.clone(), cx)
                    })
                    .await?;
            }

            Ok(())
        })
    }

    fn save_as(
        &mut self,
        project: Entity<Project>,
        path: ProjectPath,
        _: &mut Window,
        cx: &mut Context<Self>,
    ) -> Task<Result<()>> {
        let buffer = self
            .buffer()
            .read(cx)
            .as_singleton()
            .expect("cannot call save_as on an excerpt list");

        let file_extension = path.path.extension().map(|a| a.to_string());
        self.report_editor_event(
            ReportEditorEvent::Saved { auto_saved: false },
            file_extension,
            cx,
        );

        project.update(cx, |project, cx| project.save_buffer_as(buffer, path, cx))
    }

    fn reload(
        &mut self,
        project: Entity<Project>,
        window: &mut Window,
        cx: &mut Context<Self>,
    ) -> Task<Result<()>> {
        let buffer = self.buffer().clone();
        let buffers = self.buffer.read(cx).all_buffers();
        let reload_buffers =
            project.update(cx, |project, cx| project.reload_buffers(buffers, true, cx));
        cx.spawn_in(window, async move |this, cx| {
            let transaction = reload_buffers.log_err().await;
            this.update(cx, |editor, cx| {
                editor.request_autoscroll(Autoscroll::fit(), cx)
            })?;
            buffer.update(cx, |buffer, cx| {
                if let Some(transaction) = transaction
                    && !buffer.is_singleton()
                {
                    buffer.push_transaction(&transaction.0, cx);
                }
            });
            Ok(())
        })
    }

    fn as_searchable(
        &self,
        handle: &Entity<Self>,
        _: &App,
    ) -> Option<Box<dyn SearchableItemHandle>> {
        Some(Box::new(handle.clone()))
    }

    fn pixel_position_of_cursor(&self, _: &App) -> Option<gpui::Point<Pixels>> {
        self.pixel_position_of_newest_cursor
    }

    fn breadcrumb_location(&self, cx: &App) -> ToolbarItemLocation {
        if self.breadcrumbs_visible() && self.buffer().read(cx).is_singleton() {
            ToolbarItemLocation::PrimaryLeft
        } else {
            ToolbarItemLocation::Hidden
        }
    }

    // In a non-singleton case, the breadcrumbs are actually shown on sticky file headers of the multibuffer.
    fn breadcrumbs(&self, cx: &App) -> Option<(Vec<HighlightedText>, Option<Font>)> {
        if self.buffer.read(cx).is_singleton() {
            let font = theme_settings::ThemeSettings::get_global(cx)
                .buffer_font
                .clone();
            Some((self.breadcrumbs_inner(cx)?, Some(font)))
        } else {
            None
        }
    }

    fn breadcrumb_prefix(
        &self,
        _window: &mut Window,
        cx: &mut Context<Self>,
    ) -> Option<gpui::AnyElement> {
        (!TabBarSettings::get_global(cx).show && ItemSettings::get_global(cx).file_icons)
            .then(|| {
                path_for_buffer(&self.buffer, 0, true, cx)
                    .and_then(|path| FileIcons::get_icon(Path::new(&*path), cx))
            })
            .flatten()
            .map(|icon_path| Icon::from_path(icon_path).into_any_element())
    }

    fn added_to_workspace(
        &mut self,
        workspace: &mut Workspace,
        window: &mut Window,
        cx: &mut Context<Self>,
    ) {
        self.workspace = Some((workspace.weak_handle(), workspace.database_id()));
        if let Some(workspace_entity) = &workspace.weak_handle().upgrade() {
            cx.subscribe(
                workspace_entity,
                |editor, _, event: &workspace::Event, cx| {
                    if let workspace::Event::ModalOpened = event {
                        editor.mouse_context_menu.take();
                        editor.hide_blame_popover(true, cx);
                    }
                },
            )
            .detach();
        }

        // Load persisted folds if this editor doesn't already have folds.
        // This handles manually-opened files (not workspace restoration).
        let display_snapshot = self
            .display_map
            .update(cx, |display_map, cx| display_map.snapshot(cx));
        let has_folds = display_snapshot
            .folds_in_range(MultiBufferOffset(0)..display_snapshot.buffer_snapshot().len())
            .next()
            .is_some();

        if !has_folds {
            if let Some(workspace_id) = workspace.database_id()
                && let Some(file_path) = self.buffer().read(cx).as_singleton().and_then(|buffer| {
                    project::File::from_dyn(buffer.read(cx).file()).map(|file| file.abs_path(cx))
                })
            {
                self.load_folds_from_db(workspace_id, file_path, window, cx);
            }
        }
    }

    fn pane_changed(&mut self, new_pane_id: EntityId, cx: &mut Context<Self>) {
        if self
            .highlighted_rows
            .get(&TypeId::of::<ActiveDebugLine>())
            .is_some_and(|lines| !lines.is_empty())
            && let Some(breakpoint_store) = self.breakpoint_store.as_ref()
        {
            breakpoint_store.update(cx, |store, _cx| {
                store.set_active_debug_pane_id(new_pane_id);
            });
        }
    }

    fn to_item_events(event: &EditorEvent, f: &mut dyn FnMut(ItemEvent)) {
        match event {
            EditorEvent::Saved | EditorEvent::TitleChanged => {
                f(ItemEvent::UpdateTab);
                f(ItemEvent::UpdateBreadcrumbs);
            }

            EditorEvent::Reparsed(_) => {
                f(ItemEvent::UpdateBreadcrumbs);
            }

            EditorEvent::SelectionsChanged { local } if *local => {
                f(ItemEvent::UpdateBreadcrumbs);
            }

            EditorEvent::BreadcrumbsChanged | EditorEvent::OutlineSymbolsChanged => {
                f(ItemEvent::UpdateBreadcrumbs);
            }

            EditorEvent::DirtyChanged | EditorEvent::CapabilityChanged => {
                f(ItemEvent::UpdateTab);
            }

            EditorEvent::BufferEdited => {
                f(ItemEvent::Edit);
                f(ItemEvent::UpdateBreadcrumbs);
            }

            EditorEvent::BufferRangesUpdated { .. } | EditorEvent::BuffersRemoved { .. } => {
                f(ItemEvent::Edit);
            }

            _ => {}
        }
    }

    fn tab_extra_context_menu_actions(
        &self,
        _window: &mut Window,
        cx: &mut Context<Self>,
    ) -> Vec<(SharedString, Box<dyn gpui::Action>)> {
        let mut actions = Vec::new();

        let is_markdown = self
            .buffer()
            .read(cx)
            .as_singleton()
            .and_then(|buffer| buffer.read(cx).language())
            .is_some_and(|language| language.name().as_ref() == "Markdown");

        let is_svg = self
            .buffer()
            .read(cx)
            .as_singleton()
            .and_then(|buffer| buffer.read(cx).file())
            .is_some_and(|file| {
                std::path::Path::new(file.file_name(cx))
                    .extension()
                    .is_some_and(|ext| ext.eq_ignore_ascii_case("svg"))
            });

        if is_markdown {
            actions.push((
                "Open Markdown Preview".into(),
                Box::new(OpenMarkdownPreview) as Box<dyn gpui::Action>,
            ));
        }

        if is_svg {
            actions.push((
                "Open SVG Preview".into(),
                Box::new(OpenSvgPreview) as Box<dyn gpui::Action>,
            ));
        }

        actions
    }

    fn preserve_preview(&self, cx: &App) -> bool {
        self.buffer.read(cx).preserve_preview(cx)
    }
}

impl SerializableItem for Editor {
    fn serialized_item_kind() -> &'static str {
        "Editor"
    }

    fn cleanup(
        workspace_id: WorkspaceId,
        alive_items: Vec<ItemId>,
        _window: &mut Window,
        cx: &mut App,
    ) -> Task<Result<()>> {
        workspace::delete_unloaded_items(
            alive_items,
            workspace_id,
            "editors",
            &EditorDb::global(cx),
            cx,
        )
    }

    fn deserialize(
        project: Entity<Project>,
        _workspace: WeakEntity<Workspace>,
        workspace_id: workspace::WorkspaceId,
        item_id: ItemId,
        window: &mut Window,
        cx: &mut App,
    ) -> Task<Result<Entity<Self>>> {
        let serialized_editor = match EditorDb::global(cx)
            .get_serialized_editor(item_id, workspace_id)
            .context("Failed to query editor state")
        {
            Ok(Some(serialized_editor)) => {
                if ProjectSettings::get_global(cx)
                    .session
                    .restore_unsaved_buffers
                {
                    serialized_editor
                } else {
                    SerializedEditor {
                        abs_path: serialized_editor.abs_path,
                        deleted_file: serialized_editor.deleted_file,
                        text_format: serialized_editor.text_format,
                        ..SerializedEditor::default()
                    }
                }
            }
            Ok(None) => {
                return Task::ready(Err(anyhow!(
                    "Unable to deserialize editor: No entry in database for item_id: {item_id} and workspace_id {workspace_id:?}"
                )));
            }
            Err(error) => {
                return Task::ready(Err(error));
            }
        };
        log::debug!(
            "Deserialized editor {item_id:?} in workspace {workspace_id:?}, {serialized_editor:?}"
        );

        window.spawn(cx, async move |cx| {
            let (buffer, recovered_from) = match serialized_editor {
                SerializedEditor {
                    abs_path: Some(abs_path),
                    contents,
                    language,
                    mtime,
                    deleted_file,
                    text_format,
                    ..
                } => {
                    // Open the buffer directly via the project rather than through
                    // workspace.open_abs_path(), which has the side effect of adding
                    // the item to a pane. The caller (deserialize_to) will add the
                    // returned item to the correct pane.
                    let opened_buffer = project
                        .update(cx, |project, cx| project.open_local_buffer(&abs_path, cx))
                        .await
                        .with_context(|| format!("Failed to open buffer for {abs_path:?}"));
                    match (opened_buffer, contents) {
                        (Ok(buffer), contents) => {
                            restore_file_buffer(
                                &project,
                                buffer,
                                &abs_path,
                                SavedFileBuffer {
                                    contents,
                                    mtime,
                                    deleted_file,
                                    text_format,
                                },
                                cx,
                            )
                            .await?
                        }
                        (Err(error), None) => {
                            return Err(error.context(restoration_failure(&abs_path)));
                        }
                        (Err(error), Some(contents)) => {
                            log::warn!(
                                "Restoring the unsaved contents of {abs_path:?} detached from the file: {error:#}"
                            );
                            let language = saved_language(&project, language, cx).await;
                            let buffer = recovered_buffer(
                                &project,
                                &abs_path,
                                language,
                                contents,
                                text_format,
                                cx,
                            )
                            .await?;
                            (buffer, Some(abs_path))
                        }
                    }
                }
                SerializedEditor {
                    abs_path: None,
                    contents,
                    language,
                    recovered_from,
                    shared_buffer,
                    text_format,
                    ..
                } => {
                    let detect_language = language.is_none();
                    let language = saved_language(&project, language, cx).await;
                    let key = shared_buffer.map(|buffer| RestoredBufferKey::Shared {
                        project: project.entity_id(),
                        workspace_id,
                        buffer,
                        contents: contents.clone(),
                        text_format,
                    });
                    let buffer = restored_buffer(
                        &project,
                        key,
                        language,
                        detect_language,
                        contents,
                        text_format,
                        cx,
                    )
                    .await
                    .context("Failed to create buffer while deserializing editor")?;
                    (buffer, recovered_from)
                }
            };

            cx.update(|window, cx| {
                cx.new(|cx| {
                    let mut editor = Editor::for_buffer(buffer, Some(project), window, cx);
                    editor.recovered_from = recovered_from;
                    editor.read_metadata_from_db(item_id, workspace_id, window, cx);
                    editor
                })
            })
        })
    }

    fn serialize(
        &mut self,
        workspace: &mut Workspace,
        item_id: ItemId,
        closing: bool,
        cx: &mut Context<Self>,
    ) -> Option<Task<Result<()>>> {
        let buffer_serialization = self.buffer_serialization?;
        let project = self.project.clone()?;

        let serialize_dirty_buffers = match buffer_serialization {
            // Always serialize dirty buffers, including for worktree-less windows.
            // This enables hot-exit functionality for empty windows and single files.
            BufferSerialization::All => true,
            BufferSerialization::NonDirtyBuffers => false,
        };

        if closing && !serialize_dirty_buffers {
            return None;
        }

        let workspace_id = workspace.database_id()?;

        let buffer = self.buffer().read(cx).as_singleton()?;

        let abs_path = buffer.read(cx).file().and_then(|file| {
            let worktree_id = file.worktree_id(cx);
            project
                .read(cx)
                .worktree_for_id(worktree_id, cx)
                .map(|worktree| worktree.read(cx).absolutize(file.path()))
                .or_else(|| {
                    let full_path = file.full_path(cx);
                    let project_path = project.read(cx).find_project_path(&full_path, cx)?;
                    project.read(cx).absolute_path(&project_path, cx)
                })
        });

        let recovered_from = recovered_source_path(self, cx).map(Path::to_path_buf);
        let shared_buffer = workspace
            .session_id()
            .filter(|_| buffer.read(cx).file().is_none())
            .map(|session_id| {
                let buffer_entity_id = buffer.entity_id().as_u64();
                format!("{session_id}/{buffer_entity_id}")
            });
        let (deleted_file, preserve_contents, text_format) = {
            let buffer = buffer.read(cx);
            let deleted_file = buffer
                .file()
                .filter(|file| file.disk_state() == DiskState::Deleted)
                .map(|_| DeletedFile {
                    dirty: buffer.is_dirty(),
                    read_only: buffer.read_only(),
                });
            let preserve_contents =
                buffer.is_dirty() || (deleted_file.is_some() && !buffer.is_empty());
            let text_format =
                (preserve_contents || deleted_file.is_some()).then(|| TextFormat::of(buffer));
            (deleted_file, preserve_contents, text_format)
        };
        let mtime = buffer.read(cx).saved_mtime();
        let content_language_detection_enabled =
            buffer.read(cx).content_language_detection_enabled();

        let snapshot = buffer.read(cx).snapshot();

        let db = EditorDb::global(cx);
        Some(cx.background_spawn(async move {
            let (contents, language) = if serialize_dirty_buffers && preserve_contents {
                let contents = snapshot.text();
                let language = snapshot.language().and_then(|language| {
                    if content_language_detection_enabled && *language == *PLAIN_TEXT {
                        None
                    } else {
                        Some(language.name().to_string())
                    }
                });
                (Some(contents), language)
            } else {
                (None, None)
            };

            let editor = SerializedEditor {
                abs_path,
                contents,
                language,
                mtime,
                recovered_from,
                shared_buffer,
                deleted_file,
                text_format,
            };
            log::debug!("Serializing editor {item_id:?} in workspace {workspace_id:?}");
            db.save_serialized_editor(item_id, workspace_id, editor)
                .await
                .context("failed to save serialized editor")
        }))
    }

    fn should_serialize(&self, event: &Self::Event) -> bool {
        self.should_serialize_buffer()
            && matches!(
                event,
                EditorEvent::Saved
                    | EditorEvent::DirtyChanged
                    | EditorEvent::BufferEdited
                    | EditorEvent::FileHandleChanged
            )
    }
}

#[derive(Debug, Default)]
struct EditorRestorationData {
    entries: HashMap<PathBuf, RestorationData>,
}

#[derive(Default, Debug)]
pub struct RestorationData {
    pub scroll_position: (BufferRow, gpui::Point<ScrollOffset>),
    pub folds: Vec<Range<Point>>,
    pub selections: Vec<Range<Point>>,
}

impl ProjectItem for Editor {
    type Item = Buffer;

    fn project_item_kind() -> Option<ProjectItemKind> {
        Some(ProjectItemKind("Editor"))
    }

    fn for_project_item(
        project: Entity<Project>,
        pane: Option<&Pane>,
        buffer: Entity<Buffer>,
        window: &mut Window,
        cx: &mut Context<Self>,
    ) -> Self {
        let mut editor = Self::for_buffer(buffer.clone(), Some(project), window, cx);
        let multibuffer_snapshot = editor.buffer().read(cx).snapshot(cx);

        if let Some(buffer_snapshot) = editor.buffer().read(cx).snapshot(cx).as_singleton()
            && WorkspaceSettings::get(None, cx).restore_on_file_reopen
            && let Some(restoration_data) = Self::project_item_kind()
                .and_then(|kind| pane.as_ref()?.project_item_restoration_data.get(&kind))
                .and_then(|data| data.downcast_ref::<EditorRestorationData>())
                .and_then(|data| {
                    let file = project::File::from_dyn(buffer.read(cx).file())?;
                    data.entries.get(&file.abs_path(cx))
                })
        {
            if !restoration_data.folds.is_empty() {
                editor.fold_ranges(
                    clip_ranges(&restoration_data.folds, buffer_snapshot),
                    false,
                    window,
                    cx,
                );
            }
            if !restoration_data.selections.is_empty() {
                editor.change_selections(SelectionEffects::no_scroll(), window, cx, |s| {
                    s.select_ranges(clip_ranges(&restoration_data.selections, buffer_snapshot));
                });
            }
            let (top_row, offset) = restoration_data.scroll_position;
            let anchor = multibuffer_snapshot.anchor_before(Point::new(top_row, 0));
            editor.set_scroll_anchor(ScrollAnchor { anchor, offset }, window, cx);
        }

        editor
    }

    fn for_broken_project_item(
        abs_path: &Path,
        is_local: bool,
        e: &anyhow::Error,
        window: &mut Window,
        cx: &mut App,
    ) -> Option<InvalidItemView> {
        Some(InvalidItemView::new(abs_path, is_local, e, window, cx))
    }
}

fn clip_ranges<'a>(
    original: impl IntoIterator<Item = &'a Range<Point>> + 'a,
    snapshot: &'a BufferSnapshot,
) -> Vec<Range<Point>> {
    original
        .into_iter()
        .map(|range| {
            snapshot.clip_point(range.start, Bias::Left)
                ..snapshot.clip_point(range.end, Bias::Right)
        })
        .collect()
}

impl EventEmitter<SearchEvent> for Editor {}

impl Editor {
    pub fn update_restoration_data(
        &self,
        cx: &mut Context<Self>,
        write: impl for<'a> FnOnce(&'a mut RestorationData) + 'static,
    ) {
        if self.mode.is_minimap() || !WorkspaceSettings::get(None, cx).restore_on_file_reopen {
            return;
        }

        let editor = cx.entity();
        cx.defer(move |cx| {
            editor.update(cx, |editor, cx| {
                let kind = Editor::project_item_kind()?;
                let pane = editor.workspace()?.read(cx).pane_for(&cx.entity())?;
                let buffer = editor.buffer().read(cx).as_singleton()?;
                let file_abs_path = project::File::from_dyn(buffer.read(cx).file())?.abs_path(cx);
                pane.update(cx, |pane, _| {
                    let data = pane
                        .project_item_restoration_data
                        .entry(kind)
                        .or_insert_with(|| Box::new(EditorRestorationData::default()) as Box<_>);
                    let data = match data.downcast_mut::<EditorRestorationData>() {
                        Some(data) => data,
                        None => {
                            *data = Box::new(EditorRestorationData::default());
                            data.downcast_mut::<EditorRestorationData>()
                                .expect("just written the type downcasted to")
                        }
                    };

                    let data = data.entries.entry(file_abs_path).or_default();
                    write(data);
                    Some(())
                })
            });
        });
    }
}

// Replace-all commonly expands several hits against the same line.
#[derive(Default)]
struct SearchHitContext {
    row: Option<u32>,
    text: String,
}

impl SearchHitContext {
    fn for_hit(
        &mut self,
        snapshot: &MultiBufferSnapshot,
        hit: &Range<Anchor>,
    ) -> (&str, Range<usize>) {
        let start = hit.start.to_point(snapshot);
        let end = hit.end.to_point(snapshot);
        let range = if start.row == end.row {
            if self.row != Some(start.row) {
                self.text.clear();
                self.text.extend(snapshot.text_for_range(
                    Point::new(start.row, 0)
                        ..Point::new(start.row, snapshot.line_len(MultiBufferRow(start.row))),
                ));
                self.row = Some(start.row);
            }
            start.column as usize..end.column as usize
        } else {
            self.row = None;
            self.text.clear();
            self.text.extend(snapshot.text_for_range(start..end));
            0..self.text.len()
        };
        (&self.text, range)
    }
}

impl SearchableItem for Editor {
    type Match = Range<Anchor>;

    fn get_matches(&self, _window: &mut Window, _: &mut App) -> (Vec<Range<Anchor>>, SearchToken) {
        (
            self.background_highlights
                .get(&HighlightKey::BufferSearchHighlights)
                .map_or(Vec::new(), |(_color, ranges)| {
                    ranges.iter().cloned().collect()
                }),
            SearchToken::default(),
        )
    }

    fn clear_matches(&mut self, _: &mut Window, cx: &mut Context<Self>) {
        if self
            .clear_background_highlights(HighlightKey::BufferSearchHighlights, cx)
            .is_some()
        {
            cx.emit(SearchEvent::MatchesInvalidated);
        }
    }

    fn update_matches(
        &mut self,
        matches: &[Range<Anchor>],
        active_match_index: Option<usize>,
        _token: SearchToken,
        _: &mut Window,
        cx: &mut Context<Self>,
    ) {
        let existing_range = self
            .background_highlights
            .get(&HighlightKey::BufferSearchHighlights)
            .map(|(_, range)| range.as_ref());
        let updated = existing_range != Some(matches);
        self.highlight_background(
            HighlightKey::BufferSearchHighlights,
            matches,
            move |index, theme| {
                if active_match_index == Some(*index) {
                    theme.colors().search_active_match_background
                } else {
                    theme.colors().search_match_background
                }
            },
            cx,
        );
        if updated {
            cx.emit(SearchEvent::MatchesInvalidated);
        }
    }

    fn has_filtered_search_ranges(&mut self) -> bool {
        self.has_background_highlights(HighlightKey::SearchWithinRange)
    }

    fn toggle_filtered_search_ranges(
        &mut self,
        enabled: Option<FilteredSearchRange>,
        _: &mut Window,
        cx: &mut Context<Self>,
    ) {
        if self.has_filtered_search_ranges() {
            self.previous_search_ranges = self
                .clear_background_highlights(HighlightKey::SearchWithinRange, cx)
                .map(|(_, ranges)| ranges)
        }

        if let Some(range) = enabled {
            let ranges = self.selections.disjoint_anchor_ranges().collect::<Vec<_>>();

            if ranges.iter().any(|s| s.start != s.end) {
                self.set_search_within_ranges(&ranges, cx);
            } else if let Some(previous_search_ranges) = self.previous_search_ranges.take()
                && range != FilteredSearchRange::Selection
            {
                self.set_search_within_ranges(&previous_search_ranges, cx);
            }
        }
    }

    fn supported_options(&self) -> SearchOptions {
        if self.in_project_search {
            SearchOptions {
                case: true,
                word: true,
                regex: true,
                replacement: false,
                selection: false,
                select_all: true,
                find_in_results: true,
            }
        } else {
            SearchOptions {
                case: true,
                word: true,
                regex: true,
                replacement: true,
                selection: true,
                select_all: true,
                find_in_results: false,
            }
        }
    }

    fn query_suggestion(
        &mut self,
        seed_query_override: Option<SeedQuerySetting>,
        window: &mut Window,
        cx: &mut Context<Self>,
    ) -> String {
        let setting = seed_query_override
            .unwrap_or_else(|| EditorSettings::get_global(cx).seed_search_query_from_cursor);
        let snapshot = self.snapshot(window, cx);
        let selection = self.selections.newest_adjusted(&snapshot.display_snapshot);
        let buffer_snapshot = snapshot.buffer_snapshot();

        match setting {
            SeedQuerySetting::Never => String::new(),
            SeedQuerySetting::Selection | SeedQuerySetting::Always if !selection.is_empty() => {
                buffer_snapshot
                    .text_for_range(selection.start..selection.end)
                    .collect()
            }
            SeedQuerySetting::Selection => String::new(),
            SeedQuerySetting::Always => {
                let (range, kind) = buffer_snapshot
                    .surrounding_word(selection.start, Some(CharScopeContext::Completion));
                if kind == Some(CharKind::Word) {
                    let text: String = buffer_snapshot.text_for_range(range).collect();
                    if !text.trim().is_empty() {
                        return text;
                    }
                }
                String::new()
            }
        }
    }

    fn activate_match(
        &mut self,
        index: usize,
        matches: &[Range<Anchor>],
        _token: SearchToken,
        window: &mut Window,
        cx: &mut Context<Self>,
    ) {
        self.unfold_ranges(&[matches[index].clone()], false, true, cx);
        let range = self.range_for_match(&matches[index]);
        let autoscroll = if EditorSettings::get_global(cx).search.center_on_match {
            Autoscroll::center()
        } else {
            Autoscroll::fit()
        };
        self.change_selections(
            SelectionEffects::scroll(autoscroll).from_search(true),
            window,
            cx,
            |s| {
                s.select_ranges([range]);
            },
        )
    }

    fn select_matches(
        &mut self,
        matches: &[Self::Match],
        _token: SearchToken,
        window: &mut Window,
        cx: &mut Context<Self>,
    ) {
        self.unfold_ranges(matches, false, false, cx);
        self.change_selections(SelectionEffects::no_scroll(), window, cx, |s| {
            s.select_ranges(matches.iter().cloned())
        });
    }
    fn replace(
        &mut self,
        identifier: &Self::Match,
        query: &SearchQuery,
        _token: SearchToken,
        window: &mut Window,
        cx: &mut Context<Self>,
    ) {
        let replacement = if query.replacement_requires_context() {
            let snapshot = self.buffer.read(cx).snapshot(cx);
            let mut context = SearchHitContext::default();
            let (line, hit) = context.for_hit(&snapshot, identifier);
            query
                .replacement_for(line, hit)
                .map(|replacement| Arc::<str>::from(&*replacement))
        } else {
            query.replacement().map(Arc::<str>::from)
        };

        if let Some(replacement) = replacement {
            self.transact(window, cx, |this, _, cx| {
                this.edit([(identifier.clone(), replacement)], cx);
            });
        }
    }
    fn replace_all(
        &mut self,
        matches: &mut dyn Iterator<Item = &Self::Match>,
        query: &SearchQuery,
        _token: SearchToken,
        window: &mut Window,
        cx: &mut Context<Self>,
    ) {
        let snapshot = self.buffer.read(cx).snapshot(cx);
        let mut edits = vec![];

        // A regex might have replacement variables so we cannot apply
        // the same replacement to all matches
        if query.replacement_requires_context() {
            let mut context = SearchHitContext::default();
            edits = matches
                .filter_map(|m| {
                    let (line, hit) = context.for_hit(&snapshot, m);
                    query
                        .replacement_for(line, hit)
                        .map(|replacement| (m.clone(), Arc::from(&*replacement)))
                })
                .collect();
        } else if let Some(replacement) = query.replacement().map(Arc::<str>::from) {
            edits = matches.map(|m| (m.clone(), replacement.clone())).collect();
        }

        if !edits.is_empty() {
            self.transact(window, cx, |this, _, cx| {
                this.edit(edits, cx);
            });
        }
    }

    /// Takes the current cursor position and finds the next match in the
    /// provided `direction`, the provide `count` number of times, wrapping
    /// around if necessary.
    fn match_index_for_direction(
        &mut self,
        matches: &[Range<Anchor>],
        current_index: usize,
        direction: Direction,
        count: usize,
        _token: SearchToken,
        _: &mut Window,
        cx: &mut Context<Self>,
    ) -> usize {
        if count == 0 {
            return current_index;
        }

        let cursor = if self.selections.disjoint_anchors_arc().len() == 1 {
            self.selections.newest_anchor().head()
        } else {
            matches[current_index].start
        };

        let buffer = self.buffer().read(cx).snapshot(cx);
        let new_idx = match direction {
            Direction::Next => matches
                .iter()
                .position(|m| m.start.cmp(&cursor, &buffer).is_gt())
                .unwrap_or(0),
            Direction::Prev => matches
                .iter()
                .rposition(|m| m.end.cmp(&cursor, &buffer).is_lt())
                .unwrap_or(matches.len() - 1),
        } as isize;

        // We'll use `count - 1` because the first jump to the next or previous
        // match already happens in the scenario above, when we find the next or
        // previous match starting from the cursor position.
        let count = count.saturating_sub(1);
        let count = match direction {
            Direction::Prev => -(count as isize),
            Direction::Next => count as isize,
        };

        let new_idx = (new_idx + count) % matches.len() as isize;
        let new_idx = if new_idx.is_negative() {
            // We need a `matches.len() - 1` here in case `next_idx` has now been
            // set to `0`, otherwise we'd end up returning `matches.len()`, which
            // would be out of bounds.
            new_idx + (matches.len() - 1) as isize
        } else {
            new_idx
        };
        assert!(new_idx < matches.len() as isize);
        new_idx as usize
    }

    fn find_matches(
        &mut self,
        query: Arc<project::search::SearchQuery>,
        _: &mut Window,
        cx: &mut Context<Self>,
    ) -> Task<Vec<Range<Anchor>>> {
        let buffer = self.buffer().read(cx).snapshot(cx);
        let search_within_ranges = self
            .background_highlights
            .get(&HighlightKey::SearchWithinRange)
            .map_or(vec![], |(_color, ranges)| {
                ranges.iter().cloned().collect::<Vec<_>>()
            });

        let executor = cx.background_executor().clone();
        cx.background_spawn(async move {
            let mut ranges = Vec::new();

            let search_within_ranges = if search_within_ranges.is_empty() {
                vec![buffer.anchor_before(MultiBufferOffset(0))..buffer.anchor_after(buffer.len())]
            } else {
                search_within_ranges
            };
            let num_cpus = executor.num_cpus();
            for range in search_within_ranges {
                for (search_buffer, search_range, deleted_hunk_anchor) in
                    buffer.range_to_buffer_ranges_with_deleted_hunks(range)
                {
                    let query = query.clone();

                    let mut results = Vec::new();
                    executor
                        .scoped(|scope| {
                            for search_range in chunk_search_range(
                                search_buffer.text.clone(),
                                &query,
                                num_cpus as u32,
                                search_range,
                            ) {
                                let query = query.clone();
                                let buffer = buffer.clone();

                                let (tx, rx) = oneshot::channel();
                                results.push(rx);
                                scope.spawn(async move {
                                    let chunk_result = query
                                        .search(
                                            search_buffer,
                                            Some(search_range.start..search_range.end),
                                        )
                                        .await
                                        .into_iter()
                                        .filter_map(|match_range| {
                                            if let Some(deleted_hunk_anchor) = deleted_hunk_anchor {
                                                let start = search_buffer.anchor_after(
                                                    search_range.start + match_range.start,
                                                );
                                                let end = search_buffer.anchor_before(
                                                    search_range.start + match_range.end,
                                                );
                                                Some(
                                                    deleted_hunk_anchor.with_diff_base_anchor(start)
                                                        ..deleted_hunk_anchor
                                                            .with_diff_base_anchor(end),
                                                )
                                            } else {
                                                let start = search_buffer.anchor_after(
                                                    search_range.start + match_range.start,
                                                );
                                                let end = search_buffer.anchor_before(
                                                    search_range.start + match_range.end,
                                                );
                                                buffer.anchor_range_in_buffer(start..end)
                                            }
                                        })
                                        .collect::<Vec<_>>();
                                    _ = tx.send(chunk_result);
                                });
                            }
                        })
                        .await;

                    for rx in results {
                        if let Ok(results) = rx.await {
                            ranges.extend(results);
                        }
                    }
                }
            }

            ranges
        })
    }

    fn active_match_index(
        &mut self,
        direction: Direction,
        matches: &[Range<Anchor>],
        _token: SearchToken,
        _: &mut Window,
        cx: &mut Context<Self>,
    ) -> Option<usize> {
        active_match_index(
            direction,
            matches,
            &self.selections.newest_anchor().head(),
            &self.buffer().read(cx).snapshot(cx),
        )
    }

    fn search_bar_visibility_changed(&mut self, _: bool, _: &mut Window, _: &mut Context<Self>) {
        self.expect_bounds_change = self.last_bounds;
    }

    fn set_select_search_options(
        &mut self,
        select_search_options: Option<SelectSearchOptions>,
        _cx: &mut Context<Self>,
    ) {
        if self.select_next_options == select_search_options {
            return;
        }

        self.select_next_options = select_search_options;
        self.select_next_state = None;
        self.select_prev_state = None;
    }
}

pub fn active_match_index(
    direction: Direction,
    ranges: &[Range<Anchor>],
    cursor: &Anchor,
    buffer: &MultiBufferSnapshot,
) -> Option<usize> {
    if ranges.is_empty() {
        None
    } else {
        let r = ranges.binary_search_by(|probe| {
            if probe.end.cmp(cursor, buffer).is_lt() {
                Ordering::Less
            } else if probe.start.cmp(cursor, buffer).is_gt() {
                Ordering::Greater
            } else {
                Ordering::Equal
            }
        });
        match direction {
            Direction::Prev => match r {
                Ok(i) => Some(i),
                Err(i) => Some(i.saturating_sub(1)),
            },
            Direction::Next => match r {
                Ok(i) | Err(i) => Some(cmp::min(i, ranges.len() - 1)),
            },
        }
    }
}

/// Opens a path-like target (e.g. `items.rs:100:5`) in the workspace, moving the cursor
/// to the one-based row/column if present. Returns whether the target was opened.
pub async fn open_resolved_target(
    workspace: &WeakEntity<Workspace>,
    open_target: &workspace::path_link::OpenTarget,
    cx: &mut AsyncWindowContext,
) -> Result<bool> {
    let path_to_open = open_target.path();
    let mut opened_items = workspace
        .update_in(cx, |workspace, window, cx| {
            workspace.open_paths(
                vec![path_to_open.path.clone()],
                workspace::OpenOptions {
                    visible: Some(workspace::OpenVisible::OnlyDirectories),
                    ..Default::default()
                },
                None,
                window,
                cx,
            )
        })
        .context("workspace update")?
        .await;
    if opened_items.len() != 1 {
        debug_panic!(
            "Received {} items for one path {path_to_open:?}",
            opened_items.len(),
        );
    }
    let Some(opened_item) = opened_items.pop() else {
        return Ok(false);
    };

    if open_target.is_file() {
        let Some(opened_item) = opened_item else {
            return Ok(false);
        };
        let opened_item =
            opened_item.with_context(|| format!("opening {:?}", path_to_open.path))?;
        if let Some(row) = path_to_open.row
            && let Some(editor) = opened_item.downcast::<Editor>()
        {
            let column = path_to_open.column.unwrap_or(0);
            editor
                .downgrade()
                .update_in(cx, |editor, window, cx| {
                    if let Some(buffer) = editor.buffer().read(cx).as_singleton() {
                        let point = buffer.read(cx).snapshot().point_from_external_input(
                            row.saturating_sub(1),
                            column.saturating_sub(1),
                        );
                        editor.go_to_singleton_buffer_point(point, window, cx);
                    }
                })
                .log_err();
        }
        Ok(true)
    } else if open_target.is_dir() {
        workspace.update(cx, |workspace, cx| {
            workspace.project().update(cx, |_, cx| {
                cx.emit(project::Event::ActivateProjectPanel);
            })
        })?;
        Ok(true)
    } else {
        Ok(false)
    }
}

pub fn entry_label_color(selected: bool) -> Color {
    if selected {
        Color::Default
    } else {
        Color::Muted
    }
}

pub fn entry_diagnostic_aware_icon_name_and_color(
    diagnostic_severity: Option<DiagnosticSeverity>,
) -> Option<(IconName, Color)> {
    match diagnostic_severity {
        Some(DiagnosticSeverity::ERROR) => Some((IconName::Close, Color::Error)),
        Some(DiagnosticSeverity::WARNING) => Some((IconName::Triangle, Color::Warning)),
        _ => None,
    }
}

pub fn entry_diagnostic_aware_icon_decoration_and_color(
    diagnostic_severity: Option<DiagnosticSeverity>,
) -> Option<(IconDecorationKind, Color)> {
    match diagnostic_severity {
        Some(DiagnosticSeverity::ERROR) => Some((IconDecorationKind::X, Color::Error)),
        Some(DiagnosticSeverity::WARNING) => Some((IconDecorationKind::Triangle, Color::Warning)),
        _ => None,
    }
}

pub fn entry_git_aware_label_color(git_status: GitSummary, ignored: bool, selected: bool) -> Color {
    let tracked = git_status.index + git_status.worktree;
    if git_status.conflict > 0 {
        Color::Conflict
    } else if tracked.deleted > 0 {
        Color::Deleted
    } else if tracked.modified > 0 {
        Color::Modified
    } else if tracked.added > 0 || git_status.untracked > 0 {
        Color::Created
    } else if ignored {
        Color::Ignored
    } else {
        entry_label_color(selected)
    }
}

fn tab_title<'a>(editor: &Editor, cx: &'a App) -> Cow<'a, str> {
    match recovered_source_path(editor, cx).and_then(|path| path.file_name()) {
        Some(file_name) => Cow::Owned(format!("{} (recovered)", file_name.to_string_lossy())),
        None => editor.title(cx),
    }
}

fn recovered_source_path<'a>(editor: &'a Editor, cx: &App) -> Option<&'a Path> {
    let buffer = editor.buffer.read(cx).as_singleton()?;
    editor
        .recovered_from
        .as_deref()
        .filter(|_| buffer.read(cx).file().is_none())
}

fn path_for_buffer<'a>(
    buffer: &Entity<MultiBuffer>,
    height: usize,
    include_filename: bool,
    cx: &'a App,
) -> Option<Cow<'a, str>> {
    let file = buffer.read(cx).as_singleton()?.read(cx).file()?;
    path_for_file(file, height, include_filename, cx)
}

fn path_for_file<'a>(
    file: &'a Arc<dyn language::File>,
    mut height: usize,
    include_filename: bool,
    cx: &'a App,
) -> Option<Cow<'a, str>> {
    if project::File::from_dyn(Some(file)).is_none() {
        return None;
    }

    let file = file.as_ref();
    // Ensure we always render at least the filename.
    height += 1;

    let mut prefix = file.path().as_ref();
    while height > 0 {
        if let Some(parent) = prefix.parent() {
            prefix = parent;
            height -= 1;
        } else {
            break;
        }
    }

    // The full_path method allocates, so avoid calling it if height is zero.
    if height > 0 {
        let mut full_path = file.full_path(cx);
        if !include_filename {
            if !full_path.pop() {
                return None;
            }
        }
        Some(full_path.to_string_lossy().into_owned().into())
    } else {
        let mut path = file.path().strip_prefix(prefix).ok()?;
        if !include_filename {
            path = path.parent()?;
        }
        Some(path.display(file.path_style(cx)))
    }
}

struct SavedFileBuffer {
    contents: Option<String>,
    mtime: Option<MTime>,
    deleted_file: Option<DeletedFile>,
    text_format: Option<TextFormat>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum LiveDiskState {
    Present,
    New,
    Deleted,
}

#[derive(Clone, Copy, Debug)]
struct LiveFileBuffer {
    disk_state: LiveDiskState,
    has_unsaved_edits: bool,
    has_saved_snapshot: bool,
    has_saved_encoding: bool,
}

impl LiveFileBuffer {
    fn new(buffer: &Buffer, saved: &SavedFileBuffer) -> Self {
        let disk_state = match buffer.file().map(|file| file.disk_state()) {
            Some(DiskState::New) => LiveDiskState::New,
            Some(DiskState::Deleted) => LiveDiskState::Deleted,
            Some(DiskState::Present { .. } | DiskState::Historic { .. }) | None => {
                LiveDiskState::Present
            }
        };
        Self {
            disk_state,
            has_unsaved_edits: buffer.has_unsaved_edits(),
            has_saved_snapshot: saved.contents.as_deref().is_some_and(|contents| {
                holds_snapshot(buffer, contents, saved.text_format.as_ref())
            }),
            has_saved_encoding: saved
                .text_format
                .is_none_or(|text_format| buffer.encoding() == text_format.encoding),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum FileBufferRestoration {
    UseLive,
    Recover,
    Overwrite,
    RestoreDeleted,
    Redecode,
}

fn plan_file_buffer_restoration(
    saved: &SavedFileBuffer,
    live: LiveFileBuffer,
) -> FileBufferRestoration {
    let has_contents_to_recover = saved.contents.is_some() && !live.has_saved_snapshot;
    if live.has_unsaved_edits {
        return if has_contents_to_recover {
            FileBufferRestoration::Recover
        } else {
            FileBufferRestoration::UseLive
        };
    }
    match (saved.deleted_file, live.disk_state) {
        (Some(_), LiveDiskState::New) => FileBufferRestoration::RestoreDeleted,
        (Some(_), LiveDiskState::Deleted) => {
            if has_contents_to_recover {
                FileBufferRestoration::Recover
            } else {
                FileBufferRestoration::UseLive
            }
        }
        (Some(deleted_file), LiveDiskState::Present) if !deleted_file.dirty => {
            if live.has_saved_encoding {
                FileBufferRestoration::UseLive
            } else {
                FileBufferRestoration::Redecode
            }
        }
        _ if saved.contents.is_some() => FileBufferRestoration::Overwrite,
        _ => FileBufferRestoration::UseLive,
    }
}

async fn restore_file_buffer(
    project: &Entity<Project>,
    buffer: Entity<Buffer>,
    abs_path: &Path,
    saved: SavedFileBuffer,
    cx: &mut AsyncWindowContext,
) -> Result<(Entity<Buffer>, Option<PathBuf>)> {
    let plan = buffer.read_with(cx, |buffer, _| {
        plan_file_buffer_restoration(&saved, LiveFileBuffer::new(buffer, &saved))
    });
    let SavedFileBuffer {
        contents,
        mtime,
        deleted_file,
        text_format,
    } = saved;
    match plan {
        FileBufferRestoration::UseLive => {}
        FileBufferRestoration::Recover => {
            let language = buffer.read_with(cx, |buffer, _| buffer.language().cloned());
            let recovered = recovered_buffer(
                project,
                abs_path,
                language,
                contents.unwrap_or_default(),
                text_format,
                cx,
            )
            .await?;
            return Ok((recovered, Some(abs_path.to_path_buf())));
        }
        FileBufferRestoration::Overwrite => {
            buffer.update(cx, |buffer, cx| {
                restore_serialized_buffer_contents(
                    buffer,
                    contents.unwrap_or_default(),
                    mtime,
                    text_format,
                    cx,
                );
                if !buffer.is_dirty() {
                    buffer.set_conflict();
                }
            });
        }
        FileBufferRestoration::RestoreDeleted => {
            project.update(cx, |project, cx| {
                project.buffer_store().update(cx, |buffer_store, cx| {
                    buffer_store.mark_file_deleted(&buffer, cx)
                })
            });
            buffer.update(cx, |buffer, cx| {
                restore_serialized_buffer_contents(
                    buffer,
                    contents.unwrap_or_default(),
                    mtime,
                    text_format,
                    cx,
                );
                let Some(deleted_file) = deleted_file else {
                    return;
                };
                if !deleted_file.dirty {
                    buffer.did_reload(buffer.version(), buffer.line_ending(), mtime, cx);
                }
                if deleted_file.read_only && buffer.capability() == Capability::ReadWrite {
                    buffer.set_capability(Capability::Read, cx);
                }
            });
        }
        FileBufferRestoration::Redecode => {
            if let Some(text_format) = text_format {
                let reload = buffer.update(cx, |buffer, cx| {
                    buffer.reload_with_encoding(text_format.encoding, cx)
                });
                if reload.await.is_err() {
                    log::warn!(
                        "Failed to reload {abs_path:?} with its saved encoding {}",
                        text_format.encoding.name()
                    );
                }
            }
        }
    }
    Ok((buffer, None))
}

#[derive(Clone, PartialEq, Eq, Hash)]
enum RestoredBufferKey {
    Recovery {
        project: EntityId,
        abs_path: PathBuf,
        contents: String,
        text_format: Option<TextFormat>,
    },
    Shared {
        project: EntityId,
        workspace_id: workspace::WorkspaceId,
        buffer: String,
        contents: Option<String>,
        text_format: Option<TextFormat>,
    },
}

impl RestoredBufferKey {
    fn reusable(&self, buffer: &Buffer) -> bool {
        match self {
            Self::Recovery {
                contents,
                text_format,
                ..
            } => buffer.file().is_none() && holds_snapshot(buffer, contents, text_format.as_ref()),
            Self::Shared { .. } => true,
        }
    }
}

fn holds_snapshot(buffer: &Buffer, contents: &str, text_format: Option<&TextFormat>) -> bool {
    buffer.text() == contents
        && text_format.is_none_or(|text_format| TextFormat::of(buffer) == *text_format)
}

#[derive(Default)]
struct RestoredBuffers(HashMap<RestoredBufferKey, RestoredBuffer>);

impl Global for RestoredBuffers {}

#[derive(Clone)]
enum RestoredBuffer {
    Pending(Shared<Task<Result<Entity<Buffer>, Arc<anyhow::Error>>>>),
    Ready(WeakEntity<Buffer>),
}

async fn saved_language(
    project: &Entity<Project>,
    language_name: Option<String>,
    cx: &mut AsyncWindowContext,
) -> Option<Arc<Language>> {
    let language_name = language_name?;
    let language_registry = project.read_with(cx, |project, _| project.languages().clone());
    // We don't fail here, because we'd rather not set the language if the name changed
    // than fail to restore the buffer.
    language_registry
        .language_for_name(&language_name)
        .await
        .ok()
}

async fn recovered_buffer(
    project: &Entity<Project>,
    abs_path: &Path,
    language: Option<Arc<Language>>,
    contents: String,
    text_format: Option<TextFormat>,
    cx: &mut AsyncWindowContext,
) -> Result<Entity<Buffer>> {
    let key = RestoredBufferKey::Recovery {
        project: project.entity_id(),
        abs_path: abs_path.to_path_buf(),
        contents: contents.clone(),
        text_format,
    };
    let detect_language = language.is_none();
    restored_buffer(
        project,
        Some(key),
        language,
        detect_language,
        Some(contents),
        text_format,
        cx,
    )
    .await
    .context("Failed to create a buffer for the restored contents")
}

async fn restored_buffer(
    project: &Entity<Project>,
    key: Option<RestoredBufferKey>,
    language: Option<Arc<Language>>,
    detect_language: bool,
    contents: Option<String>,
    text_format: Option<TextFormat>,
    cx: &mut AsyncWindowContext,
) -> Result<Entity<Buffer>> {
    let create = |cx: &mut App| {
        new_buffer(
            project,
            language,
            detect_language,
            contents,
            text_format,
            cx,
        )
    };
    let Some(key) = key else {
        return cx.update(|_, cx| create(cx))?.await;
    };
    let earlier = cx.update(|_, cx| cx.try_global::<RestoredBuffers>()?.0.get(&key).cloned())?;
    let earlier = match earlier {
        Some(RestoredBuffer::Ready(buffer)) => buffer.upgrade(),
        Some(RestoredBuffer::Pending(restoration)) => restoration.await.ok(),
        None => None,
    };
    if let Some(earlier) = earlier
        && earlier.read_with(cx, |buffer, _| key.reusable(buffer))
    {
        return Ok(earlier);
    }

    let restoration = cx.update(|_, cx| {
        let create = create(cx);
        let restoration = cx
            .spawn({
                let key = key.clone();
                async move |cx| {
                    let restored = create.await.map_err(Arc::new);
                    cx.update(|cx| finish_buffer_restoration(key, &restored, cx));
                    restored
                }
            })
            .shared();
        cx.default_global::<RestoredBuffers>()
            .0
            .insert(key, RestoredBuffer::Pending(restoration.clone()));
        restoration
    })?;
    restoration.await.map_err(|error| anyhow!("{error:#}"))
}

fn finish_buffer_restoration(
    key: RestoredBufferKey,
    restored: &Result<Entity<Buffer>, Arc<anyhow::Error>>,
    cx: &mut App,
) {
    let restored_buffers = &mut cx.default_global::<RestoredBuffers>().0;
    let Ok(buffer) = restored else {
        restored_buffers.remove(&key);
        return;
    };
    restored_buffers.insert(key.clone(), RestoredBuffer::Ready(buffer.downgrade()));
    let buffer_id = buffer.entity_id();
    cx.observe_release(buffer, move |_, cx| {
        let restored_buffers = &mut cx.default_global::<RestoredBuffers>().0;
        if let Some(RestoredBuffer::Ready(released)) = restored_buffers.get(&key)
            && released.entity_id() == buffer_id
        {
            restored_buffers.remove(&key);
        }
    })
    .detach();
}

fn restoration_failure(abs_path: &Path) -> RestorationFailure {
    RestorationFailure {
        label: SharedString::from(
            abs_path
                .file_name()
                .unwrap_or(abs_path.as_os_str())
                .to_string_lossy()
                .into_owned(),
        ),
        tooltip: Some(SharedString::from(abs_path.to_string_lossy().into_owned())),
    }
}

fn new_buffer(
    project: &Entity<Project>,
    language: Option<Arc<Language>>,
    detect_language: bool,
    contents: Option<String>,
    text_format: Option<TextFormat>,
    cx: &mut App,
) -> Task<Result<Entity<Buffer>>> {
    let language_registry = project.read(cx).languages().clone();
    let create_buffer = project.update(cx, |project, cx| project.create_buffer(language, true, cx));
    cx.spawn(async move |cx| {
        let buffer = create_buffer.await?;
        buffer.update(cx, |buffer, cx| {
            if detect_language {
                buffer.set_content_language_detection_enabled(true);
            }
            // Then set the text so that the dirty bit is set correctly
            if let Some(contents) = contents {
                buffer.set_language_registry(language_registry);
                restore_serialized_buffer_contents(buffer, contents, None, text_format, cx);
            }
        });
        Ok(buffer)
    })
}

/// Restores serialized buffer contents by overwriting the buffer with saved text.
/// This is somewhat wasteful since we load the whole buffer from disk then overwrite it,
/// but keeps implementation simple as we don't need to persist all metadata from loading
/// (git diff base, etc.).
fn restore_serialized_buffer_contents(
    buffer: &mut Buffer,
    contents: String,
    mtime: Option<MTime>,
    text_format: Option<TextFormat>,
    cx: &mut Context<Buffer>,
) {
    // If we did restore an mtime, store it on the buffer so that
    // the next edit will mark the buffer as dirty/conflicted.
    if mtime.is_some() {
        buffer.did_reload(buffer.version(), buffer.line_ending(), mtime, cx);
    }
    buffer.set_text(contents, cx);
    if let Some(entry) = buffer.peek_undo_stack() {
        buffer.forget_transaction(entry.transaction_id());
    }
    if let Some(text_format) = text_format {
        buffer.set_line_ending(text_format.line_ending, cx);
        buffer.set_encoding(text_format.encoding);
        buffer.set_has_bom(text_format.has_bom);
    }
}

fn serialize_path_key(path_key: &PathKey) -> proto::PathKey {
    proto::PathKey {
        sort_prefix: path_key.sort_prefix,
        path: path_key.path.as_unix_str().to_owned(),
    }
}

fn deserialize_path_key(path_key: proto::PathKey) -> Option<PathKey> {
    Some(PathKey {
        sort_prefix: path_key.sort_prefix,
        path: RelPath::from_unix_str(&path_key.path).ok()?.into(),
    })
}

fn chunk_search_range(
    buffer: BufferSnapshot,
    query: &SearchQuery,
    num_cpus: u32,
    initial_range: Range<BufferOffset>,
) -> Box<dyn Iterator<Item = Range<usize>> + 'static> {
    let range = initial_range.to_offset(&buffer);
    if range.is_empty() {
        return Box::new(std::iter::empty());
    }

    let summary: TextSummary = buffer.text_summary_for_range(initial_range);
    let num_chunks = if !query.is_regex() && !query.as_str().contains('\n') {
        NonZeroU32::new(summary.lines.row.saturating_add(1).min(num_cpus.max(1)))
    } else {
        NonZeroU32::new(1)
    };

    let Some(num_chunks) = num_chunks else {
        return Box::new(std::iter::empty());
    };

    let mut chunk_start = range.start;
    let rope = buffer.as_rope().clone();
    let range_end = range.end;
    let average_chunk_length = summary.len.div_ceil(num_chunks.get() as usize);
    Box::new(std::iter::from_fn(move || {
        if chunk_start >= range_end {
            return None;
        }
        let candidate_position = chunk_start + average_chunk_length;
        let adjusted = rope.ceil_char_boundary(candidate_position);
        let mut as_point = rope.offset_to_point(adjusted);
        as_point.row += 1;
        as_point.column = 0;
        let end_offset = buffer.point_to_offset(as_point).min(range_end);
        let ret = chunk_start..end_offset;
        chunk_start = end_offset;
        Some(ret)
    }))
}

/// Decides what to format based on the `format_on_save` settings of the saved buffers.
///
/// In the modifications modes, only lines with unstaged changes are formatted.
/// When no git diff is available for a buffer, `modifications` skips formatting while `modifications_if_available`
/// falls back to formatting entire buffers.
/// When a diff is available but empty, nothing is formatted in either mode.
fn compute_format_target(
    buffers: &HashSet<Entity<Buffer>>,
    trigger: FormatTrigger,
    multi_buffer: &Entity<MultiBuffer>,
    git_store: &Entity<GitStore>,
    cx: &App,
) -> Option<FormatTarget> {
    if trigger == FormatTrigger::Manual {
        return Some(FormatTarget::Buffers(buffers.clone()));
    }

    let multi_buffer_snapshot = multi_buffer.read(cx).snapshot(cx);
    let git_store = git_store.read(cx);

    let mut fall_back_to_full_format = false;
    let mut modified_ranges: Vec<Range<Point>> = Vec::new();

    for buffer_entity in buffers.iter() {
        let buffer = buffer_entity.read(cx);
        let settings = LanguageSettings::for_buffer(buffer, cx);
        match settings.format_on_save {
            FormatOnSave::On | FormatOnSave::Off => {
                return Some(FormatTarget::Buffers(buffers.clone()));
            }
            FormatOnSave::Modifications | FormatOnSave::ModificationsIfAvailable => {}
        }

        let Some(diff_snapshot) = git_store
            .get_unstaged_diff(buffer.remote_id(), cx)
            .map(|diff| diff.read(cx).snapshot(cx))
        else {
            if settings.format_on_save == FormatOnSave::ModificationsIfAvailable {
                fall_back_to_full_format = true;
            }
            continue;
        };

        let anchor_ranges = compute_modified_ranges(&buffer.snapshot(), &diff_snapshot);
        let flat_anchors = anchor_ranges
            .iter()
            .flat_map(|range| [range.start, range.end])
            .collect::<Vec<_>>();
        let multi_buffer_anchors =
            multi_buffer_snapshot.text_anchors_to_visible_anchors(flat_anchors);
        for pair in multi_buffer_anchors.chunks_exact(2) {
            let (Some(start), Some(end)) = (&pair[0], &pair[1]) else {
                continue;
            };
            modified_ranges
                .push(start.to_point(&multi_buffer_snapshot)..end.to_point(&multi_buffer_snapshot));
        }
    }

    if fall_back_to_full_format {
        Some(FormatTarget::Buffers(buffers.clone()))
    } else if modified_ranges.is_empty() {
        None
    } else {
        Some(FormatTarget::Ranges(modified_ranges))
    }
}

/// Computes the buffer ranges that have unstaged changes, expanded to full lines and
/// with adjacent hunks merged, for use with format-on-save. An empty result means the
/// buffer has no formatable modifications.
fn compute_modified_ranges(
    buffer_snapshot: &language::BufferSnapshot,
    diff_snapshot: &buffer_diff::BufferDiffSnapshot,
) -> Vec<Range<text::Anchor>> {
    let mut merged: Vec<Range<text::Anchor>> = Vec::new();
    for hunk in diff_snapshot.hunks(buffer_snapshot) {
        let range = hunk.buffer_range;
        if range.start.cmp(&range.end, buffer_snapshot).is_eq() {
            // Deletion-only hunks produce no buffer content to format.
            continue;
        }
        let start_point = range.start.to_point(buffer_snapshot);
        let end_point = range.end.to_point(buffer_snapshot);
        let start_row = start_point.row;
        let end_row = if end_point.column == 0 && end_point.row > start_point.row {
            end_point.row - 1
        } else {
            end_point.row
        };
        let line_start = text::Point::new(start_row, 0);
        let line_end = text::Point::new(end_row, buffer_snapshot.line_len(end_row));
        let expanded =
            buffer_snapshot.anchor_before(line_start)..buffer_snapshot.anchor_after(line_end);

        if let Some(last) = merged.last_mut() {
            let last_end_point = last.end.to_point(buffer_snapshot);
            if start_row <= last_end_point.row + 1 {
                if expanded.end.to_point(buffer_snapshot) > last_end_point {
                    last.end = expanded.end;
                }
                continue;
            }
        }
        merged.push(expanded);
    }
    merged
}

pub(crate) fn handle_lsp_show_document(
    workspace: &mut Workspace,
    request: &LanguageServerShowDocumentRequest,
    window: &mut Window,
    cx: &mut Context<Workspace>,
) -> Task<()> {
    let request = request.clone();
    if request.external {
        cx.open_url(request.uri.as_str());
        request.respond(true);
        return Task::ready(());
    }
    let Ok(abs_path) = request.uri.to_file_path_ext(workspace.path_style(cx)) else {
        log::error!(
            "language server requested to show document with unsupported uri {}",
            request.uri.as_str()
        );
        request.respond(false);
        return Task::ready(());
    };
    let open_task = workspace.open_abs_path(
        abs_path,
        OpenOptions {
            visible: Some(OpenVisible::None),
            focus: Some(request.take_focus),
            ..OpenOptions::default()
        },
        window,
        cx,
    );
    cx.spawn_in(window, async move |_, cx| {
        let success = match open_task.await {
            Ok(item) => match item.downcast::<Editor>().zip(request.selection) {
                Some((editor, selection)) => editor
                    .update_in(cx, |editor, window, cx| {
                        let snapshot = editor.buffer().read(cx).snapshot(cx);
                        let range = language::range_from_lsp(selection);
                        let start = snapshot.point_utf16_to_offset(
                            snapshot.clip_point_utf16(range.start, Bias::Left),
                        );
                        let end = snapshot.point_utf16_to_offset(
                            snapshot.clip_point_utf16(range.end, Bias::Left),
                        );
                        editor.change_selections(
                            SelectionEffects::scroll(Autoscroll::center()),
                            window,
                            cx,
                            |selections| selections.select_ranges([start..end]),
                        );
                    })
                    .is_ok(),
                None => true,
            },
            Err(error) => {
                log::error!("failed to show document for a language server: {error:#}");
                false
            }
        };
        request.respond(success);
    })
}

#[cfg(test)]
mod tests {
    use crate::editor_tests::init_test;
    use fs::Fs;
    use workspace::MultiWorkspace;

    use super::*;
    use fs::MTime;
    use gpui::{App, VisualTestContext};
    use language::{LanguageName, TestFile};
    use project::FakeFs;
    use serde_json::json;
    use settings::{SettingsStore, SplicingVec};
    use std::path::{Path, PathBuf};
    use text::{LineEnding, ReplicaId};
    use util::{
        path,
        paths::PathWithPosition,
        rel_path::{RelPath, rel_path},
    };
    use workspace::path_link::{OpenTarget, OpenTargetFoundBy};

    #[gpui::test]
    fn test_path_for_file(cx: &mut App) {
        let file: Arc<dyn language::File> = Arc::new(TestFile {
            path: RelPath::empty_arc(),
            root_name: String::new(),
            local_root: None,
        });
        assert_eq!(path_for_file(&file, 0, false, cx), None);
    }

    #[gpui::test]
    fn test_chunk_search_range_multi_line(cx: &mut App) {
        let text = "line one\nline two\nline three\nline four\nline five\nline six\n";
        let buffer = cx.new(|cx| Buffer::local(text, cx));
        let snapshot = buffer.read(cx).snapshot();

        let chunks = chunk_search_range_for_test(&snapshot, "line", 4, 0..text.len());

        assert_chunks_are_contiguous(&chunks, 0..text.len());
        assert!(
            chunks.len() <= 4,
            "got {} chunks, expected <= num_cpus (4)",
            chunks.len()
        );
        for chunk in &chunks {
            let end = chunk.end;
            assert!(
                end == text.len() || text.as_bytes()[end - 1] == b'\n',
                "chunk ending at {end} is not a line boundary",
            );
        }
    }

    #[gpui::test]
    fn test_chunk_search_range_single_line(cx: &mut App) {
        let text = "hello world hello again";
        let buffer = cx.new(|cx| Buffer::local(text, cx));
        let snapshot = buffer.read(cx).snapshot();

        let chunks = chunk_search_range_for_test(&snapshot, "hello", 4, 0..text.len());
        assert_chunks_are_contiguous(&chunks, 0..text.len());
    }

    #[gpui::test]
    fn test_chunk_search_range_empty_range(cx: &mut App) {
        let buffer = cx.new(|cx| Buffer::local("hello world", cx));
        let snapshot = buffer.read(cx).snapshot();

        let chunks = chunk_search_range_for_test(&snapshot, "hello", 4, 5..5);
        assert!(chunks.is_empty());
    }

    #[gpui::test]
    fn test_chunk_search_range_does_not_start_at_zero(cx: &mut App) {
        let line = "abcdefghij\n";
        let text = line.repeat(20);
        let buffer = cx.new(|cx| Buffer::local(text.clone(), cx));
        let snapshot = buffer.read(cx).snapshot();

        let start = line.len() * 7;
        let end = line.len() * 14;
        let chunks = chunk_search_range_for_test(&snapshot, "abc", 4, start..end);

        assert_chunks_are_contiguous(&chunks, start..end);
    }

    fn chunk_search_range_for_test(
        snapshot: &language::BufferSnapshot,
        query: &str,
        num_cpus: u32,
        range: Range<usize>,
    ) -> Vec<Range<usize>> {
        let query = SearchQuery::text(
            query,
            false,
            false,
            false,
            Default::default(),
            Default::default(),
            false,
            None,
        )
        .unwrap();
        chunk_search_range(
            snapshot.text.clone(),
            &query,
            num_cpus,
            BufferOffset(range.start)..BufferOffset(range.end),
        )
        .collect()
    }

    #[track_caller]
    fn assert_chunks_are_contiguous(chunks: &[Range<usize>], expected: Range<usize>) {
        assert!(!chunks.is_empty(), "expected at least one chunk");
        assert_eq!(
            chunks.first().unwrap().start,
            expected.start,
            "first chunk does not start at {}",
            expected.start
        );
        assert_eq!(
            chunks.last().unwrap().end,
            expected.end,
            "last chunk does not end at {}",
            expected.end
        );
        for chunk in chunks {
            assert!(chunk.start < chunk.end, "empty chunk: {:?}", chunk);
        }
        for window in chunks.windows(2) {
            assert_eq!(
                window[0].end, window[1].start,
                "gap or overlap between chunks {:?} and {:?}",
                window[0], window[1],
            );
        }
    }

    #[gpui::test]
    async fn test_suggested_filename_uses_language_extension_for_untitled_buffer(
        cx: &mut gpui::TestAppContext,
    ) {
        init_test(cx, |_| {});

        let buffer = cx.update(|cx| {
            cx.new(|cx| Buffer::local("", cx).with_language(languages::rust_lang(), cx))
        });
        let (editor, cx) =
            cx.add_window_view(|window, cx| Editor::for_buffer(buffer, None, window, cx));

        editor.read_with(cx, |editor, cx| {
            assert_eq!(editor.suggested_filename(cx).as_ref(), "untitled.rs");
        });
    }

    #[gpui::test]
    async fn test_suggested_filename_appends_extension_to_content_title(
        cx: &mut gpui::TestAppContext,
    ) {
        init_test(cx, |_| {});

        let buffer = cx.update(|cx| {
            cx.new(|cx| {
                Buffer::local("sadsdsads\nmore text", cx).with_language(languages::rust_lang(), cx)
            })
        });
        let (editor, cx) =
            cx.add_window_view(|window, cx| Editor::for_buffer(buffer, None, window, cx));

        editor.read_with(cx, |editor, cx| {
            assert_eq!(editor.tab_content_text(0, cx).as_ref(), "sadsdsads");
            assert_eq!(editor.suggested_filename(cx).as_ref(), "sadsdsads.rs");
        });
    }

    #[gpui::test]
    async fn test_suggested_filename_does_not_duplicate_extension(cx: &mut gpui::TestAppContext) {
        init_test(cx, |_| {});

        let buffer = cx.update(|cx| {
            cx.new(|cx| {
                Buffer::local("main.rs\nfn main() {}", cx).with_language(languages::rust_lang(), cx)
            })
        });
        let (editor, cx) =
            cx.add_window_view(|window, cx| Editor::for_buffer(buffer, None, window, cx));

        editor.read_with(cx, |editor, cx| {
            assert_eq!(editor.suggested_filename(cx).as_ref(), "main.rs");
        });
    }

    #[gpui::test]
    async fn test_suggested_filename_keeps_content_title_for_plain_text(
        cx: &mut gpui::TestAppContext,
    ) {
        init_test(cx, |_| {});

        let buffer = cx.update(|cx| {
            cx.new(|cx| {
                Buffer::local("shopping list\nmilk", cx)
                    .with_language(language::PLAIN_TEXT.clone(), cx)
            })
        });
        let (editor, cx) =
            cx.add_window_view(|window, cx| Editor::for_buffer(buffer, None, window, cx));

        editor.read_with(cx, |editor, cx| {
            assert_eq!(editor.suggested_filename(cx).as_ref(), "shopping list");
        });
    }

    #[gpui::test]
    async fn test_suggested_filename_keeps_content_title_without_language(
        cx: &mut gpui::TestAppContext,
    ) {
        init_test(cx, |_| {});

        let buffer = cx.update(|cx| cx.new(|cx| Buffer::local("shopping list\nmilk", cx)));
        let (editor, cx) =
            cx.add_window_view(|window, cx| Editor::for_buffer(buffer, None, window, cx));

        editor.read_with(cx, |editor, cx| {
            assert_eq!(editor.suggested_filename(cx).as_ref(), "shopping list");
        });
    }

    async fn deserialize_editor(
        item_id: ItemId,
        workspace_id: WorkspaceId,
        workspace: Entity<Workspace>,
        project: Entity<Project>,
        cx: &mut VisualTestContext,
    ) -> Entity<Editor> {
        workspace
            .update_in(cx, |workspace, window, cx| {
                let pane = workspace.active_pane();
                pane.update(cx, |_, cx| {
                    Editor::deserialize(
                        project.clone(),
                        workspace.weak_handle(),
                        workspace_id,
                        item_id,
                        window,
                        cx,
                    )
                })
            })
            .await
            .unwrap()
    }

    #[gpui::test]
    async fn test_deserialize(cx: &mut gpui::TestAppContext) {
        init_test(cx, |_| {});
        cx.update(|cx| cx.set_global(db::AppDatabase::test_new()));

        let fs = FakeFs::new(cx.executor());
        fs.insert_file(path!("/file.rs"), Default::default()).await;

        // Test case 1: Deserialize with path and contents
        {
            let project = Project::test(fs.clone(), [path!("/file.rs").as_ref()], cx).await;
            let (multi_workspace, cx) = cx.add_window_view(|window, cx| {
                MultiWorkspace::test_new(project.clone(), window, cx)
            });
            let workspace = multi_workspace.read_with(cx, |mw, _| mw.workspace().clone());
            let db = cx.update(|_, cx| workspace::WorkspaceDb::global(cx));
            let workspace_id = db.next_id().await.unwrap();
            let editor_db = cx.update(|_, cx| EditorDb::global(cx));
            let item_id = 1234 as ItemId;
            let mtime = fs
                .metadata(Path::new(path!("/file.rs")))
                .await
                .unwrap()
                .unwrap()
                .mtime;

            let serialized_editor = SerializedEditor {
                abs_path: Some(PathBuf::from(path!("/file.rs"))),
                contents: Some("fn main() {}".to_string()),
                language: Some("Rust".to_string()),
                mtime: Some(mtime),
                ..SerializedEditor::default()
            };

            editor_db
                .save_serialized_editor(item_id, workspace_id, serialized_editor.clone())
                .await
                .unwrap();

            let deserialized =
                deserialize_editor(item_id, workspace_id, workspace, project, cx).await;

            deserialized.update(cx, |editor, cx| {
                assert_eq!(editor.text(cx), "fn main() {}");
                assert!(editor.is_dirty(cx));
                assert!(!editor.has_conflict(cx));
                let buffer = editor.buffer().read(cx).as_singleton().unwrap().read(cx);
                assert!(buffer.file().is_some());
            });
        }

        // Test case 2: Deserialize with only path
        {
            let project = Project::test(fs.clone(), [path!("/file.rs").as_ref()], cx).await;
            let (multi_workspace, cx) = cx.add_window_view(|window, cx| {
                MultiWorkspace::test_new(project.clone(), window, cx)
            });
            let workspace = multi_workspace.read_with(cx, |mw, _| mw.workspace().clone());
            let db = cx.update(|_, cx| workspace::WorkspaceDb::global(cx));
            let editor_db = cx.update(|_, cx| EditorDb::global(cx));

            let workspace_id = db.next_id().await.unwrap();

            let item_id = 5678 as ItemId;
            let serialized_editor = SerializedEditor {
                abs_path: Some(PathBuf::from(path!("/file.rs"))),
                contents: None,
                language: None,
                mtime: None,
                ..SerializedEditor::default()
            };

            editor_db
                .save_serialized_editor(item_id, workspace_id, serialized_editor)
                .await
                .unwrap();

            let deserialized =
                deserialize_editor(item_id, workspace_id, workspace, project, cx).await;

            deserialized.update(cx, |editor, cx| {
                assert_eq!(editor.text(cx), ""); // The file should be empty as per our initial setup
                assert!(!editor.is_dirty(cx));
                assert!(!editor.has_conflict(cx));

                let buffer = editor.buffer().read(cx).as_singleton().unwrap().read(cx);
                assert!(buffer.file().is_some());
            });
        }

        // Test case 3: Deserialize with no path (untitled buffer, with content and language)
        {
            let project = Project::test(fs.clone(), [path!("/file.rs").as_ref()], cx).await;
            // Add Rust to the language, so that we can restore the language of the buffer
            project.read_with(cx, |project, _| {
                project.languages().add(languages::rust_lang())
            });

            let (multi_workspace, cx) = cx.add_window_view(|window, cx| {
                MultiWorkspace::test_new(project.clone(), window, cx)
            });
            let workspace = multi_workspace.read_with(cx, |mw, _| mw.workspace().clone());
            let db = cx.update(|_, cx| workspace::WorkspaceDb::global(cx));
            let editor_db = cx.update(|_, cx| EditorDb::global(cx));

            let workspace_id = db.next_id().await.unwrap();

            let item_id = 9012 as ItemId;
            let serialized_editor = SerializedEditor {
                abs_path: None,
                contents: Some("hello".to_string()),
                language: Some("Rust".to_string()),
                mtime: None,
                ..SerializedEditor::default()
            };

            editor_db
                .save_serialized_editor(item_id, workspace_id, serialized_editor)
                .await
                .unwrap();

            let deserialized =
                deserialize_editor(item_id, workspace_id, workspace, project, cx).await;

            deserialized.update(cx, |editor, cx| {
                assert_eq!(editor.text(cx), "hello");
                assert!(editor.is_dirty(cx)); // The editor should be dirty for an untitled buffer

                let buffer = editor.buffer().read(cx).as_singleton().unwrap().read(cx);
                assert_eq!(
                    buffer.language().map(|lang| lang.name()),
                    Some("Rust".into())
                ); // Language should be set to Rust
                assert!(!buffer.content_language_detection_enabled());
                assert!(buffer.file().is_none()); // The buffer should not have an associated file
            });
        }

        // Test case 4: Deserialize with path, content, and old mtime
        {
            let project = Project::test(fs.clone(), [path!("/file.rs").as_ref()], cx).await;
            let (multi_workspace, cx) = cx.add_window_view(|window, cx| {
                MultiWorkspace::test_new(project.clone(), window, cx)
            });
            let workspace = multi_workspace.read_with(cx, |mw, _| mw.workspace().clone());
            let db = cx.update(|_, cx| workspace::WorkspaceDb::global(cx));
            let editor_db = cx.update(|_, cx| EditorDb::global(cx));

            let workspace_id = db.next_id().await.unwrap();

            let item_id = 9345 as ItemId;
            let old_mtime = MTime::from_seconds_and_nanos(0, 50);
            let serialized_editor = SerializedEditor {
                abs_path: Some(PathBuf::from(path!("/file.rs"))),
                contents: Some("fn main() {}".to_string()),
                language: Some("Rust".to_string()),
                mtime: Some(old_mtime),
                ..SerializedEditor::default()
            };

            editor_db
                .save_serialized_editor(item_id, workspace_id, serialized_editor)
                .await
                .unwrap();

            let deserialized =
                deserialize_editor(item_id, workspace_id, workspace, project, cx).await;

            deserialized.update(cx, |editor, cx| {
                assert_eq!(editor.text(cx), "fn main() {}");
                assert!(editor.has_conflict(cx)); // The editor should have a conflict
            });
        }

        // Test case 5: Deserialize with no path, no content, no language, and no old mtime (new, empty, unsaved buffer)
        {
            let project = Project::test(fs.clone(), [path!("/file.rs").as_ref()], cx).await;
            let (multi_workspace, cx) = cx.add_window_view(|window, cx| {
                MultiWorkspace::test_new(project.clone(), window, cx)
            });
            let workspace = multi_workspace.read_with(cx, |mw, _| mw.workspace().clone());
            let db = cx.update(|_, cx| workspace::WorkspaceDb::global(cx));
            let editor_db = cx.update(|_, cx| EditorDb::global(cx));

            let workspace_id = db.next_id().await.unwrap();

            let item_id = 10000 as ItemId;
            let serialized_editor = SerializedEditor {
                abs_path: None,
                contents: None,
                language: None,
                mtime: None,
                ..SerializedEditor::default()
            };

            editor_db
                .save_serialized_editor(item_id, workspace_id, serialized_editor)
                .await
                .unwrap();

            let deserialized =
                deserialize_editor(item_id, workspace_id, workspace, project, cx).await;

            deserialized.update(cx, |editor, cx| {
                assert_eq!(editor.text(cx), "");
                assert!(!editor.is_dirty(cx));
                assert!(!editor.has_conflict(cx));

                let buffer = editor.buffer().read(cx).as_singleton().unwrap().read(cx);
                assert!(buffer.file().is_none());
                assert!(buffer.content_language_detection_enabled());
            });
        }

        // Test case 6: Deserialize with path and contents in an empty workspace (no worktree)
        // This tests the hot-exit scenario where a file is opened in an empty workspace
        // and has unsaved changes that should be restored.
        {
            let fs = FakeFs::new(cx.executor());
            fs.insert_file(path!("/standalone.rs"), "original content".into())
                .await;

            // Create an empty project with no worktrees
            let project = Project::test(fs.clone(), [], cx).await;
            let (multi_workspace, cx) = cx.add_window_view(|window, cx| {
                MultiWorkspace::test_new(project.clone(), window, cx)
            });
            let workspace = multi_workspace.read_with(cx, |mw, _| mw.workspace().clone());
            let db = cx.update(|_, cx| workspace::WorkspaceDb::global(cx));
            let editor_db = cx.update(|_, cx| EditorDb::global(cx));

            let workspace_id = db.next_id().await.unwrap();
            let item_id = 11000 as ItemId;

            let mtime = fs
                .metadata(Path::new(path!("/standalone.rs")))
                .await
                .unwrap()
                .unwrap()
                .mtime;

            // Simulate serialized state: file with unsaved changes
            let serialized_editor = SerializedEditor {
                abs_path: Some(PathBuf::from(path!("/standalone.rs"))),
                contents: Some("modified content".to_string()),
                language: Some("Rust".to_string()),
                mtime: Some(mtime),
                ..SerializedEditor::default()
            };

            editor_db
                .save_serialized_editor(item_id, workspace_id, serialized_editor)
                .await
                .unwrap();

            let deserialized =
                deserialize_editor(item_id, workspace_id, workspace, project, cx).await;

            deserialized.update(cx, |editor, cx| {
                // The editor should have the serialized contents, not the disk contents
                assert_eq!(editor.text(cx), "modified content");
                assert!(editor.is_dirty(cx));
                assert!(!editor.has_conflict(cx));

                let buffer = editor.buffer().read(cx).as_singleton().unwrap().read(cx);
                assert!(buffer.file().is_some());
            });
        }
    }

    // Verify that renaming an open file emits EditorEvent::FileHandleChanged so that
    // the workspace re-serializes the editor with the updated path.
    #[gpui::test]
    async fn test_file_handle_changed_on_rename(cx: &mut gpui::TestAppContext) {
        use serde_json::json;
        use std::cell::RefCell;
        use std::rc::Rc;

        init_test(cx, |_| {});

        let fs = FakeFs::new(cx.executor());
        fs.insert_tree(path!("/root"), json!({ "file.rs": "fn main() {}" }))
            .await;

        let project = Project::test(fs.clone(), [path!("/root").as_ref()], cx).await;

        let buffer = project
            .update(cx, |project, cx| {
                project.open_local_buffer(path!("/root/file.rs"), cx)
            })
            .await
            .unwrap();

        let received_file_handle_changed = Rc::new(RefCell::new(false));
        let (editor, cx) = cx.add_window_view({
            let project = project.clone();
            let received_file_handle_changed = received_file_handle_changed.clone();
            move |window, cx| {
                let mut editor = Editor::for_buffer(buffer, Some(project), window, cx);
                editor.set_should_serialize(true, cx);
                let entity = cx.entity();
                cx.subscribe_in(&entity, window, move |_, _, event: &EditorEvent, _, _| {
                    if matches!(event, EditorEvent::FileHandleChanged) {
                        *received_file_handle_changed.borrow_mut() = true;
                    }
                })
                .detach();
                editor
            }
        });

        cx.run_until_parked();

        let (entry_id, worktree_id) = project.update(cx, |project, cx| {
            let worktree = project.worktrees(cx).next().unwrap();
            let worktree = worktree.read(cx);
            let entry = worktree.entry_for_path(rel_path("file.rs")).unwrap();
            (entry.id, worktree.id())
        });

        project
            .update(cx, |project, cx| {
                project.rename_entry(entry_id, (worktree_id, rel_path("renamed.rs")).into(), cx)
            })
            .await
            .unwrap();

        cx.run_until_parked();

        assert!(
            *received_file_handle_changed.borrow(),
            "EditorEvent::FileHandleChanged must be emitted when the open file is renamed"
        );

        editor.update(cx, |editor, cx| {
            let buffer = editor.buffer().read(cx).as_singleton().unwrap();
            let path = buffer.read(cx).file().unwrap().path();
            assert!(
                path.as_std_path().ends_with("renamed.rs"),
                "buffer path must reflect the renamed file, got {path:?}"
            );
        });
    }

    // Regression test for https://github.com/zed-industries/zed/issues/35947
    // Verifies that deserializing a non-worktree editor does not add the item
    // to any pane as a side effect.
    #[gpui::test]
    async fn test_deserialize_non_worktree_file_does_not_add_to_pane(
        cx: &mut gpui::TestAppContext,
    ) {
        init_test(cx, |_| {});
        cx.update(|cx| cx.set_global(db::AppDatabase::test_new()));

        let fs = FakeFs::new(cx.executor());
        fs.insert_tree(path!("/outside"), json!({ "settings.json": "{}" }))
            .await;

        // Project with a different root — settings.json is NOT in any worktree
        let project = Project::test(fs.clone(), [], cx).await;
        let (multi_workspace, cx) =
            cx.add_window_view(|window, cx| MultiWorkspace::test_new(project.clone(), window, cx));
        let workspace = multi_workspace.read_with(cx, |mw, _| mw.workspace().clone());
        let db = cx.update(|_, cx| workspace::WorkspaceDb::global(cx));
        let editor_db = cx.update(|_, cx| EditorDb::global(cx));

        let workspace_id = db.next_id().await.unwrap();
        let item_id = 99999 as ItemId;

        let serialized_editor = SerializedEditor {
            abs_path: Some(PathBuf::from(path!("/outside/settings.json"))),
            contents: None,
            language: None,
            mtime: None,
            ..SerializedEditor::default()
        };

        editor_db
            .save_serialized_editor(item_id, workspace_id, serialized_editor)
            .await
            .unwrap();

        // Count items in all panes before deserialization
        let pane_items_before = workspace.read_with(cx, |workspace, cx| {
            workspace
                .panes()
                .iter()
                .map(|pane| pane.read(cx).items_len())
                .sum::<usize>()
        });

        let deserialized =
            deserialize_editor(item_id, workspace_id, workspace.clone(), project, cx).await;

        cx.run_until_parked();

        // The editor should exist and have the file
        deserialized.update(cx, |editor, cx| {
            let buffer = editor.buffer().read(cx).as_singleton().unwrap().read(cx);
            assert!(buffer.file().is_some());
        });

        // No items should have been added to any pane as a side effect
        let pane_items_after = workspace.read_with(cx, |workspace, cx| {
            workspace
                .panes()
                .iter()
                .map(|pane| pane.read(cx).items_len())
                .sum::<usize>()
        });

        assert_eq!(
            pane_items_before, pane_items_after,
            "Editor::deserialize should not add items to panes as a side effect"
        );
    }

    #[gpui::test]
    async fn test_restoring_unsaved_contents_of_open_files(cx: &mut gpui::TestAppContext) {
        init_test(cx, |_| {});

        let fs = FakeFs::new(cx.executor());
        fs.insert_tree(
            path!("/root"),
            json!({ "edited.txt": "disk", "split.txt": "disk", "emptied.txt": "disk" }),
        )
        .await;
        let project = Project::test(fs.clone(), [path!("/root").as_ref()], cx).await;
        let edited_buffer = project
            .update(cx, |project, cx| {
                project.open_local_buffer(path!("/root/edited.txt"), cx)
            })
            .await
            .unwrap();
        edited_buffer.update(cx, |buffer, cx| buffer.edit([(0..0, "live ")], None, cx));
        let mtime = fs
            .metadata(Path::new(path!("/root/emptied.txt")))
            .await
            .unwrap()
            .unwrap()
            .mtime;

        let serialized_editors = [
            ("edited.txt", "saved", None),
            ("edited.txt", "saved", None),
            ("edited.txt", "", None),
            ("split.txt", "older", None),
            ("split.txt", "older", None),
            ("split.txt", "newer", None),
            ("emptied.txt", "", Some(mtime)),
            ("emptied.txt", "", Some(mtime)),
        ]
        .into_iter()
        .map(|(file_name, contents, mtime)| SerializedEditor {
            abs_path: Some(PathBuf::from(path!("/root")).join(file_name)),
            contents: Some(contents.to_string()),
            mtime,
            ..SerializedEditor::default()
        })
        .collect();
        let (editors, cx) = restore_editors(&project, serialized_editors, false, cx).await;

        assert_eq!(
            (
                edited_buffer.read_with(cx, |buffer, _| buffer.text()),
                restored_states(&editors, cx),
            ),
            (
                "live disk".to_string(),
                vec![
                    (
                        "saved".to_string(),
                        "edited.txt (recovered)".to_string(),
                        true,
                        0
                    ),
                    (
                        "saved".to_string(),
                        "edited.txt (recovered)".to_string(),
                        true,
                        0
                    ),
                    (String::new(), "edited.txt (recovered)".to_string(), true, 1),
                    ("older".to_string(), "split.txt".to_string(), true, 2),
                    ("older".to_string(), "split.txt".to_string(), true, 2),
                    (
                        "newer".to_string(),
                        "split.txt (recovered)".to_string(),
                        true,
                        3
                    ),
                    (String::new(), "emptied.txt".to_string(), true, 4),
                    (String::new(), "emptied.txt".to_string(), true, 4),
                ],
            )
        );
    }

    #[gpui::test]
    async fn test_unopenable_file_restores_its_unsaved_contents_as_recovered(
        cx: &mut gpui::TestAppContext,
    ) {
        init_test(cx, |_| {});

        let fs = FakeFs::new(cx.executor());
        fs.insert_tree(path!("/root"), json!({ "notes.txt": {} }))
            .await;
        let project = Project::test(fs, [path!("/root").as_ref()], cx).await;
        project.read_with(cx, |project, _| {
            project.languages().add(languages::rust_lang())
        });

        let serialized_editors = ["unsaved", "unsaved", "diverged"]
            .into_iter()
            .map(|contents| SerializedEditor {
                abs_path: Some(PathBuf::from(path!("/root/notes.txt"))),
                contents: Some(contents.to_string()),
                language: Some("Rust".to_string()),
                ..SerializedEditor::default()
            })
            .collect();
        let (editors, cx) = restore_editors(&project, serialized_editors, true, cx).await;

        assert_eq!(
            (
                restored_states(&editors, cx),
                editors[0].read_with(cx, |editor, cx| {
                    editor.buffer().read(cx).as_singleton().and_then(|buffer| {
                        buffer.read(cx).language().map(|language| language.name())
                    })
                }),
            ),
            (
                vec![
                    (
                        "unsaved".to_string(),
                        "notes.txt (recovered)".to_string(),
                        true,
                        0
                    ),
                    (
                        "unsaved".to_string(),
                        "notes.txt (recovered)".to_string(),
                        true,
                        0
                    ),
                    (
                        "diverged".to_string(),
                        "notes.txt (recovered)".to_string(),
                        true,
                        1
                    ),
                ],
                Some(LanguageName::new_static("Rust")),
            )
        );
    }

    #[gpui::test]
    async fn test_restoring_unsaved_buffers_without_files(cx: &mut gpui::TestAppContext) {
        init_test(cx, |_| {});

        let project = Project::test(FakeFs::new(cx.executor()), [], cx).await;
        let recovered_from = PathBuf::from(path!("/root/edited.txt"));
        let serialized_editors = [
            (Some("session/7"), Some("unsaved"), None),
            (Some("session/7"), Some("unsaved"), None),
            (Some("session/8"), Some("unsaved"), None),
            (Some("session/7"), Some("stale"), None),
            (Some("session/9"), Some("recovered"), Some(&recovered_from)),
            (Some("session/9"), Some("recovered"), Some(&recovered_from)),
            (None, None, Some(&recovered_from)),
        ]
        .into_iter()
        .map(
            |(shared_buffer, contents, recovered_from)| SerializedEditor {
                contents: contents.map(str::to_string),
                recovered_from: recovered_from.cloned(),
                shared_buffer: shared_buffer.map(str::to_string),
                ..SerializedEditor::default()
            },
        )
        .collect();
        let (editors, cx) = restore_editors(&project, serialized_editors, false, cx).await;

        assert_eq!(
            (
                restored_states(&editors, cx),
                editors[6].read_with(cx, |editor, cx| editor.suggested_filename(cx)),
            ),
            (
                vec![
                    ("unsaved".to_string(), "unsaved".to_string(), true, 0),
                    ("unsaved".to_string(), "unsaved".to_string(), true, 0),
                    ("unsaved".to_string(), "unsaved".to_string(), true, 1),
                    ("stale".to_string(), "stale".to_string(), true, 2),
                    (
                        "recovered".to_string(),
                        "edited.txt (recovered)".to_string(),
                        true,
                        3
                    ),
                    (
                        "recovered".to_string(),
                        "edited.txt (recovered)".to_string(),
                        true,
                        3
                    ),
                    (String::new(), "edited.txt (recovered)".to_string(), true, 4),
                ],
                SharedString::from("edited.txt"),
            )
        );
    }

    #[gpui::test]
    async fn test_fileless_buffers_with_equal_remote_ids_restore_separately(
        cx: &mut gpui::TestAppContext,
    ) {
        init_test(cx, |_| {});

        let project = Project::test(FakeFs::new(cx.executor()), [], cx).await;
        let (workspace, cx) = workspace_with_database_id(&project, cx).await;
        let buffers = [0, 1].map(|_| {
            cx.new(|cx| {
                let mut buffer = Buffer::remote(
                    BufferId::new(7).unwrap(),
                    ReplicaId::LOCAL,
                    Capability::ReadWrite,
                    "",
                    cx,
                );
                buffer.edit([(0..0, "same")], None, cx);
                buffer
            })
        });
        let editors = [&buffers[0], &buffers[0], &buffers[1]].map(|buffer| {
            cx.new_window_entity(|window, cx| {
                Editor::for_buffer(buffer.clone(), Some(project.clone()), window, cx)
            })
        });
        serialize_editors(&workspace, &editors, cx).await;

        let restored_project = Project::test(FakeFs::new(cx.executor()), [], cx).await;
        let restored = restore_serialized_editors(&workspace, &restored_project, 3, cx).await;

        assert_eq!(
            restored_states(&restored, cx),
            vec![
                ("same".to_string(), "same".to_string(), true, 0),
                ("same".to_string(), "same".to_string(), true, 0),
                ("same".to_string(), "same".to_string(), true, 1),
            ]
        );
    }

    #[gpui::test]
    async fn test_deleted_files_restore_like_live_buffers(cx: &mut gpui::TestAppContext) {
        init_test(cx, |_| {});

        let fs = FakeFs::new(cx.executor());
        fs.insert_tree(
            path!("/root"),
            json!({
                "clean.txt": "clean text",
                "dirty.txt": "saved text",
                "locked.txt": "locked text",
                "empty.txt": "",
            }),
        )
        .await;
        let project = Project::test(fs.clone(), [path!("/root").as_ref()], cx).await;
        let (workspace, cx) = workspace_with_database_id(&project, cx).await;
        let file_names = [
            "clean.txt",
            "clean.txt",
            "dirty.txt",
            "locked.txt",
            "empty.txt",
        ];
        let live_buffers = open_root_buffers(&project, &file_names, cx).await;
        live_buffers[2].update(cx, |buffer, cx| buffer.edit([(0..0, "unsaved ")], None, cx));
        live_buffers[3].update(cx, |buffer, cx| buffer.set_capability(Capability::Read, cx));
        remove_root_files(&fs, &file_names[1..], cx).await;
        let editors = editors_for_buffers(&project, &live_buffers, cx);
        serialize_editors(&workspace, &editors, cx).await;
        cx.update(|_, cx| {
            cx.update_global::<SettingsStore, _>(|store, cx| {
                store.update_user_settings(cx, |settings| {
                    settings.project.worktree.file_scan_exclusions =
                        Some(SplicingVec::from(Vec::from([String::from("**/dirty.txt")])));
                });
            });
        });

        let restored_project = Project::test(fs.clone(), [path!("/root").as_ref()], cx).await;
        let restored = restore_serialized_editors(&workspace, &restored_project, 5, cx).await;
        let restored_buffers = singleton_buffers(&restored, cx);
        let saved_mtimes = [&live_buffers, &restored_buffers].map(|buffers| {
            buffers
                .iter()
                .map(|buffer| buffer.read_with(cx, |buffer, _| buffer.saved_mtime()))
                .collect::<Vec<_>>()
        });
        let states = [&live_buffers, &restored_buffers].map(|buffers| buffer_states(buffers, cx));
        restored_project
            .update(cx, |project, cx| {
                project.save_buffer(restored_buffers[2].clone(), cx)
            })
            .await
            .unwrap();
        cx.run_until_parked();
        let saved_text = fs.load(Path::new(path!("/root/dirty.txt"))).await.unwrap();
        let saved_state = buffer_states(&restored_buffers[2..3], cx);

        let expected_states = vec![
            buffer_state("clean text", false, false, "deleted", Capability::ReadWrite),
            buffer_state("clean text", false, false, "deleted", Capability::ReadWrite),
            buffer_state(
                "unsaved saved text",
                true,
                false,
                "deleted",
                Capability::ReadWrite,
            ),
            buffer_state("locked text", false, false, "deleted", Capability::Read),
            buffer_state("", false, false, "deleted", Capability::ReadWrite),
        ];
        assert_eq!(
            (
                states,
                saved_mtimes[1] == saved_mtimes[0],
                restored_buffers[0] == restored_buffers[1],
                saved_text,
                saved_state,
            ),
            (
                [expected_states.clone(), expected_states],
                true,
                true,
                "unsaved saved text".to_string(),
                vec![buffer_state(
                    "unsaved saved text",
                    false,
                    false,
                    "present",
                    Capability::ReadWrite,
                )],
            )
        );
    }

    #[gpui::test]
    async fn test_files_changed_while_closed_restore_like_live_buffers(
        cx: &mut gpui::TestAppContext,
    ) {
        init_test(cx, |_| {});

        let fs = FakeFs::new(cx.executor());
        fs.insert_tree(
            path!("/root"),
            json!({
                "clean.txt": "clean text",
                "dirty.txt": "saved text",
                "same.txt": "saved text",
                "emptied.txt": "saved text",
            }),
        )
        .await;
        let project = Project::test(fs.clone(), [path!("/root").as_ref()], cx).await;
        let (workspace, cx) = workspace_with_database_id(&project, cx).await;
        let file_names = ["clean.txt", "dirty.txt", "same.txt", "emptied.txt"];
        let live_buffers = open_root_buffers(&project, &file_names, cx).await;
        for buffer in &live_buffers[1..3] {
            buffer.update(cx, |buffer, cx| buffer.edit([(0..0, "unsaved ")], None, cx));
        }
        live_buffers[3].update(cx, |buffer, cx| buffer.set_text("", cx));
        remove_root_files(&fs, &file_names[..3], cx).await;
        let editors = editors_for_buffers(&project, &live_buffers, cx);
        serialize_editors(&workspace, &editors, cx).await;
        for (file_name, text) in [
            ("clean.txt", "reappeared"),
            ("dirty.txt", "reappeared"),
            ("same.txt", "unsaved saved text"),
            ("emptied.txt", ""),
        ] {
            fs.insert_file(
                PathBuf::from(path!("/root")).join(file_name),
                text.as_bytes().to_vec(),
            )
            .await;
        }
        cx.run_until_parked();

        let restored_project = Project::test(fs, [path!("/root").as_ref()], cx).await;
        let restored = restore_serialized_editors(&workspace, &restored_project, 4, cx).await;
        let restored_buffers = singleton_buffers(&restored, cx);
        let states = [&live_buffers, &restored_buffers].map(|buffers| buffer_states(buffers, cx));

        let expected_states = vec![
            buffer_state("reappeared", false, false, "present", Capability::ReadWrite),
            buffer_state(
                "unsaved saved text",
                true,
                true,
                "present",
                Capability::ReadWrite,
            ),
            buffer_state(
                "unsaved saved text",
                true,
                true,
                "present",
                Capability::ReadWrite,
            ),
            buffer_state("", true, true, "present", Capability::ReadWrite),
        ];
        assert_eq!(states, [expected_states.clone(), expected_states]);
    }

    #[gpui::test]
    async fn test_restored_text_format_saves_like_live_buffers(cx: &mut gpui::TestAppContext) {
        init_test(cx, |_| {});

        let utf16_bytes = [0xFF, 0xFE]
            .into_iter()
            .chain("saved\r\ntext".encode_utf16().flat_map(u16::to_le_bytes))
            .collect::<Vec<_>>();
        let fs = FakeFs::new(cx.executor());
        fs.insert_tree(path!("/root"), json!({ "windows.txt": "saved\r\ntext" }))
            .await;
        fs.insert_file(path!("/root/utf16.txt"), utf16_bytes).await;
        let project = Project::test(fs.clone(), [path!("/root").as_ref()], cx).await;
        let (workspace, cx) = workspace_with_database_id(&project, cx).await;
        let mut live_buffers = open_root_buffers(&project, &["utf16.txt", "windows.txt"], cx).await;
        live_buffers.push(project.update(cx, |project, cx| {
            project.create_local_buffer("", None, false, cx)
        }));
        for buffer in &live_buffers {
            buffer.update(cx, |buffer, cx| buffer.edit([(0..0, "unsaved ")], None, cx));
        }
        live_buffers[1].update(cx, |buffer, cx| {
            buffer.set_line_ending(LineEnding::Unix, cx)
        });
        live_buffers[2].update(cx, |buffer, cx| {
            buffer.set_line_ending(LineEnding::Windows, cx);
            buffer.set_encoding(encoding_rs::UTF_16BE);
            buffer.set_has_bom(true);
            buffer.edit([(buffer.len()..buffer.len(), "\nline")], None, cx);
        });
        remove_root_files(&fs, &["utf16.txt"], cx).await;
        let editors = editors_for_buffers(&project, &live_buffers, cx);
        serialize_editors(&workspace, &editors, cx).await;

        let restored_project = Project::test(fs.clone(), [path!("/root").as_ref()], cx).await;
        let restored = restore_serialized_editors(&workspace, &restored_project, 3, cx).await;
        let restored_buffers = singleton_buffers(&restored, cx);
        let formats = [&live_buffers, &restored_buffers].map(|buffers| {
            buffers
                .iter()
                .map(|buffer| {
                    buffer.read_with(cx, |buffer, _| {
                        (
                            buffer.line_ending(),
                            buffer.encoding().name(),
                            buffer.has_bom(),
                        )
                    })
                })
                .collect::<Vec<_>>()
        });
        let mut saved_bytes = Vec::new();
        for (project, buffers, untitled_name) in [
            (&restored_project, &restored_buffers, "restored.txt"),
            (&project, &live_buffers, "live.txt"),
        ] {
            saved_bytes.push(save_buffers(&fs, project, buffers, untitled_name, cx).await);
        }

        let utf16_text = "unsaved saved\r\ntext";
        let untitled_text = "unsaved \r\nline";
        let expected_bytes = vec![
            [0xFF, 0xFE]
                .into_iter()
                .chain(utf16_text.encode_utf16().flat_map(u16::to_le_bytes))
                .collect::<Vec<_>>(),
            b"unsaved saved\ntext".to_vec(),
            [0xFE, 0xFF]
                .into_iter()
                .chain(untitled_text.encode_utf16().flat_map(u16::to_be_bytes))
                .collect::<Vec<_>>(),
        ];
        assert_eq!(
            (formats[1].clone(), saved_bytes),
            (
                formats[0].clone(),
                vec![expected_bytes.clone(), expected_bytes]
            )
        );
    }

    #[gpui::test]
    async fn test_restoring_equal_text_saved_in_different_formats_keeps_each_format(
        cx: &mut gpui::TestAppContext,
    ) {
        init_test(cx, |_| {});

        let fs = FakeFs::new(cx.executor());
        fs.insert_tree(path!("/root"), json!({ "file.txt": "saved" }))
            .await;
        let project = Project::test(fs.clone(), [path!("/root").as_ref()], cx).await;
        let (workspace, cx) = workspace_with_database_id(&project, cx).await;
        let buffer = open_root_buffers(&project, &["file.txt"], cx)
            .await
            .remove(0);
        buffer.update(cx, |buffer, cx| {
            buffer.edit([(0..0, "unsaved ")], None, cx);
            buffer.set_encoding(encoding_rs::WINDOWS_1252);
        });
        let editors = editors_for_buffers(&project, &[buffer.clone(), buffer.clone()], cx);
        serialize_editors(&workspace, &editors, cx).await;
        buffer.update(cx, |buffer, _| buffer.set_encoding(encoding_rs::UTF_8));
        serialize_editors(&workspace, &editors[..1], cx).await;

        let restored_project = Project::test(fs.clone(), [path!("/root").as_ref()], cx).await;
        let restored = restore_serialized_editors(&workspace, &restored_project, 2, cx).await;
        let restored_buffers = singleton_buffers(&restored, cx);
        let restored_formats = restored_buffers
            .iter()
            .map(|buffer| {
                buffer.read_with(cx, |buffer, _| (buffer.text(), buffer.encoding().name()))
            })
            .collect::<Vec<_>>();

        assert_eq!(
            (restored_buffers[0] == restored_buffers[1], restored_formats),
            (
                false,
                vec![
                    ("unsaved saved".to_string(), "UTF-8"),
                    ("unsaved saved".to_string(), "windows-1252"),
                ]
            )
        );
    }

    #[test]
    fn test_restoration_rewrites_only_buffers_without_unsaved_edits() {
        let mut plans = HashSet::default();
        for deleted_file in [
            None,
            Some(DeletedFile {
                dirty: false,
                read_only: false,
            }),
            Some(DeletedFile {
                dirty: true,
                read_only: true,
            }),
        ] {
            for contents in [None, Some(String::new()), Some(String::from("saved"))] {
                for disk_state in [
                    LiveDiskState::Present,
                    LiveDiskState::New,
                    LiveDiskState::Deleted,
                ] {
                    for (has_saved_snapshot, has_saved_encoding) in
                        [(false, false), (false, true), (true, false), (true, true)]
                    {
                        let saved = SavedFileBuffer {
                            contents: contents.clone(),
                            mtime: None,
                            deleted_file,
                            text_format: None,
                        };
                        let live = LiveFileBuffer {
                            disk_state,
                            has_unsaved_edits: true,
                            has_saved_snapshot,
                            has_saved_encoding,
                        };
                        plans.insert((
                            has_saved_snapshot,
                            plan_file_buffer_restoration(&saved, live),
                        ));
                    }
                }
            }
        }

        assert_eq!(
            plans,
            HashSet::from_iter([
                (false, FileBufferRestoration::UseLive),
                (false, FileBufferRestoration::Recover),
                (true, FileBufferRestoration::UseLive),
            ])
        );
    }

    #[gpui::test]
    async fn test_restoration_keeps_live_buffer_state_that_diverged_from_the_saved_tab(
        cx: &mut gpui::TestAppContext,
    ) {
        init_test(cx, |_| {});

        let fs = FakeFs::new(cx.executor());
        fs.insert_tree(path!("/root"), json!({ "locked.txt": "locked" }))
            .await;
        fs.insert_file(path!("/root/encoded.txt"), Vec::from([0xFF, 0xFE]))
            .await;
        let project = Project::test(fs.clone(), [path!("/root").as_ref()], cx).await;
        let (workspace, cx) = workspace_with_database_id(&project, cx).await;
        let file_names = ["encoded.txt", "locked.txt"];
        let live_buffers = open_root_buffers(&project, &file_names, cx).await;
        let original_encoding = live_buffers[0].read_with(cx, |buffer, _| buffer.encoding().name());
        remove_root_files(&fs, &file_names, cx).await;
        let editors = editors_for_buffers(&project, &live_buffers, cx);
        serialize_editors(&workspace, &editors, cx).await;
        for file_name in file_names {
            fs.insert_file(
                PathBuf::from(path!("/root")).join(file_name),
                b"recreated".to_vec(),
            )
            .await;
        }
        cx.update(|_, cx| {
            cx.update_global::<SettingsStore, _>(|store, cx| {
                store.update_user_settings(cx, |settings| {
                    settings.project.worktree.read_only_files = Some(SplicingVec::from(Vec::from(
                        [String::from("**/locked.txt")],
                    )));
                });
            });
        });
        cx.run_until_parked();

        let restored_project = Project::test(fs.clone(), [path!("/root").as_ref()], cx).await;
        let opened_before_restoration =
            open_root_buffers(&restored_project, &["encoded.txt"], cx).await;
        opened_before_restoration[0]
            .update(cx, |buffer, cx| buffer.edit([(0..0, "unsaved ")], None, cx));
        let restored = restore_serialized_editors(&workspace, &restored_project, 2, cx).await;
        cx.run_until_parked();
        let restored_buffers = singleton_buffers(&restored, cx);
        let encodings = restored_buffers
            .iter()
            .map(|buffer| buffer.read_with(cx, |buffer, _| buffer.encoding().name()))
            .collect::<Vec<_>>();

        assert_eq!(
            (
                original_encoding,
                restored_buffers[0] == opened_before_restoration[0],
                buffer_states(&restored_buffers, cx),
                encodings,
            ),
            (
                "UTF-16LE",
                true,
                vec![
                    buffer_state(
                        "unsaved recreated",
                        true,
                        false,
                        "present",
                        Capability::ReadWrite
                    ),
                    buffer_state("recreated", false, false, "present", Capability::Read),
                ],
                vec!["UTF-8", "UTF-8"],
            )
        );
    }

    #[gpui::test]
    async fn test_restored_deleted_file_notifies_guests_like_live_deletion(
        cx: &mut gpui::TestAppContext,
    ) {
        init_test(cx, |_| {});

        let fs = FakeFs::new(cx.executor());
        fs.insert_tree(path!("/root"), json!({ "deleted.txt": "text" }))
            .await;
        let project = Project::test(fs.clone(), [path!("/root").as_ref()], cx).await;
        let (workspace, cx) = workspace_with_database_id(&project, cx).await;
        let live_guest = share_with_recording_guest(&project, cx);
        let live_buffers = open_root_buffers(&project, &["deleted.txt"], cx).await;
        remove_root_files(&fs, &["deleted.txt"], cx).await;
        let editors = editors_for_buffers(&project, &live_buffers, cx);
        serialize_editors(&workspace, &editors, cx).await;

        let restored_project = Project::test(fs, [path!("/root").as_ref()], cx).await;
        let restored_guest = share_with_recording_guest(&restored_project, cx);
        restore_serialized_editors(&workspace, &restored_project, 1, cx).await;

        let updates = [live_guest, restored_guest].map(|guest| guest.buffer_file_updates());
        assert_eq!(
            updates,
            [
                vec![("deleted.txt".to_string(), true, None)],
                vec![("deleted.txt".to_string(), true, None)],
            ]
        );
    }

    #[gpui::test]
    async fn test_files_of_deleted_roots_restore_like_live_buffers(cx: &mut gpui::TestAppContext) {
        init_test(cx, |_| {});

        let fs = FakeFs::new(cx.executor());
        fs.insert_tree(
            path!("/root"),
            json!({ "clean.txt": "clean text", "dirty.txt": "saved text" }),
        )
        .await;
        fs.insert_file(path!("/single.txt"), b"single text".to_vec())
            .await;
        let project = Project::test(fs.clone(), [path!("/root").as_ref()], cx).await;
        let single_project = Project::test(fs.clone(), [path!("/single.txt").as_ref()], cx).await;
        let (workspace, cx) = workspace_with_database_id(&project, cx).await;
        let live_guest = share_with_recording_guest(&project, cx);
        let single_guest = share_with_recording_guest(&single_project, cx);
        let mut live_buffers = open_root_buffers(&project, &["clean.txt", "dirty.txt"], cx).await;
        live_buffers.push(
            single_project
                .update(cx, |project, cx| {
                    project.open_local_buffer(path!("/single.txt"), cx)
                })
                .await
                .unwrap(),
        );
        live_buffers[1].update(cx, |buffer, cx| buffer.edit([(0..0, "unsaved ")], None, cx));
        fs.remove_dir(
            Path::new(path!("/root")),
            fs::RemoveOptions {
                recursive: true,
                ignore_if_not_exists: false,
            },
        )
        .await
        .unwrap();
        fs.remove_file(
            Path::new(path!("/single.txt")),
            fs::RemoveOptions::default(),
        )
        .await
        .unwrap();
        cx.run_until_parked();
        cx.executor()
            .advance_clock(std::time::Duration::from_secs(1));
        cx.run_until_parked();
        let mut editors = editors_for_buffers(&project, &live_buffers[..2], cx);
        editors.extend(editors_for_buffers(&single_project, &live_buffers[2..], cx));
        serialize_editors(&workspace, &editors, cx).await;

        let restored_project = Project::test(fs, [path!("/root").as_ref()], cx).await;
        let restored_guest = share_with_recording_guest(&restored_project, cx);
        let restored = restore_serialized_editors(&workspace, &restored_project, 3, cx).await;
        let restored_buffers = singleton_buffers(&restored, cx);
        let states = [&live_buffers, &restored_buffers].map(|buffers| buffer_states(buffers, cx));
        let mut live_updates = live_guest.buffer_file_updates();
        live_updates.extend(single_guest.buffer_file_updates());
        let updates = [live_updates, restored_guest.buffer_file_updates()].map(|mut updates| {
            updates.sort_by(|left, right| left.0.cmp(&right.0));
            updates
        });

        let expected_states = vec![
            buffer_state("clean text", false, false, "deleted", Capability::ReadWrite),
            buffer_state(
                "unsaved saved text",
                true,
                false,
                "deleted",
                Capability::ReadWrite,
            ),
            buffer_state(
                "single text",
                false,
                false,
                "deleted",
                Capability::ReadWrite,
            ),
        ];
        let expected_updates = vec![
            (String::new(), true, None),
            ("clean.txt".to_string(), true, None),
            ("dirty.txt".to_string(), true, None),
        ];
        assert_eq!(
            (states, updates),
            (
                [expected_states.clone(), expected_states],
                [expected_updates.clone(), expected_updates]
            )
        );
    }

    #[gpui::test]
    async fn test_open_resolved_target_at_non_ascii_column(cx: &mut gpui::TestAppContext) {
        init_test(cx, |_| {});

        let fs = FakeFs::new(cx.executor());
        fs.insert_tree(
            path!("/root"),
            json!({
                "src": {
                    "main.rs": "first\naéøbc\n",
                },
            }),
        )
        .await;

        let project = Project::test(fs.clone(), [path!("/root").as_ref()], cx).await;
        let (multi_workspace, cx) =
            cx.add_window_view(|window, cx| MultiWorkspace::test_new(project.clone(), window, cx));
        let workspace = multi_workspace.read_with(cx, |mw, _| mw.workspace().clone());

        let open_target = OpenTarget::Path(
            PathWithPosition {
                path: PathBuf::from(path!("/root/src/main.rs")),
                row: Some(2),
                column: Some(4),
            },
            false,
            OpenTargetFoundBy::BackgroundPathResolution,
        );

        let opened = workspace
            .update_in(cx, |_, window, cx| {
                cx.spawn_in(window, async move |workspace, cx| {
                    open_resolved_target(&workspace, &open_target, cx).await
                })
            })
            .await
            .expect("opening the target should succeed");
        assert!(opened, "target should open as a file");

        let editor = workspace.read_with(cx, |workspace, cx| {
            workspace
                .active_item(cx)
                .and_then(|item| item.act_as::<Editor>(cx))
                .expect("active item should be an editor")
        });
        let cursor = editor.update_in(cx, |editor, _, cx| {
            editor
                .selections
                .newest::<language::Point>(&editor.display_snapshot(cx))
                .head()
        });
        // Column 4 is the fourth character of `aéøbc` (the `b`), which starts at byte 5.
        assert_eq!(cursor, language::Point::new(1, 5));
    }

    #[gpui::test]
    fn test_compute_modified_ranges_git_diff(cx: &mut gpui::TestAppContext) {
        let base_text = "line0\nline1\nline2\nline3\nline4\nline5\nline6\n";
        // Modify line1 and line5 to create two non-adjacent hunks.
        let buffer_text = "line0\nMOD1\nline2\nline3\nline4\nMOD5\nline6\n";

        let buffer = cx.new(|cx| language::Buffer::local(buffer_text, cx));
        let diff_snapshot = buffer.update(cx, |buffer, cx| {
            let diff = cx.new(|cx| {
                buffer_diff::BufferDiff::new_with_base_text(base_text, &buffer.text_snapshot(), cx)
            });
            diff.read(cx).snapshot(cx)
        });

        let ranges = buffer.update(cx, |buffer, _cx| {
            compute_modified_ranges(&buffer.snapshot(), &diff_snapshot)
        });

        assert_eq!(ranges.len(), 2, "expected 2 non-adjacent ranges");

        buffer.update(cx, |buffer, _cx| {
            let text_snapshot: &text::BufferSnapshot = buffer;
            let r0 = ranges[0].start.to_point(text_snapshot)..ranges[0].end.to_point(text_snapshot);
            let r1 = ranges[1].start.to_point(text_snapshot)..ranges[1].end.to_point(text_snapshot);
            assert_eq!(r0.start.row, 1, "first hunk should start at row 1");
            assert_eq!(r0.end.row, 1, "first hunk should end at row 1");
            assert_eq!(r1.start.row, 5, "second hunk should start at row 5");
            assert_eq!(r1.end.row, 5, "second hunk should end at row 5");
        });
    }

    #[gpui::test]
    fn test_compute_modified_ranges_unchanged_buffer(cx: &mut gpui::TestAppContext) {
        let buffer_text = "line0\nline1\nline2\n";
        let buffer = cx.new(|cx| language::Buffer::local(buffer_text, cx));
        let diff_snapshot = buffer.update(cx, |buffer, cx| {
            let diff = cx.new(|cx| {
                buffer_diff::BufferDiff::new_with_base_text(
                    buffer_text,
                    &buffer.text_snapshot(),
                    cx,
                )
            });
            diff.read(cx).snapshot(cx)
        });

        let ranges = buffer.update(cx, |buffer, _cx| {
            compute_modified_ranges(&buffer.snapshot(), &diff_snapshot)
        });

        assert_eq!(
            ranges,
            Vec::new(),
            "buffer that matches its diff base should produce no modified ranges"
        );
    }

    #[gpui::test]
    fn test_compute_modified_ranges_deletion_only(cx: &mut gpui::TestAppContext) {
        let base_text = "line0\nline1\nline2\n";
        // Buffer has line1 deleted (pure deletion).
        let buffer_text = "line0\nline2\n";

        let buffer = cx.new(|cx| language::Buffer::local(buffer_text, cx));
        let diff_snapshot = buffer.update(cx, |buffer, cx| {
            let diff = cx.new(|cx| {
                buffer_diff::BufferDiff::new_with_base_text(base_text, &buffer.text_snapshot(), cx)
            });
            diff.read(cx).snapshot(cx)
        });

        // Verify the diff has a deletion hunk.
        let hunk_count = buffer.update(cx, |buffer, _cx| {
            let text_snapshot: &text::BufferSnapshot = buffer;
            diff_snapshot.hunks(text_snapshot).count()
        });
        assert!(hunk_count > 0, "diff should have hunks");

        let ranges = buffer.update(cx, |buffer, _cx| {
            compute_modified_ranges(&buffer.snapshot(), &diff_snapshot)
        });

        assert_eq!(
            ranges,
            Vec::new(),
            "deletion-only hunks should be skipped, leaving no ranges"
        );
    }

    #[gpui::test]
    fn test_compute_modified_ranges_adjacent_hunks(cx: &mut gpui::TestAppContext) {
        let base_text = "line0\nline1\nline2\nline3\nline4\n";
        // Modify lines 2 and 3 which are adjacent; they should merge into one range.
        let buffer_text = "line0\nline1\nMOD2\nMOD3\nline4\n";

        let buffer = cx.new(|cx| language::Buffer::local(buffer_text, cx));
        let diff_snapshot = buffer.update(cx, |buffer, cx| {
            let diff = cx.new(|cx| {
                buffer_diff::BufferDiff::new_with_base_text(base_text, &buffer.text_snapshot(), cx)
            });
            diff.read(cx).snapshot(cx)
        });

        let ranges = buffer.update(cx, |buffer, _cx| {
            compute_modified_ranges(&buffer.snapshot(), &diff_snapshot)
        });

        assert_eq!(
            ranges.len(),
            1,
            "adjacent hunks (rows 2 and 3) should be merged into one range"
        );
        buffer.update(cx, |buffer, _cx| {
            let text_snapshot: &text::BufferSnapshot = buffer;
            let r = ranges[0].start.to_point(text_snapshot)..ranges[0].end.to_point(text_snapshot);
            assert_eq!(r.start.row, 2, "merged range should start at row 2");
            assert_eq!(r.end.row, 3, "merged range should end at row 3");
        });
    }

    // Regression test for a multi-buffer (e.g. project search results) that excerpts
    // an untitled buffer alongside a file-backed one. Saving used to error out with
    // "buffer doesn't have a file", which aborted `workspace: reload` and quit flows.
    #[gpui::test]
    async fn test_save_multi_buffer_with_untitled_buffer_skips_untitled(
        cx: &mut gpui::TestAppContext,
    ) {
        init_test(cx, |_| {});

        let fs = FakeFs::new(cx.executor());
        fs.insert_tree(path!("/dir"), json!({ "file.txt": "the cat sat" }))
            .await;
        let project = Project::test(fs.clone(), [path!("/dir").as_ref()], cx).await;
        let window =
            cx.add_window(|window, cx| MultiWorkspace::test_new(project.clone(), window, cx));
        let cx = &mut VisualTestContext::from_window(*window, cx);

        let file_buffer = project
            .update(cx, |project, cx| {
                project.open_local_buffer(path!("/dir/file.txt"), cx)
            })
            .await
            .unwrap();
        let untitled_buffer = project.update(cx, |project, cx| {
            project.create_local_buffer("the cat", None, false, cx)
        });

        // Make both buffers dirty so both are candidates to be saved.
        file_buffer.update(cx, |buffer, cx| {
            buffer.edit([(0..0, "X")], None, cx);
        });
        untitled_buffer.update(cx, |buffer, cx| {
            buffer.edit([(0..0, "Y")], None, cx);
        });

        let multi_buffer = cx.new(|cx| {
            let mut multi_buffer = MultiBuffer::new(project.read(cx).capability());
            multi_buffer.set_excerpts_for_path(
                PathKey::sorted(0),
                file_buffer.clone(),
                [Point::new(0, 0)..Point::new(0, 3)],
                0,
                cx,
            );
            multi_buffer.set_excerpts_for_path(
                PathKey::sorted(1),
                untitled_buffer.clone(),
                [Point::new(0, 0)..Point::new(0, 3)],
                0,
                cx,
            );
            multi_buffer
        });
        let editor = cx.new_window_entity(|window, cx| {
            Editor::for_multibuffer(multi_buffer, Some(project.clone()), window, cx)
        });
        cx.run_until_parked();

        editor.update(cx, |editor, cx| {
            assert!(!editor.buffer().read(cx).is_singleton());
        });

        let save = editor.update_in(cx, |editor, window, cx| {
            editor.save(
                SaveOptions {
                    format: false,
                    force_format: false,
                    autosave: false,
                },
                project.clone(),
                window,
                cx,
            )
        });
        save.await
            .expect("saving a multi-buffer that excerpts an untitled buffer should not error");
        cx.run_until_parked();

        // The file-backed buffer is saved; the untitled buffer is skipped and stays dirty.
        file_buffer.update(cx, |buffer, _| assert!(!buffer.is_dirty()));
        untitled_buffer.update(cx, |buffer, _| {
            assert!(buffer.file().is_none());
            assert!(buffer.is_dirty());
        });
    }

    async fn restore_editors<'a>(
        project: &Entity<Project>,
        serialized_editors: Vec<SerializedEditor>,
        concurrently: bool,
        cx: &'a mut gpui::TestAppContext,
    ) -> (Vec<Entity<Editor>>, &'a mut VisualTestContext) {
        cx.update(|cx| cx.set_global(db::AppDatabase::test_new()));
        let (multi_workspace, cx) =
            cx.add_window_view(|window, cx| MultiWorkspace::test_new(project.clone(), window, cx));
        let workspace =
            multi_workspace.read_with(cx, |multi_workspace, _| multi_workspace.workspace().clone());
        let workspace_id = cx
            .update(|_, cx| workspace::WorkspaceDb::global(cx))
            .next_id()
            .await
            .unwrap();
        let editor_db = cx.update(|_, cx| EditorDb::global(cx));
        let item_ids = 1..=serialized_editors.len() as ItemId;
        for (item_id, serialized_editor) in item_ids.clone().zip(serialized_editors) {
            editor_db
                .save_serialized_editor(item_id, workspace_id, serialized_editor)
                .await
                .unwrap();
        }

        let editors = if concurrently {
            let restorations = cx.update(|window, cx| {
                item_ids
                    .map(|item_id| {
                        Editor::deserialize(
                            project.clone(),
                            workspace.downgrade(),
                            workspace_id,
                            item_id,
                            window,
                            cx,
                        )
                    })
                    .collect::<Vec<_>>()
            });
            try_join_all(restorations).await.unwrap()
        } else {
            let mut editors = Vec::new();
            for item_id in item_ids {
                editors.push(
                    deserialize_editor(
                        item_id,
                        workspace_id,
                        workspace.clone(),
                        project.clone(),
                        cx,
                    )
                    .await,
                );
            }
            editors
        };
        (editors, cx)
    }

    async fn workspace_with_database_id<'a>(
        project: &Entity<Project>,
        cx: &'a mut gpui::TestAppContext,
    ) -> (Entity<Workspace>, &'a mut VisualTestContext) {
        cx.update(|cx| cx.set_global(db::AppDatabase::test_new()));
        let (multi_workspace, cx) =
            cx.add_window_view(|window, cx| MultiWorkspace::test_new(project.clone(), window, cx));
        let workspace_id = cx
            .update(|_, cx| workspace::WorkspaceDb::global(cx))
            .next_id()
            .await
            .unwrap();
        let workspace = multi_workspace.update_in(cx, |multi_workspace, window, cx| {
            let app_state = multi_workspace.workspace().read(cx).app_state().clone();
            cx.new(|cx| Workspace::new(Some(workspace_id), project.clone(), app_state, window, cx))
        });
        (workspace, cx)
    }

    async fn serialize_editors(
        workspace: &Entity<Workspace>,
        editors: &[Entity<Editor>],
        cx: &mut VisualTestContext,
    ) {
        let serializations = workspace.update(cx, |workspace, cx| {
            editors
                .iter()
                .zip(1..)
                .map(|(editor, item_id)| {
                    editor
                        .update(cx, |editor, cx| {
                            SerializableItem::serialize(editor, workspace, item_id, false, cx)
                        })
                        .unwrap()
                })
                .collect::<Vec<_>>()
        });
        try_join_all(serializations).await.unwrap();
    }

    async fn restore_serialized_editors(
        workspace: &Entity<Workspace>,
        project: &Entity<Project>,
        count: ItemId,
        cx: &mut VisualTestContext,
    ) -> Vec<Entity<Editor>> {
        let workspace_id = workspace
            .read_with(cx, |workspace, _| workspace.database_id())
            .unwrap();
        let mut editors = Vec::new();
        for item_id in 1..=count {
            editors.push(
                deserialize_editor(
                    item_id,
                    workspace_id,
                    workspace.clone(),
                    project.clone(),
                    cx,
                )
                .await,
            );
        }
        editors
    }

    async fn open_root_buffers(
        project: &Entity<Project>,
        file_names: &[&str],
        cx: &mut VisualTestContext,
    ) -> Vec<Entity<Buffer>> {
        let mut buffers = Vec::new();
        for file_name in file_names {
            let abs_path = PathBuf::from(path!("/root")).join(file_name);
            buffers.push(
                project
                    .update(cx, |project, cx| project.open_local_buffer(abs_path, cx))
                    .await
                    .unwrap(),
            );
        }
        buffers
    }

    async fn remove_root_files(fs: &FakeFs, file_names: &[&str], cx: &mut VisualTestContext) {
        for file_name in file_names {
            fs.remove_file(
                &PathBuf::from(path!("/root")).join(file_name),
                fs::RemoveOptions::default(),
            )
            .await
            .unwrap();
        }
        cx.run_until_parked();
    }

    fn editors_for_buffers(
        project: &Entity<Project>,
        buffers: &[Entity<Buffer>],
        cx: &mut VisualTestContext,
    ) -> Vec<Entity<Editor>> {
        buffers
            .iter()
            .map(|buffer| {
                cx.new_window_entity(|window, cx| {
                    Editor::for_buffer(buffer.clone(), Some(project.clone()), window, cx)
                })
            })
            .collect()
    }

    fn singleton_buffers(
        editors: &[Entity<Editor>],
        cx: &mut VisualTestContext,
    ) -> Vec<Entity<Buffer>> {
        editors
            .iter()
            .map(|editor| {
                editor.read_with(cx, |editor, cx| {
                    editor.buffer().read(cx).as_singleton().unwrap()
                })
            })
            .collect()
    }

    fn buffer_states(
        buffers: &[Entity<Buffer>],
        cx: &mut VisualTestContext,
    ) -> Vec<(String, bool, bool, &'static str, Capability)> {
        buffers
            .iter()
            .map(|buffer| {
                buffer.read_with(cx, |buffer, _| {
                    let disk_state = match buffer.file().map(|file| file.disk_state()) {
                        Some(DiskState::Present { .. }) => "present",
                        Some(DiskState::Deleted) => "deleted",
                        Some(DiskState::New) => "new",
                        Some(DiskState::Historic { .. }) => "historic",
                        None => "none",
                    };
                    buffer_state(
                        &buffer.text(),
                        buffer.is_dirty(),
                        buffer.has_conflict(),
                        disk_state,
                        buffer.capability(),
                    )
                })
            })
            .collect()
    }

    fn buffer_state(
        text: &str,
        dirty: bool,
        conflict: bool,
        disk_state: &'static str,
        capability: Capability,
    ) -> (String, bool, bool, &'static str, Capability) {
        (text.to_string(), dirty, conflict, disk_state, capability)
    }

    async fn save_buffers(
        fs: &FakeFs,
        project: &Entity<Project>,
        buffers: &[Entity<Buffer>],
        untitled_name: &'static str,
        cx: &mut VisualTestContext,
    ) -> Vec<Vec<u8>> {
        let worktree_id = project.read_with(cx, |project, cx| {
            project.worktrees(cx).next().unwrap().read(cx).id()
        });
        let mut saved_bytes = Vec::new();
        for buffer in buffers {
            let has_file = buffer.read_with(cx, |buffer, _| buffer.file().is_some());
            let save = project.update(cx, |project, cx| {
                if has_file {
                    project.save_buffer(buffer.clone(), cx)
                } else {
                    let path = ProjectPath {
                        worktree_id,
                        path: rel_path(untitled_name).into_arc(),
                    };
                    project.save_buffer_as(buffer.clone(), path, cx)
                }
            });
            save.await.unwrap();
            cx.run_until_parked();
            let abs_path = buffer.read_with(cx, |buffer, cx| {
                File::from_dyn(buffer.file()).unwrap().abs_path(cx)
            });
            saved_bytes.push(fs.read_file_sync(abs_path).unwrap());
        }
        saved_bytes
    }

    fn share_with_recording_guest(
        project: &Entity<Project>,
        cx: &mut VisualTestContext,
    ) -> Arc<RecordingGuest> {
        let guest = Arc::new(RecordingGuest::default());
        project.update(cx, |project, cx| {
            project.buffer_store().update(cx, |buffer_store, cx| {
                buffer_store.shared(1, rpc::AnyProtoClient::new(guest.clone()), cx)
            })
        });
        guest
    }

    #[derive(Default)]
    struct RecordingGuest {
        sent: parking_lot::Mutex<Vec<proto::Envelope>>,
        handler_set: parking_lot::Mutex<rpc::ProtoMessageHandlerSet>,
    }

    impl RecordingGuest {
        fn buffer_file_updates(&self) -> Vec<(String, bool, Option<proto::Timestamp>)> {
            self.sent
                .lock()
                .iter()
                .filter_map(|envelope| match &envelope.payload {
                    Some(proto::envelope::Payload::UpdateBufferFile(update)) => {
                        let file = update.file.as_ref()?;
                        Some((file.path.clone(), file.is_deleted, file.mtime))
                    }
                    _ => None,
                })
                .collect()
        }
    }

    impl rpc::ProtoClient for RecordingGuest {
        fn request(
            &self,
            _: proto::Envelope,
            request_type: &'static str,
        ) -> futures::future::BoxFuture<'static, Result<proto::Envelope>> {
            Box::pin(async move { Err(anyhow!("unexpected {request_type} request")) })
        }

        fn send(&self, envelope: proto::Envelope, _: &'static str) -> Result<()> {
            self.sent.lock().push(envelope);
            Ok(())
        }

        fn send_response(&self, _: proto::Envelope, _: &'static str) -> Result<()> {
            Ok(())
        }

        fn message_handler_set(&self) -> &parking_lot::Mutex<rpc::ProtoMessageHandlerSet> {
            &self.handler_set
        }

        fn is_via_collab(&self) -> bool {
            true
        }

        fn has_wsl_interop(&self) -> bool {
            false
        }
    }

    fn restored_states(
        editors: &[Entity<Editor>],
        cx: &mut VisualTestContext,
    ) -> Vec<(String, String, bool, usize)> {
        let mut buffer_ids = Vec::new();
        editors
            .iter()
            .map(|editor| {
                editor.update(cx, |editor, cx| {
                    let buffer_id = editor.buffer().read(cx).as_singleton().unwrap().entity_id();
                    let buffer_index = buffer_ids
                        .iter()
                        .position(|id| *id == buffer_id)
                        .unwrap_or_else(|| {
                            buffer_ids.push(buffer_id);
                            buffer_ids.len() - 1
                        });
                    (
                        editor.text(cx),
                        editor.tab_content_text(0, cx).to_string(),
                        editor.is_dirty(cx),
                        buffer_index,
                    )
                })
            })
            .collect()
    }
}
