use std::{
    any::Any,
    fmt,
    rc::{self, Rc},
};

use anyhow::{Context as _, Result};
use gpui::{
    App, AppContext as _, AsyncWindowContext, Context, EventEmitter, FocusHandle, Focusable,
    IntoElement, PromptLevel, SharedString, Task, WeakEntity, Window,
};
use itertools::Itertools as _;
use ui::{
    Button, ButtonCommon, ButtonStyle, Clickable, Disableable, Icon, IconName, InteractiveElement,
    Label, LabelCommon, LabelSize, ParentElement, Render, Styled as _, h_flex, v_flex,
};

use crate::{
    Item, Pane, SerializableItemRegistry, Workspace, WorkspaceId,
    item::{ItemHandle, SerializableItemHandle},
    persistence::model::ItemId,
};

#[derive(Debug)]
pub struct RestorationFailure {
    pub label: SharedString,
    pub tooltip: Option<SharedString>,
}

impl fmt::Display for RestorationFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "failed to restore {}", self.label)
    }
}

pub struct UnrestoredItemView {
    kind: SharedString,
    pub(crate) item_id: ItemId,
    workspace_id: WorkspaceId,
    workspace: WeakEntity<Workspace>,
    label: SharedString,
    tooltip: Option<SharedString>,
    error: SharedString,
    focus_handle: FocusHandle,
    pending: Option<Task<()>>,
    close_holds: Vec<rc::Weak<()>>,
}

pub(crate) struct UnrestoredItemsHold {
    _hold: Rc<()>,
}

impl UnrestoredItemView {
    pub fn new(
        kind: SharedString,
        item_id: ItemId,
        workspace_id: WorkspaceId,
        workspace: WeakEntity<Workspace>,
        error: &anyhow::Error,
        cx: &mut App,
    ) -> Self {
        let failure = error.downcast_ref::<RestorationFailure>();
        Self {
            label: failure
                .map(|failure| failure.label.clone())
                .unwrap_or_else(|| kind.clone()),
            tooltip: failure.and_then(|failure| failure.tooltip.clone()),
            error: error.root_cause().to_string().into(),
            kind,
            item_id,
            workspace_id,
            workspace,
            focus_handle: cx.focus_handle(),
            pending: None,
            close_holds: Vec::new(),
        }
    }

    pub fn kind(&self) -> &str {
        &self.kind
    }

    pub fn item_id(&self) -> ItemId {
        self.item_id
    }

    pub(crate) fn can_be_placed_in(&self, pane: &Pane) -> bool {
        pane.workspace.entity_id() == self.workspace.entity_id()
            && pane.restorable_items().includes(&self.kind)
    }

    pub(crate) fn try_again(&mut self, window: &mut Window, cx: &mut Context<Self>) {
        if self.held_for_close() {
            return;
        }
        let Some(workspace) = self.workspace.upgrade() else {
            return;
        };
        let project = workspace.read(cx).project().clone();
        let restore = SerializableItemRegistry::deserialize(
            &self.kind,
            project,
            self.workspace.clone(),
            self.workspace_id,
            self.item_id,
            window,
            cx,
        );
        self.pending = Some(cx.spawn_in(window, async move |this, cx| {
            let replaced = match restore.await {
                Ok(item) => Self::replace(&this, item, cx).await,
                Err(error) => Err(error),
            };
            this.update(cx, |this, cx| {
                this.pending = None;
                if let Err(error) = replaced {
                    this.error = error.root_cause().to_string().into();
                }
                cx.notify();
            })
            .ok();
        }));
        cx.notify();
    }

    async fn replace(
        this: &WeakEntity<Self>,
        item: Box<dyn ItemHandle>,
        cx: &mut AsyncWindowContext,
    ) -> Result<()> {
        let placeholder_id = this.entity_id();
        let workspace = this.read_with(cx, |this, _| this.workspace.clone())?;
        let pane = workspace
            .read_with(cx, |workspace, _| {
                workspace.pane_for_item_id(placeholder_id)
            })?
            .context("the tab is no longer open")?;
        pane.update_in(cx, |pane, window, cx| {
            pane.replace_item(placeholder_id, item, window, cx)
        })?
    }

    fn held_for_close(&self) -> bool {
        self.close_holds.iter().any(|hold| hold.strong_count() > 0)
    }

    fn hold_for_close(&mut self, hold: &Rc<()>, cx: &mut Context<Self>) {
        self.close_holds.retain(|hold| hold.strong_count() > 0);
        self.close_holds.push(Rc::downgrade(hold));
        if self.pending.take().is_some() {
            cx.notify();
        }
    }
}

impl Item for UnrestoredItemView {
    type Event = ();

    fn tab_content_text(&self, _detail: usize, _cx: &App) -> SharedString {
        self.label.clone()
    }

    fn tab_tooltip_text(&self, _cx: &App) -> Option<SharedString> {
        self.tooltip.clone()
    }

    fn tab_icon(&self, _window: &Window, _cx: &App) -> Option<Icon> {
        Some(Icon::new(IconName::Warning))
    }

    fn is_dirty(&self, _: &App) -> bool {
        true
    }
}

impl EventEmitter<()> for UnrestoredItemView {}

impl Focusable for UnrestoredItemView {
    fn focus_handle(&self, _: &App) -> FocusHandle {
        self.focus_handle.clone()
    }
}

impl Render for UnrestoredItemView {
    fn render(&mut self, _window: &mut Window, cx: &mut Context<Self>) -> impl IntoElement {
        let pending = self.pending.is_some();
        v_flex()
            .size_full()
            .track_focus(&self.focus_handle(cx))
            .justify_center()
            .overflow_hidden()
            .key_context("UnrestoredItem")
            .child(
                h_flex().size_full().justify_center().child(
                    v_flex()
                        .justify_center()
                        .gap_2()
                        .child(
                            h_flex()
                                .justify_center()
                                .child(format!("Could not restore {}", self.label)),
                        )
                        .child(
                            h_flex()
                                .justify_center()
                                .child(Label::new(self.error.clone()).size(LabelSize::Small)),
                        )
                        .child(
                            h_flex().justify_center().child(
                                Button::new("try-again", "Try Again")
                                    .style(ButtonStyle::Outlined)
                                    .disabled(pending)
                                    .on_click(cx.listener(|this, _, window, cx| {
                                        this.try_again(window, cx)
                                    })),
                            ),
                        ),
                ),
            )
    }
}

impl SerializableItemHandle for gpui::Entity<UnrestoredItemView> {
    fn serialized_item_kind(&self, cx: &App) -> SharedString {
        self.read(cx).kind.clone()
    }

    fn persistent_item_id(&self, cx: &mut App) -> ItemId {
        self.read(cx).item_id
    }

    fn serialize(
        &self,
        _workspace: &mut Workspace,
        _closing: bool,
        _cx: &mut App,
    ) -> Option<Task<Result<()>>> {
        Some(Task::ready(Ok(())))
    }

    fn should_serialize(&self, _event: &dyn Any, _cx: &App) -> bool {
        false
    }
}

pub(crate) fn hold_unrestored_items<'a>(
    items: impl IntoIterator<Item = &'a Box<dyn ItemHandle>>,
    cx: &mut App,
) -> UnrestoredItemsHold {
    let hold = Rc::new(());
    for unrestored in items
        .into_iter()
        .filter_map(|item| item.downcast::<UnrestoredItemView>())
    {
        unrestored.update(cx, |unrestored, cx| unrestored.hold_for_close(&hold, cx));
    }
    UnrestoredItemsHold { _hold: hold }
}

pub(crate) fn unrestored_labels<'a>(
    items: impl IntoIterator<Item = &'a Box<dyn ItemHandle>>,
    cx: &App,
) -> Vec<SharedString> {
    items
        .into_iter()
        .filter_map(|item| item.downcast::<UnrestoredItemView>())
        .map(|unrestored| unrestored.read(cx).label.clone())
        .collect()
}

pub(crate) fn confirm_discarding_restoring_items(
    count: usize,
    window: &mut Window,
    cx: &mut App,
) -> Task<bool> {
    let message = if count == 1 {
        "A tab is still being restored. Closing now discards its saved state.".to_string()
    } else {
        format!("{count} tabs are still being restored. Closing now discards their saved state.")
    };
    let answer = window.prompt(
        PromptLevel::Warning,
        &message,
        None,
        &["Discard", "Cancel"],
        cx,
    );
    cx.background_spawn(async move { answer.await.ok() == Some(0) })
}

pub(crate) fn confirm_discarding_unrestored(
    labels: &[SharedString],
    window: &mut Window,
    cx: &mut App,
) -> Task<bool> {
    let (message, detail) = match labels {
        [] => return Task::ready(true),
        [label] => (
            format!("{label} could not be restored. Closing it discards its saved state."),
            None,
        ),
        labels => (
            "These tabs could not be restored. Closing them discards their saved state."
                .to_string(),
            Some(labels.iter().join("\n")),
        ),
    };
    let answer = window.prompt(
        PromptLevel::Warning,
        &message,
        detail.as_deref(),
        &["Discard", "Cancel"],
        cx,
    );
    cx.background_spawn(async move { answer.await.ok() == Some(0) })
}
