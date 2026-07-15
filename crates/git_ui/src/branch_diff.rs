use crate::{
    branch_picker,
    diff_multibuffer::{DiffFileEntry, DiffMultibuffer},
    git_status_icon,
    project_diff::{
        self, CompareWithBranch, DeployBranchDiff, ReviewDiff, render_send_review_to_agent_button,
    },
};
use agent_settings::AgentSettings;
use anyhow::{Context as _, Result, anyhow};
use collections::{BTreeMap, HashMap};
use editor::{
    Addon, Editor, EditorEvent, RestoreOnlyDiffHunkDelegate, SplittableEditor,
    actions::SendReviewToAgent,
};
use file_icons::FileIcons;
use git::{repository::DiffType, status::FileStatus};
use gpui::{
    Action, AnyElement, App, AppContext as _, ClickEvent, DragMoveEvent, Entity, EventEmitter,
    FocusHandle, Focusable, MouseButton, Pixels, Render, ScrollStrategy, SharedString,
    Subscription, Task, UniformListScrollHandle, WeakEntity, actions, deferred, px, uniform_list,
};
use language::{BufferId, Capability};
use project::{
    Project, ProjectPath,
    git_store::{
        Repository,
        diff_buffer_list::{self, DiffBase},
    },
};
use settings::Settings;
use std::{
    any::{Any, TypeId},
    ops::Range,
    rc::Rc,
    sync::Arc,
};
use ui::{
    DiffStat, Divider, IndentGuideColors, ListItem, ListItemSpacing, PopoverMenu, Tooltip,
    WithScrollbar, prelude::*,
};
use workspace::{
    ItemHandle, ItemNavHistory, SerializableItem, ToolbarItemEvent, ToolbarItemLocation,
    ToolbarItemView, Workspace,
    item::{Item, ItemEvent, SaveOptions, TabContentParams},
    notifications::NotifyTaskExt,
    searchable::SearchableItemHandle,
};
use zed_actions::agent::ReviewBranchDiff;

const BRANCH_DIFF_TREE_DEFAULT_WIDTH: Pixels = px(240.);
const BRANCH_DIFF_TREE_MIN_WIDTH: Pixels = px(160.);
const BRANCH_DIFF_EDITOR_MIN_WIDTH: Pixels = px(240.);
const BRANCH_DIFF_TREE_RESIZE_HANDLE_WIDTH: Pixels = px(8.);
const TREE_INDENT: f32 = 20.;

struct DraggedBranchDiffTreeResizeHandle;

fn clamped_branch_diff_tree_width(requested: Pixels, available: Pixels) -> Pixels {
    let max_width = (available - BRANCH_DIFF_EDITOR_MIN_WIDTH).max(BRANCH_DIFF_TREE_MIN_WIDTH);
    requested.clamp(BRANCH_DIFF_TREE_MIN_WIDTH, max_width)
}

actions!(
    git,
    [
        /// Toggles the file tree in the branch diff view.
        ToggleBranchDiffTree
    ]
);

/// The workspace item for a branch (merge-base) diff: "Changes since {branch}".
/// It wraps a single [`DiffMultibuffer`] over [`DiffBase::Merge`] and delegates
/// the [`Item`] surface to it. The merge base can be changed in place via the
/// [`BranchDiffToolbar`]'s branch picker, which reloads without reconfiguring
/// the editor (the merge styling is identical for every base ref).
pub struct BranchDiff {
    diff: Entity<DiffMultibuffer>,
    project: Entity<Project>,
    workspace: WeakEntity<Workspace>,
    show_tree: bool,
    tree_width: Pixels,
    tree_expanded_dirs: HashMap<git::repository::RepoPath, bool>,
    tree_scroll_handle: UniformListScrollHandle,
    _subscriptions: Subscription,
}

enum BranchDiffTreeEntry {
    Directory(BranchDiffDirectoryEntry),
    File(BranchDiffTreeFileEntry),
}

impl BranchDiffTreeEntry {
    fn depth(&self) -> usize {
        match self {
            Self::Directory(entry) => entry.depth,
            Self::File(entry) => entry.depth,
        }
    }
}

struct BranchDiffTreeFileEntry {
    entry: DiffFileEntry,
    depth: usize,
}

struct BranchDiffDirectoryEntry {
    path: git::repository::RepoPath,
    name: SharedString,
    depth: usize,
    expanded: bool,
}

#[derive(Default)]
struct BranchDiffTreeNode {
    name: SharedString,
    path: Option<git::repository::RepoPath>,
    children: BTreeMap<SharedString, BranchDiffTreeNode>,
    files: Vec<DiffFileEntry>,
}

fn build_branch_diff_tree_entries(
    mut files: Vec<DiffFileEntry>,
    expanded_dirs: &HashMap<git::repository::RepoPath, bool>,
) -> Vec<BranchDiffTreeEntry> {
    files.sort_by(|a, b| a.repo_path.cmp(&b.repo_path));

    let mut root = BranchDiffTreeNode::default();
    for file in files {
        let components: Vec<&str> = file.repo_path.components().collect();
        if components.is_empty() {
            root.files.push(file);
            continue;
        }

        let mut current = &mut root;
        let mut current_path = String::new();
        for (ix, component) in components.iter().enumerate() {
            if ix == components.len() - 1 {
                current.files.push(file.clone());
            } else {
                if !current_path.is_empty() {
                    current_path.push('/');
                }
                current_path.push_str(component);

                let Ok(path) = git::repository::RepoPath::new(&current_path) else {
                    continue;
                };
                let name = SharedString::from(component.to_string());
                current =
                    current
                        .children
                        .entry(name.clone())
                        .or_insert_with(|| BranchDiffTreeNode {
                            name,
                            path: Some(path),
                            ..Default::default()
                        });
            }
        }
    }

    flatten_branch_diff_tree(&root, 0, expanded_dirs)
}

fn flatten_branch_diff_tree(
    node: &BranchDiffTreeNode,
    depth: usize,
    expanded_dirs: &HashMap<git::repository::RepoPath, bool>,
) -> Vec<BranchDiffTreeEntry> {
    let mut entries = Vec::new();
    for child in node.children.values() {
        let (terminal, name) = compact_branch_diff_directory_chain(child);
        let Some(path) = terminal.path.clone().or_else(|| child.path.clone()) else {
            continue;
        };
        let expanded = *expanded_dirs.get(&path).unwrap_or(&true);
        let child_entries = flatten_branch_diff_tree(terminal, depth + 1, expanded_dirs);

        entries.push(BranchDiffTreeEntry::Directory(BranchDiffDirectoryEntry {
            path,
            name,
            depth,
            expanded,
        }));
        if expanded {
            entries.extend(child_entries);
        }
    }
    entries.extend(
        node.files
            .iter()
            .cloned()
            .map(|entry| BranchDiffTreeEntry::File(BranchDiffTreeFileEntry { entry, depth })),
    );
    entries
}

fn compact_branch_diff_directory_chain(
    mut node: &BranchDiffTreeNode,
) -> (&BranchDiffTreeNode, SharedString) {
    let mut parts = vec![node.name.clone()];
    while node.files.is_empty() && node.children.len() == 1 {
        let Some(child) = node.children.values().next() else {
            break;
        };
        if child.path.is_none() {
            break;
        }
        parts.push(child.name.clone());
        node = child;
    }
    (node, SharedString::from(parts.join("/")))
}

struct BranchDiffAddon {
    branch_diff: Entity<diff_buffer_list::DiffBufferList>,
}

impl Addon for BranchDiffAddon {
    fn to_any(&self) -> &dyn std::any::Any {
        self
    }

    fn override_status_for_buffer_id(&self, buffer_id: BufferId, cx: &App) -> Option<FileStatus> {
        self.branch_diff
            .read(cx)
            .status_for_buffer_id(buffer_id, cx)
    }
}

impl BranchDiff {
    pub(crate) fn register(workspace: &mut Workspace, cx: &mut Context<Workspace>) {
        workspace.register_action(Self::deploy_branch_diff);
        workspace.register_action(Self::compare_with_branch);
        workspace::register_serializable_item::<Self>(cx);
    }

    fn deploy_branch_diff(
        workspace: &mut Workspace,
        _: &DeployBranchDiff,
        window: &mut Window,
        cx: &mut Context<Workspace>,
    ) {
        telemetry::event!("Git Branch Diff Opened");
        let project = workspace.project().clone();
        let Some(intended_repo) = project.read(cx).active_repository(cx) else {
            let workspace = cx.entity().downgrade();
            window
                .spawn(cx, async |_cx| {
                    let result: Result<()> = Err(anyhow!("No active repository"));
                    result
                })
                .detach_and_notify_err(workspace, window, cx);
            return;
        };

        let default_branch = intended_repo.update(cx, |repo, _| repo.default_branch(true));
        let workspace = cx.entity();
        let workspace_weak = workspace.downgrade();
        window
            .spawn(cx, async move |cx| {
                let base_ref = default_branch
                    .await??
                    .context("Could not determine default branch")?;

                workspace.update_in(cx, |workspace, window, cx| {
                    Self::deploy_branch_diff_with_base_ref(
                        workspace,
                        project,
                        intended_repo,
                        base_ref,
                        window,
                        cx,
                    );
                })?;

                anyhow::Ok(())
            })
            .detach_and_notify_err(workspace_weak, window, cx);
    }

    fn compare_with_branch(
        workspace: &mut Workspace,
        _: &CompareWithBranch,
        window: &mut Window,
        cx: &mut Context<Workspace>,
    ) {
        let project = workspace.project().clone();
        let Some(repository) = project.read(cx).active_repository(cx) else {
            let workspace = cx.entity().downgrade();
            window
                .spawn(cx, async |_cx| {
                    let result: Result<()> = Err(anyhow!("No active repository"));
                    result
                })
                .detach_and_notify_err(workspace, window, cx);
            return;
        };
        let selected_branch = workspace.active_item_as::<Self>(cx).and_then(|item| {
            match item.read(cx).diff_base(cx) {
                DiffBase::Merge { base_ref } => Some(base_ref.clone()),
                DiffBase::Head | DiffBase::Index | DiffBase::Staged => None,
            }
        });
        let workspace_handle = workspace.weak_handle();
        let on_select = Arc::new({
            let repository = repository.clone();
            let workspace = workspace_handle.clone();
            move |branch: git::repository::Branch, window: &mut Window, cx: &mut App| {
                let base_ref: SharedString = branch.name().to_owned().into();
                workspace
                    .update(cx, |workspace, cx| {
                        Self::deploy_branch_diff_with_base_ref(
                            workspace,
                            project.clone(),
                            repository.clone(),
                            base_ref,
                            window,
                            cx,
                        );
                    })
                    .ok();
            }
        });

        workspace.toggle_modal(window, cx, |window, cx| {
            branch_picker::select_modal(
                workspace_handle,
                Some(repository),
                selected_branch,
                on_select,
                window,
                cx,
            )
        });
    }

    fn deploy_branch_diff_with_base_ref(
        workspace: &mut Workspace,
        project: Entity<Project>,
        intended_repo: Entity<Repository>,
        base_ref: SharedString,
        window: &mut Window,
        cx: &mut Context<Workspace>,
    ) {
        let existing = workspace.items_of_type::<Self>(cx).find(|item| {
            let item = item.read(cx);
            matches!(
                item.diff_base(cx),
                DiffBase::Merge { base_ref: existing_base_ref } if existing_base_ref == &base_ref
            )
        });
        if let Some(existing) = existing {
            workspace.activate_item(&existing, true, true, window, cx);

            let needs_switch = existing.read(cx).repo(cx).map_or(true, |current| {
                current.read(cx).id != intended_repo.read(cx).id
            });

            if needs_switch {
                existing.update(cx, |branch_diff, cx| {
                    branch_diff.set_repo(Some(intended_repo), cx);
                });
            }

            return;
        }

        let workspace = cx.entity();
        let workspace_weak = workspace.downgrade();
        window
            .spawn(cx, async move |cx| {
                let this = cx
                    .update(|window, cx| {
                        Self::new_with_branch_base(
                            project,
                            workspace.clone(),
                            base_ref,
                            intended_repo,
                            window,
                            cx,
                        )
                    })?
                    .await?;
                workspace
                    .update_in(cx, |workspace, window, cx| {
                        workspace.add_item_to_active_pane(Box::new(this), None, true, window, cx);
                    })
                    .ok();
                anyhow::Ok(())
            })
            .detach_and_notify_err(workspace_weak, window, cx);
    }

    #[cfg(any(test, feature = "test-support"))]
    pub fn new_with_default_branch(
        project: Entity<Project>,
        workspace: Entity<Workspace>,
        window: &mut Window,
        cx: &mut App,
    ) -> Task<Result<Entity<Self>>> {
        let Some(repo) = project.read(cx).git_store().read(cx).active_repository() else {
            return Task::ready(Err(anyhow!("No active repository")));
        };
        let main_branch = repo.update(cx, |repo, _| repo.default_branch(true));
        window.spawn(cx, async move |cx| {
            let base_ref = main_branch
                .await??
                .context("Could not determine default branch")?;
            cx.update(|window, cx| {
                cx.new(|cx| {
                    Self::new_with_base_ref(project, workspace, base_ref, Some(repo), window, cx)
                })
            })
        })
    }

    pub(crate) fn new_with_branch_base(
        project: Entity<Project>,
        workspace: Entity<Workspace>,
        base_ref: SharedString,
        repo: Entity<Repository>,
        window: &mut Window,
        cx: &mut App,
    ) -> Task<Result<Entity<Self>>> {
        window.spawn(cx, async move |cx| {
            cx.update(|window, cx| {
                cx.new(|cx| {
                    Self::new_with_base_ref(project, workspace, base_ref, Some(repo), window, cx)
                })
            })
        })
    }

    pub(crate) fn new_with_base_ref(
        project: Entity<Project>,
        workspace: Entity<Workspace>,
        base_ref: SharedString,
        repo: Option<Entity<Repository>>,
        window: &mut Window,
        cx: &mut Context<Self>,
    ) -> Self {
        let branch_diff = cx.new(|cx| {
            let mut branch_diff = diff_buffer_list::DiffBufferList::new(
                DiffBase::Merge { base_ref },
                project.clone(),
                window,
                cx,
            );
            if repo.is_some() {
                branch_diff.set_repo(repo, cx);
            }
            branch_diff
        });
        let branch_diff_for_addon = branch_diff.clone();
        let diff = cx.new(|cx| {
            DiffMultibuffer::new(
                branch_diff,
                Capability::ReadWrite,
                "No changes",
                move |editor, cx| {
                    editor.set_diff_hunk_delegate(Some(Arc::new(RestoreOnlyDiffHunkDelegate)), cx);
                    editor.rhs_editor().update(cx, move |rhs_editor, _cx| {
                        rhs_editor.set_read_only(false);
                        rhs_editor.register_addon(BranchDiffAddon {
                            branch_diff: branch_diff_for_addon,
                        });
                    });
                },
                project.clone(),
                workspace.clone(),
                window,
                cx,
            )
        });
        Self::from_diff(diff, project, workspace, cx)
    }

    fn from_diff(
        diff: Entity<DiffMultibuffer>,
        project: Entity<Project>,
        workspace: Entity<Workspace>,
        cx: &mut Context<Self>,
    ) -> Self {
        let diff_event_subscription = cx.subscribe(&diff, |_, _, event: &EditorEvent, cx| {
            cx.emit(event.clone());
            cx.notify();
        });
        let diff_observation = cx.observe(&diff, |_, _, cx| cx.notify());
        Self {
            diff,
            project,
            workspace: workspace.downgrade(),
            show_tree: true,
            tree_width: BRANCH_DIFF_TREE_DEFAULT_WIDTH,
            tree_expanded_dirs: HashMap::default(),
            tree_scroll_handle: UniformListScrollHandle::new(),
            _subscriptions: Subscription::join(diff_event_subscription, diff_observation),
        }
    }

    fn toggle_tree(&mut self, _: &ToggleBranchDiffTree, _: &mut Window, cx: &mut Context<Self>) {
        self.show_tree = !self.show_tree;
        self.tree_scroll_handle
            .scroll_to_item(0, ScrollStrategy::Top);
        cx.notify();
    }

    fn active_repo_path(&self, cx: &App) -> Option<git::repository::RepoPath> {
        let project_path = self.diff.read(cx).active_project_path(cx)?;
        let repo = self.diff.read(cx).repo(cx)?;
        repo.read(cx).project_path_to_repo_path(&project_path, cx)
    }

    fn render_tree_entry(
        &self,
        ix: usize,
        entry: &BranchDiffTreeEntry,
        active_path: Option<&git::repository::RepoPath>,
        cx: &Context<Self>,
    ) -> AnyElement {
        match entry {
            BranchDiffTreeEntry::Directory(entry) => {
                let path = entry.path.clone();
                let expanded = entry.expanded;
                let folder_icon =
                    FileIcons::get_folder_icon(expanded, entry.path.as_std_path(), cx)
                        .map(|icon| {
                            Icon::from_path(icon)
                                .size(IconSize::Small)
                                .color(Color::Muted)
                        })
                        .unwrap_or_else(|| {
                            Icon::new(if expanded {
                                IconName::FolderOpen
                            } else {
                                IconName::Folder
                            })
                            .size(IconSize::Small)
                            .color(Color::Muted)
                        });

                ListItem::new(("branch-diff-directory", ix))
                    .spacing(ListItemSpacing::Sparse)
                    .indent_level(entry.depth)
                    .indent_step_size(px(TREE_INDENT))
                    .start_slot(folder_icon)
                    .child(
                        Label::new(entry.name.clone())
                            .size(LabelSize::Small)
                            .color(Color::Muted)
                            .truncate(),
                    )
                    .tooltip({
                        let name = entry.name.clone();
                        move |_, cx| Tooltip::with_meta("Toggle Folder", None, name.clone(), cx)
                    })
                    .on_click(cx.listener(move |this, _, _, cx| {
                        this.tree_expanded_dirs.insert(path.clone(), !expanded);
                        cx.notify();
                    }))
                    .into_any_element()
            }
            BranchDiffTreeEntry::File(entry) => {
                let repo_path = entry.entry.repo_path.clone();
                let status = entry.entry.status;
                let path_key = entry.entry.path_key.clone();
                let selected = active_path == Some(&repo_path);
                let file_name: SharedString = repo_path
                    .file_name()
                    .map(|name| name.to_string())
                    .unwrap_or_default()
                    .into();
                let full_path: SharedString = repo_path.as_unix_str().to_string().into();

                ListItem::new(("branch-diff-file", ix))
                    .spacing(ListItemSpacing::Sparse)
                    .indent_level(entry.depth)
                    .indent_step_size(px(TREE_INDENT))
                    .toggle_state(selected)
                    .start_slot(git_status_icon(status))
                    .child(Label::new(file_name).size(LabelSize::Small).truncate())
                    .tooltip(move |_, cx| {
                        Tooltip::with_meta("View Changes", None, full_path.clone(), cx)
                    })
                    .on_click(cx.listener(move |this, _, window, cx| {
                        this.diff.update(cx, |diff, cx| {
                            diff.move_to_path(path_key.clone(), window, cx);
                            diff.editor()
                                .read(cx)
                                .rhs_editor()
                                .read(cx)
                                .focus_handle(cx)
                                .focus(window, cx);
                        });
                    }))
                    .into_any_element()
            }
        }
    }

    fn render_tree(&self, window: &mut Window, cx: &mut Context<Self>) -> AnyElement {
        let files = self.diff.read(cx).file_entries().to_vec();
        let file_count = files.len();
        let entries = Rc::new(build_branch_diff_tree_entries(
            files,
            &self.tree_expanded_dirs,
        ));
        let active_path = self.active_repo_path(cx);
        let list_entries = entries.clone();
        let indent_entries = entries.clone();

        div()
            .id("branch-diff-tree-container")
            .relative()
            .w(self.tree_width)
            .min_w(BRANCH_DIFF_TREE_MIN_WIDTH)
            .h_full()
            .flex_shrink_0()
            .child(
                v_flex()
                    .size_full()
                    .overflow_hidden()
                    .bg(cx.theme().colors().editor_background)
                    .border_r_1()
                    .border_color(cx.theme().colors().border_variant)
                    .child(
                        h_flex()
                            .h_8()
                            .px_2()
                            .justify_between()
                            .border_b_1()
                            .border_color(cx.theme().colors().border_variant)
                            .child(Label::new("Files").size(LabelSize::Small))
                            .child(
                                Label::new(file_count.to_string())
                                    .size(LabelSize::XSmall)
                                    .color(Color::Muted),
                            ),
                    )
                    .child(
                        div()
                            .flex_1()
                            .min_h_0()
                            .relative()
                            .child(
                                uniform_list(
                                    "branch-diff-tree-entries",
                                    entries.len(),
                                    cx.processor(move |this, range: Range<usize>, _window, cx| {
                                        range
                                            .filter_map(|ix| {
                                                list_entries.get(ix).map(|entry| {
                                                    this.render_tree_entry(
                                                        ix,
                                                        entry,
                                                        active_path.as_ref(),
                                                        cx,
                                                    )
                                                })
                                            })
                                            .collect()
                                    }),
                                )
                                .with_decoration(
                                    ui::indent_guides(
                                        px(TREE_INDENT),
                                        IndentGuideColors::panel(cx),
                                    )
                                    .with_left_offset(
                                        ui::LIST_ITEM_INDENT_GUIDE_LEFT_OFFSET - px(2.),
                                    )
                                    .with_compute_indents_fn(
                                        cx.entity(),
                                        move |_, range, _window, _cx| {
                                            range
                                                .map(|ix| {
                                                    indent_entries
                                                        .get(ix)
                                                        .map_or(0, BranchDiffTreeEntry::depth)
                                                })
                                                .collect()
                                        },
                                    ),
                                )
                                .size_full()
                                .track_scroll(&self.tree_scroll_handle),
                            )
                            .vertical_scrollbar_for(&self.tree_scroll_handle, window, cx),
                    ),
            )
            .child(deferred(
                div()
                    .id("branch-diff-tree-resize-handle")
                    .absolute()
                    .right(-BRANCH_DIFF_TREE_RESIZE_HANDLE_WIDTH / 2.)
                    .top_0()
                    .h_full()
                    .w(BRANCH_DIFF_TREE_RESIZE_HANDLE_WIDTH)
                    .cursor_col_resize()
                    .block_mouse_except_scroll()
                    .on_mouse_down(MouseButton::Left, |_, _, cx| cx.stop_propagation())
                    .on_click(cx.listener(|this, event: &ClickEvent, _, cx| {
                        if event.click_count() >= 2 {
                            this.tree_width = BRANCH_DIFF_TREE_DEFAULT_WIDTH;
                            cx.notify();
                        }
                        cx.stop_propagation();
                    }))
                    .on_drag(DraggedBranchDiffTreeResizeHandle, |_, _, _, cx| {
                        cx.new(|_| gpui::Empty)
                    }),
            ))
            .into_any_element()
    }

    pub(crate) fn diff_base<'a>(&'a self, cx: &'a App) -> &'a DiffBase {
        self.diff.read(cx).diff_base(cx)
    }

    pub(crate) fn repo(&self, cx: &App) -> Option<Entity<Repository>> {
        self.diff.read(cx).repo(cx)
    }

    pub(crate) fn set_repo(&mut self, repo: Option<Entity<Repository>>, cx: &mut Context<Self>) {
        self.diff.update(cx, |diff, cx| diff.set_repo(repo, cx));
    }

    fn set_merge_base(&mut self, base_ref: SharedString, cx: &mut Context<Self>) {
        self.diff.update(cx, |diff, cx| {
            diff.branch_diff().update(cx, |branch_diff, cx| {
                branch_diff.set_diff_base(DiffBase::Merge { base_ref }, cx);
            });
        });
    }

    fn review_diff(&mut self, _: &ReviewDiff, window: &mut Window, cx: &mut Context<Self>) {
        let DiffBase::Merge { base_ref } = self.diff_base(cx).clone() else {
            return;
        };
        let Some(repo) = self.repo(cx) else {
            return;
        };

        let diff_receiver = repo.update(cx, |repo, cx| {
            repo.diff(
                DiffType::MergeBase {
                    base_ref: base_ref.clone(),
                },
                cx,
            )
        });

        let workspace = self.workspace.clone();
        window
            .spawn(cx, {
                let workspace = workspace.clone();
                async move |cx| {
                    let diff_text = diff_receiver.await??;

                    if let Some(workspace) = workspace.upgrade() {
                        workspace.update_in(cx, |_workspace, window, cx| {
                            window.dispatch_action(
                                ReviewBranchDiff {
                                    diff_text: diff_text.into(),
                                    base_ref,
                                }
                                .boxed_clone(),
                                cx,
                            );
                        })?;
                    }

                    anyhow::Ok(())
                }
            })
            .detach_and_notify_err(workspace, window, cx);
    }

    #[cfg(any(test, feature = "test-support"))]
    pub fn editor(&self, cx: &App) -> Entity<SplittableEditor> {
        self.diff.read(cx).editor().clone()
    }
}

impl EventEmitter<EditorEvent> for BranchDiff {}

impl Focusable for BranchDiff {
    fn focus_handle(&self, cx: &App) -> FocusHandle {
        self.diff.read(cx).focus_handle(cx)
    }
}

impl Item for BranchDiff {
    type Event = EditorEvent;

    fn tab_icon(&self, _window: &Window, _cx: &App) -> Option<Icon> {
        Some(Icon::new(IconName::GitBranch).color(Color::Muted))
    }

    fn to_item_events(event: &EditorEvent, f: &mut dyn FnMut(ItemEvent)) {
        Editor::to_item_events(event, f)
    }

    fn deactivated(&mut self, window: &mut Window, cx: &mut Context<Self>) {
        self.diff
            .update(cx, |diff, cx| diff.deactivated(window, cx));
    }

    fn navigate(
        &mut self,
        data: Arc<dyn Any + Send>,
        window: &mut Window,
        cx: &mut Context<Self>,
    ) -> bool {
        self.diff
            .update(cx, |diff, cx| diff.navigate(data, window, cx))
    }

    fn tab_tooltip_text(&self, cx: &App) -> Option<SharedString> {
        Some(self.tab_content_text(0, cx))
    }

    fn tab_content(&self, params: TabContentParams, _window: &Window, cx: &App) -> AnyElement {
        Label::new(self.tab_content_text(0, cx))
            .color(if params.selected {
                Color::Default
            } else {
                Color::Muted
            })
            .into_any_element()
    }

    fn tab_content_text(&self, _detail: usize, cx: &App) -> SharedString {
        match self.diff_base(cx) {
            DiffBase::Merge { base_ref } => format!("Changes since {}", base_ref).into(),
            DiffBase::Head | DiffBase::Index | DiffBase::Staged => "Changes".into(),
        }
    }

    fn telemetry_event_text(&self) -> Option<&'static str> {
        Some("Branch Diff Opened")
    }

    fn as_searchable(&self, _: &Entity<Self>, cx: &App) -> Option<Box<dyn SearchableItemHandle>> {
        Some(Box::new(self.diff.read(cx).editor().clone()))
    }

    fn for_each_project_item(
        &self,
        cx: &App,
        f: &mut dyn FnMut(gpui::EntityId, &dyn project::ProjectItem),
    ) {
        self.diff.read(cx).for_each_project_item(cx, f);
    }

    fn active_project_path(&self, cx: &App) -> Option<ProjectPath> {
        self.diff.read(cx).active_project_path(cx)
    }

    fn set_nav_history(
        &mut self,
        nav_history: ItemNavHistory,
        _: &mut Window,
        cx: &mut Context<Self>,
    ) {
        self.diff
            .update(cx, |diff, cx| diff.set_nav_history(nav_history, cx));
    }

    fn can_split(&self) -> bool {
        true
    }

    fn clone_on_split(
        &self,
        _workspace_id: Option<workspace::WorkspaceId>,
        window: &mut Window,
        cx: &mut Context<Self>,
    ) -> Task<Option<Entity<Self>>>
    where
        Self: Sized,
    {
        let Some(workspace) = self.workspace.upgrade() else {
            return Task::ready(None);
        };
        let DiffBase::Merge { base_ref } = self.diff_base(cx).clone() else {
            return Task::ready(None);
        };
        let repo = self.repo(cx);
        let project = self.project.clone();
        Task::ready(Some(cx.new(|cx| {
            Self::new_with_base_ref(project, workspace, base_ref, repo, window, cx)
        })))
    }

    fn is_dirty(&self, cx: &App) -> bool {
        self.diff.read(cx).is_dirty(cx)
    }

    fn has_conflict(&self, cx: &App) -> bool {
        self.diff.read(cx).has_conflict(cx)
    }

    fn can_save(&self, _cx: &App) -> bool {
        true
    }

    fn save(
        &mut self,
        options: SaveOptions,
        project: Entity<Project>,
        window: &mut Window,
        cx: &mut Context<Self>,
    ) -> Task<Result<()>> {
        self.diff
            .update(cx, |diff, cx| diff.save(options, project, window, cx))
    }

    fn save_as(
        &mut self,
        _: Entity<Project>,
        _: ProjectPath,
        _: &mut Window,
        _: &mut Context<Self>,
    ) -> Task<Result<()>> {
        unreachable!()
    }

    fn reload(
        &mut self,
        project: Entity<Project>,
        window: &mut Window,
        cx: &mut Context<Self>,
    ) -> Task<Result<()>> {
        self.diff
            .update(cx, |diff, cx| diff.reload(project, window, cx))
    }

    fn act_as_type<'a>(
        &'a self,
        type_id: TypeId,
        self_handle: &'a Entity<Self>,
        cx: &'a App,
    ) -> Option<gpui::AnyEntity> {
        if type_id == TypeId::of::<Self>() {
            Some(self_handle.clone().into())
        } else if type_id == TypeId::of::<DiffMultibuffer>() {
            Some(self.diff.clone().into())
        } else if type_id == TypeId::of::<Editor>() {
            Some(
                self.diff
                    .read(cx)
                    .editor()
                    .read(cx)
                    .rhs_editor()
                    .clone()
                    .into(),
            )
        } else if type_id == TypeId::of::<SplittableEditor>() {
            Some(self.diff.read(cx).editor().clone().into())
        } else if type_id == TypeId::of::<diff_buffer_list::DiffBufferList>() {
            Some(self.diff.read(cx).branch_diff().clone().into())
        } else {
            None
        }
    }

    fn added_to_workspace(
        &mut self,
        workspace: &mut Workspace,
        window: &mut Window,
        cx: &mut Context<Self>,
    ) {
        self.diff.update(cx, |diff, cx| {
            diff.added_to_workspace(workspace, window, cx)
        });
    }
}

impl Render for BranchDiff {
    fn render(&mut self, window: &mut Window, cx: &mut Context<Self>) -> impl IntoElement {
        h_flex()
            .size_full()
            .on_action(cx.listener(Self::review_diff))
            .on_action(cx.listener(Self::toggle_tree))
            .on_drag_move::<DraggedBranchDiffTreeResizeHandle>(cx.listener(
                |this, event: &DragMoveEvent<DraggedBranchDiffTreeResizeHandle>, _, cx| {
                    let requested = event.event.position.x - event.bounds.left();
                    this.tree_width =
                        clamped_branch_diff_tree_width(requested, event.bounds.size.width);
                    cx.notify();
                },
            ))
            .when(
                self.show_tree && !self.diff.read(cx).file_entries().is_empty(),
                |this| this.child(self.render_tree(window, cx)),
            )
            .child(div().flex_1().min_w_0().h_full().child(self.diff.clone()))
    }
}

impl SerializableItem for BranchDiff {
    fn serialized_item_kind() -> &'static str {
        "BranchDiff"
    }

    fn cleanup(
        _: workspace::WorkspaceId,
        _: Vec<workspace::ItemId>,
        _: &mut Window,
        _: &mut App,
    ) -> Task<Result<()>> {
        Task::ready(Ok(()))
    }

    fn deserialize(
        project: Entity<Project>,
        workspace: WeakEntity<Workspace>,
        workspace_id: workspace::WorkspaceId,
        item_id: workspace::ItemId,
        window: &mut Window,
        cx: &mut App,
    ) -> Task<Result<Entity<Self>>> {
        let db = project_diff::persistence::ProjectDiffDb::global(cx);
        window.spawn(cx, async move |cx| {
            let diff_base = db.get_project_diff_base(item_id, workspace_id)?;
            let DiffBase::Merge { base_ref } = diff_base else {
                anyhow::bail!("expected a merge base for a branch diff");
            };
            let workspace = workspace.upgrade().context("workspace gone")?;
            cx.update(|window, cx| {
                cx.new(|cx| Self::new_with_base_ref(project, workspace, base_ref, None, window, cx))
            })
        })
    }

    fn serialize(
        &mut self,
        workspace: &mut Workspace,
        item_id: workspace::ItemId,
        _closing: bool,
        _window: &mut Window,
        cx: &mut Context<Self>,
    ) -> Option<Task<Result<()>>> {
        let workspace_id = workspace.database_id()?;
        let DiffBase::Merge { base_ref } = self.diff_base(cx).clone() else {
            return None;
        };
        let diff_base = DiffBase::Merge { base_ref };
        let db = project_diff::persistence::ProjectDiffDb::global(cx);
        Some(cx.background_spawn(async move {
            db.save_project_diff_base(item_id, workspace_id, diff_base)
                .await
        }))
    }

    fn should_serialize(&self, _: &Self::Event) -> bool {
        false
    }
}

pub struct BranchDiffToolbar {
    branch_diff: Option<WeakEntity<BranchDiff>>,
}

impl BranchDiffToolbar {
    pub fn new(_cx: &mut Context<Self>) -> Self {
        Self { branch_diff: None }
    }

    fn branch_diff(&self, _: &App) -> Option<Entity<BranchDiff>> {
        self.branch_diff.as_ref()?.upgrade()
    }

    fn dispatch_action(&self, action: &dyn Action, window: &mut Window, cx: &mut Context<Self>) {
        if let Some(branch_diff) = self.branch_diff(cx) {
            branch_diff.focus_handle(cx).focus(window, cx);
        }
        let action = action.boxed_clone();
        cx.defer(move |cx| {
            cx.dispatch_action(action.as_ref());
        })
    }
}

impl EventEmitter<ToolbarItemEvent> for BranchDiffToolbar {}

impl ToolbarItemView for BranchDiffToolbar {
    fn set_active_pane_item(
        &mut self,
        active_pane_item: Option<&dyn ItemHandle>,
        _: &mut Window,
        cx: &mut Context<Self>,
    ) -> ToolbarItemLocation {
        self.branch_diff = active_pane_item
            .and_then(|item| item.act_as::<BranchDiff>(cx))
            .map(|entity| entity.downgrade());
        if self.branch_diff.is_some() {
            ToolbarItemLocation::PrimaryRight
        } else {
            ToolbarItemLocation::Hidden
        }
    }

    fn pane_focus_update(
        &mut self,
        _pane_focused: bool,
        _window: &mut Window,
        _cx: &mut Context<Self>,
    ) {
    }
}

impl Render for BranchDiffToolbar {
    fn render(&mut self, _: &mut Window, cx: &mut Context<Self>) -> impl IntoElement {
        let Some(branch_diff) = self.branch_diff(cx) else {
            return div();
        };
        let focus_handle = branch_diff.focus_handle(cx);
        let review_count = branch_diff
            .read(cx)
            .diff
            .read(cx)
            .total_review_comment_count();
        let (additions, deletions) = branch_diff
            .read(cx)
            .diff
            .read(cx)
            .calculate_changed_lines(cx);
        let diff_base = branch_diff.read(cx).diff_base(cx).clone();
        let DiffBase::Merge { base_ref } = diff_base else {
            return div();
        };
        let selected_base_ref = base_ref.clone();
        let base_ref_label = format!("Base: {base_ref}");
        let show_tree = branch_diff.read(cx).show_tree;
        let repository = branch_diff.read(cx).repo(cx);
        let workspace = branch_diff.read(cx).workspace.clone();
        let view_for_picker = branch_diff.downgrade();

        let is_multibuffer_empty = branch_diff
            .read(cx)
            .diff
            .read(cx)
            .multibuffer()
            .read(cx)
            .is_empty();
        let is_ai_enabled = AgentSettings::get_global(cx).enabled(cx);

        let show_review_button = !is_multibuffer_empty && is_ai_enabled;

        h_flex()
            .my_neg_1()
            .py_1()
            .gap_1p5()
            .flex_wrap()
            .justify_between()
            .when(!is_multibuffer_empty, |this| {
                this.child(DiffStat::new(
                    "branch-diff-stat",
                    additions as usize,
                    deletions as usize,
                ))
            })
            .child(
                IconButton::new("toggle-branch-diff-tree", IconName::ListTree)
                    .icon_size(IconSize::Small)
                    .toggle_state(show_tree)
                    .tooltip(move |_, cx| {
                        Tooltip::for_action(
                            if show_tree {
                                "Hide File Tree"
                            } else {
                                "Show File Tree"
                            },
                            &ToggleBranchDiffTree,
                            cx,
                        )
                    })
                    .on_click(cx.listener(|this, _, window, cx| {
                        this.dispatch_action(&ToggleBranchDiffTree, window, cx);
                    })),
            )
            .child(Divider::vertical().ml_1())
            .child(
                PopoverMenu::new("branch-diff-base-branch-picker")
                    .menu(move |window, cx| {
                        let view_for_picker = view_for_picker.clone();
                        let on_select = Arc::new(
                            move |branch: git::repository::Branch,
                                  _window: &mut Window,
                                  cx: &mut App| {
                                let base_ref: SharedString = branch.name().to_owned().into();
                                view_for_picker
                                    .update(cx, |branch_diff, cx| {
                                        branch_diff.set_merge_base(base_ref, cx);
                                        cx.notify();
                                    })
                                    .ok();
                            },
                        );

                        Some(branch_picker::select_popover(
                            workspace.clone(),
                            repository.clone(),
                            Some(selected_base_ref.clone()),
                            on_select,
                            window,
                            cx,
                        ))
                    })
                    .trigger_with_tooltip(
                        Button::new("branch-diff-base-branch", base_ref_label).end_icon(
                            Icon::new(IconName::ChevronDown)
                                .size(IconSize::XSmall)
                                .color(Color::Muted),
                        ),
                        Tooltip::text("Select Base Branch"),
                    ),
            )
            .when(show_review_button, |this| {
                let focus_handle = focus_handle.clone();
                this.child(Divider::vertical()).child(
                    Button::new("review-diff", "Review Diff")
                        .start_icon(
                            Icon::new(IconName::ZedAssistant)
                                .size(IconSize::Small)
                                .color(Color::Muted),
                        )
                        .tooltip(move |_, cx| {
                            Tooltip::with_meta_in(
                                "Review Diff",
                                Some(&ReviewDiff),
                                "Send this diff for your last agent to review.",
                                &focus_handle,
                                cx,
                            )
                        })
                        .on_click(cx.listener(|this, _, window, cx| {
                            this.dispatch_action(&ReviewDiff, window, cx);
                        })),
                )
            })
            .when(review_count > 0, |this| {
                this.child(Divider::vertical()).child(
                    render_send_review_to_agent_button(review_count, &focus_handle).on_click(
                        cx.listener(|this, _, window, cx| {
                            this.dispatch_action(&SendReviewToAgent, window, cx)
                        }),
                    ),
                )
            })
    }
}

#[cfg(test)]
mod tests {
    use anyhow::anyhow;
    use collections::HashMap;
    use editor::test::editor_test_context::assert_state_with_diff;
    use git::{
        repository::repo_path,
        status::{FileStatus, StatusCode, TrackedStatus, UnmergedStatus, UnmergedStatusCode},
    };
    use gpui::TestAppContext;
    use language::ToOffset as _;
    use project::FakeFs;
    use serde_json::json;
    use settings::{DiffViewStyle, SettingsStore};
    use std::path::Path;
    use std::sync::Arc;
    use unindent::Unindent as _;
    use util::{
        path,
        rel_path::{RelPath, rel_path},
    };
    use workspace::MultiWorkspace;

    fn tree_test_file(path: &str) -> DiffFileEntry {
        let repo_path = repo_path(path);
        DiffFileEntry {
            path_key: multi_buffer::PathKey::with_sort_prefix(2, repo_path.clone().into_arc()),
            repo_path,
            status: StatusCode::Modified.worktree(),
        }
    }

    #[test]
    fn test_branch_diff_tree_entries_and_collapsed_directories() {
        let files = vec![
            tree_test_file("src/lib/a.rs"),
            tree_test_file("README.md"),
            tree_test_file("tests/test.rs"),
            tree_test_file("src/lib/b.rs"),
        ];

        let entries = build_branch_diff_tree_entries(files.clone(), &HashMap::default());
        assert_eq!(entries.len(), 6);
        assert!(matches!(
            &entries[0],
            BranchDiffTreeEntry::Directory(entry)
                if entry.path == repo_path("src/lib")
                    && entry.name.as_ref() == "src/lib"
                    && entry.depth == 0
                    && entry.expanded
        ));
        assert!(matches!(
            &entries[1],
            BranchDiffTreeEntry::File(entry)
                if entry.entry.repo_path == repo_path("src/lib/a.rs") && entry.depth == 1
        ));
        assert!(matches!(
            &entries[2],
            BranchDiffTreeEntry::File(entry)
                if entry.entry.repo_path == repo_path("src/lib/b.rs") && entry.depth == 1
        ));
        assert!(matches!(
            &entries[3],
            BranchDiffTreeEntry::Directory(entry)
                if entry.path == repo_path("tests") && entry.depth == 0
        ));
        assert!(matches!(
            &entries[5],
            BranchDiffTreeEntry::File(entry)
                if entry.entry.repo_path == repo_path("README.md") && entry.depth == 0
        ));

        let mut collapsed = HashMap::default();
        collapsed.insert(repo_path("src/lib"), false);
        let entries = build_branch_diff_tree_entries(files, &collapsed);
        assert_eq!(entries.len(), 4);
        assert!(matches!(
            &entries[0],
            BranchDiffTreeEntry::Directory(entry) if !entry.expanded
        ));
        assert!(!entries.iter().any(|entry| matches!(
            entry,
            BranchDiffTreeEntry::File(entry)
                if entry.entry.repo_path == repo_path("src/lib/a.rs")
                    || entry.entry.repo_path == repo_path("src/lib/b.rs")
        )));
    }

    #[test]
    fn test_branch_diff_tree_width_is_clamped_to_available_space() {
        assert_eq!(
            clamped_branch_diff_tree_width(px(120.), px(1000.)),
            BRANCH_DIFF_TREE_MIN_WIDTH
        );
        assert_eq!(
            clamped_branch_diff_tree_width(px(480.), px(1000.)),
            px(480.)
        );
        assert_eq!(
            clamped_branch_diff_tree_width(px(900.), px(1000.)),
            px(760.)
        );
    }

    #[gpui::test]
    async fn test_branch_diff_tree_navigation_targets_file_hunk_and_unfolds(
        cx: &mut TestAppContext,
    ) {
        init_test(cx);
        cx.update_global::<SettingsStore, _>(|store, cx| {
            store.update_user_settings(cx, |settings| {
                settings.editor.diff_view_style = Some(DiffViewStyle::Split);
            });
        });

        let base_text = (0..12)
            .map(|line| format!("base line {line}"))
            .collect::<Vec<_>>()
            .join("\n")
            + "\n";
        let mut modified_lines = (0..12)
            .map(|line| format!("base line {line}"))
            .collect::<Vec<_>>();
        modified_lines[9] = "changed line 9".into();
        let modified_text = modified_lines.join("\n") + "\n";

        let fs = FakeFs::new(cx.executor());
        fs.insert_tree(
            path!("/project"),
            json!({
                ".git": {},
                "modified.txt": modified_text.clone(),
                "z-last.txt": "z current\n",
            }),
        )
        .await;
        let project = Project::test(fs.clone(), [path!("/project").as_ref()], cx).await;
        let (multi_workspace, cx) =
            cx.add_window_view(|window, cx| MultiWorkspace::test_new(project.clone(), window, cx));
        let workspace = multi_workspace.read_with(cx, |mw, _| mw.workspace().clone());
        let branch_diff = cx
            .update(|window, cx| {
                BranchDiff::new_with_default_branch(project.clone(), workspace, window, cx)
            })
            .await
            .unwrap();
        cx.run_until_parked();

        fs.set_head_for_repo(
            path!("/project/.git").as_ref(),
            &[
                ("deleted.txt", "deleted from worktree\n".into()),
                ("modified.txt", modified_text),
                ("z-last.txt", "z current\n".into()),
            ],
            "head",
        );
        fs.set_merge_base_content_for_repo(
            path!("/project/.git").as_ref(),
            &[
                ("deleted.txt", "deleted from worktree\n".into()),
                ("modified.txt", base_text),
                ("z-last.txt", "z base\n".into()),
            ],
        );
        cx.run_until_parked();

        let (deleted_entry, modified_entry, splittable_editor, editor) =
            branch_diff.read_with(cx, |branch_diff, cx| {
                let diff = branch_diff.diff.read(cx);
                let deleted_entry = diff
                    .file_entries()
                    .iter()
                    .find(|entry| entry.repo_path == repo_path("deleted.txt"))
                    .cloned()
                    .unwrap();
                let modified_entry = diff
                    .file_entries()
                    .iter()
                    .find(|entry| entry.repo_path == repo_path("modified.txt"))
                    .cloned()
                    .unwrap();
                (
                    deleted_entry,
                    modified_entry,
                    diff.editor().clone(),
                    diff.editor().read(cx).rhs_editor().clone(),
                )
            });
        assert!(splittable_editor.read_with(cx, |editor, _| editor.is_split()));
        let deleted_buffer_id = editor.read_with(cx, |editor, cx| {
            editor
                .buffer()
                .read(cx)
                .all_buffers()
                .iter()
                .find(|buffer| {
                    buffer
                        .read(cx)
                        .file()
                        .is_some_and(|file| file.path().as_unix_str() == "deleted.txt")
                })
                .unwrap()
                .read(cx)
                .remote_id()
        });
        assert!(editor.read_with(cx, |editor, cx| {
            editor.is_buffer_folded(deleted_buffer_id, cx)
        }));

        cx.update_window_entity(&branch_diff, |branch_diff, window, cx| {
            branch_diff.diff.update(cx, |diff, cx| {
                diff.move_to_path(deleted_entry.path_key, window, cx)
            });
        });
        let active_path = branch_diff.read_with(cx, |branch_diff, cx| {
            branch_diff
                .diff
                .read(cx)
                .active_project_path(cx)
                .unwrap()
                .path
                .as_unix_str()
                .to_string()
        });
        assert_eq!(active_path, "deleted.txt");
        assert!(!editor.read_with(cx, |editor, cx| {
            editor.is_buffer_folded(deleted_buffer_id, cx)
        }));

        cx.update_window_entity(&branch_diff, |branch_diff, window, cx| {
            splittable_editor
                .read(cx)
                .lhs_editor()
                .unwrap()
                .read(cx)
                .focus_handle(cx)
                .focus(window, cx);
            branch_diff.diff.update(cx, |diff, cx| {
                diff.move_to_path(modified_entry.path_key, window, cx);
                diff.editor()
                    .read(cx)
                    .rhs_editor()
                    .read(cx)
                    .focus_handle(cx)
                    .focus(window, cx);
            });
        });
        cx.run_until_parked();
        let (active_path, selection, first_hunk_start) =
            branch_diff.read_with(cx, |branch_diff, cx| {
                let diff = branch_diff.diff.read(cx);
                let active_path = diff
                    .active_project_path(cx)
                    .unwrap()
                    .path
                    .as_unix_str()
                    .to_string();
                let editor = diff.editor().read(cx).rhs_editor().read(cx);
                let selection = editor.selections.newest_anchor().head();
                let snapshot = editor.buffer().read(cx).snapshot(cx);
                let target_buffer_id = snapshot
                    .anchor_to_buffer_anchor(selection)
                    .unwrap()
                    .0
                    .buffer_id;
                let first_hunk_start = editor
                    .diff_hunks_in_ranges(
                        &[multi_buffer::Anchor::Min..multi_buffer::Anchor::Max],
                        &snapshot,
                    )
                    .find(|hunk| hunk.buffer_id == target_buffer_id)
                    .unwrap()
                    .multi_buffer_range
                    .start;
                let (selection, selection_buffer) =
                    snapshot.anchor_to_buffer_anchor(selection).unwrap();
                let (first_hunk_start, hunk_buffer) =
                    snapshot.anchor_to_buffer_anchor(first_hunk_start).unwrap();
                assert_eq!(selection.buffer_id, first_hunk_start.buffer_id);
                let selection = selection.to_offset(selection_buffer);
                let first_hunk_start = first_hunk_start.to_offset(hunk_buffer);
                (active_path, selection, first_hunk_start)
            });
        assert_eq!(active_path, "modified.txt");
        assert_eq!(selection, first_hunk_start);
    }

    use super::*;

    fn init_test(cx: &mut TestAppContext) {
        cx.update(|cx| {
            let store = SettingsStore::test(cx);
            cx.set_global(store);
            cx.update_global::<SettingsStore, _>(|store, cx| {
                store.update_user_settings(cx, |settings| {
                    settings.editor.diff_view_style = Some(DiffViewStyle::Unified);
                });
            });
            theme_settings::init(theme::LoadThemes::JustBase, cx);
            editor::init(cx);
            crate::init(cx);
        });
    }

    #[gpui::test(iterations = 50)]
    async fn test_split_diff_conflict_path_transition_with_dirty_buffer_invalid_anchor_panics(
        cx: &mut TestAppContext,
    ) {
        init_test(cx);

        cx.update(|cx| {
            cx.update_global::<SettingsStore, _>(|store, cx| {
                store.update_user_settings(cx, |settings| {
                    settings.editor.diff_view_style = Some(DiffViewStyle::Split);
                });
            });
        });

        let build_conflict_text: fn(usize) -> String = |tag: usize| {
            let mut lines = (0..80)
                .map(|line_index| format!("line {line_index}"))
                .collect::<Vec<_>>();
            for offset in [5usize, 20, 37, 61] {
                lines[offset] = format!("base-{tag}-line-{offset}");
            }
            format!("{}\n", lines.join("\n"))
        };
        let initial_conflict_text = build_conflict_text(0);
        let fs = FakeFs::new(cx.executor());
        fs.insert_tree(
            path!("/project"),
            json!({
                ".git": {},
                "helper.txt": "same\n",
                "conflict.txt": initial_conflict_text,
            }),
        )
        .await;
        fs.with_git_state(path!("/project/.git").as_ref(), true, |state| {
            state
                .refs
                .insert("MERGE_HEAD".into(), "conflict-head".into());
        })
        .unwrap();
        fs.set_status_for_repo(
            path!("/project/.git").as_ref(),
            &[(
                "conflict.txt",
                FileStatus::Unmerged(UnmergedStatus {
                    first_head: UnmergedStatusCode::Updated,
                    second_head: UnmergedStatusCode::Updated,
                }),
            )],
        );
        fs.set_merge_base_content_for_repo(
            path!("/project/.git").as_ref(),
            &[
                ("conflict.txt", build_conflict_text(1)),
                ("helper.txt", "same\n".to_string()),
            ],
        );

        let project = Project::test(fs.clone(), [path!("/project").as_ref()], cx).await;
        let (multi_workspace, cx) =
            cx.add_window_view(|window, cx| MultiWorkspace::test_new(project.clone(), window, cx));
        let workspace = multi_workspace.read_with(cx, |mw, _| mw.workspace().clone());
        let _branch_diff = cx
            .update(|window, cx| {
                BranchDiff::new_with_default_branch(project.clone(), workspace, window, cx)
            })
            .await
            .unwrap();
        cx.run_until_parked();

        let buffer = project
            .update(cx, |project, cx| {
                project.open_local_buffer(path!("/project/conflict.txt"), cx)
            })
            .await
            .unwrap();
        buffer.update(cx, |buffer, cx| buffer.edit([(0..0, "dirty\n")], None, cx));
        assert!(buffer.read_with(cx, |buffer, _| buffer.is_dirty()));
        cx.run_until_parked();

        cx.update(|window, cx| {
            let fs = fs.clone();
            window
                .spawn(cx, async move |cx| {
                    cx.background_executor().simulate_random_delay().await;
                    fs.with_git_state(path!("/project/.git").as_ref(), true, |state| {
                        state.refs.insert("HEAD".into(), "head-1".into());
                        state.refs.remove("MERGE_HEAD");
                    })
                    .unwrap();
                    fs.set_status_for_repo(
                        path!("/project/.git").as_ref(),
                        &[
                            (
                                "conflict.txt",
                                FileStatus::Tracked(TrackedStatus {
                                    index_status: git::status::StatusCode::Modified,
                                    worktree_status: git::status::StatusCode::Modified,
                                }),
                            ),
                            (
                                "helper.txt",
                                FileStatus::Tracked(TrackedStatus {
                                    index_status: git::status::StatusCode::Modified,
                                    worktree_status: git::status::StatusCode::Modified,
                                }),
                            ),
                        ],
                    );
                    // FakeFs assigns deterministic OIDs by entry position; flipping order churns
                    // conflict diff identity without reaching into view internals.
                    fs.set_merge_base_content_for_repo(
                        path!("/project/.git").as_ref(),
                        &[
                            ("helper.txt", "helper-base\n".to_string()),
                            ("conflict.txt", build_conflict_text(2)),
                        ],
                    );
                })
                .detach();
        });

        cx.update(|window, cx| {
            let buffer = buffer.clone();
            window
                .spawn(cx, async move |cx| {
                    cx.background_executor().simulate_random_delay().await;
                    for edit_index in 0..10 {
                        if edit_index > 0 {
                            cx.background_executor().simulate_random_delay().await;
                        }
                        buffer.update(cx, |buffer, cx| {
                            let len = buffer.len();
                            if edit_index % 2 == 0 {
                                buffer.edit(
                                    [(0..0, format!("status-burst-head-{edit_index}\n"))],
                                    None,
                                    cx,
                                );
                            } else {
                                buffer.edit(
                                    [(len..len, format!("status-burst-tail-{edit_index}\n"))],
                                    None,
                                    cx,
                                );
                            }
                        });
                    }
                })
                .detach();
        });

        cx.run_until_parked();
    }

    #[gpui::test]
    async fn test_branch_diff(cx: &mut TestAppContext) {
        init_test(cx);

        let fs = FakeFs::new(cx.executor());
        fs.insert_tree(
            path!("/project"),
            json!({
                ".git": {},
                "a.txt": "C",
                "b.txt": "new",
                "c.txt": "in-merge-base-and-work-tree",
                "d.txt": "created-in-head",
            }),
        )
        .await;
        let project = Project::test(fs.clone(), [path!("/project").as_ref()], cx).await;
        let (multi_workspace, cx) =
            cx.add_window_view(|window, cx| MultiWorkspace::test_new(project.clone(), window, cx));
        let workspace = multi_workspace.read_with(cx, |mw, _| mw.workspace().clone());
        let diff = cx
            .update(|window, cx| {
                BranchDiff::new_with_default_branch(project.clone(), workspace, window, cx)
            })
            .await
            .unwrap();
        cx.run_until_parked();

        fs.set_head_for_repo(
            Path::new(path!("/project/.git")),
            &[("a.txt", "B".into()), ("d.txt", "created-in-head".into())],
            "sha",
        );
        fs.set_merge_base_content_for_repo(
            Path::new(path!("/project/.git")),
            &[
                ("a.txt", "A".into()),
                ("c.txt", "in-merge-base-and-work-tree".into()),
            ],
        );
        cx.run_until_parked();

        let editor = diff.read_with(cx, |diff, cx| diff.editor(cx).read(cx).rhs_editor().clone());

        assert_state_with_diff(
            &editor,
            cx,
            &"
                - A
                + ˇC
                + new
                + created-in-head"
                .unindent(),
        );

        let statuses: HashMap<Arc<RelPath>, Option<FileStatus>> =
            editor.update(cx, |editor, cx| {
                editor
                    .buffer()
                    .read(cx)
                    .all_buffers()
                    .iter()
                    .map(|buffer| {
                        (
                            buffer.read(cx).file().unwrap().path().clone(),
                            editor.status_for_buffer_id(buffer.read(cx).remote_id(), cx),
                        )
                    })
                    .collect()
            });

        assert_eq!(
            statuses,
            HashMap::from_iter([
                (
                    rel_path("a.txt").into_arc(),
                    Some(FileStatus::Tracked(TrackedStatus {
                        index_status: git::status::StatusCode::Modified,
                        worktree_status: git::status::StatusCode::Modified
                    }))
                ),
                (rel_path("b.txt").into_arc(), Some(FileStatus::Untracked)),
                (
                    rel_path("d.txt").into_arc(),
                    Some(FileStatus::Tracked(TrackedStatus {
                        index_status: git::status::StatusCode::Added,
                        worktree_status: git::status::StatusCode::Added
                    }))
                )
            ])
        );
    }

    #[gpui::test]
    async fn test_branch_diff_action_matches_existing_item_by_base_ref(cx: &mut TestAppContext) {
        init_test(cx);

        let fs = FakeFs::new(cx.executor());
        fs.insert_tree(
            path!("/project"),
            json!({
                ".git": {},
                "a.txt": "changed",
            }),
        )
        .await;
        let project = Project::test(fs.clone(), [path!("/project").as_ref()], cx).await;
        let (multi_workspace, cx) =
            cx.add_window_view(|window, cx| MultiWorkspace::test_new(project.clone(), window, cx));
        let workspace = multi_workspace.read_with(cx, |mw, _| mw.workspace().clone());

        let target_branch_diff = cx
            .update(|window, cx| {
                let Some(repository) = project.read(cx).active_repository(cx) else {
                    return Task::ready(Err(anyhow!("No active repository")));
                };
                BranchDiff::new_with_branch_base(
                    project.clone(),
                    workspace.clone(),
                    "topic".into(),
                    repository,
                    window,
                    cx,
                )
            })
            .await
            .unwrap();
        workspace.update_in(cx, |workspace, window, cx| {
            workspace.add_item_to_active_pane(
                Box::new(target_branch_diff.clone()),
                None,
                true,
                window,
                cx,
            );
        });
        cx.run_until_parked();

        cx.focus(&workspace);
        cx.update(|window, cx| {
            window.dispatch_action(DeployBranchDiff.boxed_clone(), cx);
        });
        cx.run_until_parked();

        let (active_base_ref, mut base_refs) = workspace.update(cx, |workspace, cx| {
            let active_item = workspace.active_item_as::<BranchDiff>(cx).unwrap();
            let active_base_ref = match active_item.read(cx).diff_base(cx) {
                DiffBase::Merge { base_ref } => base_ref.to_string(),
                DiffBase::Head | DiffBase::Index | DiffBase::Staged => {
                    panic!("expected active item to be a branch diff")
                }
            };
            let base_refs = workspace
                .items_of_type::<BranchDiff>(cx)
                .filter_map(|item| match item.read(cx).diff_base(cx) {
                    DiffBase::Merge { base_ref } => Some(base_ref.to_string()),
                    DiffBase::Head | DiffBase::Index | DiffBase::Staged => None,
                })
                .collect::<Vec<_>>();
            (active_base_ref, base_refs)
        });
        base_refs.sort();

        assert_eq!(active_base_ref, "origin/main");
        assert_eq!(base_refs, vec!["origin/main", "topic"]);
    }
}
