use super::{Analyzer, BlockId, Condition, GuardBodyPair, MayM4, NodeId, ShellCommand};

impl Analyzer {
    /// Remove a node, children nodes, and empty parent nodes recursively
    pub(super) fn remove_node(&mut self, node_id: NodeId) {
        // Get parent information before removing the node
        let parent_info = self.get_node(node_id).info.parent;

        self.remove_node_and_children(node_id);

        // Clean up parent references
        if let Some((parent, block_id)) = parent_info {
            self.cleanup_parent(parent, block_id);
        }
    }

    fn remove_node_and_children(&mut self, node_id: NodeId) {
        // Get children information before removing the node
        let children_info = self.get_children(node_id);

        self.cleanup_node(node_id);

        if let Some(children) = children_info {
            for child in children {
                if self.pool.nodes.contains(child) {
                    self.remove_node_and_children(child);
                }
            }
        }
    }

    fn cleanup_node(&mut self, node_id: NodeId) {
        // Remove from top_ids if it's a top-level node
        self.top_ids.retain(|&id| id != node_id);

        // Clean up any references in other data structures
        self.var_definitions.retain(|_, locations| {
            locations.retain(|loc| loc.node_id != node_id);
            !locations.is_empty()
        });

        // Remove block information
        for child_block_id in self.get_node(node_id).info.child_blocks.clone() {
            if self.blocks.contains(child_block_id) {
                self.blocks.remove(child_block_id);
            }
        }
        if let Some((_, block_id)) = self.get_node(node_id).info.parent {
            let is_block_empty = if let Some(block) = self.blocks.get_mut(block_id) {
                block.children.retain(|id| *id != node_id);
                block.children.is_empty()
            } else {
                false
            };
            if is_block_empty {
                self.blocks.remove(block_id);
            }
        }

        // Remove the node from the pool
        self.pool.nodes.remove(node_id);
    }

    fn cleanup_parent(&mut self, parent_id: NodeId, block_id: BlockId) {
        if self.is_effectively_empty_node(parent_id) {
            // If parent has no children left, recursively remove it
            self.remove_node(parent_id);
        } else if self.get_block(block_id).is_none() {
            // When the parent is not empty but its branch (block) is, prune the branch
            let branch_index = self.get_branch_index(parent_id, block_id).unwrap();
            if let MayM4::Shell(cmd) = &mut self.get_node_mut(parent_id).cmd.0 {
                match cmd {
                    ShellCommand::If {
                        conditionals,
                        else_branch,
                    } => {
                        if branch_index < conditionals.len() {
                            let removed_conditon = conditionals.remove(branch_index).condition;
                            if !conditionals.is_empty() {
                                conditionals[branch_index].condition = Condition::And(
                                    Box::new(removed_conditon.flip()),
                                    Box::new(conditionals[branch_index].condition.clone()),
                                );
                            } else {
                                conditionals.push(GuardBodyPair {
                                    condition: removed_conditon.flip(),
                                    body: else_branch.clone(),
                                });
                                else_branch.clear();
                            }
                        } else {
                            else_branch.clear();
                        }
                    }
                    ShellCommand::Case { word: _, arms } => {
                        arms.remove(branch_index);
                    }
                    _ => unreachable!(),
                }
            }
            // Unlink parent to block relationship
            self.get_node_mut(parent_id)
                .info
                .child_blocks
                .retain(|id| *id != block_id);
        }
    }

    /// Check if a node contains only "effectively empty" commands like echo or AC_MSG_RESULT
    fn is_effectively_empty_node(&self, node_id: NodeId) -> bool {
        use crate::analyzer::{as_literal, as_shell, MayM4};
        use autotools_parser::ast::node::ShellCommand;

        if let Some(node) = self.pool.nodes.get(node_id) {
            match &node.cmd.0 {
                MayM4::Shell(ShellCommand::Cmd(words)) => {
                    // Check if it's an echo command or similar
                    if let Some(first_word) = words.first() {
                        if let Some(shell_word) = as_shell(first_word) {
                            if let Some(literal) = as_literal(shell_word) {
                                return matches!(literal, "echo" | "printf");
                            }
                        }
                    }
                    false
                }
                MayM4::Macro(m4_macro) => {
                    // Check if it's AC_MSG_RESULT or similar informational macros
                    matches!(
                        m4_macro.name.as_str(),
                        "AC_MSG_RESULT" | "AC_MSG_NOTICE" | "AC_MSG_CHECKING"
                    )
                }
                MayM4::Shell(ShellCommand::Redirect(_, _)) => false,
                MayM4::Shell(ShellCommand::Pipe(_, _)) => false,
                _ => self
                    .get_children(node_id)
                    .is_some_and(|children| self.children_effectively_empty(&children)),
            }
        } else {
            false
        }
    }

    /// Check if all children are effectively empty (either actually empty or only contain echo/AC_MSG_RESULT)
    fn children_effectively_empty(&self, children: &[NodeId]) -> bool {
        children.is_empty()
            || children
                .iter()
                .all(|&child_id| self.is_effectively_empty_node(child_id))
    }
}
