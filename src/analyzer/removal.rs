use crate::analyzer::as_single;

use super::{Analyzer, BlockId, Condition, GuardBodyPair, M4Argument, MayM4, NodeId, ShellCommand};

impl Analyzer {
    /// Remove a node, children nodes, and empty parent nodes recursively
    pub(super) fn remove_node(&mut self, node_id: NodeId) {
        if self.get_node(node_id).is_none() {
            return;
        }
        // Get parent information before removing the node
        let parent = self.get_node(node_id).unwrap().info.parent;
        let block = self.get_node(node_id).unwrap().info.block;

        self.remove_node_and_children(node_id);

        // Clean up parent references
        if let (Some(parent), Some(block_id)) = (parent, block) {
            self.cleanup_parent(parent, node_id, block_id);
        }
    }

    fn remove_node_and_children(&mut self, node_id: NodeId) {
        // Get children information before removing the node
        let children_info = self.get_children(node_id);

        self.cleanup_node(node_id);

        if let Some(children) = children_info {
            for id in children {
                if self.pool.nodes.contains(id) {
                    self.remove_node_and_children(id);
                }
            }
        }
    }

    fn cleanup_node(&mut self, node_id: NodeId) {
        // Remove from top_ids if it's a top-level node
        self.top_ids.retain(|&id| id != node_id);

        // Clean up any references in other data structures
        if let Some(v) = self.var_definitions.as_mut() {
            v.retain(|_, locations| {
                locations.retain(|loc| loc.node_id != node_id);
                !locations.is_empty()
            })
        }
        if let Some(v) = self.var_propagated_definitions.as_mut() {
            v.retain(|_, locations| {
                locations.retain(|loc| loc.node_id != node_id);
                !locations.is_empty()
            })
        }
        if let Some(v) = self.var_usages.as_mut() {
            v.retain(|_, locations| {
                locations.retain(|loc| loc.node_id != node_id);
                !locations.is_empty()
            })
        }

        // Remove the node's child blocks
        for block_id in self.get_node(node_id).unwrap().info.branches.clone() {
            if self.blocks.contains(block_id) {
                self.blocks.remove(block_id);
            }
        }

        // Remove the node from the pool
        self.pool.nodes.remove(node_id);
    }

    fn cleanup_parent(&mut self, parent_id: NodeId, node_id: NodeId, block_id: BlockId) {
        // Remove the information of the node's block
        let is_block_empty = {
            let block = self.blocks.get_mut(block_id).unwrap();
            block.nodes.retain(|id| *id != node_id);
            if block.nodes.is_empty() {
                self.blocks.remove(block_id);
                true
            } else {
                false
            }
        };
        if self.is_effectively_empty_node(parent_id) {
            // If parent has no children left, recursively remove it
            self.remove_node(parent_id);
        } else if is_block_empty {
            // When the parent is not empty but its branch (block) is, the parent node
            // should have multiple branches (either if/case). Prune the empty branch
            self.prune_block(parent_id, block_id);
        } else {
            // When the parent & its branch are not empty, prune the command
            self.prune_command(parent_id, node_id, block_id);
        }
    }

    fn prune_block(&mut self, parent_id: NodeId, block_id: BlockId) {
        let branch_index = self.get_branch_index(parent_id, block_id).unwrap();
        #[cfg(debug_assertions)]
        let mut num_arms = None;
        if let MayM4::Shell(cmd) = &mut self.get_node_mut(parent_id).unwrap().cmd.0 {
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
                    #[cfg(debug_assertions)]
                    num_arms.replace(arms.len());
                }
                _ => {
                    dbg!(&cmd);
                    unreachable!();
                }
            }
        }
        // Unlink parent to block relationship
        self.get_node_mut(parent_id)
            .unwrap()
            .info
            .branches
            .retain(|id| *id != block_id);

        #[cfg(debug_assertions)]
        if let Some(num_arms) = num_arms {
            assert_eq!(
                num_arms,
                self.get_node(parent_id).unwrap().info.branches.len()
            );
        }
    }

    fn prune_command(&mut self, parent_id: NodeId, node_id: NodeId, block_id: BlockId) {
        let branch_index = self.get_branch_index(parent_id, block_id).unwrap();
        match &mut self.get_node_mut(parent_id).unwrap().cmd.0 {
            MayM4::Shell(cmd) => match cmd {
                ShellCommand::If {
                    conditionals,
                    else_branch,
                } => {
                    if branch_index < conditionals.len() {
                        if let Some(pair) = conditionals.get_mut(branch_index) {
                            pair.body.retain(|id| *id != node_id)
                        }
                    } else {
                        else_branch.retain(|id| *id != node_id);
                    }
                }
                ShellCommand::Case { word: _, arms } => {
                    if let Some(pair) = arms.get_mut(branch_index) {
                        pair.body.retain(|id| *id != node_id)
                    }
                }
                ShellCommand::Brace(body) | ShellCommand::Subshell(body) => {
                    body.retain(|id| *id != node_id);
                }
                ShellCommand::While(pair) | ShellCommand::Until(pair) => {
                    pair.body.retain(|id| *id != node_id);
                }
                ShellCommand::For {
                    var: _,
                    words: _,
                    body,
                } => {
                    body.retain(|id| *id != node_id);
                }
                _ => {
                    dbg!(&cmd);
                    unreachable!();
                }
            },
            MayM4::Macro(m4_macro) => {
                for arg in m4_macro.args.iter_mut() {
                    if let M4Argument::Commands(cmds) = arg {
                        cmds.retain(|id| *id != node_id);
                    }
                }
            }
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
                        if let Some(shell_word) = as_single(first_word).and_then(as_shell) {
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
                    .get_body(node_id)
                    .is_some_and(|body| self.is_body_effectively_empty(&body)),
            }
        } else {
            false
        }
    }

    /// Check if all children are effectively empty (either actually empty or only contain echo/AC_MSG_RESULT)
    fn is_body_effectively_empty(&self, body: &[NodeId]) -> bool {
        body.is_empty() || body.iter().all(|&id| self.is_effectively_empty_node(id))
    }
}
