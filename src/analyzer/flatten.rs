use std::collections::HashMap;

use super::{
    as_literal, as_shell, AcCommand, AcWord, Analyzer, AstVisitor, Block, BlockId, GuardBodyPair,
    Node, NodeId, NodeInfo, PatternBodyPair, ShellCommand,
};
use std::collections::HashSet;

/// A visitor to flatten and collect AST nodes into a linear sequence.
///
/// The Flattener transforms deeply nested command structures into a flatter representation
/// by breaking apart large commands (those exceeding a line threshold) and reorganizing
/// their child nodes for better analysis.
#[derive(Debug)]
pub(super) struct Flattener<'a> {
    /// Line count threshold - commands exceeding this size will be flattened
    threshold: usize,
    /// Analyzer containing various information
    analyzer: &'a mut Analyzer,
    /// IDs of top-level nodes after flattening
    flattened_top_ids: Vec<NodeId>,
    /// Stack tracking parent nodes and whether they should be flattened
    parent_stack: Vec<ParentInfo>,
    #[cfg(debug_assertions)]
    /// For debugging: tracks the last range start to ensure proper ordering
    last_range_start: Option<usize>,
}

#[derive(Debug)]
struct ParentInfo {
    node_id: NodeId,
    flatten: bool,
}

impl<'a> Flattener<'a> {
    /// Checks if a command is a 'break'/'continue' command
    fn is_loop_interruption_cmd(&self, node_id: NodeId) -> bool {
        let node = self.get_node(node_id);
        if let super::MayM4::Shell(ShellCommand::Cmd(words)) = &node.cmd.0 {
            if let Some(first_word) = words.first() {
                if let Some(shell_word) = as_shell(first_word) {
                    if let Some(literal) = as_literal(shell_word) {
                        return literal == "break" || literal == "continue";
                    }
                }
            }
        }
        false
    }

    /// Recursively checks if any descendant node contains a break/continue command
    /// that would break out of the current scope (stops at nested loops)
    fn has_loop_interruption_in_descendants(&self, node_id: NodeId) -> bool {
        if self.is_loop_interruption_cmd(node_id) {
            return true;
        }

        use super::MayM4::*;
        use ShellCommand::*;

        match &self.get_node(node_id).cmd.0 {
            Shell(While(_)) | Shell(Until(_)) => {
                // Don't traverse into nested loops as breaks there don't affect current scope
                false
            }
            Shell(For { .. }) => {
                // Don't traverse into nested loops as breaks there don't affect current scope
                false
            }
            _ => self.analyzer.get_body(node_id).is_some_and(|body| {
                body.iter()
                    .any(|child| self.has_loop_interruption_in_descendants(*child))
            }),
        }
    }

    /// Splits a block into sub-blocks based on marked nodes
    /// Returns a vector of (block, is_marked) tuples
    fn split_block_by_marks(
        &mut self,
        nodes: &[NodeId],
        marked: &HashSet<NodeId>,
    ) -> Vec<(Vec<NodeId>, bool)> {
        let mut blocks = Vec::new();
        let mut current_block = (Vec::new(), false);

        for &node_id in nodes {
            let mark_status = marked.contains(&node_id);
            if mark_status == current_block.1 {
                // If we have accumulated nodes of the same mark status, add the node to them.
                current_block.0.push(node_id);
            } else {
                if !current_block.0.is_empty() {
                    blocks.push(current_block);
                }
                // Add the node to its own block
                current_block = (vec![node_id], mark_status);
            }
        }

        // Add any remaining nodes as an unmarked block
        if !current_block.0.is_empty() {
            blocks.push(current_block);
        }

        if blocks.len() > 1 {
            // if given nodes actually get split, we modify blocks to ensure the integrity.
            let old_block_id = self._block_id_of_nodes(nodes);
            let old_block = self.analyzer.blocks.remove(old_block_id);
            let parent_id = old_block.parent;
            let branch_idx = self
                .analyzer
                .get_branch_index(parent_id, old_block_id)
                .unwrap();
            self.get_node_mut(parent_id)
                .info
                .branches
                .remove(branch_idx);
            for (nodes, _) in blocks.iter().rev() {
                let new_block_id = self.analyzer.add_block(Block {
                    block_id: 0,
                    parent: parent_id,
                    nodes: nodes.clone(),
                    guards: old_block.guards.clone(),
                });
                self.get_node_mut(parent_id)
                    .info
                    .branches
                    .insert(branch_idx, new_block_id);
                for &node_id in nodes {
                    self.get_node_mut(node_id).info.parent = Some((parent_id, new_block_id));
                }
            }
        }

        blocks
    }

    /// Main entry point for flattening an AST
    ///
    /// Takes a collection of nodes and their initial top-level IDs, then flattens
    /// commands that exceed the line threshold into a more linear structure.
    /// Returns the new top-level node IDs and the modified node collection.
    pub fn flatten(analyzer: &'a mut Analyzer, threshold: usize) {
        let mut s = Self {
            threshold,
            analyzer,
            flattened_top_ids: Vec::new(),
            parent_stack: vec![],
            #[cfg(debug_assertions)]
            last_range_start: None,
        };

        for id in s.analyzer.get_top_ids() {
            s.visit_top(id);
        }

        s.analyzer.top_ids = s.flattened_top_ids;
    }

    /// Determines if a node is "large" and should be flattened
    ///
    /// A node is considered large if its line span exceeds the threshold
    fn is_large(&self, node_id: NodeId) -> bool {
        self.get_node(node_id)
            .range
            .first()
            .is_some_and(|(start, end)| end - start > self.threshold)
    }

    /// Returns the current node ID if it will be flattened
    ///
    /// Checks the parent stack to see if we're currently inside a node
    /// that is being flattened
    fn will_flatten(&self) -> Option<NodeId> {
        self.parent_stack
            .last()
            .filter(|p| p.flatten)
            .map(|p| p.node_id)
    }

    fn _block_id_of_nodes(&self, nodes: &[NodeId]) -> BlockId {
        let mut id = nodes
            .iter()
            .map(|id| self.get_node(*id).info.parent.unwrap().1)
            .collect::<HashSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        assert!(id.len() == 1);
        id.pop().unwrap()
    }

    /// Creates a synthetic "brace" node to group children under a flattened parent
    ///
    /// When flattening a large command, smaller child commands are grouped under
    /// a brace node to maintain the hierarchical structure while keeping the
    /// parent command at the top level
    fn insert_brace(&mut self, parent: NodeId, children: &[NodeId]) -> NodeId {
        let old_block_id = self._block_id_of_nodes(children);

        // create a new brace node
        let new_node_id = self.analyzer.pool.nodes.insert(Node {
            comment: None,
            range: children
                .iter()
                .flat_map(|id| self.get_node(*id).range.clone())
                .collect::<Vec<_>>(),
            cmd: AcCommand::new_cmd(ShellCommand::Brace(children.to_vec())),
            // FIXME: this brace's block id is strage
            info: NodeInfo {
                branches: vec![old_block_id],
                ..Default::default()
            },
        });
        self.get_node_mut(new_node_id).info.node_id = new_node_id;
        self.get_node_mut(new_node_id).info.top_id = Some(new_node_id);
        // crate a new block
        let new_block_id = self.analyzer.add_block(Block {
            block_id: 0,
            parent,
            nodes: vec![new_node_id],
            guards: self.get_block(old_block_id).guards.clone(),
        });
        self.get_node_mut(new_node_id).info.parent = Some((parent, new_block_id));

        // update original children & their block
        self.get_block_mut(old_block_id).parent = new_node_id;
        for &child in children {
            self.get_node_mut(child).info.parent = Some((new_node_id, old_block_id));
        }

        // update parent
        if let Some(branch_index) = self.analyzer.get_branch_index(parent, old_block_id) {
            self.get_node_mut(parent).info.branches[branch_index] = new_block_id;
        }

        // add top id
        self.flattened_top_ids.push(new_node_id);
        new_node_id
    }

    /// Calculates the line range spanned by a collection of body nodes
    fn body_range(&self, body: &[NodeId]) -> Option<(usize, usize)> {
        if body.is_empty() {
            None
        } else {
            let body_start = self.get_node(*body.first().unwrap()).range_start().unwrap();
            let body_end = self.get_node(*body.last().unwrap()).range_end().unwrap();
            Some((body_start, body_end))
        }
    }

    fn get_node_mut(&mut self, node_id: NodeId) -> &mut Node {
        self.analyzer.get_node_mut(node_id)
    }

    fn get_block(&self, block_id: BlockId) -> &Block {
        self.analyzer.get_block(block_id)
    }

    fn get_block_mut(&mut self, block_id: BlockId) -> &mut Block {
        self.analyzer.get_block_mut(block_id)
    }
}

impl<'a> AstVisitor for Flattener<'a> {
    fn get_node(&self, node_id: NodeId) -> &Node {
        self.analyzer.get_node(node_id)
    }

    /// Visits a top-level node and adds it to the top-level ID list
    fn visit_top(&mut self, node_id: NodeId) {
        self.flattened_top_ids.push(node_id);
        self.visit_node(node_id);
    }

    /// Visits any node and handles flattening logic
    ///
    /// Sets up parent-child relationships and determines the top_id for each node
    /// based on whether it's being flattened or not
    fn visit_node(&mut self, node_id: NodeId) {
        let is_large = self.is_large(node_id);

        // Assign the top_id for this node - this determines which top-level node
        // this node belongs to in the flattened structure
        self.get_node_mut(node_id).info.top_id = Some(if is_large {
            // Large nodes become their own top-level nodes
            node_id
        } else {
            // For small nodes, we need to find which top-level node they belong to.
            // This is the most complex part of the flattening algorithm.

            // First, get the topmost ancestor (root of current traversal path)
            let top_most = self
                .parent_stack
                .first()
                .map(|p| p.node_id)
                .unwrap_or(node_id);

            // Now we need to find the correct top-level node for this small node.
            // The key insight: we want to find the LAST (most recent) ancestor
            // that is being flattened, then assign this node to the NEXT node
            // in the stack after that flattened ancestor.
            //
            // Why? Because when a node is flattened, its children get promoted
            // to be siblings of the flattened node. So if we have:
            // A (large) -> B (small) -> C (current small node)
            // Then C should belong to B's top-level group, not A's.
            self.parent_stack
                .iter()
                .rposition(|p| p.flatten) // Find rightmost flattened ancestor
                .and_then(|i| {
                    // If we found a flattened ancestor, look at what comes after it
                    Some(if i + 1 < self.parent_stack.len() {
                        // There's a node after the flattened ancestor - use that as top_id
                        // This node represents the "container" for children of the flattened ancestor
                        self.parent_stack[i + 1].node_id
                    } else {
                        // No node after the flattened ancestor - this node becomes its own top
                        // This happens when we're directly under a flattened node
                        node_id
                    })
                })
                .unwrap_or(top_most) // Fallback: if no flattened ancestors, use topmost
        });
        #[cfg(debug_assertions)]
        {
            self.last_range_start = self.get_node(node_id).range.first().map(|r| r.0);
        }

        // Push this node onto the parent stack with its flattening status
        // The parent_stack serves two purposes:
        // 1. Track the current path from root to this node (for parent-child relationships)
        // 2. Track which ancestors are being flattened (the boolean flag)
        //    This helps determine top_id assignment for descendant nodes
        self.parent_stack.push(ParentInfo {
            node_id,
            flatten: is_large,
        });

        // Recursively process this node's children
        self.walk_node(node_id);

        // Pop this node from the stack when done processing its subtree
        self.parent_stack.pop();
    }

    /// Handles flattening of for loops
    ///
    /// Enhanced logic that handles break commands:
    /// 1. Detects break commands in descendants (scope-aware)
    /// 2. Marks direct children containing breaks
    /// 3. Splits the body based on marked nodes
    /// 4. Only flattens unmarked blocks that are large enough
    fn visit_for(&mut self, var: &str, words: &[AcWord], body: &[NodeId]) {
        if let Some(cur) = self.will_flatten() {
            #[cfg(debug_assertions)]
            {
                let start = self.get_node(cur).range_start().unwrap();
                if let Some(prev) = self.last_range_start {
                    if !(prev <= start) {
                        dbg!(&self.get_node(cur).range, cur, self.last_range_start);
                        panic!();
                    }
                }
                self.last_range_start = Some(start);
            }
            // Step 1 & 2: Mark nodes containing break/continue commands (scope-aware)
            let marked_nodes = body
                .iter()
                .filter(|&&node_id| self.has_loop_interruption_in_descendants(node_id))
                .cloned()
                .collect();

            // Step 3: Split blocks based on marked nodes
            let split_blocks = self.split_block_by_marks(body, &marked_nodes);

            // Step 4: Check sizes and flatten only eligible blocks
            let mut new_body = Vec::new();
            let mut gaps = Vec::new();

            for (node_ids, is_marked) in split_blocks {
                if node_ids.is_empty() {
                    continue;
                }

                let block_start = self
                    .get_node(*node_ids.first().unwrap())
                    .range_start()
                    .unwrap();
                let block_end = self
                    .get_node(*node_ids.last().unwrap())
                    .range_end()
                    .unwrap();
                let block_size = block_end - block_start;

                if !is_marked && block_size > self.threshold {
                    // Large unmarked block: promote to top-level
                    let brace_id = self.insert_brace(cur, &node_ids);
                    new_body.push(brace_id);
                    gaps.push((block_start + 1, block_end));
                    self.parent_stack.push(ParentInfo {
                        node_id: brace_id,
                        flatten: false,
                    });
                    self.walk_body(&node_ids);
                    self.parent_stack.pop();
                } else {
                    // Small block or marked block: leave them as they were
                    new_body.extend(node_ids.iter());
                }
            }

            // Update the for loop structure
            self.get_node_mut(cur).range = gap_range(
                self.get_node_mut(cur).range.pop().unwrap(),
                gaps.into_iter(),
            );
            for word in words {
                self.visit_word(word);
            }

            self.get_node_mut(cur).cmd = AcCommand::new_cmd(ShellCommand::For {
                var: var.to_owned(),
                words: words.to_owned(),
                body: new_body,
            });
        } else {
            self.walk_for(var, words, body)
        }
    }

    /// Handles flattening of case statements
    ///
    /// Large case arms have their body commands promoted to top-level,
    /// while small arms get their commands grouped under brace nodes
    fn visit_case(&mut self, word: &AcWord, arms: &[PatternBodyPair<AcWord>]) {
        if let Some(cur) = self.will_flatten() {
            #[cfg(debug_assertions)]
            {
                let start = self.get_node(cur).range_start().unwrap();
                if let Some(prev) = self.last_range_start {
                    if !(prev <= start) {
                        dbg!(cur, self.last_range_start);
                        panic!();
                    }
                }
                self.last_range_start = Some(start);
            }
            let ranges = arms
                .iter()
                .map(|arm| self.body_range(&arm.body))
                .collect::<Vec<_>>();
            let gaps = ranges
                .iter()
                .flatten()
                .filter(|(s, e)| e - s > 0)
                .cloned()
                .collect::<Vec<_>>();
            self.get_node_mut(cur).range = gap_range(
                self.get_node_mut(cur).range.pop().unwrap(),
                gaps.into_iter(),
            );
            let mut new_arms = Vec::new();
            for (arm, body_range) in arms.iter().zip(ranges.iter()) {
                if let Some((body_start, body_end)) = body_range {
                    if (body_end - body_start) > self.threshold {
                        new_arms.push(arm.clone());
                        self.flattened_top_ids.extend(&arm.body);
                        self.walk_pattern_body_pair(arm);
                    } else {
                        let brace_id = self.insert_brace(cur, &arm.body);
                        new_arms.push(PatternBodyPair {
                            comments: arm.comments.to_owned(),
                            patterns: arm.patterns.to_owned(),
                            body: vec![brace_id],
                        });
                        for w in &arm.patterns {
                            self.visit_word(w);
                        }
                        self.parent_stack.push(ParentInfo {
                            node_id: brace_id,
                            flatten: false,
                        });
                        self.walk_body(&arm.body);
                        self.parent_stack.pop();
                    }
                } else {
                    // arm.body should be empty
                    new_arms.push(arm.clone());
                }
            }
            // Update the case statement to use the new structure
            self.get_node_mut(cur).cmd = AcCommand::new_cmd(ShellCommand::Case {
                word: word.to_owned(),
                arms: new_arms,
            })
        } else {
            self.walk_case(word, arms);
        }
    }

    /// Handles flattening of if statements
    ///
    /// Large if/else branches have their body commands promoted to top-level,
    /// while small branches get their commands grouped under brace nodes
    fn visit_if(&mut self, conditionals: &[GuardBodyPair<AcWord>], else_branch: &[NodeId]) {
        if let Some(cur) = self.will_flatten() {
            #[cfg(debug_assertions)]
            {
                let start = self.get_node(cur).range_start().unwrap();
                if let Some(prev) = self.last_range_start {
                    if !(prev <= start) {
                        dbg!(cur, self.last_range_start);
                        panic!();
                    }
                }
                self.last_range_start = Some(start);
            }
            let gaps = conditionals
                .iter()
                .map(|c| c.body.as_slice())
                .chain(std::iter::once(else_branch))
                .filter(|body| !body.is_empty())
                .map(|body| self.body_range(body))
                .collect::<Vec<_>>();
            self.analyzer.get_node_mut(cur).range = gap_range(
                self.get_node_mut(cur).range.pop().unwrap(),
                gaps.into_iter().flatten(),
            );
            let mut new_conditionals = Vec::new();
            let mut new_else_branch = Vec::new();
            for pair in conditionals.iter() {
                if let Some((body_start, body_end)) = self.body_range(&pair.body) {
                    if body_end - body_start > self.threshold {
                        new_conditionals.push(pair.clone());
                        self.flattened_top_ids.extend(&pair.body);
                        self.walk_guard_body_pair(pair);
                    } else {
                        let brace_id = self.insert_brace(cur, &pair.body);
                        new_conditionals.push(GuardBodyPair {
                            condition: pair.condition.to_owned(),
                            body: vec![brace_id],
                        });
                        self.parent_stack.push(ParentInfo {
                            node_id: brace_id,
                            flatten: false,
                        });
                        self.walk_guard_body_pair(pair);
                        self.parent_stack.pop();
                    }
                } else {
                    // pair.body should be empty
                    new_conditionals.push(pair.clone());
                }
            }
            if !else_branch.is_empty() {
                let (body_start, body_end) = self.body_range(else_branch).unwrap();
                if body_end - body_start > self.threshold {
                    new_else_branch.extend(else_branch);
                    self.flattened_top_ids.extend(else_branch);
                    self.walk_body(else_branch);
                } else {
                    let brace_id = self.insert_brace(cur, &else_branch);
                    new_else_branch.push(brace_id);
                    self.parent_stack.push(ParentInfo {
                        node_id: brace_id,
                        flatten: false,
                    });
                    self.walk_body(else_branch);
                    self.parent_stack.pop();
                }
            }
            // Update the if statement to use the new structure
            self.analyzer.get_node_mut(cur).cmd = AcCommand::new_cmd(ShellCommand::If {
                conditionals: new_conditionals,
                else_branch: new_else_branch,
            });
        } else {
            self.walk_if(conditionals, else_branch);
        }
    }
}

/// Breaks a range into multiple ranges by removing overlapping parts with gaps
///
/// This function takes a source range and a list of gap ranges, then returns
/// a list of ranges that represent the original range with the gaps removed.
/// Used when flattening to exclude child command ranges from parent ranges.
fn gap_range<I: Iterator<Item = (usize, usize)>>(
    range: (usize, usize),
    gaps: I,
) -> Vec<(usize, usize)> {
    let mut result = Vec::new();
    let mut current_start = range.0;
    let range_end = range.1;

    let mut gaps = gaps.collect::<Vec<_>>();
    gaps.sort_by_key(|g| g.0);

    for (gap_start, gap_end) in gaps {
        if gap_end < current_start {
            continue;
        }
        if gap_start > range_end {
            break;
        }

        if gap_start > current_start {
            result.push((current_start, gap_start));
        }

        // Update current position to after this gap
        current_start = current_start.max(gap_end);
    }
    if current_start <= range_end {
        result.push((current_start, range_end));
    }
    result
}
