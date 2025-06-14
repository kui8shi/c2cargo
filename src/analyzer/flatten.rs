use std::collections::{HashMap, HashSet};

use super::{AstVisitor, GuardBodyPair, Node, NodeId, NodeKind, PatternBodyPair, Word};
use slab::Slab;

/// A visitor to flatten and collect AST nodes into a linear sequence.
///
/// The Flattener transforms deeply nested command structures into a flatter representation
/// by breaking apart large commands (those exceeding a line threshold) and reorganizing
/// their child nodes for better analysis.
#[derive(Debug)]
pub(super) struct Flattener {
    /// Line count threshold - commands exceeding this size will be flattened
    threshold: usize,
    /// Collection of all nodes in the AST
    nodes: Slab<Node>,
    /// IDs of top-level nodes after flattening
    top_ids: Vec<NodeId>,
    /// Stack tracking parent nodes and whether they should be flattened
    parent_stack: Vec<(NodeId, bool)>,
    #[cfg(debug_assertions)]
    /// For debugging: tracks the last range start to ensure proper ordering
    last_range_start: Option<usize>,
}

impl Flattener {
    /// Main entry point for flattening an AST
    ///
    /// Takes a collection of nodes and their initial top-level IDs, then flattens
    /// commands that exceed the line threshold into a more linear structure.
    /// Returns the new top-level node IDs and the modified node collection.
    pub fn flatten(
        nodes: Slab<Node>,
        initial_top_ids: Vec<NodeId>,
        threshold: usize,
    ) -> (Vec<NodeId>, Slab<Node>) {
        let mut s = Self {
            threshold,
            nodes,
            top_ids: Vec::new(),
            parent_stack: vec![],
            #[cfg(debug_assertions)]
            last_range_start: None,
        };

        for id in initial_top_ids {
            s.visit_top(id);
        }

        (s.top_ids, s.nodes)
    }

    /// Determines if a node is "large" and should be flattened
    ///
    /// A node is considered large if its line span exceeds the threshold
    fn is_large(&self, node_id: NodeId) -> bool {
        self.nodes[node_id]
            .ranges
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
            .filter(|(_, flatten)| *flatten)
            .map(|(id, _)| *id)
    }

    /// Creates a synthetic "brace" node to group children under a flattened parent
    ///
    /// When flattening a large command, smaller child commands are grouped under
    /// a brace node to maintain the hierarchical structure while keeping the
    /// parent command at the top level
    fn insert_brace(&mut self, parent: NodeId, children: &[NodeId]) -> NodeId {
        let brace_id = self.nodes.insert(Node {
            node_id: 0,
            top_id: None,
            comment: None,
            ranges: children
                .iter()
                .flat_map(|id| self.nodes[*id].ranges.clone())
                .collect::<Vec<_>>(),
            kind: NodeKind::Brace(children.to_vec()),
            parent: Some(parent),
            children: Some(Vec::new()), // intentionally left blank to be filled later
            defines: HashMap::new(),
            uses: HashMap::new(),
            var_dependencies: HashSet::new(),
            var_dependents: HashSet::new(),
        });
        self.nodes[brace_id].node_id = brace_id;
        self.nodes[brace_id].top_id = Some(brace_id);
        self.top_ids.push(brace_id);
        brace_id
    }

    /// Calculates the line range spanned by a collection of body nodes
    fn body_range(&self, body: &[NodeId]) -> (usize, usize) {
        let body_start = self.nodes[*body.first().unwrap()].range_start().unwrap();
        let body_end = self.nodes[*body.last().unwrap()].range_end().unwrap();
        (body_start, body_end)
    }
}

impl AstVisitor for Flattener {
    fn get_node(&self, node_id: NodeId) -> &Node {
        &self.nodes[node_id]
    }

    /// Visits a top-level node and adds it to the top-level ID list
    fn visit_top(&mut self, node_id: NodeId) {
        self.top_ids.push(node_id);
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
        self.nodes[node_id].top_id = Some(if is_large {
            // Large nodes become their own top-level nodes
            node_id
        } else {
            // For small nodes, we need to find which top-level node they belong to.
            // This is the most complex part of the flattening algorithm.

            // First, get the topmost ancestor (root of current traversal path)
            let top_most = self
                .parent_stack
                .first()
                .map(|(id, _)| *id)
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
                .rposition(|&(_, flatten)| flatten) // Find rightmost flattened ancestor
                .and_then(|i| {
                    // If we found a flattened ancestor, look at what comes after it
                    Some(if i + 1 < self.parent_stack.len() {
                        // There's a node after the flattened ancestor - use that as top_id
                        // This node represents the "container" for children of the flattened ancestor
                        self.parent_stack[i + 1].0
                    } else {
                        // No node after the flattened ancestor - this node becomes its own top
                        // This happens when we're directly under a flattened node
                        node_id
                    })
                })
                .unwrap_or(top_most) // Fallback: if no flattened ancestors, use topmost
        });
        if let Some((parent, _)) = self.parent_stack.last().copied() {
            // Set up parent-child relationships
            self.nodes[node_id].parent = Some(parent);
            self.nodes[parent]
                .children
                .get_or_insert_default()
                .push(node_id);
        }
        #[cfg(debug_assertions)]
        {
            self.last_range_start = self.nodes[node_id].ranges.first().map(|r| r.0);
        }

        // Push this node onto the parent stack with its flattening status
        // The parent_stack serves two purposes:
        // 1. Track the current path from root to this node (for parent-child relationships)
        // 2. Track which ancestors are being flattened (the boolean flag)
        //    This helps determine top_id assignment for descendant nodes
        self.parent_stack.push((node_id, is_large));

        // Recursively process this node's children
        self.walk_node(node_id);

        // Pop this node from the stack when done processing its subtree
        self.parent_stack.pop();
    }

    /// Handles flattening of for loops
    ///
    /// Large for loops have their body commands promoted to top-level,
    /// while small ones get their commands grouped under a brace node
    fn visit_for(&mut self, var: &str, words: &[Word<String>], body: &[NodeId]) {
        if let Some(cur) = self.will_flatten() {
            #[cfg(debug_assertions)]
            {
                let start = self.nodes[cur].range_start().unwrap();
                if let Some(prev) = self.last_range_start {
                    if !(prev <= start) {
                        dbg!(&self.nodes[cur].ranges, cur, self.last_range_start);
                        panic!();
                    }
                }
                self.last_range_start = Some(start);
            }
            let body_start = self.nodes[*body.first().unwrap()].range_start().unwrap();
            let body_end = self.nodes[*body.last().unwrap()].range_end().unwrap();
            let gaps = &[(body_start + 1, body_end)];
            self.nodes[cur].ranges = gap_range(self.nodes[cur].ranges.pop().unwrap(), gaps);
            if (body_end - body_start) > self.threshold {
                // For large bodies, promote child commands to top-level
                self.top_ids.extend(body);
                self.walk_for(var, words, body);
            } else {
                // For small bodies, group children under a brace node
                let brace_id = self.insert_brace(cur, body);
                for word in words {
                    self.visit_word(word);
                }
                self.parent_stack.push((brace_id, false));
                self.visit_brace(body);
                self.parent_stack.pop();
                // Update the for loop to use the new structure
                self.nodes[cur].kind = NodeKind::For {
                    var: var.to_owned(),
                    words: words.to_owned(),
                    body: vec![brace_id],
                };
            }
        } else {
            self.walk_for(var, words, body)
        }
    }

    /// Handles flattening of case statements
    ///
    /// Large case arms have their body commands promoted to top-level,
    /// while small arms get their commands grouped under brace nodes
    fn visit_case(&mut self, word: &Word<String>, arms: &[PatternBodyPair<String>]) {
        if let Some(cur) = self.will_flatten() {
            #[cfg(debug_assertions)]
            {
                let start = self.nodes[cur].range_start().unwrap();
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
                .filter(|(s, e)| e - s > 0)
                .cloned()
                .collect::<Vec<_>>();
            self.nodes[cur].ranges = gap_range(self.nodes[cur].ranges.pop().unwrap(), &gaps);
            let mut new_arms = Vec::new();
            for (arm, (body_start, body_end)) in arms.iter().zip(ranges.iter()) {
                if (body_end - body_start) > self.threshold {
                    new_arms.push(arm.clone());
                    self.top_ids.extend(&arm.body);
                    self.walk_pattern_body_pair(arm);
                } else {
                    let brace_id = self.insert_brace(cur, &arm.body);
                    new_arms.push(PatternBodyPair {
                        patterns: arm.patterns.to_owned(),
                        body: vec![brace_id],
                    });
                    for w in &arm.patterns {
                        self.visit_word(w);
                    }
                    self.parent_stack.push((brace_id, false));
                    self.walk_brace(&arm.body);
                    self.parent_stack.pop();
                }
            }
            // Update the case statement to use the new structure
            self.nodes[cur].kind = NodeKind::Case {
                word: word.to_owned(),
                arms: new_arms,
            }
        } else {
            self.walk_case(word, arms);
        }
    }

    /// Handles flattening of if statements
    ///
    /// Large if/else branches have their body commands promoted to top-level,
    /// while small branches get their commands grouped under brace nodes
    fn visit_if(&mut self, conditionals: &[GuardBodyPair<String>], else_branch: &[NodeId]) {
        if let Some(cur) = self.will_flatten() {
            #[cfg(debug_assertions)]
            {
                let start = self.nodes[cur].range_start().unwrap();
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
            self.nodes[cur].ranges = gap_range(self.nodes[cur].ranges.pop().unwrap(), &gaps);
            let mut new_conditionals = Vec::new();
            let mut new_else_branch = Vec::new();
            for pair in conditionals {
                let (body_start, body_end) = self.body_range(&pair.body);
                if body_end - body_start > self.threshold {
                    new_conditionals.push(pair.clone());
                    self.top_ids.extend(&pair.body);
                    self.walk_guard_body_pair(pair);
                } else {
                    let brace_id = self.insert_brace(cur, &pair.body);
                    new_conditionals.push(GuardBodyPair {
                        condition: pair.condition.to_owned(),
                        body: vec![brace_id],
                    });
                    self.parent_stack.push((brace_id, false));
                    self.walk_guard_body_pair(pair);
                    self.parent_stack.pop();
                }
            }
            if !else_branch.is_empty() {
                let (body_start, body_end) = self.body_range(else_branch);
                if body_end - body_start > self.threshold {
                    new_else_branch.extend(else_branch);
                    self.top_ids.extend(else_branch);
                    self.walk_brace(else_branch);
                } else {
                    let brace_id = self.insert_brace(cur, &else_branch);
                    new_else_branch.push(brace_id);
                    self.parent_stack.push((brace_id, true));
                    self.walk_brace(else_branch);
                    self.parent_stack.pop();
                }
            }
            // Update the if statement to use the new structure
            self.nodes[cur].kind = NodeKind::If {
                conditionals: new_conditionals,
                else_branch: new_else_branch,
            };
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
fn gap_range(range: (usize, usize), gaps: &[(usize, usize)]) -> Vec<(usize, usize)> {
    let mut result = Vec::new();
    let mut current_start = range.0;
    let range_end = range.1;

    let mut gaps = gaps.to_vec();
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
