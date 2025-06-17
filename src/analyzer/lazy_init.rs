use std::collections::{HashMap, HashSet};

use super::{AstVisitor, GuardBodyPair, Node, NodeId, NodeKind, PatternBodyPair, Word};
use slab::Slab;

/// A visitor to initialize several blank fields of Node
#[derive(Debug)]
pub(super) struct LazyInitializer {
    /// Collection of all nodes in the AST
    nodes: Slab<Node>,
    /// Stack tracking parent nodes 
    parent_stack: Vec<ParentInfo>,
}

#[derive(Debug)]
struct ParentInfo {
    node_id: NodeId,
    branch: Option<usize>,
    ranges: Option<Vec<(usize, usize)>>,
}

impl LazyInitializer {
    pub fn lazy_init(
        nodes: Slab<Node>,
        top_ids: &[NodeId],
    ) -> Slab<Node> {
        let mut s = Self {
            nodes,
            parent_stack: vec![],
        };

        for &id in top_ids {
            s.visit_top(id);
        }

        s.nodes
    }
}

impl AstVisitor for LazyInitializer {
    fn get_node(&self, node_id: NodeId) -> &Node {
        &self.nodes[node_id]
    }

    /// Visits a top-level node and adds it to the top-level ID list
    fn visit_top(&mut self, node_id: NodeId) {
        self.visit_node(node_id);
    }

    fn visit_node(&mut self, node_id: NodeId) {
        if let Some(parent) = self.parent_stack.last() {
            // Set up parent-child relationships
            self.nodes[node_id].parent = Some((parent.node_id, parent.branch));
            self.nodes[parent.node_id]
                .children
                .get_or_insert_default()
                .push(node_id);
            if self.nodes[node_id].ranges.is_empty() {
                if let Some(ref ranges) = parent.ranges {
                    // propagate ranges information if child doesn't know its range.
                    self.nodes[node_id].ranges = ranges.clone();
                }
            }
        }

        // Push this node onto the parent stack
        self.parent_stack.push(ParentInfo {
            node_id,
            branch: None,
            ranges: Some(self.nodes[node_id].ranges.clone()),
        });

        // Recursively process this node's children
        self.walk_node(node_id);

        // Pop this node from the stack when done processing its subtree
        self.parent_stack.pop();
    }
}
