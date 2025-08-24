use std::collections::HashMap;

use super::{Analyzer, AstVisitor, M4Macro, Node, NodeId};
use slab::Slab;

/// Visitor to find case statements branching given variables.
#[derive(Debug)]
pub(super) struct MacroCallFinder<'a> {
    nodes: &'a Slab<Node>,
    cursor: Option<NodeId>,
    /// Collected case branches where the variable branches one of `var_names`.
    pub found: HashMap<String, Vec<(NodeId, M4Macro)>>,
}

impl Analyzer {
    /// Find case statements matching the given variables in the top-level commands.
    pub fn find_macro_calls(&self) -> HashMap<String, Vec<(NodeId, M4Macro)>> {
        MacroCallFinder::find_macro_calls(&self.pool.nodes, &self.top_ids)
    }
}

impl<'a> MacroCallFinder<'a> {
    /// Create a new BranchFinder for the given variable names.
    pub fn find_macro_calls(
        nodes: &'a Slab<Node>,
        top_ids: &[NodeId],
    ) -> HashMap<String, Vec<(NodeId, M4Macro)>> {
        let mut s = Self {
            nodes,
            cursor: None,
            found: HashMap::new(),
        };
        for &id in top_ids {
            s.visit_top(id);
        }
        s.found
    }
}

impl<'a> AstVisitor for MacroCallFinder<'a> {
    fn get_node(&self, node_id: NodeId) -> &Node {
        &self.nodes[node_id]
    }

    fn visit_top(&mut self, node_id: NodeId) {
        self.cursor.replace(node_id);
        self.walk_node(node_id);
    }

    fn visit_node(&mut self, node_id: NodeId) {
        let saved_cursor = self.cursor.replace(node_id);

        if !self.get_node(node_id).info.is_top_node() {
            self.walk_node(node_id);
        }

        self.cursor = saved_cursor;
    }

    fn visit_m4_macro(&mut self, m4_macro: &M4Macro) {
        self.found
            .entry(m4_macro.name.to_owned())
            .or_default()
            .push((self.cursor.unwrap(), m4_macro.clone()));
        self.walk_m4_macro(m4_macro);
    }
}
