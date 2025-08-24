use super::{
    AcWord, Analyzer, AstVisitor, MayM4, Node, NodeId, Parameter, PatternBodyPair, WordFragment,
};
use autotools_parser::ast::minimal::Word;
use slab::Slab;

/// Visitor to find case statements branching given variables.
#[derive(Debug)]
pub(super) struct CaseBranchFinder<'a, 'b> {
    nodes: &'a Slab<Node>,
    var_names: &'b [&'b str],
    cursor: Option<NodeId>,
    /// Collected case branches where the variable branches one of `var_names`.
    pub found: Vec<NodeId>,
    pub ids: Vec<usize>,
}

impl Analyzer {
    /// Find case statements matching the given variables in the top-level commands.
    pub fn find_case_branches(&self, var_names: &[&str]) -> Vec<NodeId> {
        CaseBranchFinder::find_case_branches(&self.pool.nodes, &self.top_ids, var_names)
    }
}

impl<'a, 'b> CaseBranchFinder<'a, 'b> {
    /// Create a new BranchFinder for the given variable names.
    pub fn find_case_branches(
        nodes: &'a Slab<Node>,
        top_ids: &[NodeId],
        var_names: &'b [&str],
    ) -> Vec<NodeId> {
        let mut s = Self {
            nodes,
            var_names,
            cursor: None,
            found: Vec::new(),
            ids: Vec::new(),
        };
        for &id in top_ids {
            let old = s.found.len();
            s.visit_top(id);
            let found = old < s.found.len();
            if found {
                s.ids.push(id);
            }
        }
        s.found
    }
}

impl<'a, 'b> AstVisitor for CaseBranchFinder<'a, 'b> {
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

    fn visit_case(&mut self, word: &AcWord, arms: &[PatternBodyPair<AcWord>]) {
        if let Word::Single(fragment) = &word.0 {
            if let MayM4::Shell(WordFragment::Param(Parameter::Var(name))) = fragment {
                if self.var_names.contains(&name.as_str()) {
                    self.found.push(self.cursor.unwrap());
                }
            }
        }
        self.walk_case(word, arms);
    }
}
