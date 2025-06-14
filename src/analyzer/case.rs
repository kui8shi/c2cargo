use super::{AstVisitor, Node, NodeId, Parameter, PatternBodyPair, Word, WordFragment};
use slab::Slab;

/// Represents a matched case statement on a specific variable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CaseMatch {
    /// The variable being matched (the word in `case $var in`).
    pub var: Word<String>,
    /// The arms (patterns and bodies) of the case statement.
    pub arms: Vec<PatternBodyPair<String>>,
}

/// Visitor to find case statements matching given variables.
#[derive(Debug)]
pub(super) struct CaseAnalyzer<'a> {
    nodes: &'a Slab<Node>,
    var_names: Vec<String>,
    /// Collected case matches where the variable matches one of `var_names`.
    pub matches: Vec<CaseMatch>,
    pub ids: Vec<usize>,
}

impl<'a> CaseAnalyzer<'a> {
    /// Create a new MatchFinder for the given variable names.
    pub fn find_case_matches(
        nodes: &'a Slab<Node>,
        top_ids: &[NodeId],
        var_names: Vec<String>,
    ) -> Self {
        let mut s = Self {
            nodes,
            var_names,
            matches: Vec::new(),
            ids: Vec::new(),
        };
        for &id in top_ids {
            let old = s.matches.len();
            s.visit_top(id);
            let found = old < s.matches.len();
            if found {
                s.ids.push(id);
            }
        }
        s
    }
}

impl<'a> AstVisitor for CaseAnalyzer<'a> {
    fn get_node(&self, node_id: NodeId) -> &Node {
        &self.nodes[node_id]
    }

    fn visit_case(&mut self, word: &Word<String>, arms: &[PatternBodyPair<String>]) {
        if let Word::Single(fragment) = word {
            if let WordFragment::Param(Parameter::Var(name)) = fragment {
                if self.var_names.contains(name) {
                    self.matches.push(CaseMatch {
                        var: word.clone(),
                        arms: arms.to_vec(),
                    });
                }
            }
        }
        self.walk_case(word, arms);
    }
}
