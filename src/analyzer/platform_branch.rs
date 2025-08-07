use std::collections::{HashMap, HashSet};

use crate::analyzer::{as_shell, as_var};

use super::{
    AcWord, Analyzer, AstVisitor, 
    Node, NodeId, PatternBodyPair,
};

#[derive(Debug)]
pub(super) struct PlatformBranchPrunner<'a> {
    analyzer: &'a Analyzer,
    cursor: Option<NodeId>,
}

impl Analyzer {
    /// run value set analysis to obtain value candidates of variables appeared in eval statements.
    pub fn prune_platform_branch(&self) -> HashSet<NodeId> {
        PlatformBranchPrunner::prune_platform_branch(&self)
    }
}

impl<'a> PlatformBranchPrunner<'a> {
    /// run value set analysis to obtain value candidates of variables appeared in eval statements.
    pub fn prune_platform_branch(analyzer: &'a Analyzer) -> HashSet<NodeId> {
        // we assume variable enumeration is already completed.
        let mut s = Self {
            analyzer,
            cursor: None,
        };
        for &id in &analyzer.top_ids {
            s.visit_top(id);
        }
        HashSet::new()
    }
}

impl<'a> AstVisitor for PlatformBranchPrunner<'a> {
    fn get_node(&self, node_id: NodeId) -> &Node {
        &self.analyzer.get_node(node_id)
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
        if let Some(var) = as_shell(word).and_then(as_var) {
            if matches!(var, "host" | "host_alias" | "host_cpu") {
                println!("Found {}", var);
                println!("{}", self.analyzer.display_node(self.cursor.unwrap()));
            }
        }
    }
}
