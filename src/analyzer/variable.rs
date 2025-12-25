use std::{
    collections::{HashMap, HashSet},
    hash::Hash,
};

use bincode::{Decode, Encode};

use super::{
    location::Location, AcWord, AcWordFragment, Analyzer, Arithmetic, AstVisitor, ExecId, M4Macro,
    MayM4, Node, NodeId, Parameter, ShellCommand, VariableMap, Word, WordFragment,
};

/// Struct represents various types of variable names used in assignments.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Encode, Decode)]
pub(crate) enum Identifier {
    /// String literal. Direct variable reference.
    Name(String),
    /// Variable name. Indirect variable reference.
    Indirect(String),
    /// Dynamically constructed variable name. Indirect variable reference.
    Concat(Vec<Self>),
}

/// Struct represents various types of values assigned to variables.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Encode, Decode)]
pub(crate) enum ValueExpr {
    /// String literal. It could be used in lhs or rhs.
    Lit(String),
    /// Values referenced via a variable. It could used in lhs or rhs.
    Var(String, Location),
    /// String literal represented as a concatenation of values
    Concat(Vec<ValueExpr>),
    /// Dynamically constructed variable name.
    /// e.g. \"\$${var1}_${var2}_suffix\" becomes DynName([Var(var1), Lit(_), Var(var2), Lit(_suffix)])
    DynName(Vec<ValueExpr>),
    /// Arbitrary shell commands applied to emit values
    /// (shell_string, depending_variables)
    Shell(String, Vec<ValueExpr>),
}

impl Identifier {
    pub(crate) fn is_indirect(&self) -> bool {
        match self {
            Self::Concat(v) => v.iter().any(|i| i.is_indirect()),
            Self::Indirect(_) => true,
            Self::Name(_) => false,
        }
    }

    pub(crate) fn vars(&self) -> Option<Vec<String>> {
        match self {
            Self::Name(_) => None,
            Self::Indirect(s) => Some(vec![s.to_owned()]),
            Self::Concat(v) => Some(v.iter().filter_map(|e| e.vars()).flatten().collect()),
        }
    }

    pub(crate) fn positional_vars(&self) -> Vec<Option<String>> {
        match self {
            Self::Name(_) => vec![None],
            Self::Indirect(s) => vec![Some(s.to_owned())],
            Self::Concat(v) => v.iter().flat_map(|e| e.positional_vars()).collect(),
        }
    }
}

impl ValueExpr {
    pub(crate) fn vars(&self) -> Option<Vec<String>> {
        match self {
            Self::Lit(_) => None,
            Self::Var(s, _) => Some(vec![s.to_owned()]),
            Self::Concat(v) => Some(v.iter().filter_map(|e| e.vars()).flatten().collect()),
            Self::DynName(v) => Some(v.iter().filter_map(|e| e.vars()).flatten().collect()),
            Self::Shell(_, v) => Some(v.iter().filter_map(|e| e.vars()).flatten().collect()),
        }
    }
}

impl Into<Option<Identifier>> for &ValueExpr {
    fn into(self) -> Option<Identifier> {
        match self {
            ValueExpr::Lit(_) => None,
            ValueExpr::Var(name, _loc) => Some(Identifier::Name(name.to_owned())),
            ValueExpr::DynName(values) => {
                let mut concat = Vec::new();
                for val in values {
                    match val {
                        ValueExpr::Lit(lit) => {
                            concat.push(Identifier::Name(lit.to_owned()));
                        }
                        ValueExpr::Var(name, _) => {
                            concat.push(Identifier::Indirect(name.to_owned()));
                        }
                        _ => return None,
                    }
                }
                if concat.len() <= 1 {
                    concat.pop()
                } else {
                    Some(Identifier::Concat(concat))
                }
            }
            _ => None,
        }
    }
}

#[derive(Debug)]
pub(super) struct VariableAnalyzer<'a> {
    analyzer: &'a mut Analyzer,
    cursor: Option<NodeId>,
    order: usize,
    exec_id: ExecId,
}

impl<'a> VariableAnalyzer<'a> {
    /// Create a new VariableAnalyzer and visit the given command.
    pub fn analyze_variables(analyzer: &'a mut Analyzer) {
        analyzer.eval_assigns.replace(Default::default());

        let mut s = Self {
            analyzer,
            cursor: None,
            order: 0,
            exec_id: 0,
        };

        for id in s.analyzer.get_top_ids() {
            s.visit_top(id);
        }
    }
}

impl<'a> VariableAnalyzer<'a> {
    fn increment_order(&mut self) {
        self.order += 1;
    }

    fn set_order(&mut self, order: usize) -> usize {
        let old = self.order;
        self.order = order;
        old
    }

    fn current_location(&self) -> Location {
        let node_id = self.cursor.unwrap();
        let node = self.get_node(node_id).unwrap();
        let exec_id = node.info.exec_id;
        let order = self.order;
        let line = node.range_start().unwrap();
        Location {
            node_id,
            exec_id,
            order_in_expr: order,
            line,
        }
    }

    fn record_exec_id(&mut self) {
        let node_id = self.cursor.unwrap();
        self.analyzer.get_node_mut(node_id).unwrap().info.exec_id = self.exec_id;
        self.exec_id += 1;
    }

    fn record_exit(&mut self) {
        let node_id = self.cursor.unwrap();
        self.analyzer.get_node_mut(node_id).unwrap().info.exit = self.exec_id;
    }

    fn record_variable_definition(&mut self, name: &str) {
        let node_id = self.cursor.unwrap();
        let def_loc = self.current_location();
        self.analyzer
            .get_node_mut(node_id)
            .unwrap()
            .info
            .definitions
            .entry(name.to_owned())
            .or_default()
            .push(def_loc);
        self.increment_order();
    }

    fn record_variable_usage(&mut self, name: &str) {
        let node_id = self.cursor.unwrap();
        let ref_loc = self.current_location();
        self.analyzer
            .get_node_mut(node_id)
            .unwrap()
            .info
            .usages
            .entry(name.to_owned())
            .or_default()
            .push(ref_loc);
        self.increment_order();
    }

    fn record_variable_bind(&mut self, name: &str) {
        let node_id = self.cursor.unwrap();
        let bind_loc = self.current_location();
        self.analyzer
            .get_node_mut(node_id)
            .unwrap()
            .info
            .bounds
            .entry(name.to_owned())
            .or_default()
            .push(bind_loc);
    }

    fn check_propagation(&mut self) {
        let node_id = self.cursor.unwrap();
        let def_loc = self.current_location();
        let branches = &self.analyzer.get_node(node_id).unwrap().info.branches;
        if branches.len() > 1 {
            // FIXME this is incorrect. checking !else_branch.is_empty is more strict
            let vars_defined_across_all_branches = branches
                .iter()
                .filter(|block_id| !self.analyzer.get_block(**block_id).error_out)
                .map(|block_id| {
                    self.analyzer
                        .get_block(*block_id)
                        .nodes
                        .iter()
                        .flat_map(|id| {
                            let node = self.analyzer.get_node(*id).unwrap();
                            node.info
                                .definitions
                                .keys()
                                .chain(node.info.propagated_definitions.keys())
                        })
                        .cloned()
                        .collect::<HashSet<_>>()
                })
                .reduce(|a, b| &a & &b)
                .unwrap_or_default();
            for var in vars_defined_across_all_branches {
                self.analyzer
                    .get_node_mut(node_id)
                    .unwrap()
                    .info
                    .propagated_definitions
                    .entry(var.to_owned())
                    .or_default()
                    .push(def_loc.clone());
            }
        }
        self.increment_order();
    }

    /// parse a body of eval assignment. It is expected to take `word` as a concatenated word fragments
    /// currently we don't support mixed lhs value (eigther single literal or single variable)
    fn visit_eval_assignment(
        &mut self,
        frags: &[AcWordFragment],
    ) -> (Identifier, Option<ValueExpr>) {
        let mut lhs = Vec::new();
        let mut rhs = Vec::new();
        let mut is_lhs = true;
        let mut is_ref = false;
        for frag in frags.iter() {
            use MayM4::*;
            match frag {
                Shell(WordFragment::Escaped(s)) if s == "\"" => (),
                Shell(WordFragment::Escaped(s)) if s == "$" => {
                    is_ref = true;
                }
                Shell(WordFragment::Param(Parameter::Var(s))) if is_lhs => {
                    self.record_variable_usage(s);
                    lhs.push(Identifier::Indirect(s.to_owned()));
                }
                Shell(WordFragment::Param(Parameter::Var(s))) if !is_lhs => {
                    let ref_loc = self.current_location();
                    self.record_variable_usage(s);
                    rhs.push(ValueExpr::Var(s.to_owned(), ref_loc));
                }
                Shell(WordFragment::Literal(s)) if is_lhs => {
                    if s.contains("=") {
                        let mut split = s.split("=");
                        if let Some(lit) = split.next() {
                            if !lit.is_empty() {
                                lhs.push(Identifier::Name(lit.to_owned()));
                            }
                        }
                        if let Some(lit) = split.next() {
                            if !lit.is_empty() {
                                rhs.push(ValueExpr::Lit(lit.to_owned()));
                            }
                        }
                        is_lhs = false;
                    } else {
                        lhs.push(Identifier::Name(s.to_owned()));
                    }
                }
                Shell(WordFragment::Literal(s)) if !is_lhs => {
                    let s = s.strip_prefix("=").unwrap_or(s).to_owned();
                    rhs.push(ValueExpr::Lit(s));
                }
                Shell(WordFragment::DoubleQuoted(inner_frags)) if !is_lhs => {
                    for inner_frag in inner_frags {
                        match inner_frag {
                            WordFragment::Escaped(s) if s == "$" => {
                                is_ref = true;
                            }
                            WordFragment::Literal(s) => {
                                rhs.push(ValueExpr::Lit(s.to_owned()));
                            }
                            WordFragment::Param(Parameter::Var(s)) => {
                                let ref_loc = self.current_location();
                                self.record_variable_usage(s);
                                rhs.push(ValueExpr::Var(s.to_owned(), ref_loc));
                            }
                            _ => (),
                        }
                    }
                }
                _ => (),
            }
        }
        let lhs = if lhs.len() <= 1 {
            lhs.pop().unwrap()
        } else {
            Identifier::Concat(lhs)
        };
        if is_ref {
            rhs = vec![ValueExpr::DynName(rhs)];
        }
        if rhs.len() <= 1 {
            (lhs, rhs.pop())
        } else {
            (lhs, Some(ValueExpr::Concat(rhs)))
        }
    }
}

impl<'a> AstVisitor for VariableAnalyzer<'a> {
    fn get_node(&self, node_id: NodeId) -> Option<&Node> {
        self.analyzer.get_node(node_id)
    }

    fn visit_top(&mut self, node_id: NodeId) {
        if self
            .get_node(node_id)
            .is_none_or(|n| n.info.is_child_node())
        {
            return;
        }
        self.visit_node(node_id)
    }

    fn visit_node(&mut self, node_id: NodeId) {
        if self.get_node(node_id).is_none() {
            return;
        }
        let saved_cursor = self.cursor.replace(node_id);
        let saved_order = self.set_order(0);
        self.record_exec_id();
        self.walk_node(node_id);
        self.record_exit();
        self.check_propagation();
        self.set_order(saved_order);
        self.cursor = saved_cursor;
    }

    fn visit_assignment(&mut self, name: &str, word: &AcWord) {
        self.walk_assignment(name, word);
        self.record_variable_definition(name);
    }

    fn visit_for(&mut self, var: &str, words: &[AcWord], body: &[NodeId]) {
        for word in words {
            self.visit_word(word);
        }
        self.record_variable_definition(var);
        self.record_variable_bind(var);
        for cmd in body {
            self.visit_node(*cmd);
        }
    }

    fn visit_arithmetic(&mut self, arith: &Arithmetic<String>) {
        match arith {
            Arithmetic::Var(name)
            | Arithmetic::PostIncr(name)
            | Arithmetic::PostDecr(name)
            | Arithmetic::PreIncr(name)
            | Arithmetic::PreDecr(name) => {
                self.record_variable_usage(name);
            }
            _ => (),
        }
        self.walk_arithmetic(arith);
    }

    fn visit_parameter(&mut self, param: &Parameter<String>) {
        if let Parameter::Var(name) = param {
            self.record_variable_usage(name);
        }
        self.walk_parameter(param);
    }

    fn visit_m4_macro(&mut self, m4_macro: &M4Macro) {
        if let Some(effects) = &m4_macro.effects {
            if let Some(shell_vars) = &effects.shell_vars {
                for var in shell_vars {
                    if var.is_used() {
                        self.record_variable_usage(&var.name);
                    }
                    if var.is_defined() {
                        self.record_variable_definition(&var.name);
                    }
                }
            }
        }
        self.walk_m4_macro(m4_macro);
    }

    fn visit_command(&mut self, cmd_words: &[AcWord]) {
        if let Some(first) = cmd_words.first() {
            if is_eval(first) {
                if let Some(Word::Concat(frags)) = cmd_words.get(1).map(|t| &t.0) {
                    // FIXME: eval_loc's `order_in_expr` is inprecisely fixed to 0.
                    let eval_loc = self.current_location();
                    let (lhs, rhs) = self.visit_eval_assignment(frags);
                    if let Identifier::Name(name) = &lhs {
                        self.record_variable_definition(name);
                    }
                    self.analyzer
                        .eval_assigns
                        .as_mut()
                        .unwrap()
                        .entry(lhs)
                        .or_default()
                        .push((rhs, eval_loc.clone()));
                }
                return;
            }
        }
        self.walk_command(cmd_words);
    }
}

pub(crate) fn is_eval(word: &AcWord) -> bool {
    match &word.0 {
        Word::Single(f) => matches!(f, MayM4::Shell(WordFragment::Literal(t)) if t == "eval"),
        Word::Concat(frags) => {
            frags.len() == 1
                && matches!(&frags[0], MayM4::Shell(WordFragment::Literal(t)) if t == "eval")
        }
        _ => false,
    }
}

impl Analyzer {
    pub(super) fn remove_unused_variables(&mut self) {
        let unused_vars = self
            .var_definitions
            .as_ref()
            .unwrap()
            .iter()
            .filter(|(var, locs)| {
                let var = var.as_str();
                let no_usage = locs
                    .iter()
                    .all(|loc| self.get_all_usages_after(var, Some(loc), true).is_empty());
                let no_subst = !self.is_substituted(var);

                no_usage && no_subst
            })
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect::<HashSet<_>>();

        for (unused_var, locs) in unused_vars {
            for loc in locs {
                if self.get_node(loc.node_id).is_some_and(|n| {
                    matches!(&n.cmd.0, MayM4::Shell(ShellCommand::Assignment(_, _)))
                }) {
                    self.remove_node(loc.node_id);
                    self.var_definitions
                        .as_mut()
                        .unwrap()
                        .remove(unused_var.as_str());
                }
            }
        }
    }

    pub(super) fn aggregate_def_use(&mut self) {
        // collect recorded definitions
        let var_definitions: VariableMap = self
            .pool
            .nodes
            .iter()
            .flat_map(|(_, n)| n.info.definitions.iter())
            .fold(HashMap::new(), |mut acc: VariableMap, (name, locs)| {
                acc.entry(name.clone()).or_default().extend(locs.clone());
                acc
            })
            .into_iter()
            .map(|(name, mut locs)| {
                locs.sort();
                (name, locs)
            })
            .collect();

        let var_propagated_definitions: VariableMap = self
            .pool
            .nodes
            .iter()
            .flat_map(|(_, n)| n.info.propagated_definitions.iter())
            .fold(HashMap::new(), |mut acc: VariableMap, (name, locs)| {
                acc.entry(name.clone()).or_default().extend(locs.clone());
                acc
            })
            .into_iter()
            .map(|(name, mut locs)| {
                locs.sort();
                (name, locs)
            })
            .collect();

        // collect recorded usages
        let var_usages: VariableMap = self
            .pool
            .nodes
            .iter()
            .flat_map(|(_, n)| n.info.usages.iter())
            .fold(HashMap::new(), |mut acc: VariableMap, (name, locs)| {
                acc.entry(name.clone()).or_default().extend(locs.clone());
                acc
            })
            .into_iter()
            .map(|(name, mut locs)| {
                locs.sort();
                (name, locs)
            })
            .collect();

        self.var_definitions.replace(var_definitions);
        self.var_propagated_definitions
            .replace(var_propagated_definitions);
        self.var_usages.replace(var_usages);

        let mut def_use_edges = Vec::new();
        // Calculate dependency edges
        for (user_id, node) in &self.pool.nodes {
            for var in node.info.usages.keys() {
                if let Some(def_loc) = self.get_dominant_definition(var, user_id) {
                    def_use_edges.push((def_loc.node_id, user_id, var.to_owned()));
                }
            }
        }
        self.apply_def_use_edges(def_use_edges);
    }
}
