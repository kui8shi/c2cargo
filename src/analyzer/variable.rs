use std::{collections::HashMap, hash::Hash};

use super::{
    AcWord, AcWordFragment, Analyzer, Arithmetic, AstVisitor, M4Macro, MayM4, Node, NodeId,
    Parameter, VariableMap, Word, WordFragment, Condition
};

#[derive(Debug, Clone, PartialEq, Eq, Ord, Hash)]
pub(crate) struct Location {
    pub node_id: NodeId,
    pub line: usize,
    pub is_left: bool,
}

impl PartialOrd for Location {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some((self.line, self.is_left).cmp(&(other.line, other.is_left)))
    }
}

/// Struct represents various types of variable names used in assignments.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum Identifier {
    /// String literal. Direct variable reference.
    Name(String),
    /// Variable name. Indirect variable reference.
    Indirect(String, Location),
    /// Dynamically constructed variable name. Indirect variable reference.
    Concat(Vec<Identifier>),
}

/// Struct represents various types of values assigned to variables.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum ValueExpr {
    /// String literal. It could be used in lhs or rhs.
    Lit(String),
    /// Values referenced via a variable. It could used in lhs or rhs.
    Var(String, Location),
    /// String literal represented as a concatenation of rvalues
    Concat(Vec<ValueExpr>),
    /// Dynamically constructed variable name.
    /// e.g. \"\$${var1}_${var2}_suffix\" becomes Ref([Var(var1), Lit(_), Var(var2), Lit(_suffix)])
    DynName(Vec<ValueExpr>),
    /// Arbitrary shell commands applied to emit values
    /// (shell_string, depending_variables)
    Shell(String, Vec<ValueExpr>),
}

impl ValueExpr {
    pub(crate) fn vars(&self) -> Option<Vec<(String, Location)>> {
        match self {
            ValueExpr::Lit(_) => None,
            ValueExpr::Var(s, loc) => Some(vec![(s.to_owned(), loc.clone())]),
            ValueExpr::Concat(v) => Some(v.iter().map(|e| e.vars()).flatten().flatten().collect()),
            ValueExpr::DynName(v) => Some(v.iter().map(|e| e.vars()).flatten().flatten().collect()),
            ValueExpr::Shell(_, v) => {
                Some(v.iter().map(|e| e.vars()).flatten().flatten().collect())
            }
        }
    }
}

impl Into<Option<Identifier>> for &ValueExpr {
    fn into(self) -> Option<Identifier> {
        match self {
            ValueExpr::Lit(_) => None,
            ValueExpr::Var(name, _loc) => Some(Identifier::Name(name.to_owned())),
            ValueExpr::DynName(rvalues) => Some(Identifier::Concat({
                let mut lvalues = Vec::new();
                for rvalue in rvalues {
                    match rvalue {
                        ValueExpr::Lit(lit) => {
                            lvalues.push(Identifier::Name(lit.to_owned()));
                        }
                        ValueExpr::Var(name, loc) => {
                            lvalues.push(Identifier::Indirect(name.to_owned(), loc.clone()));
                        }
                        _ => return None,
                    }
                }
                lvalues
            })),
            _ => None,
        }
    }
}

#[derive(Debug)]
pub(super) struct VariableAnalyzer<'a> {
    analyzer: &'a mut Analyzer,
    cursor: Option<NodeId>,
}

impl<'a> VariableAnalyzer<'a> {
    /// Create a new VariableAnalyzer and visit the given command.
    pub fn analyze_variables(analyzer: &'a mut Analyzer) {
        let mut s = Self {
            analyzer,
            cursor: None,
        };

        for id in s.analyzer.get_top_ids() {
            s.visit_top(id);
        }

        // collect recorded definitions
        let var_definitions: VariableMap = s
            .analyzer
            .pool
            .nodes
            .iter()
            .map(|(_, n)| n.info.defines.iter())
            .flatten()
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
        let var_usages: VariableMap = s
            .analyzer
            .pool
            .nodes
            .iter()
            .map(|(_, n)| n.info.uses.iter())
            .flatten()
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

        s.analyzer.var_definitions = var_definitions;
        s.analyzer.var_usages = var_usages;

        let mut def_use_edges = Vec::new();
        // Calculate dependency edges
        for (user_id, node) in &s.analyzer.pool.nodes {
            for var in node.info.uses.keys() {
                if let Some(def_id) = s.analyzer.get_dominant_definition(var, user_id) {
                    def_use_edges.push((def_id, user_id, var.to_owned()));
                }
            }
        }
        s.analyzer.apply_def_use_edges(def_use_edges);
    }
}

impl<'a> VariableAnalyzer<'a> {
    fn current_location(&self) -> Location {
        Location {
            node_id: self.cursor.unwrap(),
            line: self.get_node(self.cursor.unwrap()).range_start().unwrap(),
            is_left: true,
        }
    }

    fn record_variable_definition(&mut self, name: &str) {
        let node_id = self.cursor.unwrap();
        let loc = self.current_location();
        self.analyzer
            .get_node_mut(node_id)
            .info
            .defines
            .entry(name.to_owned())
            .or_default()
            .push(loc.clone());
    }

    fn record_variable_usage(&mut self, name: &str) {
        let node_id = self.cursor.unwrap();
        let loc = self.current_location();
        self.analyzer
            .get_node_mut(node_id)
            .info
            .uses
            .entry(name.to_owned())
            .or_default()
            .push(loc.clone());
    }

    /// parse a body of eval assignment. It is expected to take `word` as a concatenated word fragments
    /// currently we don't support mixed lhs value (eigther single literal or single variable)
    fn parse_eval_assignment(&self, frags: &[AcWordFragment]) -> (Identifier, Option<ValueExpr>) {
        let mut lhs = Vec::new();
        let mut rhs = Vec::new();
        let mut is_lhs = true;
        let mut is_ref = false;
        let loc = self.current_location();
        for frag in frags.iter() {
            use MayM4::*;
            match frag {
                Shell(WordFragment::Escaped(s)) if s == "\"" => (),
                Shell(WordFragment::Escaped(s)) if s == "$" => {
                    is_ref = true;
                }
                Shell(WordFragment::Param(Parameter::Var(s))) if is_lhs => {
                    lhs.push(Identifier::Indirect(s.to_owned(), loc.clone()));
                }
                Shell(WordFragment::Param(Parameter::Var(s))) if !is_lhs => {
                    rhs.push(ValueExpr::Var(s.to_owned(), loc.clone()));
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
                                rhs.push(ValueExpr::Var(s.to_owned(), loc.clone()));
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
    fn get_node(&self, node_id: NodeId) -> &Node {
        self.analyzer.get_node(node_id)
    }

    fn visit_top(&mut self, node_id: NodeId) {
        self.cursor.replace(node_id);
        self.walk_node(node_id);
    }

    fn visit_node(&mut self, node_id: NodeId) {
        // Save
        let saved_cursor = self.cursor.replace(node_id);
        // Walk
        if !self.get_node(node_id).info.is_top_node() {
            self.walk_node(node_id);
        }
        // Recover
        self.cursor = saved_cursor;
    }

    fn visit_assignment(&mut self, name: &str, word: &AcWord) {
        self.record_variable_definition(name);
        self.walk_assignment(name, word);
    }

    fn visit_for(&mut self, var: &str, words: &[AcWord], body: &[NodeId]) {
        self.record_variable_definition(var);
        self.walk_for(var, words, body);
    }

    fn visit_word_fragment(&mut self, f: &AcWordFragment) {
        if let MayM4::Shell(WordFragment::Param(Parameter::Var(name))) = f {
            self.record_variable_usage(name);
        }
        self.walk_word_fragment(f);
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
        if let Some(first) = cmd_words.get(0) {
            if is_eval(first) {
                if let Some(Word::Concat(frags)) = cmd_words.get(1).map(|t| &t.0) {
                    let (lhs, rhs) = self.parse_eval_assignment(frags);
                    let loc = Location {
                        node_id: self.cursor.unwrap(),
                        line: self.get_node(self.cursor.unwrap()).range_start().unwrap(),
                        is_left: true,
                    };
                    self.analyzer
                        .evals
                        .entry(lhs)
                        .or_default()
                        .push((rhs, loc.clone()));
                }
            }
        }
        self.walk_command(cmd_words);
    }
}

fn is_eval(word: &AcWord) -> bool {
    match &word.0 {
        Word::Single(f) => matches!(f, MayM4::Shell(WordFragment::Literal(t)) if t == "eval"),
        Word::Concat(frags) => {
            frags.len() == 1
                && matches!(&frags[0], MayM4::Shell(WordFragment::Literal(t)) if t == "eval")
        }
        _ => false,
    }
}
