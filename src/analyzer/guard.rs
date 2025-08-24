use autotools_parser::ast::node::DisplayNode;
use itertools::Itertools;
use std::collections::HashMap;

use super::{
    AcWord, AstVisitor, AutoconfPool, Condition, GuardBodyPair, MayM4, Node, NodeId, NodeInfo,
    Operator, Parameter, ParameterSubstitution, PatternBodyPair, Word, WordFragment,
};
use crate::analyzer::{as_literal, as_shell, as_var};

/// unique Id to a scoped set of commands (NodeIds).
/// it is needed for identifying which guards are applied to a scope.
pub type ScopeId = usize;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Guard {
    N(bool, Atom), // false if negated
    And(Vec<Self>),
    Or(Vec<Self>),
}

impl Guard {
    fn confirmed(atom: Atom) -> Guard {
        Guard::N(true, atom)
    }

    fn negated(atom: Atom) -> Guard {
        Guard::N(false, atom)
    }

    fn negate_whole(self) -> Guard {
        match self {
            Guard::N(b, atom) => Guard::N(!b, atom),
            Guard::And(guards) => Guard::Or(guards.into_iter().map(|g| g.negate_whole()).collect()),
            Guard::Or(guards) => Guard::And(guards.into_iter().map(|g| g.negate_whole()).collect()),
        }
    }

    fn and(mut guards: Vec<Guard>) -> Guard {
        if guards.len() == 1 {
            guards.pop().unwrap()
        } else {
            Guard::And(guards)
        }
    }

    fn or(mut guards: Vec<Guard>) -> Guard {
        if guards.len() == 1 {
            guards.pop().unwrap()
        } else {
            Guard::Or(guards)
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Atom {
    Arg(ArgCond),
    Arch(String),         // glob string
    OsAbi(String),        // glob string
    CpuExtension(String), // e.g. sse, neon
    BigEndian,
    HasProgram(String),
    HasLibrary(String),
    HasHeader(String),
    /// "${dir}/filename" -> [Var("dir"), Lit("filename")]
    /// true if absolute
    PathExists(Vec<VoL>, bool),
    Compiler(CompilerCheck),
    Var(String, VarCond),
    Cmd(NodeId),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ArgCond {
    Empty,
    Bool(bool),
    Arbitrary,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VarCond {
    Yes,
    No,
    Empty,
    Unset,
    Set,
    Eq(VoL),
    Lt(VoL),
    Le(VoL),
    Gt(VoL),
    Ge(VoL),
    Match(String), // glob string
    MatchAny,      // *
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VoL {
    Var(String),
    Lit(String),
}

fn as_vol(value: &WordFragment<AcWord>) -> Option<VoL> {
    match value {
        WordFragment::Literal(lit) => Some(VoL::Lit(lit.to_owned())),
        WordFragment::DoubleQuoted(frags) if frags.len() == 1 => as_vol(frags.first().unwrap()),
        WordFragment::Param(Parameter::Var(name)) => Some(VoL::Var(name.to_owned())),
        _ => None,
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CompilerCheck {
    Func(String),
    Symbol { name: String, lib: Option<String> },
    Sizeof(String),
    Attribute(String),
    Link(String),
    Compile(String),
}

/// Compare two conditions.
pub(crate) fn cmp_guards(lhs: &Vec<Guard>, rhs: &Vec<Guard>) -> Option<std::cmp::Ordering> {
    for (l, r) in lhs.iter().rev().zip(rhs.iter().rev()) {
        if l != r {
            // not comparable.
            return None;
        }
    }
    // Here, we know that either condition is a subset of the other.
    // we can decide the order simply by the lengths.
    Some(lhs.len().cmp(&rhs.len()))
}

#[derive(Debug)]
pub(super) struct GuardInfo {
    /// node id -> scope id
    pub node_to_scope: HashMap<NodeId, ScopeId>,
    /// scope id -> scope
    pub scopes: Vec<Scope>,
}

#[derive(Debug)]
pub(super) struct Scope {
    pub node_ids: Vec<NodeId>,
    pub owner: NodeId,
    pub guards: Vec<Guard>,
}

/// Visitor to find case statements branching given variables.
#[derive(Debug)]
pub(super) struct GuardAnalyzer<'a> {
    pool: &'a AutoconfPool<NodeInfo>,
    cursor: Option<NodeId>,
    stack: Vec<Guard>,
    info: GuardInfo,
}

impl<'a> GuardAnalyzer<'a> {
    /// Create a new BranchFinder for the given variable names.
    pub fn analyze_guards(pool: &'a AutoconfPool<NodeInfo>, top_ids: &[NodeId]) -> GuardInfo {
        let mut s = Self {
            pool,
            cursor: None,
            stack: Vec::new(),
            info: GuardInfo {
                node_to_scope: HashMap::new(),
                scopes: Vec::new(),
            },
        };
        for &id in top_ids {
            s.visit_top(id);
        }
        s.info
    }

    fn add_scope(&mut self, node_ids: &[NodeId]) {
        if node_ids.is_empty() {
            return
        }
        let new_scope_id = self.info.scopes.len();
        for node_id in node_ids {
            self.info.node_to_scope.insert(*node_id, new_scope_id);
        }
        self.info.scopes.push(Scope {
            node_ids: node_ids.to_vec(),
            owner: self.cursor.unwrap(),
            guards: self.stack.clone(),
        });
    }

    fn negate_last_guard(&mut self) {
        let guard = self.stack.pop().unwrap();
        self.stack.push(guard.negate_whole());
    }

    fn equality(&self, a: &AcWord, b: &AcWord) -> Option<Atom> {
        fn interpret_literal(lit: &str) -> VarCond {
            match lit {
                "yes" => VarCond::Yes,
                "no" => VarCond::No,
                "" => VarCond::Empty,
                _ => VarCond::Eq(VoL::Lit(lit.to_owned())),
            }
        }

        fn cancel_x(
            x: &WordFragment<AcWord>,
            var: &WordFragment<AcWord>,
            x_lit: &WordFragment<AcWord>,
        ) -> Option<Atom> {
            if Some("x") == as_literal(x) {
                if let Some(var) = as_var(var) {
                    if let Some(x_lit) = as_literal(x_lit) {
                        if let Some(lit) = x_lit.strip_prefix("x") {
                            return Some(Atom::Var(var.to_owned(), interpret_literal(lit)));
                        }
                    }
                }
            }
            None
        }
        match &a.0 {
            Word::Empty => {
                if let Some(var) = as_shell(b).and_then(as_var) {
                    Some(Atom::Var(var.to_owned(), VarCond::Empty))
                } else {
                    None
                }
            }
            Word::Single(MayM4::Shell(w)) => {
                if let WordFragment::Subst(subst) = w {
                    if let ParameterSubstitution::Alternative(
                        _,
                        Parameter::Var(name),
                        Some(alter),
                    ) = &**subst
                    {
                        if alter == b {
                            return Some(Atom::Var(name.to_owned(), VarCond::Set));
                        }
                    } else if let ParameterSubstitution::Default(
                        _,
                        Parameter::Var(name),
                        Some(default),
                    ) = &**subst
                    {
                        if default == b {
                            return Some(Atom::Var(name.to_owned(), VarCond::Unset));
                        }
                    } else if let ParameterSubstitution::Assign(
                        _,
                        Parameter::Var(name),
                        Some(default),
                    ) = &**subst
                    {
                        if default == b {
                            return Some(Atom::Var(name.to_owned(), VarCond::Unset));
                        }
                    }
                } else if let Some(b) = as_shell(b) {
                    if let WordFragment::DoubleQuoted(frags) = w {
                        if frags.len() == 2 {
                            return cancel_x(&frags[0], &frags[1], b);
                        }
                    } else if let Some(var) = as_var(w) {
                        if let Some(lit) = as_literal(b) {
                            return Some(Atom::Var(var.to_owned(), interpret_literal(lit)));
                        } else if let Some(b) = as_vol(b) {
                            return Some(Atom::Var(var.to_owned(), VarCond::Eq(b)));
                        }
                    }
                }
                None
            }
            Word::Concat(concat) if concat.len() == 2 => {
                if let Some(b) = as_shell(b) {
                    if let MayM4::Shell(x) = concat.get(0).unwrap() {
                        if let MayM4::Shell(a) = concat.get(1).unwrap() {
                            return cancel_x(x, a, b);
                        }
                    }
                }
                None
            }
            _ => None,
        }
    }

    fn condition_to_guard(&self, cond: &Condition<AcWord>) -> Guard {
        match cond {
            Condition::And(c1, c2) => Guard::And(vec![
                self.condition_to_guard(c1),
                self.condition_to_guard(c2),
            ]),
            Condition::Or(c1, c2) => Guard::Or(vec![
                self.condition_to_guard(c1),
                self.condition_to_guard(c2),
            ]),
            Condition::Eval(cmd) | Condition::ReturnZero(cmd) => Guard::N(true, Atom::Cmd(**cmd)),
            Condition::Cond(op) => match op {
                Operator::Eq(w1, w2) => {
                    let atom = if let Some(res) = self.equality(w1, w2) {
                        res
                    } else if let Some(res) = self.equality(w2, w1) {
                        res
                    } else {
                        dbg!(w1, w2);
                        panic!("unsupported syntax");
                    };
                    Guard::confirmed(atom)
                }
                Operator::Neq(w1, w2) => {
                    let atom = if let Some(res) = self.equality(w1, w2) {
                        res
                    } else if let Some(res) = self.equality(w2, w1) {
                        res
                    } else {
                        dbg!(w1, w2);
                        panic!("unsupported syntax");
                    };
                    Guard::negated(atom)
                }
                Operator::Ge(w1, w2) => {
                    let atom = if let Some(v1) = as_shell(w1).and_then(as_var) {
                        if let Some(v2) = as_shell(w2).and_then(as_vol) {
                            Atom::Var(v1.to_owned(), VarCond::Ge(v2))
                        } else {
                            panic!("unsupported syntax");
                        }
                    } else if let Some(v2) = as_shell(w2).and_then(as_var) {
                        if let Some(v1) = as_shell(w1).and_then(as_vol) {
                            Atom::Var(v2.to_owned(), VarCond::Le(v1))
                        } else {
                            panic!("unsupported syntax");
                        }
                    } else {
                        panic!("unsupported syntax");
                    };
                    Guard::confirmed(atom)
                }
                Operator::Gt(w1, w2) => {
                    let atom = if let Some(v1) = as_shell(w1).and_then(as_var) {
                        if let Some(v2) = as_shell(w2).and_then(as_vol) {
                            Atom::Var(v1.to_owned(), VarCond::Gt(v2))
                        } else {
                            panic!("unsupported syntax");
                        }
                    } else if let Some(v2) = as_shell(w2).and_then(as_var) {
                        if let Some(v1) = as_shell(w1).and_then(as_vol) {
                            Atom::Var(v2.to_owned(), VarCond::Lt(v1))
                        } else {
                            panic!("unsupported syntax");
                        }
                    } else {
                        dbg!(w1, w2);
                        panic!("unsupported syntax");
                    };
                    Guard::confirmed(atom)
                }
                Operator::Le(w1, w2) => {
                    let atom = if let Some(v1) = as_shell(w1).and_then(as_var) {
                        if let Some(v2) = as_shell(w2).and_then(as_vol) {
                            Atom::Var(v1.to_owned(), VarCond::Le(v2))
                        } else {
                            panic!("unsupported syntax");
                        }
                    } else if let Some(v2) = as_shell(w2).and_then(as_var) {
                        if let Some(v1) = as_shell(w1).and_then(as_vol) {
                            Atom::Var(v2.to_owned(), VarCond::Ge(v1))
                        } else {
                            panic!("unsupported syntax");
                        }
                    } else {
                        panic!("unsupported syntax");
                    };
                    Guard::confirmed(atom)
                }
                Operator::Lt(w1, w2) => {
                    let atom = if let Some(v2) = as_shell(w2).and_then(as_var) {
                        if let Some(v1) = as_shell(w1).and_then(as_vol) {
                            Atom::Var(v2.to_owned(), VarCond::Lt(v1))
                        } else {
                            panic!("unsupported syntax");
                        }
                    } else if let Some(v2) = as_shell(w2).and_then(as_var) {
                        if let Some(v1) = as_shell(w1).and_then(as_vol) {
                            Atom::Var(v2.to_owned(), VarCond::Gt(v1))
                        } else {
                            panic!("unsupported syntax");
                        }
                    } else {
                        panic!("unsupported syntax");
                    };
                    Guard::confirmed(atom)
                }
                Operator::Empty(w) => {
                    if let Some(name) = as_shell(w).and_then(as_var) {
                        Guard::confirmed(Atom::Var(name.to_owned(), VarCond::Empty))
                    } else {
                        panic!("unsupported syntax");
                    }
                }
                Operator::NonEmpty(w) => {
                    if let Some(name) = as_shell(w).and_then(as_var) {
                        Guard::negated(Atom::Var(name.to_owned(), VarCond::Empty))
                    } else {
                        panic!("unsupported syntax");
                    }
                }
                Operator::Dir(w) | Operator::File(w) => {
                    let (path, is_absolute) = analyze_path(w);
                    Guard::confirmed(Atom::PathExists(path, is_absolute))
                }
                Operator::NoExists(w) => {
                    let (path, is_absolute) = analyze_path(w);
                    Guard::negated(Atom::PathExists(path, is_absolute))
                }
            },
        }
    }

    fn pattern_to_guard(&self, word: &AcWord, pattern: &AcWord) -> Option<Guard> {
        if let Some(word) = as_shell(word) {
            let word = if let &WordFragment::DoubleQuoted(frags) = &word {
                if frags.len() == 1 {
                    frags.first().clone().unwrap()
                } else {
                    word
                }
            } else {
                word
            };
            if let Some(var) = as_var(word) {
                match &pattern.0 {
                    Word::Empty => {
                        Some(Guard::confirmed(Atom::Var(var.to_owned(), VarCond::Empty)))
                    }
                    Word::Single(MayM4::Shell(pat)) => {
                        if let Some(lit) = as_literal(pat) {
                            if var == "host_cpu" {
                                Some(Guard::confirmed(Atom::Arch(lit.to_owned())))
                            } else if var == "host_os" {
                                Some(Guard::confirmed(Atom::OsAbi(lit.to_owned())))
                            } else {
                                Some(Guard::confirmed(Atom::Var(
                                    var.to_owned(),
                                    VarCond::Eq(VoL::Lit(lit.to_owned())),
                                )))
                            }
                        } else if let &WordFragment::Star = pat {
                            Some(Guard::confirmed(Atom::Var(
                                var.to_owned(),
                                VarCond::MatchAny,
                            )))
                        } else {
                            None
                        }
                    }
                    _ => {
                        let pattern_string = self.pool.display_word(pattern, false);
                        if var == "host" {
                            let (arch, _, os): (String, String, String) =
                                split_glob_triplet(&pattern_string)
                                    .into_iter()
                                    .take(3)
                                    .tuples()
                                    .collect();
                            if arch != "*" && os != "*" {
                                Some(Guard::And(vec![
                                    Guard::confirmed(Atom::Arch(arch)),
                                    Guard::confirmed(Atom::OsAbi(os)),
                                ]))
                            } else if arch != "*" {
                                Some(Guard::confirmed(Atom::Arch(arch)))
                            } else if os != "*" {
                                Some(Guard::confirmed(Atom::OsAbi(os)))
                            } else {
                                Some(Guard::confirmed(Atom::Var(
                                    var.to_owned(),
                                    VarCond::MatchAny,
                                )))
                            }
                        } else if var == "host_cpu" {
                            Some(Guard::confirmed(Atom::Arch(pattern_string)))
                        } else if pattern_string.contains("*")
                            || pattern_string.contains("[")
                            || pattern_string.contains("]")
                            || pattern_string.contains("?")
                        {
                            Some(Guard::confirmed(Atom::Var(
                                var.to_owned(),
                                VarCond::Match(pattern_string),
                            )))
                        } else {
                            Some(Guard::confirmed(Atom::Var(
                                var.to_owned(),
                                VarCond::Eq(VoL::Lit(pattern_string)),
                            )))
                        }
                    }
                }
            } else if let &WordFragment::DoubleQuoted(ref frags) = word {
                let pattern_string = self.pool.display_word(pattern, false);
                let vars: Vec<String> = frags
                    .iter()
                    .filter_map(as_var)
                    .map(|s| s.to_owned())
                    .collect();
                let guard = Guard::or(
                    vars.into_iter()
                        .map(|var| {
                            Guard::confirmed(Atom::Var(var, VarCond::Match(pattern_string.clone())))
                        })
                        .collect(),
                );
                Some(guard)
            } else {
                None
            }
        } else {
            None
        }
    }
}

impl<'a> AstVisitor for GuardAnalyzer<'a> {
    fn get_node(&self, node_id: NodeId) -> &Node {
        &self.pool.nodes[node_id]
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

    fn visit_condition(&mut self, cond: &Condition<AcWord>) {
        let guard = self.condition_to_guard(cond);
        self.stack.push(guard);
    }

    fn visit_guard_body_pair(&mut self, pair: &GuardBodyPair<AcWord>) {
        self.visit_condition(&pair.condition);
        self.add_scope(&pair.body);
        for c in &pair.body {
            self.visit_node(*c);
        }
        self.stack.pop();
    }

    fn visit_if(&mut self, conditionals: &[GuardBodyPair<AcWord>], else_branch: &[NodeId]) {
        let saved_stack = self.stack.clone();
        for pair in conditionals.iter() {
            self.visit_condition(&pair.condition);
            self.add_scope(&pair.body);
            for c in &pair.body {
                self.visit_node(*c);
            }
            self.negate_last_guard();
        }
        self.add_scope(&else_branch);
        for c in else_branch {
            self.visit_node(*c);
        }
        self.stack = saved_stack;
    }

    fn visit_and_or(&mut self, negated: bool, condition: &Condition<AcWord>, cmd: NodeId) {
        self.visit_condition(condition);
        if negated {
            self.negate_last_guard();
        }
        self.add_scope(&[cmd]);
        self.walk_node(cmd);
        self.stack.pop();
    }

    fn visit_case(&mut self, word: &AcWord, arms: &[PatternBodyPair<AcWord>]) {
        let saved_stack = self.stack.clone();
        for arm in arms {
            let guard = Guard::or(
                arm.patterns
                    .iter()
                    .map(|pattern| self.pattern_to_guard(word, pattern).expect("unsupported syntax"))
                    .collect(),
            );
            self.stack.push(guard);
            self.add_scope(&arm.body);
            for c in &arm.body {
                self.visit_node(*c);
            }
            self.negate_last_guard();
        }
        self.stack = saved_stack;
    }
}

fn analyze_path(word: &AcWord) -> (Vec<VoL>, bool) {
    let mut words = match &word.0 {
        Word::Empty => panic!("unsupported syntax"),
        Word::Concat(words) => {
            let mut v = Vec::new();
            for w in words {
                if let MayM4::Shell(w) = w {
                    v.push(w);
                } else {
                    panic!("unsupported syntax");
                }
            }
            v
        }
        Word::Single(w) => {
            if let MayM4::Shell(w) = w {
                vec![w]
            } else {
                panic!("unsupported syntax");
            }
        }
    };
    let is_absolute = {
        if words
            .first()
            .and_then(|w| as_literal(w))
            .is_some_and(|s| s == "\\")
        {
            words.remove(0);
            true
        } else {
            false
        }
    };
    if words.len() > 1
        && !words[1..]
            .into_iter()
            .step_by(2)
            .all(|w| as_literal(w).is_some_and(|s| s == "\\"))
    {
        panic!("unsupported syntax");
    }
    let path = words.iter().step_by(2).filter_map(|w| as_vol(w)).collect();
    (path, is_absolute)
}

fn split_glob_triplet(s: &str) -> Vec<String> {
    let mut parts = Vec::new();
    let mut buf = String::new();
    let mut in_bracket = false;

    for c in s.chars() {
        match c {
            '[' => {
                in_bracket = true;
                buf.push(c);
            }
            ']' => {
                in_bracket = false;
                buf.push(c);
            }
            '-' if !in_bracket => {
                parts.push(buf);
                buf = String::new();
            }
            _ => buf.push(c),
        }
    }
    parts.push(buf);
    parts
}
