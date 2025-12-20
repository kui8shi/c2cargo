use super::{M4Argument, M4Macro};
use itertools::Itertools;
use std::collections::{HashMap, HashSet};

use super::{
    AcWord, Analyzer, AstVisitor, Condition, GuardBodyPair, MayM4, Node, NodeId, Operator,
    Parameter, ParameterSubstitution, PatternBodyPair, Redirect, ShellCommand, Word, WordFragment,
};

use super::{as_literal, as_shell, as_var};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum Guard {
    N(bool, Atom), // true if negated
    And(Vec<Self>),
    Or(Vec<Self>),
}

pub(super) type BlockId = usize;

#[derive(Debug, Clone, Default)]
pub(super) struct Block {
    pub block_id: BlockId,
    pub parent: NodeId,
    pub nodes: Vec<NodeId>,
    pub guards: Vec<Guard>,
    pub error_out: bool,
}

impl Guard {
    pub(super) fn confirmed(atom: Atom) -> Guard {
        Guard::N(false, atom)
    }

    pub(super) fn negated(atom: Atom) -> Guard {
        Guard::N(true, atom)
    }

    pub(super) fn negate_whole(self) -> Guard {
        match self {
            Guard::N(b, atom) => Guard::N(!b, atom),
            Guard::And(guards) => Guard::Or(guards.into_iter().map(|g| g.negate_whole()).collect()),
            Guard::Or(guards) => Guard::And(guards.into_iter().map(|g| g.negate_whole()).collect()),
        }
    }

    pub(super) fn make_and(mut guards: Vec<Guard>) -> Guard {
        if guards.len() == 1 {
            guards.pop().unwrap()
        } else {
            Guard::And(guards)
        }
    }

    pub(super) fn make_or(mut guards: Vec<Guard>) -> Guard {
        if guards.len() == 1 {
            guards.pop().unwrap()
        } else {
            Guard::Or(guards)
        }
    }

    pub(super) fn has_variable(&self, var_name: &str) -> bool {
        use Atom::*;
        use Guard::*;
        match self {
            N(_, atom) => match atom {
                Var(name, _) => name == var_name,
                Arg(name, _) => name == var_name,
                _ => false,
            },
            And(guards) | Or(guards) => guards.iter().any(|guard| guard.has_variable(var_name)),
        }
    }

    pub(super) fn print(
        &self,
        printed_cmds: &HashMap<NodeId, String>,
    ) -> Result<String, HashSet<NodeId>> {
        use Atom::*;
        use VarCond::*;
        match self {
            Guard::N(negated, atom) => Ok(format!(
                "test {} {}",
                if *negated { "!" } else { "" },
                match atom {
                    ArchGlob(_) | OsAbiGlob(_) | Arch(_) | Cpu(_) | Os(_) | Env(_) | Abi(_)
                    | Ext(_) | BigEndian | HasProgram(_) | HasLibrary(_) | HasHeader(_)
                    | Compiler(_) => todo!(),
                    PathExists(vols, is_absolute) => {
                        let path_str = vols.iter().map(|vol| vol.print()).collect::<String>();
                        format!("-e {}{}", if *is_absolute { "/" } else { "" }, path_str)
                    }
                    Var(name, var_cond) | Arg(name, var_cond) => match var_cond {
                        True => format!("${{{}}} = yes", name),
                        False => format!("${{{}}} = no", name),
                        Empty => format!("-z ${{{}}}", name),
                        Unset => format!("${{{}:-set}} != set", name),
                        Set => format!("${{{}:-set}} = set", name),
                        Eq(vol) => format!("${{{}}} = {}", name, vol.print()),
                        Lt(vol) => format!("${{{}}} -lt {}", name, vol.print()),
                        Le(vol) => format!("${{{}}} -le {}", name, vol.print()),
                        Gt(vol) => format!("${{{}}} -gt {}", name, vol.print()),
                        Ge(vol) => format!("${{{}}} -ge {}", name, vol.print()),
                        Match(_) | MatchAny => todo!(),
                    },
                    Cmd(node_id) => {
                        if let Some(cmd_str) = printed_cmds.get(node_id) {
                            cmd_str.to_owned()
                        } else {
                            return Err(HashSet::from([*node_id]));
                        }
                    }
                    _ => todo!(),
                }
            )),
            Guard::Or(guards) | Guard::And(guards)
                if guards.iter().any(|g| g.print(printed_cmds).is_err()) =>
            {
                Err(guards
                    .iter()
                    .flat_map(|g| g.print(printed_cmds).err())
                    .flatten()
                    .collect())
            }
            Guard::Or(guards) => Ok(guards
                .iter()
                .map(|g| g.print(printed_cmds).unwrap())
                .join(" || ")),
            Guard::And(guards) => Ok(guards
                .iter()
                .map(|g| g.print(printed_cmds).unwrap())
                .join(" && ")),
        }
    }
}

#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum Atom {
    ArchGlob(String),  // glob string
    OsAbiGlob(String), // glob string
    Arch(String),
    Cpu(String),
    Os(String),
    Env(String),
    Abi(String),
    Ext(String), // e.g. sse, neon
    BigEndian,
    HasProgram(String),
    HasLibrary(String),
    HasHeader(String),
    /// "${dir}/filename" -> [Var("dir"), Lit("filename")]
    /// true if absolute
    PathExists(Vec<VoL>, bool),
    Compiler(CompilerCheck),
    Var(String, VarCond),
    Arg(String, VarCond),
    Cmd(NodeId),
    Tautology, // always true
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum VarCond {
    True,
    False,
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
pub(super) enum VoL {
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

impl VoL {
    fn print(&self) -> String {
        match self {
            VoL::Var(name) => format!("${{{}}}", name),
            VoL::Lit(lit) => lit.clone(),
        }
    }
}

#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum CompilerCheck {
    Func(String),
    Symbol { name: String, lib: Option<String> },
    Sizeof(String),
    Attribute(String),
    Link(String),
    Compile(String),
}

/// Compare two conditions.
pub(super) fn cmp_guards(lhs: &Vec<Guard>, rhs: &Vec<Guard>) -> Option<std::cmp::Ordering> {
    for (l, r) in lhs.iter().zip(rhs.iter()) {
        if l != r {
            // not comparable.
            return None;
        }
    }
    // Here, we know that either condition is a subset of the other.
    // we can decide the order simply by the lengths.
    Some(lhs.len().cmp(&rhs.len()))
}

/// Visitor to find case statements branching given variables.
#[allow(dead_code)]
#[derive(Debug)]
pub(super) struct GuardAnalyzer<'a> {
    analyzer: &'a mut Analyzer,
    cursor: Option<NodeId>,
    range: Option<Vec<(usize, usize)>>,
    guard_stack: Vec<Guard>,
    in_condition: bool,
}

impl Analyzer {
    pub(super) fn blocks_guarded_by_variable(&self, var_name: &str) -> Vec<Block> {
        self.blocks
            .iter()
            .filter_map(|(_, block)| {
                block
                    .guards
                    .last()
                    .is_some_and(|guard| guard.has_variable(var_name))
                    .then_some(block.clone())
            })
            .collect()
    }

    pub(super) fn parent_nodes_of_blocks_guarded_by_variable(&self, var_name: &str) -> Vec<NodeId> {
        let mut children = HashSet::<NodeId>::new();
        let mut ret = Vec::new();
        for block in self.blocks_guarded_by_variable(var_name) {
            children.extend(block.nodes.iter());
            if !children.contains(&block.parent) {
                if !ret.contains(&block.parent) {
                    ret.push(block.parent)
                }
            }
        }
        ret
    }
}

impl<'a> GuardAnalyzer<'a> {
    pub(super) fn analyze_blocks(analyzer: &'a mut Analyzer) {
        let mut s = Self {
            analyzer,
            cursor: None,
            range: None,
            guard_stack: Vec::new(),
            in_condition: false,
        };
        for node_id in s.analyzer.get_top_ids() {
            s.visit_top(node_id);
        }
    }

    fn record_block(&mut self, node_ids: &[NodeId]) -> BlockId {
        let parent = self.cursor.unwrap();
        let new_block_id = self.analyzer.add_block(Block {
            parent,
            nodes: node_ids.to_vec(),
            guards: self.guard_stack.clone(),
            ..Default::default()
        });

        // record parent-child relation ships
        for &id in node_ids {
            assert!(self.get_node(parent).unwrap().range.len() > 0);
            self.analyzer.link_body_to_parent(id, parent, new_block_id);

            if self.get_node(id).unwrap().range.is_empty() {
                // propagate ranges information if child doesn't know its range.
                self.analyzer.get_node_mut(id).unwrap().range =
                    self.get_node(parent).unwrap().range.clone();
            }
        }
        self.analyzer
            .get_node_mut(parent)
            .unwrap()
            .info
            .branches
            .push(new_block_id);

        new_block_id
    }

    fn negate_last_guard(&mut self) {
        let guard = self.guard_stack.pop().unwrap();
        self.guard_stack.push(guard.negate_whole());
    }

    fn equality(&self, w1: &AcWord, w2: &AcWord) -> Option<Guard> {
        fn interpret_literal(lit: &str) -> VarCond {
            match lit {
                "yes" => VarCond::True,
                "no" => VarCond::False,
                "" => VarCond::Empty,
                _ => VarCond::Eq(VoL::Lit(lit.to_owned())),
            }
        }

        fn cancel_prefix(
            may_prefix: &WordFragment<AcWord>,
            w1: &WordFragment<AcWord>,
            w2: &WordFragment<AcWord>,
            prefix: &str,
        ) -> Option<Guard> {
            if Some(prefix) == as_literal(may_prefix) {
                if let Some(var) = as_var(w1) {
                    if let Some(b_lit) = as_literal(w2) {
                        if let Some(b_stripped) = b_lit.strip_prefix(prefix) {
                            return Some(Guard::confirmed(Atom::Var(
                                var.to_owned(),
                                interpret_literal(b_stripped),
                            )));
                        }
                    }
                }
            }
            None
        }

        fn split_delim(
            w1: &Vec<WordFragment<AcWord>>,
            w2: &WordFragment<AcWord>,
            delimiter: &str,
        ) -> Option<Guard> {
            let delims_in_w1 = w1
                .iter()
                .enumerate()
                .filter(|(_, w)| as_literal(w).is_some_and(|lit| lit == delimiter))
                .map(|(i, _)| i)
                .collect::<Vec<_>>();
            if let Some(lit) = as_literal(w2) {
                if delims_in_w1.len() == lit.matches(delimiter).count() {
                    let mut vars = Vec::new();
                    for word in w1
                        .iter()
                        .enumerate()
                        .filter_map(|(i, w)| delims_in_w1.contains(&i).then_some(w))
                        .collect::<Vec<_>>()
                    {
                        if let Some(var) = as_var(word) {
                            vars.push(var);
                        } else {
                            return None;
                        }
                    }
                    let literals = lit.split(delimiter);
                    return Some(Guard::And(
                        vars.into_iter()
                            .zip(literals)
                            .map(|(var, lit)| {
                                Guard::confirmed(Atom::Var(
                                    var.to_owned(),
                                    VarCond::Eq(VoL::Lit(lit.to_owned())),
                                ))
                            })
                            .collect::<Vec<_>>(),
                    ));
                }
            }
            None
        }

        match &w1.0 {
            Word::Empty => {
                if let Some(var) = as_shell(w2).and_then(as_var) {
                    Some(Guard::confirmed(Atom::Var(var.to_owned(), VarCond::Empty)))
                } else {
                    None
                }
            }
            Word::Single(MayM4::Shell(w1)) => {
                if let WordFragment::Subst(subst) = w1 {
                    match &**subst {
                        ParameterSubstitution::Alternative(
                            _,
                            Parameter::Var(name),
                            Some(alter),
                        ) if alter == w2 => {
                            return Some(Guard::confirmed(Atom::Var(
                                name.to_owned(),
                                VarCond::Set,
                            )));
                        }
                        ParameterSubstitution::Default(_, Parameter::Var(name), Some(default))
                            if default == w2 =>
                        {
                            return Some(Guard::confirmed(Atom::Var(
                                name.to_owned(),
                                VarCond::Unset,
                            )));
                        }
                        ParameterSubstitution::Assign(_, Parameter::Var(name), Some(default))
                            if default == w2 =>
                        {
                            return Some(Guard::confirmed(Atom::Var(
                                name.to_owned(),
                                VarCond::Unset,
                            )));
                        }
                        _ => {}
                    }
                } else if let Some(w2) = as_shell(w2) {
                    if let WordFragment::DoubleQuoted(frags) = w1 {
                        if frags.len() >= 2 {
                            let w1_first = &frags[0];
                            let w1_second = &frags[1];
                            for pattern in ["x", "X"] {
                                if let Some(guard) = cancel_prefix(w1_first, w1_second, w2, pattern)
                                {
                                    return Some(guard);
                                }
                                if let Some(guard) = split_delim(frags, w2, pattern) {
                                    return Some(guard);
                                }
                            }
                        }
                    } else if let Some(var) = as_var(w1) {
                        if let Some(lit) = as_literal(w2) {
                            return Some(Guard::confirmed(Atom::Var(
                                var.to_owned(),
                                interpret_literal(lit),
                            )));
                        } else if let Some(vol) = as_vol(w2) {
                            return Some(Guard::confirmed(Atom::Var(
                                var.to_owned(),
                                VarCond::Eq(vol),
                            )));
                        }
                    } else if let Some(l1) = as_literal(w1) {
                        if let Some(l2) = as_literal(w2) {
                            if l1 == l2 {
                                return Some(Guard::confirmed(Atom::Tautology));
                            } else {
                                return Some(Guard::negated(Atom::Tautology));
                            }
                        }
                    }
                }
                None
            }
            Word::Concat(concat) if concat.len() == 2 => {
                if let Some(w2) = as_shell(w2) {
                    if let Some(frags) = concat
                        .into_iter()
                        .map(|w| match w {
                            MayM4::Shell(shell) => Some(shell.clone()),
                            _ => None,
                        })
                        .collect::<Option<Vec<_>>>()
                    {
                        let w1_first = &frags[0];
                        let w1_second = &frags[1];
                        for pattern in ["x", "X"] {
                            if let Some(guard) = cancel_prefix(w1_first, w1_second, w2, pattern) {
                                return Some(guard);
                            }
                            if let Some(guard) = split_delim(&frags, w2, pattern) {
                                return Some(guard);
                            }
                        }
                    }
                }
                None
            }
            _ => None,
        }
    }

    fn compare(
        &self,
        w1: &AcWord,
        w2: &AcWord,
        direct_op: fn(VoL) -> VarCond,
        swapped_op: fn(VoL) -> VarCond,
    ) -> Option<Guard> {
        let s1 = as_shell(w1);
        let s2 = as_shell(w2);

        // Case 1: Variable [OP] Value (e.g., $x >= 10)
        if let (Some(v1), Some(v2)) = (s1.and_then(as_var), s2.and_then(as_vol)) {
            return Some(Guard::confirmed(Atom::Var(v1.to_owned(), direct_op(v2))));
        }

        // Case 2: Value [OP] Variable (e.g., 10 >= $x  <==> $x <= 10)
        // We use the swapped_op here (e.g., Ge becomes Le).
        if let (Some(v1), Some(v2)) = (s1.and_then(as_vol), s2.and_then(as_var)) {
            return Some(Guard::confirmed(Atom::Var(v2.to_owned(), swapped_op(v1))));
        }

        None
    }

    fn condition_to_guard(&mut self, cond: &Condition<AcWord>) -> Guard {
        match cond {
            Condition::And(c1, c2) => Guard::And(vec![
                self.condition_to_guard(c1),
                self.condition_to_guard(c2),
            ]),
            Condition::Or(c1, c2) => Guard::Or(vec![
                self.condition_to_guard(c1),
                self.condition_to_guard(c2),
            ]),
            Condition::Not(cond) => self.condition_to_guard(cond).negate_whole(),
            Condition::Eval(cmd) | Condition::ReturnZero(cmd) => {
                let parent = self.cursor.unwrap();
                let cmd = **cmd;
                self.analyzer.add_pre_body_node(parent, cmd);
                if self.analyzer.get_node(cmd).unwrap().range.is_empty() {
                    self.analyzer.get_node_mut(cmd).unwrap().range =
                        self.analyzer.get_node(parent).unwrap().range.clone();
                }
                Guard::N(true, Atom::Cmd(cmd))
            }
            Condition::Cond(op) => match op {
                Operator::Eq(w1, w2) => {
                    let guard = if let Some(res) = self.equality(w1, w2) {
                        res
                    } else if let Some(res) = self.equality(w2, w1) {
                        res
                    } else {
                        dbg!(w1, w2);
                        panic!("unsupported syntax");
                    };
                    guard
                }
                Operator::Neq(w1, w2) => {
                    let guard = if let Some(res) = self.equality(w1, w2) {
                        res
                    } else if let Some(res) = self.equality(w2, w1) {
                        res
                    } else {
                        dbg!(w1, w2);
                        panic!("unsupported syntax");
                    };
                    guard.negate_whole()
                }
                Operator::Ge(w1, w2) => {
                    if let Some(guard) = self.compare(w1, w2, VarCond::Ge, VarCond::Le) {
                        guard
                    } else {
                        dbg!(w1, w2);
                        panic!("unsupported syntax")
                    }
                }
                Operator::Gt(w1, w2) => {
                    if let Some(guard) = self.compare(w1, w2, VarCond::Gt, VarCond::Lt) {
                        guard
                    } else {
                        dbg!(w1, w2);
                        panic!("unsupported syntax")
                    }
                }
                Operator::Le(w1, w2) => {
                    if let Some(guard) = self.compare(w1, w2, VarCond::Le, VarCond::Ge) {
                        guard
                    } else {
                        dbg!(w1, w2);
                        panic!("unsupported syntax")
                    }
                }
                Operator::Lt(w1, w2) => {
                    if let Some(guard) = self.compare(w1, w2, VarCond::Lt, VarCond::Gt) {
                        guard
                    } else {
                        dbg!(w1, w2);
                        panic!("unsupported syntax")
                    }
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
            if let WordFragment::Subst(subst) = &word {
                match &**subst {
                    ParameterSubstitution::Command(cmds) if cmds.len() == 1 => {
                        Some(Guard::confirmed(Atom::Cmd(cmds.first().unwrap().clone())))
                    }
                    _ => None,
                }
            } else if let Some(var) = as_var(word) {
                match &pattern.0 {
                    Word::Empty => {
                        Some(Guard::confirmed(Atom::Var(var.to_owned(), VarCond::Empty)))
                    }
                    Word::Single(MayM4::Shell(pat)) => {
                        if let Some(lit) = as_literal(pat) {
                            if var == "host_cpu" {
                                Some(Guard::confirmed(Atom::ArchGlob(lit.to_owned())))
                            } else if var == "host_os" {
                                Some(Guard::confirmed(Atom::OsAbiGlob(lit.to_owned())))
                            } else {
                                let cond = if lit == "yes" {
                                    VarCond::True
                                } else if lit == "no" {
                                    VarCond::False
                                } else if lit.is_empty() {
                                    VarCond::Empty
                                } else {
                                    VarCond::Eq(VoL::Lit(lit.to_owned()))
                                };
                                Some(Guard::confirmed(Atom::Var(var.to_owned(), cond)))
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
                        let pattern_string = self.analyzer.display_word(pattern);
                        if var == "host" {
                            let (arch, _vendor, os): (String, String, String) =
                                split_glob_triplet(&pattern_string)
                                    .into_iter()
                                    .take(3)
                                    .tuples()
                                    .collect();
                            if arch != "*" && os != "*" {
                                Some(Guard::And(vec![
                                    Guard::confirmed(Atom::ArchGlob(arch)),
                                    Guard::confirmed(Atom::OsAbiGlob(os)),
                                ]))
                            } else if arch != "*" {
                                Some(Guard::confirmed(Atom::ArchGlob(arch)))
                            } else if os != "*" {
                                Some(Guard::confirmed(Atom::OsAbiGlob(os)))
                            } else {
                                Some(Guard::confirmed(Atom::Var(
                                    var.to_owned(),
                                    VarCond::MatchAny,
                                )))
                            }
                        } else if var == "host_cpu" {
                            Some(Guard::confirmed(Atom::ArchGlob(pattern_string)))
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
                let pattern_string = self.analyzer.display_word(pattern);
                let vars: Vec<String> = frags
                    .iter()
                    .filter_map(as_var)
                    .map(|s| s.to_owned())
                    .collect();
                let guard = Guard::make_or(
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
        self.cursor.replace(node_id);
        self.walk_node(node_id);
    }

    fn visit_node(&mut self, node_id: NodeId) {
        if self.get_node(node_id).is_none() {
            return;
        }
        let saved_cursor = self.cursor.replace(node_id);
        self.walk_node(node_id);
        self.cursor = saved_cursor;
    }

    fn visit_condition(&mut self, cond: &Condition<AcWord>) {
        let was_in_condition = self.in_condition;
        if !was_in_condition {
            let guard = self.condition_to_guard(cond);
            self.guard_stack.push(guard);
            self.in_condition = true;
        }
        match cond {
            Condition::Cond(op) => match op {
                Operator::Eq(w1, w2)
                | Operator::Neq(w1, w2)
                | Operator::Ge(w1, w2)
                | Operator::Gt(w1, w2)
                | Operator::Le(w1, w2)
                | Operator::Lt(w1, w2) => {
                    self.visit_word(w1);
                    self.visit_word(w2);
                }
                Operator::Empty(w)
                | Operator::NonEmpty(w)
                | Operator::Dir(w)
                | Operator::File(w)
                | Operator::NoExists(w) => self.visit_word(w),
            },
            Condition::Not(cond) => self.visit_condition(cond),
            Condition::And(c1, c2) | Condition::Or(c1, c2) => {
                self.visit_condition(c1);
                self.visit_condition(c2);
            }
            Condition::Eval(cmd) => {
                self.record_block(&[**cmd]);
                self.visit_node(**cmd);
            }
            Condition::ReturnZero(cmd) => {
                self.record_block(&[**cmd]);
                self.visit_node(**cmd)
            }
            _ => {}
        }
        self.in_condition = was_in_condition;
    }

    fn visit_parameter_substitution(&mut self, subs: &ParameterSubstitution<AcWord>) {
        use autotools_parser::ast::ParameterSubstitution::*;
        if let Command(cmds) = subs {
            self.record_block(cmds);
        }
        self.walk_parameter_substitution(subs);
    }

    // Note that in this implementation, this method is not called by visit_if.
    // Only visit_while and visit_until will call it,
    fn visit_guard_body_pair(&mut self, pair: &GuardBodyPair<AcWord>) {
        self.visit_condition(&pair.condition);
        self.record_block(&pair.body);
        for c in &pair.body {
            self.visit_node(*c);
        }
        self.guard_stack.pop();
    }

    fn visit_brace(&mut self, body: &[NodeId]) {
        self.record_block(body);
        self.walk_body(body);
    }

    fn visit_subshell(&mut self, body: &[NodeId]) {
        self.record_block(body);
        self.walk_body(body);
    }

    fn visit_for(&mut self, var: &str, words: &[AcWord], body: &[NodeId]) {
        self.record_block(body);
        self.walk_for(var, words, body);
    }

    fn visit_if(&mut self, conditionals: &[GuardBodyPair<AcWord>], else_branch: &[NodeId]) {
        let saved_stack = self.guard_stack.clone();
        for pair in conditionals.iter() {
            self.visit_condition(&pair.condition);
            self.record_block(&pair.body);
            for c in &pair.body {
                self.visit_node(*c);
            }
            self.negate_last_guard();
        }
        if !else_branch.is_empty() {
            self.record_block(&else_branch);
        }
        for c in else_branch {
            self.visit_node(*c);
        }
        self.guard_stack = saved_stack;
    }

    fn visit_and_or(&mut self, negated: bool, condition: &Condition<AcWord>, cmd: NodeId) {
        self.visit_condition(condition);
        if negated {
            self.negate_last_guard();
        }
        self.record_block(&[cmd]);
        self.visit_node(cmd);
        self.guard_stack.pop();
    }

    fn visit_pipe(&mut self, bang: bool, cmds: &[NodeId]) {
        self.record_block(cmds);
        self.walk_pipe(bang, cmds);
    }

    fn visit_redirect(&mut self, cmd: NodeId, redirects: &[Redirect<AcWord>]) {
        self.record_block(&[cmd]);
        self.walk_redirect(cmd, redirects);
    }

    fn visit_case(&mut self, word: &AcWord, arms: &[PatternBodyPair<AcWord>]) {
        let saved_stack = self.guard_stack.clone();
        let mut is_platform_branch = false;
        if let Some(w) = as_shell(word) {
            let node_id = self.cursor.unwrap();
            if let WordFragment::Subst(subst) = w {
                if let ParameterSubstitution::Command(cmds) = subst.as_ref() {
                    for cmd in cmds {
                        self.analyzer.add_pre_body_node(node_id, *cmd);
                    }
                }
            }
            if let Some(var_name) = as_var(w) {
                if var_name == "host" {
                    is_platform_branch = true;
                }
                // FIXME: host_cpu, host_os?
            }
        }
        let mut removing_arm_indexes = Vec::new();
        for (arm_index, arm) in arms.into_iter().enumerate() {
            let mut guard = Guard::make_or(
                arm.patterns
                    .iter()
                    .map(|pattern| {
                        self.pattern_to_guard(word, pattern)
                            .expect("unsupported syntax")
                    })
                    .collect(),
            );
            let unsupported_platform_branch_found = if is_platform_branch {
                if let Some(converted) = self
                    .analyzer
                    .platform_support
                    .check_supported_platform(&guard)
                {
                    guard = converted;
                    false
                } else {
                    true
                }
            } else {
                false
            };
            if unsupported_platform_branch_found {
                // why not use `remove_node` in removal.rs?
                // because `remove_node` depends on the block structure,
                // that we are constructing now.
                for node_id in arm.body.iter() {
                    // FIXME: we should recurse into the body to erase all nodes from the pool.
                    self.analyzer.pool.nodes.remove(*node_id);
                }
                removing_arm_indexes.push(arm_index);
            } else {
                self.guard_stack.push(guard);
                self.record_block(&arm.body);
                for c in &arm.body {
                    self.visit_node(*c);
                }
                self.negate_last_guard();
            }
        }
        if !removing_arm_indexes.is_empty() {
            let node_id = self.cursor.unwrap();
            match &mut self.analyzer.get_node_mut(node_id).unwrap().cmd.0 {
                MayM4::Shell(ShellCommand::Case { word: _, arms }) => {
                    for arm_index in removing_arm_indexes.into_iter().rev() {
                        arms.remove(arm_index);
                    }
                }
                _ => unreachable!(),
            }
        }
        // if is_platform_branch {
        //     let mut conditionals = Vec::new();
        //     let mut else_branch = Vec::new();
        //     for (arm_index, arm) in arms.iter().enumerate() {
        //         let node_id = self.cursor.unwrap();
        //         let block_id = self.analyzer.get_node(node_id).unwrap().info.branches[arm_index];
        //         let guard = self.analyzer.get_block(block_id).guards.last().unwrap();
        //         let is_else_branch = match guard {
        //             Guard::N(false, Atom::Var(_, VarCond::MatchAny)) => true,
        //             _ => false,
        //         };
        //         if is_else_branch {
        //             else_branch = arm.body.clone();
        //         } else {
        //             let dummy_cond = Condition::Cond(Operator::Empty(AcWord(Word::Empty)));
        //             let dummy_guard_body_pair = GuardBodyPair {
        //                 condition: dummy_cond,
        //                 body: arm.body.clone(),
        //             };
        //             conditionals.push(dummy_guard_body_pair);
        //         }
        //     }
        //     ShellCommand::If {
        //         conditionals,
        //         else_branch,
        //     };
        // }
        self.guard_stack = saved_stack;
    }

    fn visit_m4_macro(&mut self, m4_macro: &M4Macro) {
        for arg in m4_macro.args.iter() {
            match arg {
                M4Argument::Word(w) => self.visit_word(w),
                M4Argument::Condition(cond) => {
                    self.visit_condition(cond);
                    self.record_block(&[]);
                    self.guard_stack.pop();
                }
                M4Argument::Commands(cmds) => {
                    self.record_block(cmds);
                    for c in cmds {
                        self.visit_node(*c);
                    }
                }
                _ => {}
            }
        }
    }
}

fn analyze_path(word: &AcWord) -> (Vec<VoL>, bool) {
    const SLASH: &'static str = "/";
    let trim_slash = |w| {
        if as_literal(w).is_some_and(|s| s.starts_with(SLASH)) {
            let trimmed = as_literal(&w).unwrap()[0..].to_string();
            vec![
                WordFragment::Literal(SLASH.into()),
                WordFragment::Literal(trimmed),
            ]
        } else {
            vec![w.clone()]
        }
    };
    let mut words = match &word.0 {
        Word::Empty => panic!("unsupported syntax"),
        Word::Concat(words) => {
            let mut v = Vec::new();
            for w in words {
                if let MayM4::Shell(w) = w {
                    v.extend(trim_slash(w));
                } else {
                    panic!("unsupported syntax");
                }
            }
            v
        }
        Word::Single(w) => {
            if let MayM4::Shell(w) = w {
                trim_slash(w)
            } else {
                panic!("unsupported syntax");
            }
        }
    };
    let is_absolute = {
        if words
            .first()
            .and_then(|w| as_literal(w))
            .is_some_and(|s| s == SLASH)
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
            .all(|w| as_literal(w).is_some_and(|s| s == SLASH))
    {
        dbg!(&words[1..].into_iter().step_by(2).collect::<Vec<_>>());
        panic!("unsupported path syntax: {:?}", words);
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
