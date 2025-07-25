//! Provides the higher level on-time analyses to improve parsing
use autotools_parser::{
    ast::{
        minimal::Word,
        node::{
            AcCommand, AcWord, AcWordFragment, AutoconfPool, Condition, DisplayNode, GuardBodyPair,
            M4Argument, M4Macro, NodeId, Operator, ParameterSubstitution, PatternBodyPair,
            ShellCommand, WordFragment,
        },
        Arithmetic, MayM4, Parameter, Redirect,
    },
    lexer::Lexer,
    parse::autoconf::NodeParser,
};
use lazy_init::LazyInitializer;
use std::{
    cell::Cell,
    cmp::Ordering,
    collections::{BTreeMap, HashMap, HashSet},
};

use case::{CaseMatch, CaseMatchFinder};
use eval::DynamicIdentifier;
use flatten::Flattener;
use variable::{LValue, Location, RValue, VariableAnalyzer};

use slab::Slab;

mod case;
mod chunk;
mod eval;
mod flatten;
mod lazy_init;
mod platform_branch;
mod type_inference;
mod variable;

type Command = ShellCommand<AcWord>;
type VariableMap = HashMap<String, Vec<Location>>;
type Node = autotools_parser::ast::node::Node<AcCommand, NodeInfo>;

fn as_shell(word: &AcWord) -> Option<&WordFragment<AcWord>> {
    if let Word::Single(MayM4::Shell(shell_word)) = &word.0 {
        Some(shell_word)
    } else {
        None
    }
}

fn as_literal(word: &WordFragment<AcWord>) -> Option<&str> {
    if let WordFragment::Literal(lit) = &word {
        Some(lit.as_str())
    } else {
        None
    }
}

fn as_var(word: &WordFragment<AcWord>) -> Option<&str> {
    if let WordFragment::Param(Parameter::Var(name)) = &word {
        Some(name.as_str())
    } else {
        None
    }
}

/// Visitor trait for walking over the AST nodes.
pub trait AstVisitor: Sized {
    /// Return Node from NodeId
    fn get_node(&self, node_id: NodeId) -> &Node;

    /// Entry function for visiting a top-level AST node.
    fn visit_top(&mut self, node_id: NodeId) {
        self.walk_node(node_id);
    }

    /// Intermediate function for visiting an AST node.
    fn visit_node(&mut self, node_id: NodeId) {
        if !self.get_node(node_id).info.is_top_node() {
            self.walk_node(node_id);
        }
    }

    /// Intermediate function for visiting a command.
    fn visit_command(&mut self, cmd_words: &[AcWord]) {
        self.walk_command(cmd_words);
    }

    /// Intermediate function for visiting an assignment statement.
    fn visit_assignment(&mut self, name: &str, word: &AcWord) {
        self.walk_assignment(name, word);
    }

    /// Intermediate function for visiting a brace statement
    fn visit_brace(&mut self, body: &[NodeId]) {
        self.walk_brace(body);
    }

    /// Intermediate function for visiting a guard-body pair (e.g., in while/until/if).
    fn visit_guard_body_pair(&mut self, pair: &GuardBodyPair<AcWord>) {
        self.walk_guard_body_pair(pair);
    }

    /// Intermediate function for visiting a pattern-body pair (an arm in case).
    fn visit_pattern_body_pair(&mut self, arm: &PatternBodyPair<AcWord>) {
        self.walk_pattern_body_pair(arm);
    }

    /// Intermediate function for visiting an `if` statement
    fn visit_if(&mut self, conditionals: &[GuardBodyPair<AcWord>], else_branch: &[NodeId]) {
        self.walk_if(conditionals, else_branch);
    }

    /// Intermediate function for visiting a `for` statement
    fn visit_for(&mut self, var: &str, words: &[AcWord], body: &[NodeId]) {
        self.walk_for(var, words, body);
    }

    /// Intermediate function for visiting a `case` statement
    fn visit_case(&mut self, word: &AcWord, arms: &[PatternBodyPair<AcWord>]) {
        self.walk_case(word, arms);
    }

    /// Intermediate function for visiting a word
    fn visit_word(&mut self, w: &AcWord) {
        self.walk_word(w);
    }

    /// Intermediate function for visiting a word fragment
    fn visit_word_fragment(&mut self, f: &AcWordFragment) {
        self.walk_word_fragment(f);
    }

    /// Intermediate function for visiting a pipe
    fn visit_pipe(&mut self, bang: bool, cmds: &[NodeId]) {
        self.walk_pipe(bang, cmds);
    }

    /// Intermediate function for visiting a command chain
    fn visit_and_or(&mut self, negated: bool, condition: &Condition<AcWord>, cmd: NodeId) {
        self.walk_and_or(negated, condition, cmd);
    }

    /// Intermediate function for visiting a conditional expression.
    fn visit_condition(&mut self, cond: &Condition<AcWord>) {
        self.walk_condition(cond);
    }

    /// Intermediate function for visiting an arithmetic expression.
    fn visit_arithmetic(&mut self, arith: &Arithmetic<String>) {
        self.walk_arithmetic(arith);
    }

    /// Intermediate function for visiting a parameter.
    fn visit_parameter(&mut self, param: &Parameter<String>) {
        self.walk_parameter(param);
    }

    /// Intermediate function for visiting a parameter substitution.
    fn visit_parameter_substitution(&mut self, subs: &ParameterSubstitution<AcWord>) {
        self.walk_parameter_substitution(subs);
    }

    /// Intermediate function for visiting an IO redirect.
    fn visit_redirect(&mut self, cmd: NodeId, redirects: &[Redirect<AcWord>]) {
        self.walk_redirect(cmd, redirects);
    }

    /// Intermediate function for visiting a M4 macro invocation.
    fn visit_m4_macro(&mut self, m4_macro: &M4Macro) {
        self.walk_m4_macro(m4_macro);
    }

    /// Intermediate function for visiting a function definition.
    fn visit_function_definition(&mut self, name: &str, body: NodeId) {
        self.walk_function_definition(name, body);
    }

    /// Walk a node: wrappper of arbitrary command.
    fn walk_node(&mut self, node_id: NodeId) {
        let node = self.get_node(node_id);
        use autotools_parser::ast::node::ShellCommand::*;
        use MayM4::*;
        match &node.cmd.0.clone() {
            Shell(Assignment(name, word)) => self.visit_assignment(name, word),
            Shell(Cmd(words)) => self.visit_command(words),
            Shell(Brace(body)) => self.visit_brace(body),
            Shell(Subshell(body)) => {
                for n in body {
                    self.visit_node(*n);
                }
            }
            Shell(While(pair)) => self.visit_guard_body_pair(pair),
            Shell(Until(pair)) => self.visit_guard_body_pair(pair),
            Shell(If {
                conditionals,
                else_branch,
            }) => {
                self.visit_if(conditionals, else_branch);
            }
            Shell(For { var, words, body }) => self.visit_for(var, words, body),
            Shell(Case { word, arms }) => self.visit_case(word, arms),
            Shell(And(condition, cmd)) => self.visit_and_or(true, condition, *cmd),
            Shell(Or(condition, cmd)) => self.visit_and_or(false, condition, *cmd),
            Shell(Pipe(bang, cmds)) => self.visit_pipe(*bang, cmds),
            Shell(Redirect(cmd, redirects)) => self.visit_redirect(*cmd, redirects),
            Shell(Background(cmd)) => self.visit_node(*cmd),
            Shell(FunctionDef { name, body }) => self.visit_function_definition(name, *body),
            Macro(m4_macro) => self.visit_m4_macro(m4_macro),
        };
    }

    /// Walk an assignment statement.
    fn walk_assignment(&mut self, _name: &str, word: &AcWord) {
        self.visit_word(word);
    }

    /// Walk a brace statement.
    fn walk_brace(&mut self, body: &[NodeId]) {
        for n in body {
            self.visit_node(*n);
        }
    }

    /// Walk a command.
    fn walk_command(&mut self, cmd_words: &[AcWord]) {
        for word in cmd_words {
            self.visit_word(word);
        }
    }

    /// Walk an `if` statement
    fn walk_if(&mut self, conditionals: &[GuardBodyPair<AcWord>], else_branch: &[NodeId]) {
        for pair in conditionals {
            self.visit_guard_body_pair(pair);
        }
        for cmd in else_branch {
            self.visit_node(*cmd);
        }
    }

    /// Walk a `for` statement
    fn walk_for(&mut self, _var: &str, words: &[AcWord], body: &[NodeId]) {
        for word in words {
            self.visit_word(word);
        }
        for cmd in body {
            self.visit_node(*cmd);
        }
    }

    /// Walk a `case` statement
    fn walk_case(&mut self, word: &AcWord, arms: &[PatternBodyPair<AcWord>]) {
        self.visit_word(word);
        for arm in arms {
            self.visit_pattern_body_pair(arm);
        }
    }

    /// Walk a guard-body pair node.
    fn walk_guard_body_pair(&mut self, pair: &GuardBodyPair<AcWord>) {
        self.visit_condition(&pair.condition);
        for c in &pair.body {
            self.visit_node(*c);
        }
    }

    /// Walk a pattern-body pair node.
    fn walk_pattern_body_pair(&mut self, arm: &PatternBodyPair<AcWord>) {
        for w in &arm.patterns {
            self.visit_word(w);
        }
        for c in &arm.body {
            self.visit_node(*c);
        }
    }

    /// Walk a pipe
    fn walk_pipe(&mut self, _bang: bool, cmds: &[NodeId]) {
        for cmd in cmds {
            self.visit_node(*cmd);
        }
    }

    /// Walk commands concatenated via and/or.
    fn walk_and_or(&mut self, _negated: bool, condition: &Condition<AcWord>, cmd: NodeId) {
        self.visit_condition(condition);
        self.visit_node(cmd);
    }

    /// Walk an IO redirect.
    fn walk_redirect(&mut self, cmd: NodeId, redirects: &[Redirect<AcWord>]) {
        self.visit_node(cmd);
        for redirect in redirects {
            match redirect {
                Redirect::Read(_, w)
                | Redirect::Write(_, w)
                | Redirect::ReadWrite(_, w)
                | Redirect::Append(_, w)
                | Redirect::Clobber(_, w)
                | Redirect::Heredoc(_, w)
                | Redirect::DupRead(_, w)
                | Redirect::DupWrite(_, w) => self.visit_word(w),
            }
        }
    }

    /// Walk a word node.
    fn walk_word(&mut self, w: &AcWord) {
        use Word::*;
        match &w.0 {
            Concat(frags) => {
                for f in frags {
                    self.visit_word_fragment(f);
                }
            }
            Single(f) => self.visit_word_fragment(f),
            Empty => {}
        }
    }

    /// Walk a word fragment node.
    fn walk_word_fragment(&mut self, f: &AcWordFragment) {
        use autotools_parser::ast::minimal::WordFragment::*;
        use MayM4::*;
        match f {
            Shell(Param(param)) => self.visit_parameter(param),
            Shell(DoubleQuoted(frags)) => {
                for f in frags {
                    self.visit_word_fragment(&Shell(f.clone()));
                }
            }
            Shell(Subst(subst)) => self.visit_parameter_substitution(subst.as_ref()),
            Macro(m4) => self.visit_m4_macro(m4),
            _ => {}
        }
    }

    /// Walk a conditional expression.
    fn walk_condition(&mut self, cond: &Condition<AcWord>) {
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
            Condition::And(c1, c2) | Condition::Or(c1, c2) => {
                self.visit_condition(c1);
                self.visit_condition(c2);
            }
            Condition::Eval(cmds) => {
                for cmd in cmds {
                    self.visit_node(*cmd);
                }
            }
            Condition::ReturnZero(cmd) => self.visit_node(**cmd),
        }
    }

    /// Walk an arithmetic expression node.
    fn walk_arithmetic(&mut self, arith: &Arithmetic<String>) {
        use autotools_parser::ast::Arithmetic::*;
        match arith {
            UnaryPlus(x) | UnaryMinus(x) | LogicalNot(x) | BitwiseNot(x) => {
                self.visit_arithmetic(x)
            }
            Pow(x, y)
            | Mult(x, y)
            | Div(x, y)
            | Modulo(x, y)
            | Add(x, y)
            | Sub(x, y)
            | ShiftLeft(x, y)
            | ShiftRight(x, y)
            | Less(x, y)
            | LessEq(x, y)
            | Great(x, y)
            | GreatEq(x, y)
            | Eq(x, y)
            | NotEq(x, y)
            | BitwiseAnd(x, y)
            | BitwiseXor(x, y)
            | BitwiseOr(x, y)
            | LogicalAnd(x, y)
            | LogicalOr(x, y) => {
                self.visit_arithmetic(x);
                self.visit_arithmetic(y);
            }
            Ternary(x, y, z) => {
                self.visit_arithmetic(x);
                self.visit_arithmetic(y);
                self.visit_arithmetic(z);
            }
            Sequence(seq) => {
                for a in seq {
                    self.visit_arithmetic(a);
                }
            }
            _ => {}
        }
    }

    /// Walk a parameter node.
    fn walk_parameter(&mut self, param: &Parameter<String>) {}

    /// Walk a parameter substitution node.
    fn walk_parameter_substitution(&mut self, subs: &ParameterSubstitution<AcWord>) {
        use autotools_parser::ast::ParameterSubstitution::*;
        match subs {
            Command(cmds) => {
                for c in cmds {
                    self.visit_node(*c);
                }
            }
            Arith(Some(arith)) => self.visit_arithmetic(arith),
            Len(param) => self.visit_parameter(param),
            Default(_, param, word)
            | Assign(_, param, word)
            | Error(_, param, word)
            | Alternative(_, param, word)
            | RemoveSmallestSuffix(param, word)
            | RemoveLargestSuffix(param, word)
            | RemoveSmallestPrefix(param, word)
            | RemoveLargestPrefix(param, word) => {
                self.visit_parameter(param);
                if let Some(w) = word {
                    self.visit_word(w);
                }
            }
            _ => {}
        }
    }

    /// Walk a function definition.
    fn walk_function_definition(&mut self, name: &str, body: NodeId) {}

    /// Walk an M4 macro node (walks arguments only).
    fn walk_m4_macro(&mut self, m4_macro: &M4Macro) {
        for arg in &m4_macro.args {
            match arg {
                M4Argument::Word(w) => self.visit_word(w),
                M4Argument::Array(ws) => {
                    for w in ws {
                        self.visit_word(w);
                    }
                }
                M4Argument::Commands(cmds) => {
                    for c in cmds {
                        self.visit_node(*c);
                    }
                }
                _ => {}
            }
        }
    }
}

/// Represents a node extension in the dependency graph
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct NodeInfo {
    /// Index of the node in the original list
    pub node_id: NodeId,
    /// ID of the top-most parent node
    pub top_id: Option<NodeId>,
    /// trailing comments
    // pub comment: Option<AcWord>,
    /// Range of line numbers where the body is effectively referenced.
    // pub ranges: Vec<(usize, usize)>,
    /// Body of commands referenced by this node.
    // pub cmd: AcCommand,
    /// ID of the parent node and the branch index itself hangs on
    pub parent: Option<(NodeId, Option<usize>)>,
    /// IDs of the children
    pub children: Option<Vec<NodeId>>,
    /// Variables defined by this command
    pub defines: VariableMap,
    /// Variables used by this command
    pub uses: VariableMap,
    /// Dependencies (indices of nodes this command depends on by variables)
    pub dependencies: HashMap<NodeId, HashSet<String>>,
    /// Commands that depend on this node
    pub dependents: HashMap<NodeId, HashSet<String>>,
}

impl NodeInfo {
    pub fn is_top_node(&self) -> bool {
        self.top_id.is_some_and(|id| id == self.node_id)
    }

    pub fn is_child_node(&self) -> bool {
        self.parent.is_some()
    }
}

/// Represents a condition
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Guard {
    /// doc
    Not(Box<Self>),
    /// doc
    Cond(Condition<AcWord>),
    /// doc
    Match(AcWord, Vec<AcWord>),
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

/// Analyzer which conducts various kinds of analyses:
/// 1. construction of a dependency graph by tracking variable usages
/// 2. flattening of large commands
/// etc..
#[derive(Debug)]
pub struct Analyzer {
    /// Original contents of analyzed script
    lines: Vec<String>,
    /// Nodes in the dependency graph
    pool: AutoconfPool<NodeInfo>,
    /// Ids of top-level commands
    top_ids: Vec<NodeId>,
    /// Map of variable names to information of commands that define them
    var_definitions: VariableMap,
    /// Map of top node (chunk) ids to information of variables defined in the chunk
    defines_per_top: HashMap<NodeId, VariableMap>,
    /// Map of top node (chunk) ids to information of variables used in the chunk
    uses_per_top: HashMap<NodeId, VariableMap>,
    /// Map of variable location to guard conditions
    guards: HashMap<Location, Vec<Guard>>,
    /// Set of variable maps that is fixed to a certain value
    fixed: HashMap<String, String>,
    /// State field used for printing a node
    focus: Cell<Option<NodeId>>,
    /// Set of variables which are used in eval statements
    pub evals: HashMap<LValue, Vec<(Option<RValue>, Location)>>,
    /// State filed used for recording resolved rvalues of variables
    resolved_values: HashMap<LValue, BTreeMap<Location, HashSet<String>>>,
    /// dynamically constructed identifiers
    dynamic_vars: HashMap<String, DynamicIdentifier>,
}

impl Analyzer {
    /// Analyze commands and build the dependency graph
    pub fn new<S: AsRef<str>>(
        contents: S,
        flatten_threshold: Option<usize>,
        fixed: Option<HashMap<String, String>>,
    ) -> Self {
        let lexer = Lexer::new(contents.as_ref().chars());
        let (nodes, top_ids) = NodeParser::<_, NodeInfo>::new(lexer).parse_all();
        let nodes = nodes
            .into_iter()
            .map(|(node_id, mut n)| {
                n.info.node_id = node_id;
                (node_id, n)
            })
            .collect::<Slab<Node>>();

        let mut nodes = LazyInitializer::lazy_init(nodes, &top_ids);

        // Create a VariableAnalyzer to extract both defined and used variables
        let mut var = VariableAnalyzer::new(&mut nodes);
        for id in &top_ids {
            // collect all defined and used variables in a command
            var.analyze(*id);
        }

        let evals = var.evals;
        let guards = var.guards;
        // collect recorded definitions
        let var_definitions: VariableMap = var
            .defines
            .into_iter()
            .flat_map(|(_, map)| map)
            .fold(HashMap::new(), |mut acc: VariableMap, (name, mut locs)| {
                acc.entry(name).or_default().append(&mut locs);
                acc
            })
            .into_iter()
            .map(|(name, mut locs)| {
                locs.sort();
                (name, locs)
            })
            .collect();

        let (top_ids, nodes) = Flattener::flatten(nodes, top_ids, flatten_threshold.unwrap_or(200));

        let mut s = Self {
            lines: contents.as_ref().lines().map(|s| s.to_string()).collect(),
            pool: AutoconfPool::new(nodes, Some(Box::new(|n| n.info.is_top_node()))),
            guards,
            evals,
            top_ids,
            var_definitions,
            defines_per_top: HashMap::new(),
            uses_per_top: HashMap::new(),
            fixed: fixed.unwrap_or_default(),
            focus: Cell::new(None),
            resolved_values: HashMap::new(),
            dynamic_vars: HashMap::new(),
        };

        // Collect
        for id in &s.top_ids {
            let (defs, uses) = s.collect_variables(*id);
            s.defines_per_top.insert(*id, defs);
            s.uses_per_top.insert(*id, uses);
        }

        let mut def_use_edges = Vec::new();
        // Calculate dependency edges
        for (id, node) in &s.pool.nodes {
            for var in node.info.uses.keys() {
                if let Some(def_id) = s.get_dominant_definition(var, id) {
                    def_use_edges.push((def_id, id, var.to_owned()));
                }
            }
        }
        // Apply initialization of depdencies to nodes
        for (def_id, use_id, var_name) in def_use_edges {
            s.get_node_mut(use_id)
                .info
                .dependencies
                .entry(def_id)
                .or_default()
                .insert(var_name.to_owned());
            s.get_node_mut(def_id)
                .info
                .dependents
                .entry(use_id)
                .or_default()
                .insert(var_name.to_owned());
        }

        s
    }

    /// Get the number of nodes (commands)
    pub fn num_nodes(&self) -> usize {
        self.pool.nodes.len()
    }

    /// Get guard conditions of given variable location
    fn guard_of_location(&self, location: &Location) -> &Vec<Guard> {
        &self.guards[location]
    }

    /// Get command that defines a variable before
    pub fn get_last_definition(&self, var_name: &str, node_id: NodeId) -> Option<NodeId> {
        if let Some(node) = self.pool.get(node_id) {
            if let Some(user_loc) = node.info.uses.get(var_name).map(|v| v.first()).flatten() {
                return self.var_definitions.get(var_name).and_then(|v| {
                    v.iter()
                        .rev()
                        .filter_map(|loc| (loc <= user_loc).then_some(loc.node_id))
                        .next()
                });
            }
        }
        None
    }

    /// Get command that defines a variable before, with consideration for the condition
    pub fn get_dominant_definition(&self, var_name: &str, node_id: NodeId) -> Option<NodeId> {
        if let Some(node) = self.pool.get(node_id) {
            if let Some(user_loc) = node.info.uses.get(var_name).map(|v| v.first()).flatten() {
                return self.var_definitions.get(var_name).and_then(|v| {
                    v.iter()
                        .rev()
                        .filter_map(|loc| {
                            // dumb heulistic to compare two guard conditions
                            (cmp_guards(
                                self.guard_of_location(loc),
                                self.guard_of_location(user_loc),
                            )
                            .is_none_or(|ord| matches!(ord, Ordering::Less | Ordering::Equal))
                                && loc <= user_loc)
                                .then_some(loc.node_id)
                        })
                        .next()
                });
            }
        }
        None
    }

    /// Get all locations that define a variable before
    pub fn get_all_definition(
        &self,
        var_name: &str,
        loc: Option<&Location>,
    ) -> Option<Vec<Location>> {
        self.var_definitions.get(var_name).map(|v| {
            v.iter()
                .filter(|def_loc| loc.is_none() || loc.is_some_and(|loc| *def_loc < loc))
                .cloned()
                .collect::<Vec<_>>()
        })
    }

    /// Get all locations that uses a variable before
    pub fn get_all_usages_before(
        &self,
        var_name: &str,
        loc: Option<&Location>,
    ) -> Option<Vec<Location>> {
        let mut ret = Vec::new();
        for id in &self.top_ids {
            if let Some(m) = self.uses_per_top.get(id) {
                if let Some(locs) = m.get(var_name) {
                    ret.extend(
                        locs.iter()
                            .filter(|use_loc| {
                                loc.is_none() || loc.is_some_and(|loc| *use_loc < loc)
                            })
                            .cloned(),
                    );
                }
            }
        }
        (!ret.is_empty()).then_some(ret)
    }

    /// Get all locations that uses a variable after
    pub fn get_all_usages_after(
        &self,
        var_name: &str,
        loc: Option<&Location>,
    ) -> Option<Vec<Location>> {
        let mut ret = Vec::new();
        for id in &self.top_ids {
            if let Some(m) = self.uses_per_top.get(id) {
                if let Some(locs) = m.get(var_name) {
                    ret.extend(
                        locs.iter()
                            .filter(|use_loc| {
                                loc.is_none() || loc.is_some_and(|loc| *use_loc < loc)
                            })
                            .cloned(),
                    );
                }
            }
        }
        (!ret.is_empty()).then_some(ret)
    }

    /// Get all variables defined by a command
    pub fn get_defined_variables(&self, node_id: NodeId) -> Option<HashSet<String>> {
        self.pool
            .get(node_id)
            .map(|node| node.info.defines.keys().cloned().collect())
    }

    /// Get all variables used by a command
    pub fn get_used_variables(&self, node_id: NodeId) -> Option<HashSet<String>> {
        self.pool
            .get(node_id)
            .map(|node| node.info.uses.keys().cloned().collect())
    }

    /// Get all commands this command depends on
    pub fn get_dependencies(&self, node_id: NodeId) -> Option<HashMap<NodeId, HashSet<String>>> {
        self.pool
            .get(node_id)
            .map(|node| node.info.dependencies.clone())
    }

    /// Get all commands that depend on this command
    pub fn get_dependents(&self, node_id: NodeId) -> Option<HashMap<NodeId, HashSet<String>>> {
        self.pool
            .get(node_id)
            .map(|node| node.info.dependencies.clone())
    }

    pub fn get_parent(&self, node_id: NodeId) -> Option<(NodeId, Option<NodeId>)> {
        self.get_node(node_id).info.parent
    }

    pub fn get_children(&self, node_id: NodeId) -> Option<Vec<NodeId>> {
        self.pool
            .get(node_id)
            .map(|n| n.info.children.clone())
            .flatten()
    }

    /// Get vector of all node ids
    pub fn get_ids(&self) -> Vec<NodeId> {
        self.pool.nodes.iter().map(|(id, _)| id).collect()
    }

    /// Get vector of all ids of top-level nodes
    pub fn get_top_ids(&self) -> Vec<NodeId> {
        self.top_ids.clone()
    }

    /// Get a range of the command at the specified index
    pub fn get_ranges(&self, id: NodeId) -> Option<&[(usize, usize)]> {
        self.pool.get(id).map(|n| n.range.as_ref())
    }
    /// Get a reference to the command at the specified index
    pub fn get_command(&self, id: NodeId) -> Option<&AcCommand> {
        self.pool.nodes.get(id).map(|n| &n.cmd)
    }

    /// Get all commands that define or use a variable
    pub fn find_commands_with_variable(&self, var_name: &str) -> HashSet<NodeId> {
        let mut result = HashSet::new();

        // Add commands that define the variable
        if let Some(defs) = self.var_definitions.get(var_name) {
            result.extend(defs.iter().map(|loc| loc.node_id));
        }

        // Add commands that use the variable
        for (id, node) in &self.pool.nodes {
            if node.info.uses.contains_key(var_name) {
                result.insert(id);
            }
        }

        result
    }

    /// Get node representation by id
    pub fn get_node(&self, node_id: NodeId) -> &Node {
        &self.pool.nodes[node_id]
    }

    /// Get node representation by id
    pub fn get_node_mut(&mut self, node_id: NodeId) -> &mut Node {
        &mut self.pool.nodes[node_id]
    }

    /// Get original content of commands in specified node
    pub fn get_content(&self, node_id: NodeId) -> Option<Vec<String>> {
        self.pool.get(node_id).map(|node| {
            node.range
                .iter()
                .map(|&(a, b)| {
                    // FIXME: Poorly working with this lines extraction logic.
                    // Will fix it later.
                    self.lines[a - 1..b - 1]
                        .iter()
                        .filter(|s| !s.is_empty())
                        .map(|s| s.as_str())
                        .collect::<Vec<_>>()
                        .join("\n")
                })
                .collect()
        })
    }

    /// Recover the content of commands from the AST structure
    pub fn recover_content(&self, node_id: NodeId) -> String {
        // FIXME: the strategy mutating self is too dumb.
        self.focus.set(Some(node_id));
        let ret = self.pool.display_node(node_id, 0);
        self.focus.set(None);
        ret
    }

    fn collect_variables(&self, node_id: NodeId) -> (VariableMap, VariableMap) {
        let mut defines = HashMap::new();
        let mut uses = HashMap::new();
        let mut stack = vec![node_id];
        let mut visited = HashSet::new();
        while let Some(id) = stack.pop() {
            assert!(!visited.contains(&id));
            visited.insert(id);
            if let Some(children) = &self.pool.nodes[id].info.children {
                stack.extend(
                    children
                        .iter()
                        .filter(|&&child| !self.pool.nodes[child].info.is_top_node()),
                );
            }
            defines.extend(
                self.pool.nodes[id]
                    .info
                    .defines
                    .iter()
                    .map(|(s, v)| (s.clone(), v.clone())),
            );
            uses.extend(
                self.pool.nodes[id]
                    .info
                    .uses
                    .iter()
                    .map(|(s, v)| (s.clone(), v.clone())),
            );
        }
        (defines, uses)
    }

    /// Find case statements matching the given variables in the top-level commands.
    pub fn find_case_matches(&self, var_names: &[String]) -> Vec<CaseMatch> {
        let finder =
            CaseMatchFinder::find_case_matches(&self.pool.nodes, &self.top_ids, var_names.to_vec());
        finder.matches
    }
}
