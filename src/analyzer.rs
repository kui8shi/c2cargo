//! Provides the higher level on-time analyses to improve parsing

use autoconf_parser::{
    ast::{
        minimal::{
            Command, CommandWrapper, CompoundCommand, Condition, GuardBodyPair, Operator, Word,
            WordFragment,
        },
        Arithmetic, Parameter, ParameterSubstitution, PatternBodyPair, Redirect,
    },
    lexer::Lexer,
    m4_macro::{M4Argument, M4Macro},
    parse::MinimalParser,
};
use std::collections::{HashMap, HashSet};

use flatten::Flattener;
use variable::VariableAnalyzer;
use case::{CaseAnalyzer, CaseMatch};
use eval::{EvalAnalyzer, EvalMatch};

mod flatten;
mod variable;
mod case;
mod eval;

type TopLevelCommand = CommandWrapper<String>;
type TopLevelWord = Word<String, TopLevelCommand>;
type MinimalParameterSubstitution =
    ParameterSubstitution<Parameter<String>, TopLevelWord, TopLevelCommand, Arithmetic<String>>;

/// Find case statements matching the given variables in the top-level commands.
pub fn find_case_matches(
    commands: &[TopLevelCommand],
    var_names: Vec<String>,
) -> Vec<CaseMatch> {
    let mut finder = CaseAnalyzer::new(var_names);
    for cw in commands {
        finder.visit_command_wrapper(cw);
    }
    finder.matches
}

/// Find `eval` commands that generate dynamic variable references.
pub fn find_eval_dynamic_refs(commands: &[TopLevelCommand]) -> Vec<EvalMatch> {
    let mut finder = EvalAnalyzer::new();
    for cw in commands {
        finder.visit_command_wrapper(cw);
    }
    finder.matches
}

/// Visitor trait for walking over the AST nodes.
pub trait AstVisitor: Sized {
    /// Visit a command wrapper (the top-level AST node).
    fn visit_command_wrapper(&mut self, cw: &TopLevelCommand) {
        self.walk_command_wrapper(cw);
    }

    /// Visit a command.
    fn visit_command(&mut self, cmd: &Command<String>) {
        self.walk_command(cmd);
    }

    /// Visit a compound command.
    fn visit_compound(&mut self, compound: &CompoundCommand<TopLevelWord, TopLevelCommand>) {
        self.walk_compound(compound);
    }

    /// Visit a guard-body pair (e.g., in while/until/if).
    fn visit_guard_body_pair(&mut self, pair: &GuardBodyPair<TopLevelWord, TopLevelCommand>) {
        self.walk_guard_body_pair(pair);
    }

    /// Visit a pattern-body pair (e.g., in case).
    fn visit_pattern_body_pair(&mut self, pair: &PatternBodyPair<TopLevelWord, TopLevelCommand>) {
        self.walk_pattern_body_pair(pair);
    }

    /// Visit a word.
    fn visit_word(&mut self, w: &TopLevelWord) {
        self.walk_word(w);
    }

    /// Visit a word fragment.
    fn visit_fragment(&mut self, f: &WordFragment<String, TopLevelWord, TopLevelCommand>) {
        self.walk_fragment(f);
    }

    /// Visit a conditional expression.
    fn visit_condition(&mut self, cond: &Condition<TopLevelWord, TopLevelCommand>) {
        self.walk_condition(cond);
    }

    /// Visit an arithmetic expression.
    fn visit_arithmetic(&mut self, arith: &Arithmetic<String>) {
        self.walk_arithmetic(arith);
    }

    /// Visit a parameter.
    fn visit_parameter(&mut self, param: &Parameter<String>) {
        self.walk_parameter(param);
    }

    /// Visit a parameter substitution.
    fn visit_parameter_substitution(&mut self, subs: &MinimalParameterSubstitution) {
        self.walk_parameter_substitution(subs);
    }

    /// Visit an IO redirect.
    fn visit_redirect(&mut self, redir: &Redirect<TopLevelWord>) {
        self.walk_redirect(redir);
    }

    /// Visit an M4 macro invocation.
    fn visit_m4_macro(&mut self, m: &M4Macro<TopLevelWord, TopLevelCommand>) {
        self.walk_m4_macro(m);
    }

    /// Walk a command wrapper node.
    fn walk_command_wrapper(&mut self, cw: &TopLevelCommand) {
        self.visit_command(&cw.cmd);
    }

    /// Walk a command node.
    fn walk_command(&mut self, cmd: &Command<String>) {
        match cmd {
            Command::Assignment(_, word) => self.visit_word(word),
            Command::Compound(compound) => self.visit_compound(compound),
            Command::Cmd(words) => {
                for w in words {
                    self.visit_word(w);
                }
            }
        }
    }

    /// Walk a compound command node.
    fn walk_compound(&mut self, compound: &CompoundCommand<TopLevelWord, TopLevelCommand>) {
        match compound {
            CompoundCommand::Macro(m4) => self.visit_m4_macro(m4),
            CompoundCommand::Brace(cmds) | CompoundCommand::Subshell(cmds) => {
                for c in cmds {
                    self.visit_command_wrapper(c);
                }
            }
            CompoundCommand::While(pair) | CompoundCommand::Until(pair) => {
                self.visit_guard_body_pair(pair)
            }
            CompoundCommand::If {
                conditionals,
                else_branch,
            } => {
                for gb in conditionals {
                    self.visit_guard_body_pair(gb);
                }
                for c in else_branch {
                    self.visit_command_wrapper(c);
                }
            }
            CompoundCommand::For { words, body, .. } => {
                for w in words {
                    self.visit_word(w);
                }
                for c in body {
                    self.visit_command_wrapper(c);
                }
            }
            CompoundCommand::Case { word, arms } => {
                self.visit_word(word);
                for arm in arms {
                    self.visit_pattern_body_pair(arm);
                }
            }
            CompoundCommand::And(cond, c) | CompoundCommand::Or(cond, c) => {
                self.visit_condition(cond);
                self.visit_command_wrapper(c);
            }
            CompoundCommand::Pipe(_, cmds) => {
                for c in cmds {
                    self.visit_command_wrapper(c);
                }
            }
            CompoundCommand::Redirect(cmd, redirects) => {
                self.visit_command_wrapper(cmd);
                for r in redirects {
                    self.visit_redirect(r);
                }
            }
            CompoundCommand::Background(cmd) => self.visit_command_wrapper(cmd),
            CompoundCommand::FunctionDef { body, .. } => self.visit_command_wrapper(body),
        }
    }

    /// Walk a guard-body pair node.
    fn walk_guard_body_pair(&mut self, pair: &GuardBodyPair<TopLevelWord, TopLevelCommand>) {
        self.visit_condition(&pair.condition);
        for c in &pair.body {
            self.visit_command_wrapper(c);
        }
    }

    /// Walk a pattern-body pair node.
    fn walk_pattern_body_pair(&mut self, pair: &PatternBodyPair<TopLevelWord, TopLevelCommand>) {
        for w in &pair.patterns {
            self.visit_word(w);
        }
        for c in &pair.body {
            self.visit_command_wrapper(c);
        }
    }

    /// Walk a word node.
    fn walk_word(&mut self, w: &TopLevelWord) {
        match w {
            Word::Concat(frags) => {
                for f in frags {
                    self.visit_fragment(f);
                }
            }
            Word::Single(f) => self.visit_fragment(f),
            Word::Empty => {}
        }
    }

    /// Walk a word fragment node.
    fn walk_fragment(&mut self, f: &WordFragment<String, TopLevelWord, TopLevelCommand>) {
        match f {
            WordFragment::Param(param) => self.visit_parameter(param),
            WordFragment::DoubleQuoted(frags) => {
                for f in frags {
                    self.visit_fragment(f);
                }
            }
            WordFragment::Macro(m4) => self.visit_m4_macro(m4),
            WordFragment::Subst(subst) => self.visit_parameter_substitution(subst.as_ref()),
            _ => {}
        }
    }

    /// Walk a conditional expression node.
    fn walk_condition(&mut self, cond: &Condition<TopLevelWord, TopLevelCommand>) {
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
                    self.visit_command(&cmd.cmd);
                }
            }
            Condition::ReturnZero(cmd) => self.visit_command(&cmd.cmd),
        }
    }

    /// Walk an arithmetic expression node.
    fn walk_arithmetic(&mut self, arith: &Arithmetic<String>) {
        match arith {
            Arithmetic::UnaryPlus(x)
            | Arithmetic::UnaryMinus(x)
            | Arithmetic::LogicalNot(x)
            | Arithmetic::BitwiseNot(x) => self.visit_arithmetic(x),
            Arithmetic::Pow(x, y)
            | Arithmetic::Mult(x, y)
            | Arithmetic::Div(x, y)
            | Arithmetic::Modulo(x, y)
            | Arithmetic::Add(x, y)
            | Arithmetic::Sub(x, y)
            | Arithmetic::ShiftLeft(x, y)
            | Arithmetic::ShiftRight(x, y)
            | Arithmetic::Less(x, y)
            | Arithmetic::LessEq(x, y)
            | Arithmetic::Great(x, y)
            | Arithmetic::GreatEq(x, y)
            | Arithmetic::Eq(x, y)
            | Arithmetic::NotEq(x, y)
            | Arithmetic::BitwiseAnd(x, y)
            | Arithmetic::BitwiseXor(x, y)
            | Arithmetic::BitwiseOr(x, y)
            | Arithmetic::LogicalAnd(x, y)
            | Arithmetic::LogicalOr(x, y) => {
                self.visit_arithmetic(x);
                self.visit_arithmetic(y);
            }
            Arithmetic::Ternary(x, y, z) => {
                self.visit_arithmetic(x);
                self.visit_arithmetic(y);
                self.visit_arithmetic(z);
            }
            Arithmetic::Sequence(seq) => {
                for a in seq {
                    self.visit_arithmetic(a);
                }
            }
            _ => {}
        }
    }

    /// Walk a parameter node.
    fn walk_parameter(&mut self, _param: &Parameter<String>) {}

    /// Walk a parameter substitution node.
    fn walk_parameter_substitution(&mut self, subs: &MinimalParameterSubstitution) {
        match subs {
            ParameterSubstitution::Command(cmds) => {
                for c in cmds {
                    self.visit_command(&c.cmd);
                }
            }
            ParameterSubstitution::Arith(Some(arith)) => self.visit_arithmetic(arith),
            ParameterSubstitution::Len(param) => self.visit_parameter(param),
            ParameterSubstitution::Default(_, param, word)
            | ParameterSubstitution::Assign(_, param, word)
            | ParameterSubstitution::Error(_, param, word)
            | ParameterSubstitution::Alternative(_, param, word)
            | ParameterSubstitution::RemoveSmallestSuffix(param, word)
            | ParameterSubstitution::RemoveLargestSuffix(param, word)
            | ParameterSubstitution::RemoveSmallestPrefix(param, word)
            | ParameterSubstitution::RemoveLargestPrefix(param, word) => {
                self.visit_parameter(param);
                if let Some(w) = word {
                    self.visit_word(w);
                }
            }
            _ => {}
        }
    }

    /// Walk an IO redirect node.
    fn walk_redirect(&mut self, redir: &Redirect<TopLevelWord>) {
        match redir {
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

    /// Walk an M4 macro node (visits arguments only).
    fn walk_m4_macro(&mut self, m4: &M4Macro<TopLevelWord, TopLevelCommand>) {
        for arg in &m4.args {
            match arg {
                M4Argument::Word(w) => self.visit_word(w),
                M4Argument::Array(ws) => {
                    for w in ws {
                        self.visit_word(w);
                    }
                }
                M4Argument::Commands(cmds) => {
                    for c in cmds {
                        self.visit_command(&c.cmd);
                    }
                }
                _ => {}
            }
        }
    }
}

/// Represents a node in the dependency graph
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Node {
    /// Index of the node in the original list
    id: usize,
    /// trailing comments
    comment: Option<String>,
    /// Range of line numbers where the body is effectively referenced.
    ranges: Vec<(usize, usize)>,
    /// Body of commands referenced by this node.
    cmd: Command<String>,
    /// ID of the parent node if the commands were flattened
    parent: Option<usize>,
    /// IDs of the children if the commands were flattened
    children: Option<Vec<usize>>,
    /// Variables defined by this command
    defines: HashMap<String, Vec<Guard>>,
    /// Variables used by this command
    uses: HashMap<String, Vec<Guard>>,
    /// Dependencies (indices of nodes this command depends on by variables)
    var_dependencies: HashSet<usize>,
    /// Commands that depend on this node
    var_dependents: HashSet<usize>,
}

/// Represents a condition
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Guard {
    /// doc
    Not(Box<Self>),
    /// doc
    Cond(Condition<TopLevelWord, TopLevelCommand>),
    /// doc
    Match(TopLevelWord, Vec<TopLevelWord>),
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
    nodes: Vec<Node>,
    /// Map of variable names to indices of commands that define them
    var_definitions: HashMap<String, Vec<(usize, Vec<Guard>)>>,
}

impl Analyzer {
    /// Analyze commands and build the dependency graph
    pub fn new<S: AsRef<str>>(contents: S, flatten_threshold: Option<usize>) -> Self {
        let lexer = Lexer::new(contents.as_ref().chars());
        let parser = MinimalParser::new(lexer);

        let mut commands = Vec::new();

        // Collect all complete commands from the parser
        for result in parser {
            if let Ok(cmd) = result {
                commands.push(cmd);
            }
        }

        let flatten_threshold = flatten_threshold.unwrap_or(100);

        let mut s = Self {
            lines: contents.as_ref().lines().map(|s| s.to_string()).collect(),
            nodes: Self::flatten_commands_to_nodes(commands, flatten_threshold),
            var_definitions: HashMap::new(),
        };

        // collect all defined and used variables in a single pass
        for i in 0..s.nodes.len() {
            // Create a VariableAnalyzer to extract both defined and used variables
            let analyzer = VariableAnalyzer::new(&s.nodes[i].cmd);

            // Get defined variables
            s.nodes[i].defines = analyzer.defines.clone();

            // Update var_definitions map
            for (var, guards) in &analyzer.defines {
                s.var_definitions
                    .entry(var.clone())
                    .or_insert_with(Vec::new)
                    .push((i, guards.clone()));
            }

            // Get used variables
            s.nodes[i].uses = analyzer.uses;
        }

        // Create dependency edges based on variable usage
        for i in 0..s.nodes.len() {
            for var in s.nodes[i].uses.clone().keys() {
                if let Some(def_idx) = s.get_definition(var, i) {
                    s.nodes[i].var_dependencies.insert(def_idx);
                    s.nodes[def_idx].var_dependents.insert(i);
                }
            }
        }

        s
    }

    fn flatten_commands_to_nodes(
        commands: Vec<TopLevelCommand>,
        flatten_threshold: usize,
    ) -> Vec<Node> {
        // Delegate flattening to the Flattener visitor
        let mut flattener = Flattener::new(flatten_threshold);
        for cw in commands {
            flattener.visit_command_wrapper(&cw);
        }
        return flattener.nodes;
    }

    /// Get command that define a variable before
    pub fn get_definition(&self, var_name: &str, cmd_index: usize) -> Option<usize> {
        if let Some(node) = self.nodes.get(cmd_index) {
            if let Some(user_guards) = node.uses.get(var_name) {
                return self.var_definitions.get(var_name).and_then(|v| {
                    v.iter()
                        .rev()
                        .filter_map(|(i, guards)| {
                            // dumb heulistic to compare two guard conditions
                            (*i < cmd_index && guards.len() <= user_guards.len()).then_some(i)
                        })
                        .next()
                        .cloned()
                });
            }
        }
        None
    }

    /// Get all variables defined by a command
    pub fn get_defined_variables(&self, cmd_index: usize) -> Option<HashSet<String>> {
        self.nodes
            .get(cmd_index)
            .map(|node| node.defines.keys().cloned().collect())
    }

    /// Get all variables used by a command
    pub fn get_used_variables(&self, cmd_index: usize) -> Option<HashSet<String>> {
        self.nodes
            .get(cmd_index)
            .map(|node| node.uses.keys().cloned().collect())
    }

    /// Get all commands this command depends on
    pub fn get_dependencies(&self, cmd_index: usize) -> Option<HashSet<usize>> {
        self.nodes.get(cmd_index).map(|node| {
            let mut deps = node.var_dependencies.clone();
            if let Some(parent) = node.parent {
                deps.insert(parent);
            }
            deps
        })
    }

    /// Get all commands that depend on this command
    pub fn get_dependents(&self, cmd_index: usize) -> Option<HashSet<usize>> {
        self.nodes.get(cmd_index).map(|node| {
            let mut deps = node.var_dependencies.clone();
            if let Some(children) = &node.children {
                deps.extend(children.iter().copied());
            }
            deps
        })
    }

    /// Get the total number of commands analyzed
    pub fn command_count(&self) -> usize {
        self.nodes.len()
    }

    /// Get a range of the command at the specified index
    pub fn get_ranges(&self, index: usize) -> Option<&[(usize, usize)]> {
        self.nodes.get(index).map(|n| n.ranges.as_ref())
    }
    /// Get a reference to the command at the specified index
    pub fn get_command(&self, index: usize) -> Option<&Command<String>> {
        self.nodes.get(index).map(|n| &n.cmd)
    }

    /// Get all commands that define or use a variable
    pub fn find_commands_with_variable(&self, var_name: &str) -> HashSet<usize> {
        let mut result = HashSet::new();

        // Add commands that define the variable
        if let Some(def_indices) = self.var_definitions.get(var_name) {
            result.extend(def_indices.iter().map(|(i, _)| i));
        }

        // Add commands that use the variable
        for (i, node) in self.nodes.iter().enumerate() {
            if node.uses.contains_key(var_name) {
                result.insert(i);
            }
        }

        result
    }

    /// Get original content of commands in specified node
    pub fn get_content(&self, node_id: usize) -> Option<Vec<String>> {
        self.nodes.get(node_id).map(|node| {
            node.ranges
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
}
