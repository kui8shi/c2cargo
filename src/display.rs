use std::cell::Cell;

use autotools_parser::ast::{
    node::{
        AcCommand, AcWord, AcWordFragment, DisplayNode, M4Argument, M4Macro, Node, NodeId, NodePool,
    },
    MayM4,
};
use slab::Slab;

#[derive(Default)]
/// A pool of autoconf commands stored as nodes.
pub struct AutoconfPool<U = ()> {
    /// Contains all nodes. `NodeId` represents indexes of nodes in this slab.
    pub nodes: Slab<Node<AcCommand, U>>,
    /// Assigned the id of top-most node while formatting a tree of nodes.
    focus: Cell<Option<NodeId>>,
    /// A user-defined function which tell the node should be displayed
    cross_boundary: Option<Box<dyn Fn(&Node<AcCommand, U>) -> bool>>,
}

impl<U: std::fmt::Debug> std::fmt::Debug for AutoconfPool<U> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AutoconfPool")
            .field("nodes", &self.nodes)
            .field("forcus", &self.focus)
            .finish()
    }
}

#[allow(dead_code)]
impl<U> AutoconfPool<U> {
    /// Construct a new pool of autoconf commands
    pub fn new(
        nodes: Slab<Node<AcCommand, U>>,
        cross_boundary: Option<Box<dyn Fn(&Node<AcCommand, U>) -> bool>>,
    ) -> Self {
        Self {
            nodes,
            focus: Cell::new(None),
            cross_boundary,
        }
    }

    /// Construct a new pool from a given vector of autoconf commands
    pub fn from_vec(nodes: Vec<Node<AcCommand, U>>) -> Self {
        let nodes = {
            let mut tmp = Slab::with_capacity(nodes.len());
            for node in nodes {
                tmp.insert(node);
            }
            tmp
        };
        Self {
            nodes,
            focus: Cell::new(None),
            cross_boundary: None,
        }
    }

    /// Get the number of nodes (commands)
    pub fn num_nodes(&self) -> usize {
        self.nodes.len()
    }

    /// Get a node by its ID.
    pub fn get(&self, id: NodeId) -> Option<&Node<AcCommand, U>> {
        self.nodes.get(id)
    }
}

impl<U> DisplayNode for AutoconfPool<U> {
    type Word = AcWord;

    fn display_node(&self, node_id: NodeId, indent_level: usize) -> String {
        if let Some(node) = self.get(node_id) {
            let is_top = self.focus.get().is_none();
            if is_top {
                self.focus.replace(Some(node_id));
            } else if let Some(beyond_boundary) = &self.cross_boundary {
                if beyond_boundary(node) {
                    // the node beyond boundary should not be displayed.
                    return String::new();
                }
            }
            use MayM4::*;
            let result = match &node.cmd.0 {
                Macro(m4_macro) => self.m4_macro_to_string(m4_macro, indent_level),
                Shell(cmd) => self.command_to_string(cmd, node.comment.clone(), indent_level),
            };
            if is_top {
                self.focus.replace(None);
            }
            result
        } else {
            String::new()
        }
    }

    fn display_word(&self, word: &AcWord, should_quote: bool) -> String {
        use autotools_parser::ast::minimal::Word::*;
        use autotools_parser::ast::minimal::WordFragment::{DoubleQuoted, Literal};
        match &word.0 {
            Empty => "\"\"".to_string(),
            Concat(frags) => frags
                .iter()
                .map(|w| self.may_m4_word_to_string(w))
                .collect::<Vec<String>>()
                .concat()
                .to_string(),
            Single(frag) => {
                let s = self.may_m4_word_to_string(frag);
                if should_quote {
                    match frag {
                        MayM4::Shell(Literal(lit)) if !lit.contains("\'") => {
                            format!("\'{}\'", s)
                        }
                        MayM4::Shell(DoubleQuoted(_)) => s,
                        _ => {
                            format!("\"{}\"", s)
                        }
                    }
                } else {
                    s
                }
            }
        }
    }
}

impl<U> AutoconfPool<U> {
    fn may_m4_word_to_string(&self, frag: &AcWordFragment) -> String {
        use MayM4::*;
        match frag {
            Macro(macro_word) => format!(
                "{}({})",
                macro_word.name,
                macro_word
                    .args
                    .iter()
                    .map(|arg| self.m4_argument_to_string(arg, 0))
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
            Shell(shell_word) => self.shell_word_to_string(shell_word),
        }
    }

    /// Format an M4 macro call (`M4Macro`) into a string
    fn m4_macro_to_string(&self, m4_macro: &M4Macro, indent_level: usize) -> String {
        const TAB_WIDTH: usize = 2;
        let tab = " ".repeat(indent_level * TAB_WIDTH);
        format!(
            "{tab}{}({})",
            // m4_macro.original_name.as_ref().unwrap_or(&m4_macro.name),
            &m4_macro.name,
            m4_macro
                .args
                .iter()
                .map(|arg| self.m4_argument_to_string(arg, indent_level + 1))
                .collect::<Vec<String>>()
                .join(&format!(",\n{tab}  "))
        )
    }

    /// Format an M4 macro argument (`M4Argument`) into a string, applying `indent_level`
    /// spaces for multiline argument formatting.
    fn m4_argument_to_string(&self, arg: &M4Argument, indent_level: usize) -> String {
        use autotools_parser::m4_macro::M4Argument::*;
        const TAB_WIDTH: usize = 2;
        let newline = format!("\n{}", " ".repeat(indent_level * TAB_WIDTH));
        match arg {
            Literal(lit) => format!("[{}]", lit),
            Word(word) => self.display_word(word, false),
            Array(words) => words
                .iter()
                .map(|w| self.display_word(w, false))
                .collect::<Vec<String>>()
                .join(if words.len() < 10 { " " } else { &newline })
                .to_string(),
            Program(prog) => format!("[{}]", prog.replace("\n", &newline)),
            Commands(cmds) => {
                if !cmds.is_empty() {
                    format!(
                        "[\n{}{newline}]",
                        cmds.iter()
                            .map(|c| self.display_node(*c, indent_level + 2))
                            .collect::<Vec<String>>()
                            .join("\n")
                    )
                } else {
                    "[]".to_owned()
                }
            }
            Condition(cond) => format!("[{}]", self.condition_to_string(cond)),
            Unknown(unknown) => format!("[{}]", unknown),
        }
    }
}

impl<U> NodePool<AcWord> for AutoconfPool<U> {}

#[cfg(test)]
mod tests {
    use super::{AcCommand, AcWord, AutoconfPool, Node, NodePool};
    use autotools_parser::ast::minimal::Word;
    use autotools_parser::ast::minimal::WordFragment::*;
    use autotools_parser::ast::node::Condition;
    use autotools_parser::ast::node::DisplayNode;
    use autotools_parser::ast::node::GuardBodyPair;
    use autotools_parser::ast::node::Operator;
    use autotools_parser::ast::node::ParameterSubstitution;
    use autotools_parser::ast::node::PatternBodyPair;
    use autotools_parser::ast::node::Redirect;
    use autotools_parser::ast::node::ShellCommand;
    use autotools_parser::ast::MayM4::*;
    use autotools_parser::ast::Parameter;
    use autotools_parser::m4_macro::{M4Argument, M4Macro};

    type C = ShellCommand<AcWord>;

    #[test]
    fn test_node_to_string_assignment_and_cmd() {
        let word: AcWord = Word::Single(Shell(Literal("value".to_string()))).into();
        let assign_node = Node::new(
            None,
            None,
            AcCommand::new_cmd(C::Assignment("var".to_string(), word.clone().into())),
            (),
        );
        let echo: AcWord = Word::Single(Shell(Literal("echo".to_string()))).into();
        let cmd_node = Node::new(
            None,
            None,
            AcCommand::new_cmd(C::Cmd(vec![echo.clone(), word.clone()])),
            (),
        );
        let pool = AutoconfPool::from_vec(vec![assign_node, cmd_node]);
        assert_eq!(pool.display_node(0, 0), "var=\'value\'");
        assert_eq!(pool.display_node(1, 1), "  echo 'value'");
    }

    #[test]
    fn test_operator_to_string() {
        let pool: AutoconfPool<()> = AutoconfPool::from_vec(vec![]);
        let op = Operator::Eq(
            Word::Single(Shell(Literal("a".to_string()))).into(),
            Word::Single(Shell(Literal("b".to_string()))).into(),
        );
        assert_eq!(pool.operator_to_string(&op), "a = b");
    }

    #[test]
    fn test_word_and_fragment_to_string() {
        let pool: AutoconfPool<()> = AutoconfPool::from_vec(vec![]);
        let frag = DoubleQuoted(vec![Literal("hi".to_string())]);
        assert_eq!(pool.shell_word_to_string(&frag), "\"hi\"");
        let word = Word::Concat(vec![
            Shell(Literal("a".to_string())),
            Shell(Literal("b".to_string())),
        ])
        .into();
        assert_eq!(pool.display_word(&word, false), "ab");
    }

    #[test]
    fn test_condition_to_string() {
        let pool: AutoconfPool<()> = AutoconfPool::from_vec(vec![]);
        let cond = Condition::Cond(Operator::Neq(
            Word::Single(Shell(Literal("x".to_string()))).into(),
            Word::Single(Shell(Literal("y".to_string()))).into(),
        ));
        assert_eq!(pool.condition_to_string(&cond), "test x != y");
    }

    #[test]
    fn test_redirect_to_string() {
        let pool: AutoconfPool<()> = AutoconfPool::from_vec(vec![]);
        let word = Word::Single(Shell(Literal("out".to_string()))).into();
        let redir = autotools_parser::ast::Redirect::Write(None, word);
        assert_eq!(pool.redirect_to_string(&redir), "> out");
    }

    #[test]
    fn test_parameter_substitution_to_string_default() {
        let pool: AutoconfPool<()> = AutoconfPool::from_vec(vec![]);
        let subst = ParameterSubstitution::Default(
            false,
            Parameter::Var("v".to_string()),
            Some(Word::Single(Shell(Literal("w".to_string()))).into()),
        );
        assert_eq!(pool.parameter_substitution_to_string(&subst), "${v:-w}");
    }

    #[test]
    fn test_m4_argument_to_string_literal() {
        let pool: AutoconfPool<()> = AutoconfPool::from_vec(vec![]);
        let arg = M4Argument::Literal("lit".to_string());
        assert_eq!(pool.m4_argument_to_string(&arg, 0), "[lit]");
    }

    #[test]
    fn test_node_to_string_brace_and_subshell() {
        let echo: AcWord = Word::Single(Shell(Literal("echo".to_string()))).into();
        let hi: AcWord = Word::Single(Shell(Literal("hi".to_string()))).into();
        let cmd = Node::new(
            None,
            None,
            AcCommand::new_cmd(C::Cmd(vec![echo.clone(), hi.clone()])),
            (),
        );
        let brace = Node::new(None, None, AcCommand::new_cmd(C::Brace(vec![0])), ());
        let subshell = Node::new(None, None, AcCommand::new_cmd(C::Subshell(vec![0])), ());
        let pool = AutoconfPool::from_vec(vec![cmd, brace, subshell]);
        assert_eq!(pool.display_node(1, 0), "{\n  echo 'hi'\n}");
        assert_eq!(pool.display_node(2, 0), "(\n  echo 'hi'\n)");
    }

    #[test]
    fn test_node_to_string_while_until() {
        let w: AcWord = Word::Single(Shell(Literal("f".to_string()))).into();
        let cond = Condition::Cond(Operator::Empty(w.clone()));
        let body = Node::new(None, None, AcCommand::new_cmd(C::Cmd(vec![w.clone()])), ());
        let gbp = GuardBodyPair {
            condition: cond.clone(),
            body: vec![0],
        };
        let while_node = Node::new(None, None, AcCommand::new_cmd(C::While(gbp.clone())), ());
        let until_node = Node::new(None, None, AcCommand::new_cmd(C::Until(gbp.clone())), ());
        let pool =
            AutoconfPool::from_vec(vec![body.clone(), while_node.clone(), until_node.clone()]);
        assert_eq!(pool.display_node(1, 0), "while test -z f; do\n  f\ndone");
        assert_eq!(pool.display_node(2, 0), "until test -z f; do\n  f\ndone");
    }

    #[test]
    fn test_node_to_string_if_else() {
        let w: AcWord = Word::Single(Shell(Literal("t".to_string()))).into();
        let cond = Condition::Cond(Operator::Empty(w.clone()));
        let cmd_true = Node::new(None, None, AcCommand::new_cmd(C::Cmd(vec![w.clone()])), ());
        let cmd_false = Node::new(
            None,
            None,
            AcCommand::new_cmd(C::Cmd(vec![
                Word::Single(Shell(Literal("f".to_string()))).into()
            ])),
            (),
        );
        let cmd_else = Node::new(
            None,
            None,
            AcCommand::new_cmd(C::Cmd(vec![
                Word::Single(Shell(Literal("e".to_string()))).into()
            ])),
            (),
        );
        let gbp1 = GuardBodyPair {
            condition: cond.clone(),
            body: vec![0],
        };
        let gbp2 = GuardBodyPair {
            condition: cond.clone(),
            body: vec![1],
        };
        let if_node = Node::new(
            None,
            None,
            AcCommand::new_cmd(C::If {
                conditionals: vec![gbp1.clone()],
                else_branch: vec![],
            }),
            (),
        );
        let if_else_node = Node::new(
            None,
            None,
            AcCommand::new_cmd(C::If {
                conditionals: vec![gbp1, gbp2],
                else_branch: vec![2],
            }),
            (),
        );
        let pool = AutoconfPool::from_vec(vec![
            cmd_true.clone(),
            cmd_false.clone(),
            cmd_else.clone(),
            if_node.clone(),
            if_else_node.clone(),
        ]);
        assert_eq!(pool.display_node(3, 0), "if test -z t; then\n  t\nfi");
        assert_eq!(
            pool.display_node(4, 0),
            "if test -z t; then\n  t\nelse if test -z t; then\n  f\nelse\n  e\nfi"
        );
    }

    #[test]
    fn test_node_to_string_for() {
        let cmd = Node::new(
            None,
            None,
            AcCommand::new_cmd(C::Cmd(vec![
                Word::Single(Shell(Literal("x".to_string()))).into()
            ])),
            (),
        );
        let words = vec![
            Word::Single(Shell(Literal("1".to_string()))).into(),
            Word::Single(Shell(Literal("2".to_string()))).into(),
        ];
        let for_node = Node::new(
            None,
            None,
            AcCommand::new_cmd(C::For {
                var: "i".to_string(),
                words: words.clone(),
                body: vec![0],
            }),
            (),
        );
        let pool = AutoconfPool::from_vec(vec![cmd.clone(), for_node.clone()]);
        assert_eq!(
            pool.display_node(1, 0),
            "for i in \'1\' \'2\'; do\n  x\ndone"
        );
    }

    #[test]
    fn test_node_to_string_case() {
        let cmd = Node::new(
            None,
            None,
            AcCommand::new_cmd(C::Cmd(vec![
                Word::Single(Shell(Literal("c".to_string()))).into()
            ])),
            (),
        );
        let pat1: AcWord = Word::Single(Shell(Literal("a".to_string()))).into();
        let pat2: AcWord = Word::Single(Shell(Literal("b".to_string()))).into();
        let arm = PatternBodyPair {
            comments: vec![],
            patterns: vec![pat1.clone(), pat2.clone()],
            body: vec![0],
        };
        let case_node = Node::new(
            None,
            None,
            AcCommand::new_cmd(C::Case {
                word: Word::Single(Shell(Literal("x".to_string()))).into(),
                arms: vec![arm],
            }),
            (),
        );
        let pool = AutoconfPool::from_vec(vec![cmd.clone(), case_node.clone()]);
        assert_eq!(
            pool.display_node(1, 0),
            "case x in\n  a|b)\n    c\n    ;;\nesac"
        );
    }

    #[test]
    fn test_node_to_string_and_or_pipe() {
        let cmd = Node::new(
            None,
            None,
            AcCommand::new_cmd(C::Cmd(vec![
                Word::Single(Shell(Literal("c".to_string()))).into()
            ])),
            (),
        );
        let eq = Operator::Eq(
            Word::Single(Shell(Literal("a".to_string()))).into(),
            Word::Single(Shell(Literal("b".to_string()))).into(),
        );
        let cond = Condition::Cond(eq.clone());
        let and_node = Node::new(None, None, AcCommand::new_cmd(C::And(cond.clone(), 0)), ());
        let or_node = Node::new(None, None, AcCommand::new_cmd(C::Or(cond.clone(), 0)), ());
        let pipe_node = Node::new(
            None,
            None,
            AcCommand::new_cmd(C::Pipe(false, vec![0, 0])),
            (),
        );
        let bang_pipe = Node::new(
            None,
            None,
            AcCommand::new_cmd(C::Pipe(true, vec![0, 0])),
            (),
        );
        let pool = AutoconfPool::from_vec(vec![
            cmd.clone(),
            and_node.clone(),
            or_node.clone(),
            pipe_node.clone(),
            bang_pipe.clone(),
        ]);
        assert_eq!(pool.display_node(1, 0), "test a = b && c");
        assert_eq!(pool.display_node(2, 0), "test a = b || c");
        assert_eq!(pool.display_node(3, 0), "c | c");
        assert_eq!(pool.display_node(4, 0), "!c | c");
    }

    #[test]
    fn test_node_to_string_redirect_and_background() {
        let cmd = Node::new(
            None,
            None,
            AcCommand::new_cmd(C::Cmd(vec![Word::Single(Shell(Literal(
                "cmd".to_string(),
            )))
            .into()])),
            (),
        );
        let r1 = Redirect::Read(None, Word::Single(Shell(Literal("in".to_string()))).into());
        let r2 = Redirect::Write(
            Some(1),
            Word::Single(Shell(Literal("out".to_string()))).into(),
        );
        let rd_node = Node::new(
            None,
            None,
            AcCommand::new_cmd(C::Redirect(0, vec![r1, r2])),
            (),
        );
        let bg_node = Node::new(None, None, AcCommand::new_cmd(C::Background(0)), ());
        let pool = AutoconfPool::from_vec(vec![cmd.clone(), rd_node.clone(), bg_node.clone()]);
        assert_eq!(pool.display_node(1, 0), "cmd < in 1> out");
        assert_eq!(pool.display_node(2, 0), "cmd &");
    }

    #[test]
    fn test_node_to_string_functiondef_and_macro() {
        let body = Node::new(
            None,
            None,
            AcCommand::new_cmd(C::Cmd(vec![
                Word::Single(Shell(Literal("b".to_string()))).into()
            ])),
            (),
        );
        let func = Node::new(
            None,
            None,
            AcCommand::new_cmd(C::FunctionDef {
                name: "f".to_string(),
                body: 0,
            }),
            (),
        );
        let m4 = M4Macro::new(
            "m".to_string(),
            vec![
                M4Argument::Literal("a".to_string()),
                M4Argument::Word(Word::Single(Shell(Literal("w".to_string()))).into()),
            ],
        );
        let mac = Node::new(None, None, m4.clone().into(), ());
        let pool = AutoconfPool::from_vec(vec![body.clone(), func.clone(), mac.clone()]);
        assert_eq!(pool.display_node(1, 0), "function f () b");
        assert_eq!(pool.display_node(2, 0), "m([a],\n  w)");
    }

    #[test]
    fn test_node_to_string_with_single_quotes_in_literal() {
        let echo: AcWord = Word::Single(Shell(Literal("echo".to_string()))).into();
        let lit = Word::Single(Shell(Literal("\')".to_string()))).into();
        let cmd = Node::new(None, None, AcCommand::new_cmd(C::Cmd(vec![echo, lit])), ());
        let redir = autotools_parser::ast::Redirect::Write(None, Word::Empty.into());
        let rd_node = Node::new(
            None,
            None,
            AcCommand::new_cmd(C::Redirect(0, vec![redir])),
            (),
        );
        let pool = AutoconfPool::from_vec(vec![cmd, rd_node]);
        assert_eq!(pool.display_node(1, 0), "echo \"\')\" > \"\"");
    }
}
