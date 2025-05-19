use std::collections::HashMap;

use autoconf_parser::{
    ast::{
        minimal::{Command, CompoundCommand, Condition, WordFragment},
        Arithmetic, Parameter, ParameterSubstitution, Redirect,
    },
    m4_macro::{M4Argument, M4Macro},
};

use super::{AstVisitor, Guard, MinimalParameterSubstitution, TopLevelCommand, TopLevelWord};

#[derive(Debug)]
pub(super) struct VariableAnalyzer {
    pub defines: HashMap<String, Vec<Guard>>,
    pub uses: HashMap<String, Vec<Guard>>,
    conds: Vec<Guard>,
}

impl VariableAnalyzer {
    /// Create a new VariableAnalyzer and visit the given command.
    pub fn new(cmd: &Command<String>) -> Self {
        let mut v = Self {
            defines: HashMap::new(),
            uses: HashMap::new(),
            conds: Vec::new(),
        };
        v.visit_command(cmd);
        v
    }
}

impl AstVisitor for VariableAnalyzer {
    fn visit_command(&mut self, cmd: &Command<String>) {
        if let Command::Assignment(var, _) = cmd {
            self.defines.insert(var.clone(), self.conds.clone());
        }
        self.walk_command(cmd);
    }

    fn visit_compound(&mut self, compound: &CompoundCommand<TopLevelWord, TopLevelCommand>) {
        match compound {
            CompoundCommand::Macro(m4) => self.visit_m4_macro(m4),
            CompoundCommand::Brace(cmds) | CompoundCommand::Subshell(cmds) => {
                for c in cmds {
                    self.visit_command_wrapper(c);
                }
            }
            CompoundCommand::While(pair) | CompoundCommand::Until(pair) => {
                self.visit_condition(&pair.condition);
                self.conds.push(Guard::Cond(pair.condition.clone()));
                for c in &pair.body {
                    self.visit_command_wrapper(c);
                }
                self.conds.pop();
            }
            CompoundCommand::If {
                conditionals,
                else_branch,
            } => {
                let mut last = None;
                for guard_body in conditionals {
                    self.visit_condition(&guard_body.condition);
                    self.conds.push(Guard::Cond(guard_body.condition.clone()));
                    for c in &guard_body.body {
                        self.visit_command_wrapper(c);
                    }
                    last = self.conds.pop();
                }
                if let Some(prev) = last {
                    self.conds.push(Guard::Not(Box::new(prev)));
                    for c in else_branch {
                        self.visit_command_wrapper(c);
                    }
                    self.conds.pop();
                } else {
                    for c in else_branch {
                        self.visit_command_wrapper(c);
                    }
                }
            }
            CompoundCommand::For { var, words, body } => {
                self.defines.insert(var.clone(), self.conds.clone());
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
                    for pat in &arm.patterns {
                        self.visit_word(pat);
                    }
                    self.conds
                        .push(Guard::Match(word.clone(), arm.patterns.clone()));
                    for c in &arm.body {
                        self.visit_command_wrapper(c);
                    }
                    self.conds.pop();
                }
            }
            CompoundCommand::And(cond, c) | CompoundCommand::Or(cond, c) => {
                self.visit_condition(cond);
                self.conds.push(Guard::Cond(cond.clone()));
                self.visit_command_wrapper(c);
                self.conds.pop();
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
            CompoundCommand::Background(cmd) => {
                self.visit_command_wrapper(cmd);
            }
            CompoundCommand::FunctionDef { body, .. } => {
                self.visit_command_wrapper(body);
            }
        }
    }

    fn visit_word(&mut self, w: &TopLevelWord) {
        self.walk_word(w);
    }

    fn visit_fragment(&mut self, f: &WordFragment<String, TopLevelWord, TopLevelCommand>) {
        match f {
            WordFragment::Param(Parameter::Var(name)) => {
                self.uses.insert(name.clone(), self.conds.clone());
            }
            WordFragment::DoubleQuoted(inner) => {
                for frag in inner {
                    self.visit_fragment(frag);
                }
            }
            WordFragment::Macro(m4) => self.visit_m4_macro(m4),
            WordFragment::Subst(subst) => self.visit_parameter_substitution(subst.as_ref()),
            _ => {}
        }
    }

    fn visit_condition(&mut self, cond: &Condition<TopLevelWord, TopLevelCommand>) {
        self.walk_condition(cond);
    }

    fn visit_arithmetic(&mut self, arith: &Arithmetic<String>) {
        match arith {
            Arithmetic::Var(name)
            | Arithmetic::PostIncr(name)
            | Arithmetic::PostDecr(name)
            | Arithmetic::PreIncr(name)
            | Arithmetic::PreDecr(name) => {
                self.uses.insert(name.clone(), self.conds.clone());
            }
            Arithmetic::UnaryPlus(x)
            | Arithmetic::UnaryMinus(x)
            | Arithmetic::LogicalNot(x)
            | Arithmetic::BitwiseNot(x) => {
                self.visit_arithmetic(x);
            }
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

    fn visit_parameter(&mut self, param: &Parameter<String>) {
        if let Parameter::Var(name) = param {
            self.uses.insert(name.clone(), self.conds.clone());
        }
        self.walk_parameter(param);
    }

    fn visit_parameter_substitution(&mut self, subs: &MinimalParameterSubstitution) {
        match subs {
            ParameterSubstitution::Command(cmds) => {
                for c in cmds {
                    self.visit_command(&c.cmd);
                }
            }
            ParameterSubstitution::Arith(Some(arith)) => {
                self.visit_arithmetic(arith);
            }
            ParameterSubstitution::Len(param) => {
                self.visit_parameter(param);
            }
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

    fn visit_redirect(&mut self, redir: &Redirect<TopLevelWord>) {
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

    fn visit_m4_macro(&mut self, m4: &M4Macro<TopLevelWord, TopLevelCommand>) {
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
        if let Some(effects) = &m4.effects {
            if let Some(shell_vars) = &effects.shell_vars {
                for var in shell_vars {
                    if var.is_used() {
                        self.uses.insert(var.0.clone(), self.conds.clone());
                    }
                    if var.is_defined() {
                        self.defines.insert(var.0.clone(), self.conds.clone());
                    }
                }
            }
        }
    }
}
