use std::collections::{HashMap, HashSet};

use crate::analyzer::{
    as_literal, as_shell, as_var,
    guard::{Atom, VarCond, VoL},
    Guard,
};

use super::{AcWord, Analyzer, AstVisitor, MayM4, Node, NodeId, Parameter, PatternBodyPair, Word};
use autotools_parser::ast::{
    condition::{Condition, Operator},
    minimal::WordFragment,
    Redirect,
};

#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum DataType {
    /// doc
    Boolean,
    /// doc
    Integer,
    /// doc
    List(Box<Self>),
    /// doc
    Path,
    /// doc
    Optional(Box<Self>),
    /// doc
    Literal,
    /// doc
    Either(Box<Self>, Vec<String>),
}

impl DataType {
    pub(crate) fn print(&self) -> String {
        use DataType::*;
        match self {
            Boolean => "bool".into(),
            Integer => "usize".into(),
            List(data_type) => format!("Vec<{}>", data_type.print()),
            Path => "PathBuf".into(),
            Optional(data_type) => format!("Option<{}>", data_type.print()),
            Literal => "String".into(),
            Either(_, _) => "String".into(),
        }
    }

    pub(crate) fn priority(&self) -> usize {
        use DataType::*;
        match self {
            Either(_, _) => 0,
            Literal => 1,
            Boolean => 2,
            Integer => 3,
            Path => 4,
            Optional(_) => 5,
            List(_) => 6,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TypeHint {
    /// the var can be assigned number string
    CanBeNum,
    /// the var can be assigned empty string
    CanBeEmpty,
    /// literals with whitespaces can be assigned to the var
    CanContainWhitespace,
    /// 'yes', 'no', '0', or '1' can be assigned,
    /// or checked its match in case statements or `test` commands
    CanBeBoolLike,
    /// the var can apper at the second argument of for statements
    AssignedInFor,
    /// the var can apper both lhs & rhs in an assignment
    AppendedSelf,
    /// the var can be appended non-numeric & non-boolean literals
    AppendedLiteral,
    /// reading the var happens before definition
    ReadBeforeWrite,
    /// the var appears at the second argument of for statements
    /// also it contains the iterated child variable
    UsedInFor(String),
    /// contents of variable is evaluated as a complete command, or as a command name
    UsedAsCommand,
    /// used in `rm` or `cat` commands.
    /// or, appear in redirection
    UsedAsPath,
    /// used in expr command
    UsedAsExpr,
}

use TypeHint::*;

/// Visitor to find case statements matching given variables.
#[derive(Debug)]
pub(super) struct TypeInferrer<'a> {
    analyzer: &'a Analyzer,
    /// Map of variable types inferred to be types other than string type.
    types: HashMap<String, DataType>,
    type_hints: HashMap<String, HashSet<TypeHint>>,
    type_relations: HashMap<String, String>,
    assigned: HashMap<String, HashSet<String>>,
    cursor: Option<NodeId>,
}

impl Analyzer {
    pub(crate) fn get_type_inference_result(
        &self,
        var_name: &str,
    ) -> Option<&(HashSet<TypeHint>, DataType)> {
        self.inferred_types
            .as_ref()
            .map(|types| types.get(var_name))
            .flatten()
    }

    /// run type inference
    pub(crate) fn run_type_inference(&mut self) {
        self.inferred_types
            .replace(TypeInferrer::run_type_inference(self));
        self.convert_guards_for_numeric_boolean();
    }

    pub(crate) fn get_inferred_type(&self, name: &str) -> DataType {
        if self.options.type_inference {
            if let Some(inferred) = self
                .get_type_inference_result(name)
                .map(|(_, data_type)| data_type.clone())
            {
                inferred
            } else if let Some(known) = has_known_type(name) {
                known
            } else {
                DataType::Literal
            }
        } else {
            DataType::Literal
        }
    }

    fn convert_guards_for_numeric_boolean(&mut self) {
        let bool_vars = self
            .inferred_types
            .as_ref()
            .unwrap()
            .iter()
            .filter(|(_, (_, ty))| ty == &DataType::Boolean)
            .map(|(var_name, _)| var_name.as_str())
            .collect::<HashSet<_>>();
        for (_, block) in self.blocks.iter_mut() {
            block.guards = block
                .guards
                .iter()
                .map(|guard| convert_guard_numeric_boolean(guard, &bool_vars))
                .collect();
        }
    }
}

impl<'a> TypeInferrer<'a> {
    /// run type inference
    pub fn run_type_inference(
        analyzer: &'a Analyzer,
    ) -> HashMap<String, (HashSet<TypeHint>, DataType)> {
        // we assume variable enumeration is already completed.
        let mut s = Self {
            analyzer,
            types: HashMap::new(),
            type_hints: HashMap::new(),
            type_relations: HashMap::new(),
            assigned: HashMap::new(),
            cursor: None,
        };
        for id in analyzer.get_top_ids() {
            s.visit_top(id);
        }

        for name in s.type_hints.clone().keys() {
            s.infer_type(name);
        }

        for (from, to) in s.type_relations.clone() {
            if s.types
                .get(&to)
                .is_none_or(|data_type| *data_type == DataType::Literal)
            {
                if let Some(from_type) = s.types.get(&from).cloned() {
                    s.types.insert(to.to_owned(), from_type);
                }
            }
        }

        let mut ret = HashMap::new();
        for name in s.types.keys() {
            ret.insert(
                name.to_owned(),
                (
                    s.type_hints.get(name).cloned().unwrap_or_default(),
                    s.types[name].clone(),
                ),
            );
        }
        ret
    }

    fn infer_type(&mut self, name: &str) -> DataType {
        if let Some(ty) = has_known_type(name) {
            return ty;
        }
        use DataType::*;
        if let Some(t) = self.types.get(name) {
            return t.clone();
        }
        let mut inferred = Literal;

        let hints = self.type_hints[name].clone();

        if hints.contains(&CanContainWhitespace) {
            inferred = List(Box::new(Literal));
        }
        if hints.contains(&CanBeNum) {
            if let Some(set) = self.assigned.get(name) {
                inferred = Either(Box::new(Integer), Vec::from_iter(set.iter().cloned()))
            } else {
                inferred = Integer;
            }
        }
        if hints.contains(&CanBeBoolLike) {
            if let Some(set) = self.assigned.get(name) {
                inferred = Either(Box::new(Boolean), Vec::from_iter(set.iter().cloned()))
            } else if !name.to_lowercase().contains("version") {
                inferred = Boolean
            }
        }
        if hints.contains(&AppendedSelf) {
            inferred = List(Box::new(Literal));
        }
        for hint in hints.iter() {
            if let UsedInFor(child) = hint {
                if hints.contains(&AppendedLiteral) {
                    self.types.insert(child.to_owned(), Literal);
                }
                inferred = List(Box::new(self.infer_type(child)));
            }
        }
        if hints.contains(&UsedAsCommand) {
            if hints.contains(&CanContainWhitespace) {
                inferred = List(Box::new(Literal));
            } else {
                inferred = Literal;
            }
        }
        if hints.contains(&UsedAsPath) {
            inferred = Path;
        }
        if hints.contains(&UsedAsExpr) {
            inferred = Integer;
        }
        // if hints.contains(&CanBeEmpty) {
        //     if !matches!(inferred, List(_)) {
        //         inferred = Optional(Box::new(inferred))
        //     }
        // }
        self.types.insert(name.to_owned(), inferred.clone());
        inferred
    }

    fn add_type_hint(&mut self, name: &str, hint: TypeHint) {
        self.type_hints
            .entry(name.to_owned())
            .or_default()
            .insert(hint);
    }

    fn check_literal(&mut self, var: &str, lit: &str) {
        let mut found_hint = false;
        if is_boolean(lit) {
            self.add_type_hint(var, CanBeBoolLike);
            found_hint = true;
        }
        if lit.is_empty() {
            self.add_type_hint(var, CanBeEmpty);
            found_hint = true;
        }
        if is_numeric(lit) {
            self.add_type_hint(var, CanBeNum);
            found_hint = true;
        }
        if lit.chars().any(|c| c.is_whitespace()) {
            self.add_type_hint(var, CanContainWhitespace);
            found_hint = true;
        }
        if !found_hint {
            self.assigned
                .entry(var.to_owned())
                .or_default()
                .insert(lit.to_owned());
        }
    }

    fn propagate_type(&mut self, from: &str, to: &str) {
        if from != to {
            self.type_relations.insert(from.to_owned(), to.to_owned());
        }
    }
}

impl<'a> AstVisitor for TypeInferrer<'a> {
    fn get_node(&self, node_id: NodeId) -> Option<&Node> {
        self.analyzer.get_node(node_id)
    }

    fn visit_top(&mut self, node_id: NodeId) {
        self.cursor.replace(node_id);
        self.walk_node(node_id);
    }

    fn visit_node(&mut self, node_id: NodeId) {
        if self.get_node(node_id).is_some() {
            let saved_cursor = self.cursor.replace(node_id);

            if self
                .get_node(node_id)
                .is_some_and(|n| !n.info.is_top_node())
            {
                self.walk_node(node_id);
            }

            self.cursor = saved_cursor;
        }
    }

    fn visit_for(&mut self, var: &str, words: &[AcWord], body: &[NodeId]) {
        if words.len() == 1 {
            for w in words {
                if let Word::Single(MayM4::Shell(WordFragment::Param(Parameter::Var(name)))) = &w.0
                {
                    self.add_type_hint(name, UsedInFor(var.to_owned()));
                }
            }
        }

        self.add_type_hint(var, AssignedInFor);
        self.walk_for(var, words, body);
    }

    fn visit_case(&mut self, word: &AcWord, arms: &[PatternBodyPair<AcWord>]) {
        if let Some(var) = as_shell(word).and_then(as_var) {
            for arm in arms {
                for pattern in &arm.patterns {
                    if let Some(lit) = as_shell(pattern).and_then(as_literal) {
                        self.check_literal(var, lit);
                    }
                    if let Some(pat_var) = as_shell(pattern).and_then(as_var) {
                        self.propagate_type(pat_var, var);
                    }
                }
            }
        }
        self.walk_case(word, arms);
    }

    fn visit_command(&mut self, cmd_words: &[AcWord]) {
        if let Some(exec) = cmd_words.first().and_then(as_shell) {
            if let Some(name) = as_var(exec) {
                self.add_type_hint(name, UsedAsCommand);
            }
            if let Some(lit) = as_literal(exec) {
                if matches!(lit, "rm" | "cat") {
                    for arg in &cmd_words[1..] {
                        if let Some(name) = as_shell(arg).and_then(as_var) {
                            self.add_type_hint(name, UsedAsPath);
                        }
                    }
                }
                if matches!(lit, "expr") {
                    for arg in &cmd_words[1..] {
                        if let Some(name) = as_shell(arg).and_then(as_var) {
                            self.add_type_hint(name, UsedAsExpr);
                        }
                    }
                }
            }
        }
        self.walk_command(cmd_words);
    }

    fn visit_condition(&mut self, cond: &Condition<NodeId, AcWord>) {
        use Operator::*;
        if let Condition::Cond(op) = cond {
            match op {
                Eq(lhs, rhs) | Neq(lhs, rhs) => {
                    if let Some(lit) = as_shell(rhs).and_then(as_literal) {
                        if let Some(var) = as_shell(lhs).and_then(as_var) {
                            self.check_literal(var, lit);
                        }
                    }
                    if let Some(lit) = as_shell(lhs).and_then(as_literal) {
                        if let Some(var) = as_shell(rhs).and_then(as_var) {
                            self.check_literal(var, lit);
                        }
                    }
                }
                Ge(lhs, rhs) | Gt(lhs, rhs) | Le(lhs, rhs) | Lt(lhs, rhs) => {
                    if let Some(var) = as_shell(lhs).and_then(as_var) {
                        self.add_type_hint(var, CanBeNum);
                    }
                    if let Some(var) = as_shell(rhs).and_then(as_var) {
                        self.add_type_hint(var, CanBeNum);
                    }
                }
                Empty(w) | NonEmpty(w) => {
                    if let Some(var) = as_shell(w).and_then(as_var) {
                        self.add_type_hint(var, CanBeEmpty);
                    }
                }
                Dir(w) | File(w) | NoExists(w) => {
                    if let Some(var) = as_shell(w).and_then(as_var) {
                        self.add_type_hint(var, UsedAsPath);
                    }
                }
            }
        }
        self.walk_condition(cond);
    }

    fn visit_assignment(&mut self, name: &str, word: &AcWord) {
        if let Word::Single(MayM4::Shell(word)) = &word.0 {
            match word {
                WordFragment::DoubleQuoted(words)
                    if words
                        .iter()
                        .any(|w| as_var(w).is_some_and(|var| name == var)) =>
                {
                    self.add_type_hint(name, AppendedSelf);
                    if words.iter().any(|w| {
                        as_literal(w).is_some_and(|lit| !is_boolean(lit) && !is_numeric(lit))
                    }) {
                        self.add_type_hint(name, AppendedLiteral);
                    }
                }
                WordFragment::Literal(lit) => self.check_literal(name, lit),
                WordFragment::Param(Parameter::Var(var)) => {
                    self.propagate_type(var, name);
                }
                _ => (),
            }
        }
        self.walk_assignment(name, word);
    }

    fn visit_redirect(&mut self, cmd: NodeId, redirects: &[Redirect<AcWord>]) {
        use Redirect::*;
        for redirect in redirects {
            match redirect {
                Read(_, w)
                | Write(_, w)
                | ReadWrite(_, w)
                | Append(_, w)
                | Clobber(_, w)
                | Heredoc(_, w)
                | DupRead(_, w)
                | DupWrite(_, w) => {
                    if let Some(var) = as_shell(w).and_then(as_var) {
                        self.add_type_hint(var, UsedAsPath);
                    }
                }
            }
        }
        self.walk_redirect(cmd, redirects);
    }

    fn visit_parameter(&mut self, param: &Parameter<String>) {
        if let Parameter::Var(name) = param {
            if self
                .analyzer
                .get_last_definition(name, self.cursor.unwrap())
                .is_none()
            {
                self.add_type_hint(name, ReadBeforeWrite);
            }
        }
    }
}

pub(crate) fn is_boolean(lit: &str) -> bool {
    matches!(lit, "yes" | "no" | "0" | "1")
}

pub(crate) fn is_numeric(lit: &str) -> bool {
    lit.chars().all(|c| c.is_numeric())
}

fn convert_guard_numeric_boolean(guard: &Guard, bool_vars: &HashSet<&str>) -> Guard {
    match guard {
        Guard::N(negated, atom) => match atom {
            Atom::Var(name, VarCond::Eq(VoL::Lit(lit)))
                if bool_vars.contains(name.as_str()) && is_numeric(lit) =>
            {
                Guard::N(
                    false,
                    Atom::Var(
                        name.clone(),
                        if (lit == "0") ^ negated {
                            VarCond::False
                        } else {
                            VarCond::True
                        },
                    ),
                )
            }
            _ => guard.clone(),
        },
        Guard::And(v) => Guard::And(
            v.iter()
                .map(|g| convert_guard_numeric_boolean(g, bool_vars))
                .collect(),
        ),
        Guard::Or(v) => Guard::Or(
            v.iter()
                .map(|g| convert_guard_numeric_boolean(g, bool_vars))
                .collect(),
        ),
    }
}

lazy_static::lazy_static! {
    /// Predefined m4/autoconf macros
    static ref KNOWN_TYPES: HashMap<&'static str, DataType> = known_types();
}

fn known_types() -> HashMap<&'static str, DataType> {
    HashMap::from([
        ("LIBS", DataType::List(Box::new(DataType::Literal))),
        ("LDFLAGS", DataType::List(Box::new(DataType::Literal))),
        ("CPPFLAGS", DataType::List(Box::new(DataType::Literal))),
        ("CFLAGS", DataType::List(Box::new(DataType::Literal))),
        ("enable_shared", DataType::Boolean),
        ("prefix", DataType::Path),
        ("exec_prefix", DataType::Path),
        ("srcdir", DataType::Path),
        ("bindir", DataType::Path),
        ("sbindir", DataType::Path),
        ("libexecdir", DataType::Path),
        ("datarootdir", DataType::Path),
        ("datadir", DataType::Path),
        ("sysconfdir", DataType::Path),
        ("sharedstatdir", DataType::Path),
        ("localstatedir", DataType::Path),
        ("localstatedir", DataType::Path),
        ("runstatedir", DataType::Path),
        ("includedir", DataType::Path),
        ("oldincludedir", DataType::Path),
        ("docdir", DataType::Path),
        ("infodir", DataType::Path),
        ("htmldir", DataType::Path),
        ("dvidir", DataType::Path),
        ("pdfdir", DataType::Path),
        ("psdir", DataType::Path),
        ("libdir", DataType::Path),
        ("localedir", DataType::Path),
        ("mandir", DataType::Path),
        ("cross_compiling", DataType::Boolean),
        ("top_srcdir", DataType::Path),
        ("abs_top_srcdir", DataType::Path),
        ("EXEEXT", DataType::Literal),
    ])
}

fn has_known_type(name: &str) -> Option<DataType> {
    KNOWN_TYPES.get(name).cloned()
}
