use std::{
    cell::{Cell, RefCell},
    collections::HashMap,
};

use crate::analyzer::{
    as_literal, as_shell,
    dictionary::{DictionaryAccess, DictionaryOperation, DictionaryValue},
    guard::{Atom, VarCond, VoL},
    location::Location,
    type_inference::DataType,
    variable::is_eval,
    Analyzer, BlockId, Guard, NodeInfo,
};
use autotools_parser::{
    ast::{
        minimal::Word,
        node::{
            AcCommand, AcWord, Condition, DisplayM4, DisplayNode, GuardBodyPair, M4Macro, Node,
            NodeId, NodePool, PatternBodyPair, WordFragment,
        },
        Arithmetic, MayM4, Parameter, Redirect,
    },
    m4_macro::M4Argument,
};

use itertools::Itertools;

pub(crate) struct TranslatingPrinter<'a> {
    /// Contains all stateful information
    analyzer: &'a Analyzer,
    /// Assigned the id of top-most node while formatting a tree of nodes.
    top_most: Cell<Option<NodeId>>,
    /// Current ID of the node to be displayed.
    node_cursor: Cell<Option<NodeId>>,
    /// Current index of the branch to be displayed.
    branch_cursor: Cell<Option<BlockId>>,
    /// The order in expression to reproduce precise Location.
    order: Cell<usize>,
    /// Nodes that should be translated as dictionary accesses.
    dict_accesses: HashMap<Location, (String, DictionaryAccess, DataType)>,
    /// Fragments that are translated while printing.
    translated_fragments: RefCell<Vec<String>>,
    /// Whether parameters are to be displayed in the style of rust's format string
    in_format_string: Cell<bool>,
    /// When `in_format_string` is set to true, we record appeared variables here.
    formatted_vars: RefCell<Vec<String>>,
    /// Whether we have found a usage of redirection.
    found_redirection: Cell<bool>,
    /// Whether we have found a usage of sed command.
    found_sed: Cell<bool>,
}

impl<'a> std::fmt::Debug for TranslatingPrinter<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Printer")
            .field("forcus", &self.top_most)
            .finish()
    }
}

impl<'a> TranslatingPrinter<'a> {
    /// Construct a new pool of autoconf commands
    pub fn new(analyzer: &'a Analyzer) -> Self {
        let mut dict_accesses = HashMap::new();
        for dict in analyzer.dicts.as_ref().unwrap() {
            for (loc, access) in dict.accesses.iter() {
                dict_accesses.insert(
                    loc.clone(),
                    (dict.name.clone(), access.clone(), dict.value_type.clone()),
                );
            }
        }
        // FIXME: we have to use bunch of `Cell` to mutate the fields because of
        // the trait NodePool defined in autoconf_parser. But we could fix this trait
        // to allow all mutation.
        Self {
            analyzer,
            top_most: Cell::new(None),
            node_cursor: Cell::new(None),
            branch_cursor: Cell::new(None),
            order: Cell::new(0),
            dict_accesses,
            translated_fragments: RefCell::new(Vec::new()),
            in_format_string: Cell::new(false),
            formatted_vars: RefCell::new(Vec::new()),
            found_redirection: Cell::new(false),
            found_sed: Cell::new(false),
        }
    }

    pub fn get_node(&self, node_id: NodeId) -> Option<&Node<AcCommand, NodeInfo>> {
        self.analyzer.get_node(node_id)
    }

    pub fn print_node(&self, node_id: NodeId) -> String {
        self.display_node(node_id, 0)
    }

    pub fn record_translated_fragment(&self, frag: String) {
        self.translated_fragments.borrow_mut().push(frag);
    }

    pub fn collect_translated_fragments(&self) -> Vec<String> {
        self.translated_fragments.borrow().clone()
    }

    fn enclose_by_rust_tags(&self, fragment: String, record: bool) -> String {
        if record {
            self.record_translated_fragment(fragment.clone());
        }
        format!("<rust>{}</rust>", fragment)
    }

    pub fn get_required_rust_funcs(&self) -> Vec<&str> {
        let mut ret = Vec::new();
        if self.found_redirection.get() {
            ret.push("write_file");
        }
        if self.found_sed.get() {
            ret.push("regex");
        }
        ret
    }
}

impl<'a> DisplayNode for TranslatingPrinter<'a> {
    type Word = AcWord;

    fn display_node(&self, node_id: NodeId, indent_level: usize) -> String {
        if let Some(node) = self.get_node(node_id) {
            let is_top = self.top_most.get().is_none();
            if is_top {
                self.top_most.replace(Some(node_id));
            } else {
                if node.info.is_top_node() {
                    // the node beyond boundary should not be displayed.
                    return String::new();
                }
            }
            let saved_node_cursor = self.node_cursor.replace(Some(node_id));
            let saved_branch_cursor = self.branch_cursor.replace(None);
            let saved_order = self.set_order(0);
            use MayM4::*;
            let result = match &node.cmd.0 {
                Macro(m4_macro) => self.display_m4_macro(m4_macro, indent_level),
                Shell(cmd) => self.display_command(cmd, node.comment.clone(), indent_level),
            };
            self.set_order(saved_order);
            self.branch_cursor.replace(saved_branch_cursor);
            self.node_cursor.replace(saved_node_cursor);
            if is_top {
                self.top_most.replace(None);
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
            Concat(frags) => {
                format!(
                    "{}",
                    frags
                        .iter()
                        .map(|w| self.display_may_m4_word(w))
                        .collect::<Vec<String>>()
                        .concat()
                )
            }
            Single(frag) => {
                let s = self.display_may_m4_word(frag);
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

impl<'a> TranslatingPrinter<'a> {
    fn set_order(&self, order: usize) -> usize {
        self.order.replace(order)
    }

    fn increment_order(&self) {
        self.order.replace(self.order.get() + 1);
    }

    fn take_location(&self) -> Location {
        let node_id = self.node_cursor.get().unwrap();
        let node = self.analyzer.get_node(node_id).unwrap();
        let exec_id = node.info.exec_id;
        let line = node.range_start().unwrap();
        let order_in_expr = self.order.get();
        let loc = Location {
            node_id,
            exec_id,
            line,
            order_in_expr,
        };
        self.increment_order();
        loc
    }

    fn display_dictionary_value(&self, val: &DictionaryValue) -> String {
        match val {
            DictionaryValue::Lit(lit) => lit.into(),
            DictionaryValue::Var(name) => format!("${{{}}}", name),
            DictionaryValue::Dict(_, loc) => {
                let (dict_name, access, value_type) = self.dict_accesses.get(loc).unwrap();
                self.display_dictionary_read(dict_name, access, value_type)
            }
        }
    }

    fn display_dictionary_read(
        &self,
        dict_name: &str,
        access: &DictionaryAccess,
        _value_type: &DataType,
    ) -> String {
        if access.operation != DictionaryOperation::Read {
            dbg!(dict_name, access, _value_type);
        }
        debug_assert_eq!(access.operation, DictionaryOperation::Read);
        let keys = access
            .keys
            .iter()
            .map(|key| key.print())
            .collect::<Vec<_>>();
        let num_keys = keys.len();
        let printed_keys = match num_keys {
            1 => keys.first().unwrap().clone(),
            _ => format!("({})", keys.join(", ")),
        };
        let operation = match num_keys {
            1 => format!("{}.get({})", dict_name, printed_keys),
            _ => format!("{}.get(&{})", dict_name, printed_keys),
        };
        operation
    }

    fn display_dictionary_write(
        &self,
        dict_name: &str,
        access: &DictionaryAccess,
        value_type: &DataType,
        value: &str,
    ) -> String {
        debug_assert_eq!(access.operation, DictionaryOperation::Write);
        let keys = access
            .keys
            .iter()
            .map(|key| key.print())
            .collect::<Vec<_>>();
        let num_keys = keys.len();
        let printed_keys = match num_keys {
            1 => keys.first().unwrap().clone(),
            _ => format!("({})", keys.join(", ")),
        };

        self.record_translated_fragment(dict_name.to_owned());
        self.record_translated_fragment(printed_keys.to_owned());
        let operation = match value_type {
            DataType::List(_) => format!("{}.entry({})", dict_name, printed_keys),
            _ => format!("{}.insert({},", dict_name, printed_keys),
        };
        let lhs = self.enclose_by_rust_tags(operation, false);
        let rhs = match value_type {
            DataType::List(_) => {
                let list = format!(
                    "[{}]",
                    value
                        .split_whitespace()
                        .map(|s| format!("\"{s}\".to_string()"))
                        .join(", ")
                );
                self.enclose_by_rust_tags(list, true)
            }
            _ => value.to_owned(),
        };
        format!("{}=\"{}\"", lhs, rhs)
    }

    fn display_cfg_atom(&self, atom: &Atom) -> String {
        use Atom::*;
        debug_assert!(should_atom_replaced(atom));
        match atom {
            Arch(arch) => format!("target_arch = \"{}\"", arch),
            Cpu(_) => todo!(),
            Os(os) => format!("target_os = \"{}\"", os),
            Env(env) => format!("target_env = \"{}\"", env),
            Abi(abi) => format!("target_abi = \"{}\"", abi),
            Arg(name, var_cond) => {
                let name = self
                    .analyzer
                    .build_option_info
                    .arg_var_to_option_name
                    .get(name)
                    .unwrap();
                match var_cond {
                    VarCond::Yes => format!("{}", name),
                    VarCond::No => format!("not({})", name),
                    VarCond::Eq(VoL::Lit(lit)) => format!("{}_{}", name, lit),
                    _ => todo!(),
                }
            }
            _ => {
                unreachable!();
            }
        }
    }

    fn display_cfg_guard(&self, guard: &Guard) -> String {
        match guard {
            Guard::N(negated, atom) => {
                if should_atom_replaced(atom) {
                    let cfg_atom_str = self.display_cfg_atom(atom);
                    let cfg_str = if *negated {
                        format!("cfg!(not({}))", cfg_atom_str)
                    } else {
                        format!("cfg!({})", cfg_atom_str)
                    };
                    self.enclose_by_rust_tags(cfg_str, true)
                } else {
                    self.display_guard(guard)
                }
            }
            Guard::Or(guards) => guards
                .iter()
                .map(|guard| self.display_cfg_guard(guard))
                .join(" || "),
            Guard::And(guards) => guards
                .iter()
                .map(|guard| self.display_cfg_guard(guard))
                .join(" && "),
        }
    }

    fn display_guard(&self, guard: &Guard) -> String {
        match guard.print(&Default::default()) {
            Ok(s) => s,
            Err(required_node_ids) => guard
                .print(
                    &required_node_ids
                        .into_iter()
                        .map(|nid| (nid, self.display_node(nid, 0)))
                        .collect(),
                )
                .unwrap(),
        }
    }

    fn display_word_as_format_string(&self, word: &AcWord) -> String {
        let (format_string, vars) = self.take_format_string_and_vars(word);
        if vars.is_empty() {
            format!("{format_string}.to_string()")
        } else {
            format!(
                "format!(\"{}\", {})",
                format_string,
                vars.into_iter().join(", ")
            )
        }
    }

    fn take_format_string_and_vars(&self, word: &AcWord) -> (String, Vec<String>) {
        self.in_format_string.replace(true);
        let word = self.display_word(word, false);
        let vars = self
            .formatted_vars
            .borrow_mut()
            .drain(..)
            .collect::<Vec<_>>();
        self.in_format_string.replace(false);
        let format_string = Self::escape_rust_string(&word);
        self.record_translated_fragment(format_string.clone());
        (format_string, vars)
    }

    fn escape_rust_string(s: &str) -> String {
        s.chars()
            .map(|c| match c {
                '"' => "\\\"".to_string(),
                '\\' => "\\\\".to_string(),
                '\n' => "\\n".to_string(),
                '\r' => "\\r".to_string(),
                '\t' => "\\t".to_string(),
                '\0' => "\\0".to_string(),
                c if c.is_control() => format!("\\u{{{:04x}}}", c as u32),
                c => c.to_string(),
            })
            .collect()
    }
}

impl<'a> NodePool<AcWord> for TranslatingPrinter<'a> {
    fn display_shell_word(&self, shell_word: &WordFragment<AcWord>) -> String {
        if self.in_format_string.get() {
            if let WordFragment::Param(Parameter::Var(var)) = shell_word {
                self.formatted_vars.borrow_mut().push(var.to_owned());
                return "{}".into();
            }
        }

        match &shell_word {
            WordFragment::Escaped(lit) => match lit.as_str() {
                "`" => lit.into(),
                _ => format!("\\{}", lit),
            },
            _ => self.shell_word_to_string(shell_word),
        }
    }

    fn display_inner_param(&self, param: &Parameter<String>) -> String {
        if matches!(param, Parameter::Var(_)) {
            let loc = self.take_location();
            if let Some((dict_name, access, value_type)) = self.dict_accesses.get(&loc) {
                return self.display_dictionary_read(dict_name, access, value_type);
            }
        }
        self.inner_param_to_string(param)
    }

    fn display_assignment(&self, name: &str, word: &AcWord, indent_level: usize) -> String {
        let tab = " ".repeat(indent_level * Self::TAB_WIDTH);
        let rhs = self.display_word(word, false);
        let loc = self.take_location();
        if let Some((dict_name, access, value_type)) = self.dict_accesses.get(&loc) {
            format!(
                "{tab}{}",
                self.display_dictionary_write(dict_name, access, value_type, &rhs)
            )
        } else {
            format!("{tab}{}=\"{}\"", name, rhs)
        }
    }

    fn display_arithmetic(&self, arith: &Arithmetic<String>) -> String {
        use Arithmetic::*;
        if matches!(
            arith,
            Var(_) | PostIncr(_) | PostDecr(_) | PreIncr(_) | PreDecr(_)
        ) {
            let loc = self.take_location();
            if let Some((dict_name, access, value_type)) = self.dict_accesses.get(&loc) {
                return self.display_dictionary_read(dict_name, access, value_type);
            }
        }
        arith.to_string()
    }

    fn display_case(
        &self,
        word: &AcWord,
        arms: &[PatternBodyPair<AcWord>],
        indent_level: usize,
    ) -> String {
        if arms.is_empty() {
            return String::new();
        }
        let tab = " ".repeat(indent_level * Self::TAB_WIDTH);
        let target = self.display_word(word, false);
        let node_id = self.node_cursor.get().unwrap();
        let block_ids = &self.analyzer.get_node(node_id).unwrap().info.branches;
        let guards = block_ids
            .iter()
            .map(|block_id| self.analyzer.get_block(*block_id).guards.last().unwrap())
            .collect::<Vec<_>>();
        assert_eq!(arms.len(), guards.len());
        let should_replace_with_ifelse = guards.iter().all(|guard| should_guard_replaced(guard));
        if should_replace_with_ifelse {
            assert_eq!(arms.len(), guards.len());
            let mut iter = arms.iter().zip(guards.iter());
            let first_if = {
                let (arm, guard) = iter.next().unwrap();
                format!(
                    "{tab}if {}; then\n{}",
                    self.display_cfg_guard(guard),
                    self.display_body(&arm.body, indent_level + 1)
                )
            };
            let mut else_if = String::new();
            let mut else_branch = None;
            for (arm, guard) in iter {
                if matches!(guard, Guard::N(false, Atom::Arg(_, VarCond::MatchAny))) {
                    else_branch.replace(format!(
                        "{tab}else\n{}",
                        self.display_body(&arm.body, indent_level + 1)
                    ));
                } else {
                    else_if.push_str(&format!(
                        "{tab}else if {}; then\n{}",
                        self.display_cfg_guard(guard),
                        self.display_body(&arm.body, indent_level + 1)
                    ));
                }
            }
            let rest = match else_branch {
                Some(s) => format!("{}{tab}fi", s),
                None => format!("{tab}fi"),
            };
            format!("{}{}{}", first_if, else_if, rest)
        } else {
            let mut arms = arms
                .iter()
                .zip(guards.iter())
                .map(|(arm, guard)| {
                    let pattern = if should_guard_replaced(guard) {
                        self.display_cfg_guard(guard)
                    } else {
                        arm.patterns
                            .iter()
                            .map(|w| self.display_word(w, false))
                            .collect::<Vec<String>>()
                            .join("|")
                    };
                    format!(
                        "{tab}  {})\n{}{tab}    ;;",
                        pattern,
                        self.display_body(&arm.body, indent_level + 2)
                    )
                })
                .collect::<Vec<String>>()
                .join("\n");
            if !arms.is_empty() {
                arms.push('\n');
            }
            format!("{tab}case {} in\n{}{tab}esac", target, arms)
        }
    }

    fn display_condition(&self, cond: &Condition<AcWord>) -> String {
        if let Some(branch_index) = self.branch_cursor.get() {
            let node_id = self.node_cursor.get().unwrap();
            let block_id = &self.analyzer.get_node(node_id).unwrap().info.branches[branch_index];
            match self.analyzer.get_block(*block_id).guards.last() {
                Some(guard) if should_guard_replaced(guard) => {
                    return self.display_cfg_guard(guard);
                }
                _ => (),
            }
        }
        self.condition_to_string(cond)
    }

    fn display_if(
        &self,
        conditionals: &[GuardBodyPair<AcWord>],
        else_branch: &[NodeId],
        indent_level: usize,
    ) -> String {
        let tab = " ".repeat(indent_level * Self::TAB_WIDTH);

        let first_if = {
            let pair = conditionals.first().unwrap();
            self.branch_cursor.set(Some(0));
            format!(
                "{tab}if {}; then\n{}",
                self.display_condition(&pair.condition),
                self.display_body(&pair.body, indent_level + 1)
            )
        };
        let else_if = conditionals
            .iter()
            .enumerate()
            .skip(1)
            .map(|(i, pair)| {
                self.branch_cursor.set(Some(i));
                format!(
                    "{tab}else if {}; then\n{}",
                    self.display_condition(&pair.condition),
                    self.display_body(&pair.body, indent_level + 1)
                )
            })
            .collect::<String>();
        let rest = if else_branch.is_empty() {
            format!("{tab}fi")
        } else {
            self.branch_cursor.set(Some(conditionals.len()));
            format!(
                "{tab}else\n{}{tab}fi",
                self.display_body(else_branch, indent_level + 1)
            )
        };
        self.branch_cursor.set(None);
        format!("{}{}{}", first_if, else_if, rest)
    }

    fn display_for(
        &self,
        var: &str,
        words: &[AcWord],
        body: &[NodeId],
        indent_level: usize,
    ) -> String {
        let tab = " ".repeat(indent_level * Self::TAB_WIDTH);
        let list = words
            .iter()
            .map(|w| self.display_word(w, true))
            .collect::<Vec<String>>()
            .join(" ");
        self.take_location(); // var
        format!(
            "{tab}for {var} in {list}; do\n{}{tab}done",
            self.display_body(body, indent_level + 1)
        )
    }

    fn display_cmd(&self, words: &[AcWord], indent_level: usize) -> String {
        let tab = " ".repeat(indent_level * Self::TAB_WIDTH);
        if let Some(first) = words.get(0) {
            if is_eval(first) {
                // FIXME: for the simplicity, we have two assumptions here.
                // 1. in eval assignments, only one dictionary gets touched, either written or read.
                // 2. the side where the dictionary appears, we won't see any other expressions
                //    such as literals.
                let node_id = self.node_cursor.get().unwrap();
                if let Some((loc, (dict_name, access, value_type))) = self
                    .dict_accesses
                    .iter()
                    .find(|(loc, _)| loc.node_id == node_id)
                {
                    match access.operation {
                        DictionaryOperation::Write => {
                            let rhs = if let Some(vals) = &access.assigned_value {
                                vals.iter()
                                    .map(|v| self.display_dictionary_value(v))
                                    .collect::<String>()
                            } else {
                                String::new()
                            };
                            return self.display_dictionary_write(dict_name, access, value_type, &rhs);
                        }
                        DictionaryOperation::Read => {
                            if access.assigned_to.is_none() {
                                dbg!(&dict_name, &access, &value_type, &loc);
                            }
                            let lhs = access.assigned_to.clone().unwrap();
                            let rhs = self.enclose_by_rust_tags(
                                self.display_dictionary_read(dict_name, access, value_type),
                                true,
                            );
                            return format!("{tab}{}={}", lhs, rhs);
                        }
                    }
                }
            }
            if as_shell(first)
                .and_then(as_literal)
                .is_some_and(|cmd| cmd == "sed")
            {
                self.found_sed.replace(true);
            }
        }
        self.cmd_to_string(words, indent_level)
    }

    fn display_redirect_cmd(
        &self,
        cmd: NodeId,
        redirects: &[Redirect<AcWord>],
        indent_level: usize,
    ) -> String {
        if !redirects.is_empty() {
            self.found_redirection.replace(true);
        }
        let tab = " ".repeat(indent_level * Self::TAB_WIDTH);
        if redirects.len() == 2 {
            match (&redirects[0], &redirects[1]) {
                (Redirect::Write(_, file), Redirect::Heredoc(_, heredoc)) => {
                    if let Word::Single(MayM4::Shell(WordFragment::Literal(filename))) = &file.0 {
                        let rust_string = {
                            let path = format!("Path::new(\"{}\")", filename);
                            self.record_translated_fragment(path.clone());
                            let content = self.display_word_as_format_string(heredoc);
                            self.enclose_by_rust_tags(
                                format!("write_file({}, &{})", path, content),
                                false,
                            )
                        };
                        return format!("{tab}{}", rust_string);
                    }
                }
                _ => (),
            }
        }
        self.redirect_cmd_to_string(cmd, redirects, indent_level)
    }
}

impl<'a> DisplayM4 for TranslatingPrinter<'a> {
    fn display_m4_macro(&self, m4_macro: &M4Macro, indent_level: usize) -> String {
        let tab = " ".repeat(indent_level * Self::M4_TAB_WIDTH);
        if let Some(effects) = &m4_macro.effects {
            if let Some(shell_vars) = &effects.shell_vars {
                for var in shell_vars {
                    if var.is_used() {
                        self.take_location();
                    }
                    if var.is_defined() {
                        self.take_location();
                    }
                }
            }
        }
        match m4_macro.name.as_str() {
            "AC_CACHE_CHECK" => {
                let description = m4_macro.get_arg_as_literal(0).unwrap();
                let body = m4_macro.get_arg_as_cmd(2).unwrap();
                return format!(
                    "{tab}# Check {description}\n{}",
                    self.display_body(&body, indent_level)
                );
            }
            "AC_DEFINE" => {
                let key = match m4_macro.args.get(0).unwrap() {
                    M4Argument::Word(word) => self.display_word(word, false),
                    M4Argument::Literal(lit) => lit.to_owned(),
                    _ => unreachable!(),
                };
                let value = {
                    let value = m4_macro.get_arg_as_literal(1).unwrap_or_default();
                    match value.as_str() {
                        "0" | "1" | "" => {
                            // should be a boolean
                            String::new()
                        }
                        _ => format!("=\"{value}\""),
                    }
                };
                let cargo_instruction = format!("\"cargo::rustc-cfg={}{}\"", key, value);
                self.record_translated_fragment(cargo_instruction.clone());
                let print_line = format!("println!({});", cargo_instruction);
                return format!("{tab}{}", self.enclose_by_rust_tags(print_line, false));
            }
            "AC_DEFINE_UNQUOTED" => {
                let (key_fstr, vars_in_key) = match m4_macro.args.get(0).unwrap() {
                    M4Argument::Word(word) => self.take_format_string_and_vars(word),
                    M4Argument::Literal(lit) => (lit.to_owned(), Vec::new()),
                    _ => unreachable!(),
                };
                let (value_fstr, vars_in_value) = match m4_macro.args.get(1) {
                    Some(M4Argument::Word(word)) => self.take_format_string_and_vars(word),
                    Some(M4Argument::Literal(lit)) => (lit.to_owned(), Vec::new()),
                    None => (Default::default(), Default::default()),
                    _ => unreachable!(),
                };
                let value_fstr = match value_fstr.as_str() {
                    "0" | "1" | "" => {
                        // should be a boolean
                        assert!(vars_in_value.is_empty());
                        String::new()
                    }
                    _ => format!("=\"{value_fstr}\""),
                };
                let cargo_instruction = format!("\"cargo::rustc-cfg={}{}\"", key_fstr, value_fstr);
                self.record_translated_fragment(cargo_instruction.clone());
                let print_line = if vars_in_key.is_empty() && vars_in_value.is_empty() {
                    format!("println!({});", cargo_instruction)
                } else {
                    format!(
                        "println!({}, {});",
                        cargo_instruction,
                        vars_in_key.iter().chain(vars_in_value.iter()).join(", ")
                    )
                };
                return format!("{tab}{}", self.enclose_by_rust_tags(print_line, false));
            }
            _ => (),
        }
        self.m4_macro_to_string(m4_macro, indent_level)
    }
}

fn should_guard_replaced(guard: &Guard) -> bool {
    match guard {
        Guard::N(_, atom) => should_atom_replaced(atom),
        Guard::Or(guards) | Guard::And(guards) => {
            guards.iter().any(|guard| should_guard_replaced(guard))
        }
    }
}

fn should_atom_replaced(atom: &Atom) -> bool {
    use Atom::*;
    match atom {
        Arch(_) | Cpu(_) | Os(_) | Env(_) | Abi(_) | Arg(_, _) => true,
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_escape_rust_string() {
        // Test basic strings
        assert_eq!(TranslatingPrinter::escape_rust_string("hello"), "hello");

        // Test special characters that need escaping
        assert_eq!(
            TranslatingPrinter::escape_rust_string("hello\tworld"),
            "hello\\tworld"
        );
        assert_eq!(
            TranslatingPrinter::escape_rust_string("hello\nworld"),
            "hello\\nworld"
        );
        assert_eq!(
            TranslatingPrinter::escape_rust_string("hello\rworld"),
            "hello\\rworld"
        );
        assert_eq!(
            TranslatingPrinter::escape_rust_string("hello\"world"),
            "hello\\\"world"
        );
        assert_eq!(
            TranslatingPrinter::escape_rust_string("hello\\world"),
            "hello\\\\world"
        );
        assert_eq!(
            TranslatingPrinter::escape_rust_string("hello\0world"),
            "hello\\0world"
        );

        // Test a complex example with multiple special characters
        assert_eq!(
            TranslatingPrinter::escape_rust_string("\thi\n\"test\"\r\\path"),
            "\\thi\\n\\\"test\\\"\\r\\\\path"
        );
    }
}
