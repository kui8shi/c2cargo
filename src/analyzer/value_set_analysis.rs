//! Structs & Methods for Value Set Analysis
use crate::utils::enumerate::enumerate_combinations;

use super::{
    guard::cmp_guards,
    location::Location,
    variable::{Identifier, ValueExpr},
    AcWord, Analyzer, MayM4, Parameter, ParameterSubstitution, ShellCommand, Word, WordFragment,
};
use autotools_parser::ast::node::{AcWordFragment, NodePool};
use bincode::{Decode, Encode};
use std::{
    cmp::Ordering,
    collections::{BTreeMap, HashMap, HashSet},
    hash::{DefaultHasher, Hash, Hasher},
};
use std::{io::Write, path::PathBuf};

/// Saving the result of backward traversal
#[derive(Debug, PartialEq, Eq)]
struct Chain {
    // lit or var
    identifier: Identifier,
    // location
    loc: Location,
    /// Set of resolved values (as literals).
    resolved: HashSet<String>,
    /// Set of unresolved values: var, or ref
    /// if Option<_> is None, it means the value is not resolvable.
    unresolved: HashSet<ValueExpr>,
}

impl Chain {
    /// Creates a new chaining struct
    pub fn new(identifier: Identifier, loc: Location) -> Self {
        Self {
            identifier,
            loc,
            resolved: HashSet::new(),
            unresolved: HashSet::new(),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Default, Clone, Encode, Decode)]
pub(crate) struct DividedVariable {
    /// a map from eval location to division info
    pub eval_locs: HashMap<Location, IdentifierDivision>,
    /// set of updated location
    pub def_locs: HashSet<Location>,
    /// set of used location
    pub use_locs: HashSet<Location>,
}

/// Saving information how an identifier is divided via eval statements.
#[derive(Debug, PartialEq, Eq, Clone, Encode, Decode)]
pub(crate) struct IdentifierDivision {
    /// components of the divided identifier
    pub division: Identifier,
    /// vector of variable to value mappings
    pub mapping: Vec<(String, String)>,
}

#[derive(Debug, Default, Encode, Decode)]
pub(crate) struct VSACache {
    resolved_identifiers: HashMap<Identifier, BTreeMap<Location, HashSet<String>>>,
    resolved_value_expresssions: HashMap<ValueExpr, HashSet<String>>,
    recorded_divided_vars: HashMap<String, DividedVariable>,
}

impl Analyzer {
    pub(crate) fn eval_assigns(&self) -> &HashMap<Identifier, Vec<(Option<ValueExpr>, Location)>> {
        self.eval_assigns.as_ref().unwrap()
    }

    pub(crate) fn divided_vars(&self) -> &HashMap<String, DividedVariable> {
        self.divided_vars.as_ref().unwrap()
    }

    /// run value set analysis to obtain value candidates of variables appeared in eval statements.
    pub(crate) fn run_value_set_analysis(&mut self) {
        self.deserialize_vsa_cache();
        self.divided_vars.replace(Default::default());
        self.var_indirect_usages.replace(Default::default());

        // we assume variable enumeration is already completed.
        let mut evals = self
            .eval_assigns()
            .iter()
            .flat_map(|(ident, assigns)| assigns.iter().zip(std::iter::repeat(ident)))
            .map(|((value, loc), ident)| (ident.clone(), value.clone(), loc.clone()))
            .collect::<Vec<_>>();
        evals.sort_by_key(|(_, _, loc)| loc.clone());
        for (ident, value, loc) in evals.iter() {
            self.resolve_eval(ident, value, loc);
        }
        self.divided_vars
            .replace(self.vsa_cache.borrow().recorded_divided_vars.clone());
        // Add def use chains caused by dynamic identifier
        let mut def_use_edges = Vec::new();
        let mut new_locs = Vec::new();
        for (name, divided) in self.divided_vars().iter() {
            if let Some(def_locs) = self.get_definition(name) {
                for def_loc in def_locs {
                    for eval_loc in divided.eval_locs.keys() {
                        def_use_edges.push((def_loc.node_id, eval_loc.node_id, name.to_owned()));
                        new_locs.push((name.to_owned(), eval_loc.clone()));
                    }
                }
            }
        }
        for (name, ref_loc) in new_locs {
            let locs = self
                .var_indirect_usages
                .as_mut()
                .unwrap()
                .entry(name)
                .or_default();
            if !locs.contains(&ref_loc) {
                locs.push(ref_loc);
            }
        }
        self.apply_def_use_edges(def_use_edges);
        self.serialize_vsa_cache();
    }

    /// collect literals of a var
    pub(crate) fn resolve_var(
        &self,
        name: &str,
        loc: Option<Location>,
        is_cache_enabled: bool,
    ) -> HashSet<String> {
        let loc = match loc {
            Some(loc) => loc,
            None => self.get_location_of_node_end(*self.top_ids.last().unwrap()),
        };
        let v = ValueExpr::Var(name.to_owned(), loc.clone());
        if is_cache_enabled {
            if let Some(cached) = self.get_cached_resolved_values(&v, &loc) {
                return cached;
            }
        }
        self.resolve_value_expression(&v, &loc, is_cache_enabled)
    }

    fn record_identifier_division(
        &self,
        identifier: Identifier,
        resolved: Vec<String>,
        eval_loc: Location,
    ) {
        let name = resolved.concat();
        if self.has_definition_before(name.as_str(), &eval_loc) || self.has_usage(name.as_str()) {
            let mut mapping = Vec::new();
            for (k, v) in identifier
                .positional_vars()
                .into_iter()
                .zip(resolved.into_iter())
            {
                if let Some(var) = k {
                    mapping.push((var, v));
                }
            }
            let (def_locs, use_locs) = {
                let all_def_locs = self.get_all_definition(&name, None);
                let mut before_eval = Vec::new();
                let mut after_eval = Vec::new();
                for loc in all_def_locs {
                    if loc < eval_loc {
                        before_eval.push(loc);
                    } else {
                        after_eval.push(loc);
                    }
                }
                let use_locs = self
                    .get_all_usages(&name, false)
                    .into_iter()
                    .filter(|loc| {
                        !self
                            .get_dominant_definition(&name, loc.node_id)
                            .is_some_and(|dom| {
                                after_eval.contains(&dom)
                                    || after_eval.iter().any(|def_loc| {
                                        self.as_propagated_definition(&name, def_loc)
                                            .is_some_and(|prop_def_loc| prop_def_loc == dom)
                                    })
                            })
                    })
                    .collect::<Vec<_>>();
                (before_eval, use_locs)
            };
            let mut cache_guard = self.vsa_cache.borrow_mut();
            let div = cache_guard
                .recorded_divided_vars
                .entry(name.clone())
                .or_default();
            div.eval_locs.insert(
                eval_loc.clone(),
                IdentifierDivision {
                    division: identifier,
                    mapping,
                },
            );
            div.def_locs.extend(def_locs);
            div.use_locs.extend(use_locs);
        }
    }

    fn cache_resolved_values(&self, val_expr: ValueExpr, loc: Location, values: HashSet<String>) {
        if let Some(identifier) = (&val_expr).into() {
            self.vsa_cache
                .borrow_mut()
                .resolved_identifiers
                .entry(identifier)
                .or_default()
                .entry(loc)
                .or_default()
                .extend(values);
        } else if !matches!(val_expr, ValueExpr::Lit(_)) {
            self.vsa_cache
                .borrow_mut()
                .resolved_value_expresssions
                .entry(val_expr)
                .or_default()
                .extend(values);
        }
    }

    fn get_cached_resolved_values(
        &self,
        val_expr: &ValueExpr,
        loc: &Location,
    ) -> Option<HashSet<String>> {
        if let Some(identifier) = val_expr.into() {
            self.vsa_cache
                .borrow()
                .resolved_identifiers
                .get(&identifier)
                .and_then(|m| m.range(..=loc).next().map(|(_, s)| s.clone()))
        } else {
            self.vsa_cache
                .borrow()
                .resolved_value_expresssions
                .get(val_expr)
                .cloned()
        }
    }

    /// construct chain of value flows in backward order and resolve them.
    fn resolve_eval(&mut self, lhs: &Identifier, rhs: &Option<ValueExpr>, loc: &Location) {
        if let Some(rhs) = rhs {
            let rhs = self.resolve_value_expression(rhs, loc, true);
            for var_name in self.resolve_identifier(lhs, loc) {
                if !var_name.is_empty() {
                    self.cache_resolved_values(
                        ValueExpr::Var(var_name, loc.clone()),
                        loc.clone(),
                        rhs.clone(),
                    );
                }
            }
            let value_expr = convert_identifier_to_value_expression(lhs.clone(), loc.clone());
            self.cache_resolved_values(value_expr, loc.clone(), rhs.clone());
        } else {
            // rhs is empty
        }
    }

    fn resolve_identifier(&mut self, identifier: &Identifier, loc: &Location) -> HashSet<String> {
        let mut result = HashSet::new();
        match identifier {
            Identifier::Name(lit) => {
                result.insert(lit.to_owned());
            }
            Identifier::Indirect(name) => {
                if let Some(chain) = self.construct_chain(name, loc, true) {
                    result.extend(self.resolve_chain(chain, true))
                }
            }
            ident @ Identifier::Concat(values) => {
                let resolved = values
                    .iter()
                    .map(|l| self.resolve_identifier(l, loc))
                    .collect::<Vec<_>>();
                // enumerate combinations
                let combos = enumerate_combinations(resolved);
                for combo in combos.iter() {
                    self.record_identifier_division(ident.clone(), combo.clone(), loc.clone());
                }
                for name in combos.into_iter().map(|words| words.concat()) {
                    result.insert(name);
                }
            }
        }
        result
    }

    pub(crate) fn resolve_value_expression(
        &self,
        value: &ValueExpr,
        loc: &Location,
        is_cache_enabled: bool,
    ) -> HashSet<String> {
        let mut result = HashSet::new();
        if is_cache_enabled {
            if let Some(resolved) = self.get_cached_resolved_values(value, loc) {
                return resolved;
            }
        }
        match value {
            ValueExpr::Lit(lit) => {
                result.extend(
                    lit.split_whitespace()
                        .filter_map(|s| (!s.is_empty()).then_some(s.to_owned())),
                );
            }
            ValueExpr::Var(name, loc) => {
                if let Some(chain) = self.construct_chain(name, loc, is_cache_enabled) {
                    let chain_result = self.resolve_chain(chain, is_cache_enabled);
                    result.extend(chain_result);
                } else {
                    // No chain found for variable
                }
            }
            ValueExpr::Concat(values) => {
                let resolved = values
                    .iter()
                    .map(|r| self.resolve_value_expression(r, loc, is_cache_enabled))
                    .collect::<Vec<_>>();
                let combos = enumerate_combinations(resolved);
                // enumerate combinations
                result.extend(combos.into_iter().map(|words| words.concat()));
            }

            v @ ValueExpr::DynName(values) => {
                let resolved = values
                    .iter()
                    .map(|r| self.resolve_value_expression(r, loc, is_cache_enabled))
                    .collect::<Vec<_>>();
                let ident = Into::<Option<Identifier>>::into(v).unwrap();
                // enumerate combinations
                let combos = enumerate_combinations(resolved);
                for combo in combos.iter() {
                    self.record_identifier_division(ident.clone(), combo.clone(), loc.clone());
                }
                for name in combos.into_iter().map(|words| words.concat()) {
                    if let Some(chain) = self.construct_chain(&name, loc, is_cache_enabled) {
                        let chain_result = self.resolve_chain(chain, is_cache_enabled);
                        result.extend(chain_result);
                    }
                }
            }
            ValueExpr::Shell(shell_string, vars) => {
                let resolved = vars
                    .iter()
                    .map(|r| self.resolve_value_expression(r, loc, is_cache_enabled))
                    .collect();
                // enumerate combinations & additoinal resolving with shell execution
                // cf. RValue::concretize
                let mut var_names = vars
                    .iter()
                    .flat_map(|r| r.vars().into_iter().map(|v| v.first().unwrap().clone()));
                let combos = enumerate_combinations(resolved);
                if combos.first().is_some_and(|combo| combo.len() == 1)
                    // FIXME: inprecise conditions on shell_string
                    && shell_string.starts_with("sed")
                    && !shell_string.contains("|")
                {
                    // in this setup, we can optimize the repetition of shell execution by
                    // do the loop **inside** the shell environment.
                    let var_name = var_names.next().unwrap();
                    let vals = combos
                        .into_iter()
                        .flat_map(|combo| combo.into_iter())
                        .collect::<Vec<_>>();
                    let mut tmp =
                        tempfile::NamedTempFile::new().expect("Unable to create a temporary file");
                    write!(tmp, "{}", vals.join("\n")).unwrap();
                    let vals_path = tmp.path().to_str().unwrap();
                    let var = &format!("\"${{{}}}\"", var_name);
                    // TODO: refine this so that we can execute xargs commands more stably.
                    let shell_string = shell_string.replace(var, "{}");
                    let xargs_script = format!(
                        "cat {} | xargs -I{{}} -P `nproc` sh -c \"{}\"",
                        &vals_path, &shell_string
                    );

                    let output = std::process::Command::new("sh")
                        .arg("-c")
                        .arg(xargs_script.clone())
                        .output()
                        .unwrap_or_else(|_| panic!("Executing: {} has failed", xargs_script));
                    let stdout_string = String::from_utf8(output.stdout)
                        .expect("Unable to convert utf-8 to String.");
                    if !stdout_string.is_empty() {
                        result.extend(stdout_string.split_whitespace().map(|s| s.to_owned()));
                    }
                } else {
                    for combo in combos {
                        let env_pairs: Vec<_> = var_names.clone().zip(combo.clone()).collect();
                        let output = std::process::Command::new("sh")
                            .arg("-c")
                            .arg(shell_string.clone())
                            .envs(env_pairs)
                            .output()
                            .unwrap_or_else(|_| panic!("Executing: {} has failed", shell_string));
                        let stdout_string = String::from_utf8(output.stdout)
                            .expect("Unable to convert utf-8 to String.");
                        if !stdout_string.is_empty() {
                            result.extend(stdout_string.split_whitespace().map(|s| s.to_owned()));
                        }
                    }
                }
            }
        }
        if is_cache_enabled {
            self.cache_resolved_values(value.clone(), loc.clone(), result.clone());
        }
        result
    }

    fn resolve_chain(&self, chain: Chain, is_cache_enabled: bool) -> HashSet<String> {
        // resolve chain
        // 1. if unresolved is not empty, recursively call resolve_value_expression on them
        // 2. else, return resolved
        if !chain.unresolved.is_empty() {
            chain
                .resolved
                .into_iter()
                .chain(chain.unresolved.into_iter().flat_map(|value| {
                    self.resolve_value_expression(&value, &chain.loc, is_cache_enabled)
                }))
                .collect()
        } else {
            chain.resolved
        }
    }

    /// Given a variable, traverse the script backward to construct chain of values
    fn construct_chain(&self, name: &str, loc: &Location, is_cache_enabled: bool) -> Option<Chain> {
        let as_ident = Identifier::Name(name.to_owned());
        let as_expr = ValueExpr::Var(name.to_owned(), loc.clone());

        let mut chain = Chain::new(as_ident.clone(), loc.clone());
        if is_cache_enabled {
            if let Some(resolved) = self.get_cached_resolved_values(&as_expr, loc) {
                chain.resolved.extend(resolved.clone());
                return Some(chain);
            }
        }
        if self.fixed.contains_key(name) {
            chain.resolved.insert(self.fixed[name].to_owned());
            return Some(chain);
        }
        let mut chain_value = |value| match value {
            ValueExpr::Lit(lit) => {
                if lit.is_empty() {
                    chain.resolved.insert(lit);
                } else {
                    chain.resolved.extend(
                        lit.split_whitespace()
                            .filter_map(|s| (!s.is_empty()).then_some(s.to_owned())),
                    );
                }
            }
            ValueExpr::Var(var, loc) => {
                if var != name {
                    let v = ValueExpr::Var(var.clone(), loc.clone());
                    if let Some(resolved) = self.get_cached_resolved_values(&v, &loc) {
                        chain.resolved.extend(resolved);
                    } else {
                        chain.unresolved.insert(v);
                    }
                }
            }
            r => {
                chain.unresolved.insert(r);
            }
        };
        let def_locs = {
            let mut locs = self.get_all_definition(name, Some(loc));
            if !locs.is_empty() {
                locs.sort();
                locs.reverse();
                locs
            } else {
                return None;
            }
        };
        for def_loc in def_locs {
            let nid = def_loc.node_id;
            let cmd = &self.get_node(nid).unwrap().cmd.0;
            match cmd.clone() {
                MayM4::Shell(ShellCommand::Assignment(lhs, rhs)) if lhs == name => {
                    let ifs = self.current_internal_field_separator(&def_loc);
                    let vals = self.vsa_inspect_word(&rhs, def_loc.order_reset(), ifs);
                    let is_rhs_concrete =
                        vals.is_empty() || vals.iter().all(|v| matches!(v, ValueExpr::Lit(_)));
                    let found_dominant_initialization = is_rhs_concrete
                        && matches!(
                            cmp_guards(
                                &self.get_guards(def_loc.node_id),
                                &self.get_guards(loc.node_id)
                            ),
                            Some(Ordering::Less | Ordering::Equal)
                        );
                    for val in vals {
                        chain_value(val);
                    }
                    if found_dominant_initialization {
                        // Found the dominant initialization of the variable. Stop searching.
                        break;
                    }
                }
                MayM4::Shell(ShellCommand::For {
                    var,
                    words,
                    body: _,
                }) if var == name => {
                    let ifs = self.current_internal_field_separator(&def_loc);
                    for word in words {
                        let vals = self.vsa_inspect_word(&word, def_loc.order_reset(), ifs);
                        for val in vals {
                            match val {
                                ValueExpr::Lit(lit) => {
                                    chain_value(ValueExpr::Lit(lit.to_owned()));
                                }
                                other => {
                                    chain_value(other);
                                }
                            }
                        }
                    }
                    // If the variable is defined by `for`,
                    // we found it a scoped variable. Stop searching.
                    break;
                }
                MayM4::Macro(_) => break, // untrackable
                _ => todo!("{} -> {}", name, self.display_node(nid)),
            }
        }
        Some(chain)
    }

    pub(crate) fn vsa_inspect_word(
        &self,
        word: &AcWord,
        mut loc: Location,
        internal_field_separator: Option<char>,
    ) -> Vec<ValueExpr> {
        let mut values = Vec::new();
        match &word.0 {
            Word::Single(word) => values.extend(self.vsa_inspect_word_fragment(
                word,
                &mut loc,
                internal_field_separator,
            )),
            Word::Concat(words) => {
                let mut current_word = Vec::new();
                for w in words.iter() {
                    let v = self.vsa_inspect_word_fragment(w, &mut loc, internal_field_separator);
                    if v.is_empty() {
                        emit_word(&mut current_word, &mut values);
                    } else {
                        current_word.extend(v);
                    }
                }
                emit_word(&mut current_word, &mut values);
            }
            Word::Empty => values.push(ValueExpr::Lit(String::new())),
        }
        values
    }

    fn vsa_inspect_word_fragment(
        &self,
        word: &AcWordFragment,
        loc: &mut Location,
        internal_field_separator: Option<char>,
    ) -> Vec<ValueExpr> {
        let mut values = Vec::new();
        use MayM4::*;
        match word {
            Shell(WordFragment::Literal(lit)) => {
                values.extend(
                    self.split_literal_with_internal_field_separator(lit, internal_field_separator)
                        .into_iter()
                        .map(ValueExpr::Lit),
                );
            }
            Shell(WordFragment::DoubleQuoted(frags)) => {
                // we have to conduct careful literal splitting due to the following reasons.
                // 1. Sorry but the current autoconf parser cannot recognize concatenation of words
                //    inside double quoted strings. For example, if we have "${a} prefix_${b}",
                //    what we really want to see is the two words like '[Var("a"), Concat([Lit("prefix_"), Var("b")])]'.
                //    However, what actually we get from the parser is just '[Var("a"), Lit(" prefix_"), Var("b")]'.
                //    Here we have to find the boundary of concatenated words from ' prefix_'.
                // 2. `IFS` can be other than just a whitespace, e.g. ':', which confuses us.

                let mut current_word = Vec::new();

                for f in frags {
                    match f {
                        WordFragment::Literal(lit) => {
                            let parts: Vec<&str> =
                                lit.split(internal_field_separator.unwrap_or(' ')).collect();

                            // First part stays with current word
                            if !parts[0].is_empty() {
                                current_word.push(ValueExpr::Lit(parts[0].to_string()));
                            }

                            // Each subsequent part creates a word boundary
                            for part in &parts[1..] {
                                emit_word(&mut current_word, &mut values);
                                if !part.is_empty() {
                                    current_word.push(ValueExpr::Lit(part.to_string()));
                                }
                            }
                        }
                        WordFragment::Param(Parameter::Var(var)) => {
                            current_word.push(ValueExpr::Var(var.to_owned(), loc.clone()));
                            loc.order_in_expr += 1;
                        }
                        WordFragment::Escaped(s) if s == "\n" => (),
                        w if internal_field_separator.is_some_and(|ifs| {
                            ifs.to_string() == self.pool.shell_word_to_string(w)
                        }) =>
                        {
                            emit_word(&mut current_word, &mut values);
                        }
                        _ => todo!("{:?}", f),
                    }
                }

                emit_word(&mut current_word, &mut values);
            }
            Shell(WordFragment::Param(Parameter::Var(var))) => {
                values.push(ValueExpr::Var(var.to_owned(), loc.clone()));
                loc.order_in_expr += 1;
            }
            Shell(WordFragment::Subst(subst)) => match &**subst {
                ParameterSubstitution::Command(cmds) => {
                    let mut shell_strings = Vec::new();
                    let mut uses = HashMap::new();
                    for &node_id in cmds {
                        let shell_string = self.display_node(node_id);
                        let (_, u) = self.collect_variables(node_id);
                        shell_strings.push(shell_string);
                        uses.extend(u);
                    }
                    values.push(ValueExpr::Shell(
                        shell_strings.join("\n"),
                        uses.keys()
                            .map(|name| {
                                let expr = ValueExpr::Var(name.to_owned(), loc.clone());
                                loc.order_in_expr += 1;
                                expr
                            })
                            .collect(),
                    ));
                }
                _ => todo!(),
            },
            Shell(w) => {
                let lit = self.pool.shell_word_to_string(w);
                if internal_field_separator.is_some_and(|ifs| ifs.to_string() == lit) {
                } else {
                    values.push(ValueExpr::Lit(lit));
                }
            }
            _ => todo!(),
        }
        values
    }

    pub(crate) fn current_internal_field_separator(&self, loc: &Location) -> Option<char> {
        let mut internal_field_separator = None;
        if let Some(ifs_loc) = self.get_dominant_definition("IFS", loc.node_id) {
            if let MayM4::Shell(ShellCommand::Assignment(_, rhs)) =
                &self.get_node(ifs_loc.node_id).unwrap().cmd.0
            {
                if let ValueExpr::Lit(lit) =
                    self.vsa_inspect_word(rhs, ifs_loc.clone(), None).pop().unwrap()
                {
                    internal_field_separator.replace(lit.chars().next().unwrap());
                }
            }
        }
        internal_field_separator
    }

    fn split_literal_with_internal_field_separator(
        &self,
        literal: &String,
        internal_field_separator: Option<char>,
    ) -> Vec<String> {
        if let Some(ifs) = internal_field_separator {
            literal
                .split(ifs)
                .filter_map(|s| (!s.is_empty()).then_some(s.to_owned()))
                .collect()
        } else {
            literal
                .split_whitespace()
                .filter_map(|s| (!s.is_empty()).then_some(s.to_owned()))
                .collect()
        }
    }

    fn serialize_vsa_cache(&self) {
        let path = self.get_vsa_cache_path();
        let config = bincode::config::standard();
        let content = bincode::encode_to_vec(&self.vsa_cache, config).unwrap();
        std::fs::write(path, content).unwrap();
    }

    fn deserialize_vsa_cache(&mut self) {
        let path = self.get_vsa_cache_path();
        if let Ok(content) = std::fs::read(path) {
            let config = bincode::config::standard();
            self.vsa_cache = bincode::decode_from_slice(&content, config).unwrap().0;
        }
    }

    fn get_vsa_cache_path(&self) -> PathBuf {
        let mut hasher = DefaultHasher::new();
        self.path.to_str().unwrap().hash(&mut hasher);
        let h = hasher.finish();
        PathBuf::from(format!("/tmp/vsa_cache.{:x}.bin", h))
    }
}

fn convert_identifier_to_value_expression(ident: Identifier, loc: Location) -> ValueExpr {
    match ident {
        Identifier::Name(name) => ValueExpr::Var(name, loc),
        Identifier::Indirect(name) => ValueExpr::DynName(vec![ValueExpr::Var(name, loc)]),
        Identifier::Concat(concat) => ValueExpr::DynName(
            concat
                .into_iter()
                .map(|ident| match ident {
                    Identifier::Name(lit) => ValueExpr::Lit(lit),
                    Identifier::Indirect(name) => ValueExpr::Var(name, loc.clone()),
                    _ => unreachable!(),
                })
                .collect(),
        ),
    }
}

fn emit_word(current_word: &mut Vec<ValueExpr>, values: &mut Vec<ValueExpr>) {
    if !current_word.is_empty() {
        if current_word.len() == 1 {
            values.push(current_word.pop().unwrap());
        } else {
            values.push(ValueExpr::Concat(std::mem::take(current_word)));
        }
    }
}
