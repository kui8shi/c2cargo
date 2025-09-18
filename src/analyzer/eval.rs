//! Structs & Methods for Value Set Analysis
use super::{
    guard::cmp_guards,
    variable::{Identifier, Location, ValueExpr},
    AcWord, Analyzer, MayM4, Parameter, ParameterSubstitution, ShellCommand, Word, WordFragment,
};
use autotools_parser::ast::node::{AcWordFragment, NodePool};
use itertools::Itertools;
use std::{
    cmp::Ordering,
    collections::{HashMap, HashSet},
};

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

/// Saving information how an identifier is divided via eval statements.
#[derive(Debug, PartialEq, Eq)]
pub(crate) struct IdentifierDivision {
    /// components of the divided identifier
    pub division: Identifier,
    /// variable to value map
    pub map: HashMap<String, String>,
}

fn enumerate_combinations(combos: Vec<HashSet<String>>) -> Vec<Vec<String>> {
    combos
        .into_iter()
        .map(|hs| hs.into_iter().collect::<Vec<_>>().into_iter())
        .multi_cartesian_product()
        .collect()
}

impl Analyzer {
    /// run value set analysis to obtain value candidates of variables appeared in eval statements.
    pub(crate) fn run_value_set_analysis(&mut self) {
        // we assume variable enumeration is already completed.
        let mut evals = self
            .eval_assigns
            .iter()
            .flat_map(|(l, v)| v.iter().zip(std::iter::repeat(l)))
            .map(|((r, loc), l)| (l.clone(), r.clone(), loc.clone()))
            .collect::<Vec<_>>();
        evals.sort_by_key(|(_, _, loc)| loc.clone());
        for (l, r, loc) in evals.iter() {
            self.resolve_eval(&l, &r, &loc);
        }
        // Add def use chains caused by dynamic identifier
        let mut def_use_edges = Vec::new();
        for (name, divided) in self.divided_vars.iter() {
            if let Some(def_locs) = self.var_definitions.get(name) {
                for def_loc in def_locs {
                    for (ref_loc, _) in divided {
                        def_use_edges.push((def_loc.node_id, ref_loc.node_id, name.to_owned()));
                        self.var_indirect_usages
                            .entry(name.to_owned())
                            .or_default()
                            .push(ref_loc.clone());
                    }
                }
            }
        }
        self.apply_def_use_edges(def_use_edges);
        dbg!(&self.eval_assigns);
        dbg!(&self.resolved_values);
        dbg!(&self.divided_vars);
    }

    /// collect literals of a var
    pub(crate) fn resolve_var(&mut self, name: &str, loc: &Location) -> HashSet<String> {
        self.get_last_resolved_values(&Identifier::Name(name.to_owned()), loc)
            .unwrap_or(
                self.resolve_value_expression(&ValueExpr::Var(name.to_owned(), loc.clone()), loc),
            )
    }

    fn record_identifier_division(
        &mut self,
        values: Vec<Identifier>,
        resolved: Vec<String>,
        ref_loc: Location,
    ) {
        let name = resolved.concat();
        if self.var_definitions.contains_key(name.as_str()) {
            let mut map = HashMap::new();
            for (k, v) in values.clone().into_iter().zip(resolved.iter()) {
                if let Identifier::Indirect(name) = k {
                    map.insert(name, v.to_owned());
                }
            }
            let division = Identifier::Concat(values);
            self.divided_vars
                .entry(name)
                .or_default()
                .insert(ref_loc, IdentifierDivision { division, map });
        }
    }

    fn record_resolved_values(&mut self, l: Identifier, loc: Location, values: HashSet<String>) {
        self.resolved_values
            .entry(l)
            .or_default()
            .entry(loc)
            .or_default()
            .extend(values);
    }

    fn get_last_resolved_values(&self, l: &Identifier, loc: &Location) -> Option<HashSet<String>> {
        self.resolved_values
            .get(l)
            .and_then(|m| m.range(..=loc).next().map(|(_, s)| s.clone()))
    }

    /// construct chain of value flows in backward order and resolve them.
    fn resolve_eval(&mut self, lhs: &Identifier, rhs: &Option<ValueExpr>, loc: &Location) {
        if let Some(rhs) = rhs {
            let rhs = self.resolve_value_expression(rhs, loc);
            for var_name in self.resolve_identifier(lhs, loc) {
                self.record_resolved_values(Identifier::Name(var_name), loc.clone(), rhs.clone());
            }
            self.record_resolved_values(lhs.clone(), loc.clone(), rhs.clone());
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
                if let Some(chain) = self.construct_chain(name, loc) {
                    result.extend(self.resolve_chain(chain))
                }
            }
            Identifier::Concat(values) => {
                let resolved = values
                    .iter()
                    .map(|l| self.resolve_identifier(l, loc))
                    .collect();
                // enumerate combinations
                let combos = enumerate_combinations(resolved);
                for combo in combos.iter() {
                    self.record_identifier_division(values.clone(), combo.clone(), loc.clone());
                }
                for name in combos.into_iter().map(|words| words.concat()) {
                    result.insert(name);
                }
            }
        }
        result
    }

    fn resolve_value_expression(&mut self, value: &ValueExpr, loc: &Location) -> HashSet<String> {
        let mut result = HashSet::new();
        // Add an empty string to the result for safety
        result.insert(String::new());
        if let Some(identifier) = value.into() {
            if let Some(resolved) = self.get_last_resolved_values(&identifier, loc) {
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
                if let Some(chain) = self.construct_chain(name, loc) {
                    let chain_result = self.resolve_chain(chain);
                    result.extend(chain_result);
                } else {
                    // No chain found for variable
                }
            }
            ValueExpr::Concat(values) => {
                let resolved = values
                    .iter()
                    .map(|r| self.resolve_value_expression(r, loc))
                    .collect();
                // enumerate combinations
                result.extend(
                    enumerate_combinations(resolved)
                        .into_iter()
                        .map(|words| words.concat()),
                );
            }

            ValueExpr::DynName(values) => {
                let resolved = values
                    .iter()
                    .map(|r| self.resolve_value_expression(r, loc))
                    .collect();
                let values = values
                    .iter()
                    .map(|v| Into::<Option<Identifier>>::into(v).unwrap())
                    .collect::<Vec<_>>();
                // enumerate combinations
                let combos = enumerate_combinations(resolved);
                for combo in combos.iter() {
                    self.record_identifier_division(values.clone(), combo.clone(), loc.clone());
                }
                for name in combos.into_iter().map(|words| words.concat()) {
                    if let Some(chain) = self.construct_chain(&name, loc) {
                        let chain_result = self.resolve_chain(chain);
                        result.extend(chain_result);
                    }
                }
            }
            ValueExpr::Shell(shell_string, vars) => {
                let resolved = vars
                    .iter()
                    .map(|r| self.resolve_value_expression(r, loc))
                    .collect();
                // enumerate combinations & additoinal resolving with shell execution
                // cf. RValue::concretize
                let var_names = vars
                    .iter()
                    .flat_map(|r| r.vars().into_iter().map(|v| v.first().unwrap().clone()));
                for vals in enumerate_combinations(resolved) {
                    let env_pairs: Vec<_> = var_names.clone().zip(vals.clone()).collect();
                    let output = std::process::Command::new("sh")
                        .arg("-c")
                        .arg(shell_string.clone())
                        .envs(env_pairs)
                        .output()
                        .expect(&format!("Executing: {} has failed", shell_string));
                    let stdout_str = String::from_utf8(output.stdout)
                        .expect("Unable to convert utf-8 to String.");
                    result.extend(stdout_str.split_whitespace().map(|s| s.to_owned()));
                }
            }
        }
        if let Some(identifier) = value.into() {
            self.record_resolved_values(identifier, loc.clone(), result.clone());
        }
        result
    }

    fn resolve_chain(&mut self, chain: Chain) -> HashSet<String> {
        // resolve chain
        // 1. if unresolved is not empty, recursively call resolve_value_expression on them
        // 2. else, return resolved
        if !chain.unresolved.is_empty() {
            chain
                .resolved
                .into_iter()
                .chain(
                    chain
                        .unresolved
                        .into_iter()
                        .flat_map(|value| self.resolve_value_expression(&value, &chain.loc)),
                )
                .collect()
        } else {
            chain.resolved
        }
    }

    /// Given a variable, traverse the script backward to construct chain of values
    fn construct_chain(&self, name: &str, loc: &Location) -> Option<Chain> {
        let identifier = Identifier::Name(name.to_owned());
        let mut chain = Chain::new(identifier.clone(), loc.clone());
        if let Some(resolved) = self.get_last_resolved_values(&identifier, loc) {
            chain.resolved.extend(resolved.clone());
            return Some(chain);
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
                    if let Some(resolved) =
                        self.get_last_resolved_values(&Identifier::Name(var.clone()), &loc)
                    {
                        chain.resolved.extend(resolved);
                    } else {
                        chain.unresolved.insert(ValueExpr::Var(var, loc));
                    }
                }
            }
            r => {
                chain.unresolved.insert(r);
            }
        };
        let def_locs = if let Some(mut locs) = self.get_all_definition(name, Some(loc)) {
            locs.sort();
            locs.reverse();
            locs
        } else {
            return None;
        };
        for def_loc in def_locs {
            let nid = def_loc.node_id;
            let cmd = &self.get_node(nid).cmd.0;
            match cmd.clone() {
                MayM4::Shell(ShellCommand::Assignment(lhs, rhs)) if lhs == name => {
                    let ifs = self.current_internal_field_separator(&def_loc);
                    let vals = self.inspect_word(&rhs, &def_loc, ifs);
                    let is_rhs_concrete =
                        vals.is_empty() || vals.iter().all(|v| matches!(v, ValueExpr::Lit(_)));
                    let found_dominant_initialization = is_rhs_concrete
                        && matches!(
                            cmp_guards(
                                &self.guard_of_location(&def_loc),
                                &self.guard_of_location(loc)
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
                        let vals = self.inspect_word(&word, &def_loc, ifs);
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

    fn inspect_word(
        &self,
        word: &AcWord,
        loc: &Location,
        internal_field_separator: Option<char>,
    ) -> Vec<ValueExpr> {
        let mut values = Vec::new();
        match &word.0 {
            Word::Single(word) => {
                values.extend(self.inspect_word_fragment(word, loc, internal_field_separator))
            }
            Word::Concat(words) => values.push(ValueExpr::Concat(
                words
                    .iter()
                    .flat_map(|w| self.inspect_word_fragment(w, loc, internal_field_separator))
                    .collect(),
            )),
            Word::Empty => values.push(ValueExpr::Lit(String::new())),
        }
        values
    }

    fn inspect_word_fragment(
        &self,
        word: &AcWordFragment,
        loc: &Location,
        internal_field_separator: Option<char>,
    ) -> Vec<ValueExpr> {
        let mut values = Vec::new();
        use MayM4::*;
        match word {
            Shell(WordFragment::Literal(lit)) => {
                values.extend(
                    self.split_literal_with_internal_field_separator(lit, internal_field_separator)
                        .into_iter()
                        .map(|s| ValueExpr::Lit(s)),
                );
            }
            Shell(WordFragment::DoubleQuoted(frags)) => {
                for f in frags {
                    match f {
                        WordFragment::Literal(lit) => {
                            values.extend(
                                self.split_literal_with_internal_field_separator(
                                    lit,
                                    internal_field_separator,
                                )
                                .into_iter()
                                .map(|s| ValueExpr::Lit(s)),
                            );
                        }
                        WordFragment::Param(Parameter::Var(var)) => {
                            values.push(ValueExpr::Var(var.to_owned(), loc.clone()));
                        }
                        WordFragment::Escaped(s) if s == "\n" => (),
                        w if internal_field_separator.is_some_and(|ifs| {
                            ifs.to_string() == self.pool.shell_word_to_string(w)
                        }) =>
                        {
                            ()
                        }
                        _ => todo!("{:?}", f),
                    }
                }
            }
            Shell(WordFragment::Param(Parameter::Var(var))) => {
                values.push(ValueExpr::Var(var.to_owned(), loc.clone()));
            }
            Shell(WordFragment::Subst(subst)) => match &**subst {
                ParameterSubstitution::Command(cmds) => {
                    let node_id = cmds.first().unwrap().clone();
                    let shell_string = self.display_node(node_id);
                    let (_, uses) = self.collect_variables(node_id);
                    values.push(ValueExpr::Shell(
                        shell_string,
                        uses.keys()
                            .map(|name| ValueExpr::Var(name.to_owned(), loc.clone()))
                            .collect(),
                    ));
                }
                _ => todo!(),
            },
            Shell(w) => {
                let lit = self.pool.shell_word_to_string(w);
                if internal_field_separator.is_some_and(|ifs| ifs.to_string() == lit) {
                    ()
                } else {
                    values.push(ValueExpr::Lit(lit));
                }
            }
            _ => todo!(),
        }
        values
    }

    fn current_internal_field_separator(&self, loc: &Location) -> Option<char> {
        let mut internal_field_separator = None;
        if let Some(ifs_loc) = self.get_dominant_definition("IFS", loc.node_id) {
            if let MayM4::Shell(ShellCommand::Assignment(_, rhs)) =
                &self.get_node(ifs_loc.node_id).cmd.0
            {
                if let ValueExpr::Lit(lit) = self.inspect_word(rhs, &ifs_loc, None).pop().unwrap() {
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
}
