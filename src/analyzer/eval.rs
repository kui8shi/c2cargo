use super::{
    guard::cmp_guards,
    type_inference::DataType,
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
pub(crate) struct DividedIdentifier {
    /// components of the divided identifier
    pub components: Vec<ValueExpr>,
    /// variable to value map
    pub map: HashMap<String, String>,
    /// The location where divided identifier is constructed.
    pub ref_loc: Location,
}

/// Represents the operation on the dictionary types
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum DictionaryOperation {
    Read,
    Write,
}

/// Saving the result of dictionary type inference.
#[derive(Debug, PartialEq, Eq)]
pub(crate) struct DictionaryAccess {
    operation: DictionaryOperation,
    keys: HashMap<String, String>,
    name: String,
    full_name: String,
    value_type: DataType,
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
            .evals
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
                    def_use_edges.push((def_loc.node_id, divided.ref_loc.node_id, name.to_owned()));
                    self.var_indirect_usages
                        .entry(name.to_owned())
                        .or_default()
                        .push(divided.ref_loc.clone());
                }
            }
        }
        self.apply_def_use_edges(def_use_edges);
        dbg!(&self.evals);
        dbg!(&self.resolved_values);
        dbg!(&self.divided_vars);
        // dbg!(self.infer_dictionary_types());
    }

    /// collect literals of a var
    pub(crate) fn resolve_var(&mut self, name: &str, loc: &Location) -> HashSet<String> {
        self.get_last_resolved_values(&Identifier::Name(name.to_owned()), loc)
            .unwrap_or(
                self.resolve_value_expression(&ValueExpr::Var(name.to_owned(), loc.clone()), loc),
            )
    }

    /// run type inference only for dictionary types based on the result of value set analysis.
    /// returns a map from location to accesses to variable as dictionary
    pub(crate) fn infer_dictionary_types(&self) -> HashMap<Location, DictionaryAccess> {
        use DictionaryOperation::*;
        let mut ret = HashMap::new();
        let strip_underscore = |s: &str| -> String {
            let s = s.strip_prefix("_").unwrap_or(s);
            let s = s.strip_suffix("_").unwrap_or(s);
            s.to_owned()
        };
        for (full_name, divided) in self.divided_vars.iter() {
            let name = divided
                .components
                .iter()
                .filter_map(|r| {
                    if let ValueExpr::Lit(lit) = r {
                        Some(strip_underscore(lit))
                    } else {
                        None
                    }
                })
                .collect::<Vec<_>>()
                .join("_");
            let keys = divided
                .map
                .iter()
                .map(|(k, v)| (k.to_owned(), strip_underscore(v)))
                .collect::<HashMap<_, _>>();
            if let Some(def_locs) = self.get_all_definition(full_name.as_str(), None) {
                for loc in def_locs {
                    ret.insert(
                        loc,
                        DictionaryAccess {
                            operation: Read,
                            keys: keys.clone(),
                            name: name.clone(),
                            full_name: full_name.clone(),
                            value_type: DataType::Literal,
                        },
                    );
                }
            }
            if let Some(use_locs) = self.get_all_usages_before(full_name.as_str(), None) {
                for loc in use_locs {
                    ret.insert(
                        loc,
                        DictionaryAccess {
                            operation: Write,
                            keys: keys.clone(),
                            name: name.clone(),
                            full_name: full_name.clone(),
                            value_type: DataType::Literal,
                        },
                    );
                }
            }
        }
        ret
    }

    fn record_identifier_division(&mut self, values: Vec<ValueExpr>, resolved: Vec<String>) {
        let name = resolved.concat();
        if self.var_definitions.contains_key(name.as_str()) {
            let mut ref_loc = None; // FIXME: so dirty data flow.
            let components = values.clone();
            let mut map = HashMap::new();
            for (r, v) in values.into_iter().zip(resolved.iter()) {
                if let ValueExpr::Var(name, loc) = r {
                    map.insert(name, v.to_owned());
                    ref_loc.replace(loc);
                }
            }
            let ref_loc = ref_loc.unwrap();
            self.divided_vars.insert(
                name,
                DividedIdentifier {
                    components,
                    map,
                    ref_loc,
                },
            );
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
    fn resolve_eval(&mut self, l: &Identifier, r: &Option<ValueExpr>, loc: &Location) {
        if let Some(r) = r {
            let rhs = self.resolve_value_expression(r, loc);
            for var_name in self.resolve_identifier(l, loc) {
                self.record_resolved_values(Identifier::Name(var_name), loc.clone(), rhs.clone());
            }
            self.record_resolved_values(l.clone(), loc.clone(), rhs.clone());
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
            Identifier::Indirect(name, loc) => {
                if let Some(chain) = self.construct_chain(name, loc) {
                    result.extend(self.resolve_chain(chain))
                }
            }
            Identifier::Concat(lvalues) => {
                let resolved = lvalues
                    .iter()
                    .map(|l| self.resolve_identifier(l, loc))
                    .collect();
                // enumerate combinations
                result.extend(
                    enumerate_combinations(resolved)
                        .into_iter()
                        .map(|words| words.concat()),
                );
            }
        }
        result
    }

    fn resolve_value_expression(&mut self, value: &ValueExpr, loc: &Location) -> HashSet<String> {
        let mut result = HashSet::new();
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
                let combos = enumerate_combinations(resolved);
                for combo in combos.iter() {
                    self.record_identifier_division(
                        values.iter().cloned().collect(),
                        combo.clone(),
                    );
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
                    .flat_map(|r| r.vars().into_iter().map(|v| v.first().unwrap().0.clone()));
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
                    let vals = self.inspect_word(&rhs, &def_loc);
                    let found_dominant_initialization = (vals.is_empty()
                        || vals.iter().all(|v| matches!(v, ValueExpr::Lit(_))))
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
                    for word in words {
                        let vals = self.inspect_word(&word, &def_loc);
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

    fn inspect_word(&self, word: &AcWord, loc: &Location) -> Vec<ValueExpr> {
        let mut values = Vec::new();
        match &word.0 {
            Word::Single(word) => values.extend(self.inspect_word_fragment(word, loc)),
            Word::Concat(words) => values.push(ValueExpr::Concat(
                words
                    .iter()
                    .flat_map(|w| self.inspect_word_fragment(w, loc))
                    .collect(),
            )),
            Word::Empty => values.push(ValueExpr::Lit(String::new())),
        }
        values
    }

    fn inspect_word_fragment(&self, word: &AcWordFragment, loc: &Location) -> Vec<ValueExpr> {
        let mut values = Vec::new();
        use MayM4::*;
        match word {
            Shell(WordFragment::Literal(lit)) => {
                values.extend(
                    lit.split_whitespace()
                        .filter_map(|s| (!s.is_empty()).then_some(ValueExpr::Lit(s.to_owned()))),
                );
            }
            Shell(WordFragment::DoubleQuoted(frags)) => {
                for f in frags {
                    match f {
                        WordFragment::Literal(lit) => {
                            values.extend(lit.split_whitespace().filter_map(|s| {
                                (!s.is_empty()).then_some(ValueExpr::Lit(s.to_owned()))
                            }));
                        }
                        WordFragment::Param(Parameter::Var(var)) => {
                            values.push(ValueExpr::Var(var.to_owned(), loc.clone()));
                        }
                        WordFragment::Escaped(s) if s == "\n" => (),
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
                values.push(ValueExpr::Lit(self.pool.shell_word_to_string(w)));
            }
            _ => todo!(),
        }
        values
    }
}
