use super::{
    guard::cmp_guards,
    type_inference::DataType,
    variable::{LValue, Location, RValue},
    AcWord, Analyzer, MayM4, Parameter, ParameterSubstitution, ShellCommand, Word, WordFragment,
};
use autotools_parser::ast::node::{AcWordFragment, NodePool};
use itertools::Itertools;
use std::{
    cmp::Ordering,
    collections::{HashMap, HashSet},
};

// Saving the result of backward traversal
#[derive(Debug, PartialEq, Eq)]
struct Chain {
    // lit or var
    name: LValue,
    // location
    loc: Location,
    /// Set of resolved rvalues (as literals).
    resolved: HashSet<String>,
    /// Set of unresolved rvalues: var, or ref
    /// if Option<_> is None, it means the rvalue is not resolvable.
    unresolved: HashSet<RValue>,
}

impl Chain {
    /// Creates a new chaining struct
    pub fn new(name: LValue, loc: Location) -> Self {
        Self {
            name,
            loc,
            resolved: HashSet::new(),
            unresolved: HashSet::new(),
        }
    }
}

// Saving how a dynamic identifier is constructed via eval statements.
#[derive(Debug, PartialEq, Eq)]
pub struct DynamicIdentifier {
    // components of the dynamic variable reference
    components: Vec<RValue>,
    // variable to value map
    map: HashMap<String, String>,
}

// Represents the operation on the dictionary types
#[derive(Debug, PartialEq, Eq)]
enum DictionaryOperation {
    Set,
    Get,
}

// Saving the result of dictionary type inference.
#[derive(Debug, PartialEq, Eq)]
struct DictionaryAccess {
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
        for (i, (l, r, loc)) in evals.iter().enumerate() {
            self.resolve_eval(&l, &r, &loc);
        }
        dbg!(&self.evals);
        dbg!(&self.resolved_values);
        dbg!(&self.dynamic_vars);
        dbg!(self.infer_dictionary_types());
    }

    /// collect literals of a var
    pub(crate) fn resolve_var(&mut self, name: &str, loc: &Location) -> HashSet<String> {
        self.get_last_resolved_values(&LValue::Lit(name.to_owned()), loc)
            .unwrap_or(self.resolve_rvalue(&RValue::Var(name.to_owned(), loc.clone()), loc))
    }

    /// run type inference only for dictionary types based on the result of value set analysis.
    /// returns a map from location to accesses to variable as dictionary
    fn infer_dictionary_types(&self) -> HashMap<Location, DictionaryAccess> {
        use DictionaryOperation::*;
        let mut ret = HashMap::new();
        let strip_underscore = |s: &str| -> String {
            let s = s.strip_prefix("_").unwrap_or(s);
            let s = s.strip_suffix("_").unwrap_or(s);
            s.to_owned()
        };
        for (full_name, dynamic) in self.dynamic_vars.iter() {
            let name = dynamic
                .components
                .iter()
                .filter_map(|r| {
                    if let RValue::Lit(lit) = r {
                        Some(strip_underscore(lit))
                    } else {
                        None
                    }
                })
                .collect::<Vec<_>>()
                .join("_");
            let keys = dynamic
                .map
                .iter()
                .map(|(k, v)| (k.to_owned(), strip_underscore(v)))
                .collect::<HashMap<_, _>>();
            if let Some(def_locs) = self.get_all_definition(full_name.as_str(), None) {
                for loc in def_locs {
                    ret.insert(
                        loc,
                        DictionaryAccess {
                            operation: Set,
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
                            operation: Get,
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

    fn record_dynamic_identifier(&mut self, rvalues: Vec<RValue>, resolved: Vec<String>) {
        let name = resolved.concat();
        if self.var_definitions.contains_key(name.as_str()) {
            let components = rvalues.clone();
            let mut map = HashMap::new();
            for (r, v) in rvalues.into_iter().zip(resolved.iter()) {
                if let RValue::Var(name, _) = r {
                    map.insert(name, v.to_owned());
                }
            }
            self.dynamic_vars
                .insert(name, DynamicIdentifier { components, map });
        }
    }

    fn record_resolved_values(&mut self, l: LValue, loc: Location, values: HashSet<String>) {
        self.resolved_values
            .entry(l)
            .or_default()
            .entry(loc)
            .or_default()
            .extend(values);
    }

    fn get_last_resolved_values(&self, l: &LValue, loc: &Location) -> Option<HashSet<String>> {
        self.resolved_values
            .get(l)
            .and_then(|m| m.range(..=loc).next().map(|(_, s)| s.clone()))
    }

    /// construct chain of value flows in backward order and resolve them.
    fn resolve_eval(&mut self, l: &LValue, r: &Option<RValue>, loc: &Location) {
        if let Some(r) = r {
            let rhs = self.resolve_rvalue(r, loc);
            for var_name in self.resolve_lvalue(l, loc) {
                self.record_resolved_values(LValue::Lit(var_name), loc.clone(), rhs.clone());
            }
            self.record_resolved_values(l.clone(), loc.clone(), rhs.clone());
        } else {
            // rhs is empty
        }
    }

    fn resolve_lvalue(&mut self, lvalue: &LValue, loc: &Location) -> HashSet<String> {
        let mut result = HashSet::new();
        match lvalue {
            LValue::Lit(lit) => {
                result.insert(lit.to_owned());
            }
            LValue::Var(name, loc) => {
                if let Some(chain) = self.construct_chain(name, loc) {
                    result.extend(self.resolve_chain(chain))
                }
            }
            LValue::Concat(lvalues) => {
                let resolved = lvalues
                    .iter()
                    .map(|l| self.resolve_lvalue(l, loc))
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

    fn resolve_rvalue(&mut self, rvalue: &RValue, loc: &Location) -> HashSet<String> {
        let mut result = HashSet::new();
        match rvalue {
            RValue::Lit(lit) => {
                result.extend(
                    lit.split_whitespace()
                        .filter_map(|s| (!s.is_empty()).then_some(s.to_owned())),
                );
            }
            RValue::Var(name, loc) => {
                if let Some(chain) = self.construct_chain(name, loc) {
                    let chain_result = self.resolve_chain(chain);
                    result.extend(chain_result);
                } else {
                    // No chain found for variable
                }
            }
            RValue::Concat(rvalues) => {
                let resolved = rvalues
                    .iter()
                    .map(|r| self.resolve_rvalue(r, loc))
                    .collect();
                // enumerate combinations
                result.extend(
                    enumerate_combinations(resolved)
                        .into_iter()
                        .map(|words| words.concat()),
                );
            }

            RValue::Ref(rvalues) => {
                let resolved = rvalues
                    .iter()
                    .map(|r| self.resolve_rvalue(r, loc))
                    .collect();
                let combos = enumerate_combinations(resolved);
                for combo in combos.iter() {
                    self.record_dynamic_identifier(
                        rvalues.iter().cloned().collect(),
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
            RValue::Shell(shell_string, vars) => {
                let resolved = vars.iter().map(|r| self.resolve_rvalue(r, loc)).collect();
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
        // if let Some(lvalue) = rvalue.into() {
        //     if let Some(resolved) = self.get_last_resolved_values(&lvalue, loc) {
        //         result.extend(resolved.clone());
        //     }
        // }
        result
    }

    fn resolve_chain(&mut self, chain: Chain) -> HashSet<String> {
        // resolve chain
        // 1. if unresolved is not empty, recursively call resolve_rvalue on them
        // 2. else, return resolved
        if !chain.unresolved.is_empty() {
            chain
                .resolved
                .into_iter()
                .chain(
                    chain
                        .unresolved
                        .into_iter()
                        .flat_map(|rvalue| self.resolve_rvalue(&rvalue, &chain.loc)),
                )
                .collect()
        } else {
            chain.resolved
        }
    }

    /// Given a variable, traverse the script backward to construct chain of values
    fn construct_chain(&self, name: &str, loc: &Location) -> Option<Chain> {
        let lvalue = LValue::Lit(name.to_owned());
        let mut chain = Chain::new(lvalue.clone(), loc.clone());
        if let Some(resolved) = self.get_last_resolved_values(&lvalue, loc) {
            chain.resolved.extend(resolved.clone());
            return Some(chain);
        }
        if self.fixed.contains_key(name) {
            chain.resolved.insert(self.fixed[name].to_owned());
            return Some(chain);
        }
        let mut chain_rvalue = |rvalue| match rvalue {
            RValue::Lit(lit) => {
                chain.resolved.extend(
                    lit.split_whitespace()
                        .filter_map(|s| (!s.is_empty()).then_some(s.to_owned())),
                );
            }
            RValue::Var(var, loc) => {
                if var != name {
                    if let Some(values) =
                        self.get_last_resolved_values(&LValue::Lit(var.clone()), &loc)
                    {
                        chain.resolved.extend(values);
                    } else {
                        chain.unresolved.insert(RValue::Var(var, loc));
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
                        || vals.iter().all(|v| matches!(v, RValue::Lit(_))))
                        && matches!(
                            cmp_guards(
                                &self.guard_of_location(&def_loc),
                                &self.guard_of_location(loc)
                            ),
                            Some(Ordering::Less | Ordering::Equal)
                        );
                    for val in vals {
                        chain_rvalue(val);
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
                                RValue::Lit(lit) => {
                                    chain_rvalue(RValue::Lit(lit.to_owned()));
                                }
                                other => {
                                    chain_rvalue(other);
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

    fn inspect_word(&self, word: &AcWord, loc: &Location) -> Vec<RValue> {
        let mut values = Vec::new();
        match &word.0 {
            Word::Single(word) => values.extend(self.inspect_word_fragment(word, loc)),
            Word::Concat(words) => values.push(RValue::Concat(
                words
                    .iter()
                    .flat_map(|w| self.inspect_word_fragment(w, loc))
                    .collect(),
            )),
            Word::Empty => (),
        }
        values
    }

    fn inspect_word_fragment(&self, word: &AcWordFragment, loc: &Location) -> Vec<RValue> {
        let mut values = Vec::new();
        use MayM4::*;
        match word {
            Shell(WordFragment::Literal(lit)) => {
                values.extend(
                    lit.split_whitespace()
                        .filter_map(|s| (!s.is_empty()).then_some(RValue::Lit(s.to_owned()))),
                );
            }
            Shell(WordFragment::DoubleQuoted(frags)) => {
                for f in frags {
                    match f {
                        WordFragment::Literal(lit) => {
                            values.extend(lit.split_whitespace().filter_map(|s| {
                                (!s.is_empty()).then_some(RValue::Lit(s.to_owned()))
                            }));
                        }
                        WordFragment::Param(Parameter::Var(var)) => {
                            values.push(RValue::Var(var.to_owned(), loc.clone()));
                        }
                        WordFragment::Escaped(s) if s == "\n" => (),
                        _ => todo!("{:?}", f),
                    }
                }
            }
            Shell(WordFragment::Param(Parameter::Var(var))) => {
                values.push(RValue::Var(var.to_owned(), loc.clone()));
            }
            Shell(WordFragment::Subst(subst)) => match &**subst {
                ParameterSubstitution::Command(cmds) => {
                    let node_id = cmds.first().unwrap().clone();
                    let shell_string = self.display_node(node_id);
                    let (_, uses) = self.collect_variables(node_id);
                    values.push(RValue::Shell(
                        shell_string,
                        uses.keys()
                            .map(|name| RValue::Var(name.to_owned(), loc.clone()))
                            .collect(),
                    ));
                }
                _ => todo!(),
            },
            Shell(w) => {
                values.push(RValue::Lit(self.pool.shell_word_to_string(w)));
            }
            _ => todo!(),
        }
        values
    }
}
