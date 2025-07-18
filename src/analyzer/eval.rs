use super::{
    cmp_guards,
    variable::{LValue, Location, RValue},
    AcWord, Analyzer, MayM4, Parameter, ParameterSubstitution, ShellCommand, Word, WordFragment,
};
use itertools::Itertools;
use std::{cmp::Ordering, collections::HashSet};

// Saving the result of backward traversal
#[derive(Debug, PartialEq, Eq)]
struct Chain {
    // lit or var
    name: LValue,
    // location
    loc: Location,
    /// Set of rvalues resolved: literals.
    resolved: HashSet<String>,
    /// Set of rvalues unresolved: var, or ref
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

// Saving the result of value set analysis
#[derive(Debug, PartialEq, Eq)]
pub struct ValueSet {
    name: LValue,
}

fn enumerate_combinations(combos: Vec<HashSet<String>>) -> Vec<Vec<String>> {
    combos
        .into_iter()
        .map(|hs| hs.into_iter().collect::<Vec<_>>().into_iter())
        .multi_cartesian_product()
        .collect()
}

/*
*

*/
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
        dbg!("Total eval statements:", evals.len());
        for (i, (l, r, loc)) in evals.iter().enumerate() {
            dbg!("Processing eval", i, l, r);
            self.resolve_eval(&l, &r, &loc);
        }
        dbg!(&self.resolved_values);
    }

    /// construct chain of value flows in backward order and resolve them.
    fn resolve_eval(&mut self, l: &LValue, r: &Option<RValue>, loc: &Location) {
        if let Some(r) = r {
            let rhs = self.resolve_rvalue(r, loc);
            for var_name in self.resolve_lvalue(l, loc) {
                self.resolved_values
                    .insert(LValue::Lit(var_name), rhs.clone());
            }
            self.resolved_values.insert(l.clone(), rhs.clone());
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
                    dbg!(&chain);
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
        if let Some(resolved) = self.resolved_values.get(&lvalue) {
            result.extend(resolved.clone());
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
                if name == "cclist_chosen" {
                    println!(
                        "Resolving cclist_chosen! resolved_values contains: {:?}",
                        self.resolved_values
                            .get(&LValue::Lit("cclist_chosen".to_owned()))
                    );
                }
                if let Some(chain) = self.construct_chain(name, loc) {
                    if name == "abilist" {
                        println!("resolving chain: {:?}", &chain);
                    }
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
                println!(
                    "RValue::Ref components: {:?} resolved to: {:?}",
                    rvalues, &resolved
                );
                for name in enumerate_combinations(resolved)
                    .into_iter()
                    .map(|words| words.concat())
                {
                    println!("Looking up variable: {:?}", &name);
                    if let Some(chain) = self.construct_chain(&name, loc) {
                        let chain_result = self.resolve_chain(chain);
                        println!("Found chain result: {:?}", &chain_result);
                        result.extend(chain_result);
                    } else {
                        println!("No chain found for: {:?}", &name);
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
        if let Some(lvalue) = rvalue.into() {
            if let Some(resolved) = self.resolved_values.get(&lvalue) {
                println!("Using resolved_values for {:?} -> {:?}", &lvalue, &resolved);
                result.extend(resolved.clone());
            }
        }
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
        println!("construct_chain for: {:?}, {:?}", name, loc);
        // if self
        //     .resolved_values
        //     .contains_key(&LValue::Lit(name.to_owned()))
        // {
        //     return Some(self.resolved_rvalues[name].clone());
        // }
        let def_locs = if let Some(mut locs) = self.get_all_definition(name, loc) {
            locs.sort();
            locs.reverse();
            println!("Found definitions for {:?}, {:?}", name, &locs);
            locs
        } else {
            println!("No definitions found for {:?}", name);
            return None;
        };
        let mut chain = Chain::new(LValue::Lit(name.to_owned()), loc.clone());
        let mut chain_rvalue = |rvalue| match rvalue {
            RValue::Lit(lit) => {
                chain.resolved.extend(
                    lit.split_whitespace()
                        .filter_map(|s| (!s.is_empty()).then_some(s.to_owned())),
                );
            }
            RValue::Var(var, loc) => {
                if var != name {
                    chain.unresolved.insert(RValue::Var(var, loc));
                }
            }
            r => {
                chain.unresolved.insert(r);
            }
        };
        for def_loc in def_locs {
            let nid = def_loc.node_id;
            let cmd = &self.get_node(nid).cmd.0;
            println!(
                "Processing definition at {:?} \n  node kind: {:?}",
                &def_loc, cmd
            );
            match cmd.clone() {
                MayM4::Shell(ShellCommand::Assignment(lhs, rhs)) if lhs == name => {
                    let vals = self.inspect_word(&rhs, &def_loc);
                    println!(
                        "Collected right values in assignment of {} ... {:?}",
                        name, &vals
                    );
                    let found_initialization = (vals.is_empty()
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
                    if found_initialization {
                        // Found the initialization of the variable. Stop searching.
                        println!(
                            "{:?} is the initialization of {}. Stop searching.",
                            &def_loc, name
                        );
                        break;
                    }
                }
                MayM4::Shell(ShellCommand::For {
                    var,
                    words,
                    body: _,
                }) if var == name => {
                    println!(
                        "Processing FOR loop for variable {:?}, words: {:?}",
                        name, &words
                    );
                    for word in words {
                        let vals = self.inspect_word(&word, &def_loc);
                        println!("For loop word values: {:?}", &vals);
                        for val in vals {
                            match val {
                                RValue::Lit(lit) => {
                                    println!("Literal value: {:?}", &lit);
                                    chain_rvalue(RValue::Lit(lit.to_owned()));
                                }
                                other => {
                                    println!("Non-literal value: {:?}", &other);
                                    chain_rvalue(other);
                                }
                            }
                        }
                    }
                    // If the variable is defined by `for`,
                    // we found it a scoped variable. Stop searching.
                    break;
                }
                _ => todo!("{} -> {}", name, self.recover_content(nid)),
            }
        }
        println!("Constructed chain for {:?}, {:?}", name, &chain);
        Some(chain)
    }

    fn inspect_word(&self, word: &AcWord, loc: &Location) -> Vec<RValue> {
        let mut values = Vec::new();
        use MayM4::*;
        match &word.0 {
            Word::Single(Shell(WordFragment::Literal(lit))) => {
                values.extend(
                    lit.split_whitespace()
                        .filter_map(|s| (!s.is_empty()).then_some(RValue::Lit(s.to_owned()))),
                );
            }
            Word::Single(Shell(WordFragment::DoubleQuoted(frags))) => {
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
                        _ => (),
                    }
                }
            }
            Word::Single(Shell(WordFragment::Param(Parameter::Var(var)))) => {
                values.push(RValue::Var(var.to_owned(), loc.clone()));
            }
            Word::Single(Shell(WordFragment::Subst(subst))) => match &**subst {
                ParameterSubstitution::Command(cmds) => {
                    let node_id = cmds.first().unwrap().clone();
                    let shell_string = self.recover_content(node_id);
                    let (_, uses) = self.collect_variables_per_top(node_id);
                    values.push(RValue::Shell(
                        shell_string,
                        uses.keys()
                            .map(|name| RValue::Var(name.to_owned(), loc.clone()))
                            .collect(),
                    ));
                }
                _ => (),
            },
            Word::Empty => (),
            _ => todo!(),
        }
        values
    }
}
