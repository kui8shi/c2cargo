//! Structs & Methods for Making Dictionary Instances
use std::collections::HashMap;

use itertools::Itertools;

use super::{
    type_inference::DataType,
    variable::{Identifier, Location, ValueExpr},
    Analyzer,
};

/// Represents the operation on the dictionary types
#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) enum DictionaryOperation {
    Read,
    Write,
    Append,
}

/// Represents the operation on the dictionary types
#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) enum DictionaryKey {
    Lit(String),
    Var(String),
}

/// Saving the result of dictionary type inference.
#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) struct DictionaryAccess {
    // Tells whether are we reading/writing to the dictionary.
    operation: DictionaryOperation,
    // The keys needed to access to the dictionary equivalently as the original script.
    keys: Vec<DictionaryKey>,
    // The variable name in the original script.
    raw_name: Option<String>,
}

/// Represent the newly developped dictionary instance
#[derive(Debug, Clone)]
pub(crate) struct DictionaryInstance {
    // The name of the dictionary instance.
    // It should not collide with any other dictionary instances.
    name: String,
    // Represent the behaviors of access to the instance.
    accesses: HashMap<Location, DictionaryAccess>,
    // The inferred type of the values
    value_type: DataType,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct DictId(String);

impl From<String> for DictId {
    fn from(value: String) -> Self {
        Self(value)
    }
}

impl Into<String> for DictId {
    fn into(self) -> String {
        self.0
    }
}

#[derive(Debug, Default)]
struct DictionaryAccessRecipe {
    operation: Option<DictionaryOperation>,
    keys: Option<Vec<DictionaryKey>>,
    raw_name: Option<String>,
    assigned_to: Option<String>,
}

#[derive(Debug, Default)]
struct DictionaryInstanceRecipe {
    accesses: HashMap<Location, DictionaryAccessRecipe>,
    name_candidates: Vec<String>,
    confirmed_name: Option<String>,
    value_type: Option<DataType>,
}

fn encode_identifier(ident: &Identifier) -> DictId {
    match ident {
        Identifier::Concat(components) => {
            let mut is_last_var = false;
            let mut encoded_components = Vec::new();
            for component in components.iter() {
                encoded_components.push(match component {
                    Identifier::Name(lit) => {
                        is_last_var = false;
                        lit
                    }
                    Identifier::Indirect(_) if !is_last_var => {
                        is_last_var = true;
                        "@"
                    }
                    _ => "",
                })
            }
            encoded_components.concat()
        }
        Identifier::Indirect(var) => var.to_owned(),
        Identifier::Name(lit) => lit.to_owned(),
    }
    .into()
}

fn make_dictionary_variable_name(dict_id: &DictId) -> String {
    let s: String = dict_id.clone().into();
    s.replace("@", "")
        .split("_")
        .filter(|s| !s.is_empty())
        .join("_")
}

fn inspect_eval_assignment(
    lhs: &Identifier,
    rhs: &Option<ValueExpr>,
) -> (
    DictId,
    DictionaryOperation,
    Vec<DictionaryKey>,
    Option<String>,
    Vec<String>,
) {
    if let Some(rhs_as_ident) = rhs
        .as_ref()
        .and_then(|e| Into::<Option<Identifier>>::into(e))
    {
        let dict_id = encode_identifier(&rhs_as_ident);

        let operation = if lhs.is_indirect() {
            // the dictionary must be on both lhs & rhs
            DictionaryOperation::Append
        } else {
            // the dictionary must be on rhs
            DictionaryOperation::Read
        };

        let vars = rhs_as_ident.vars().unwrap();
        let keys = vars.into_iter().map(DictionaryKey::Var).collect();

        let assigned_to = if let Identifier::Name(var) = lhs {
            Some(var.into())
        } else {
            None
        };

        let name_candidates = vec![
            // prefer the name created from rhs
            make_dictionary_variable_name(&dict_id),
            make_dictionary_variable_name(&encode_identifier(lhs)),
        ];

        (dict_id, operation, keys, assigned_to, name_candidates)
    } else {
        // the dictionary must be on lhs
        let dict_id = encode_identifier(lhs);

        let operation = DictionaryOperation::Write;

        let vars = lhs.vars().unwrap();
        let keys = vars.into_iter().map(DictionaryKey::Var).collect();

        let assigned_to = None;

        let name_candidates = vec![make_dictionary_variable_name(&dict_id)];

        (dict_id, operation, keys, assigned_to, name_candidates)
    }
}

impl Analyzer {
    pub(crate) fn make_dictionary_instances(&self) -> Vec<DictionaryInstance> {
        let mut recipes: HashMap<DictId, DictionaryInstanceRecipe> = Default::default();
        // inspect analyzed eval statements
        for (identifier, (expr, eval_loc)) in self
            .eval_assigns
            .iter()
            .flat_map(|(ident, evals)| std::iter::repeat(ident).zip(evals.into_iter()))
        {
            let (dict_id, operation, keys, assigned_to, name_candidates) =
                inspect_eval_assignment(identifier, expr);
            assert!(!dict_id.0.is_empty());

            let recipe = recipes.entry(dict_id.clone()).or_default();

            let access = recipe.accesses.entry(eval_loc.clone()).or_default();
            access.operation.replace(operation);
            access.keys.replace(keys);
            access.assigned_to = assigned_to;

            // add candidates of the dictionary name
            for candidate in name_candidates {
                if !candidate.is_empty() {
                    if recipe.name_candidates.contains(&candidate) {
                        recipe.name_candidates.push(candidate);
                    }
                }
            }
        }

        // confirm names of dictionaries
        self.confirm_name_of_directories(&mut recipes);

        // enumerate dictionary access
        self.enumerate_dictionary_access(&mut recipes);

        // infer dictionary value types
        self.infer_dictionary_value_types(&mut recipes);

        // make dictionary instances
        recipes
            .into_values()
            .map(|recipe| {
                let accesses = recipe
                    .accesses
                    .into_iter()
                    .map(|(k, v)| {
                        (
                            k,
                            DictionaryAccess {
                                operation: v.operation.unwrap(),
                                keys: v.keys.unwrap(),
                                raw_name: v.raw_name,
                            },
                        )
                    })
                    .collect();

                DictionaryInstance {
                    accesses,
                    name: recipe.confirmed_name.unwrap(),
                    value_type: recipe.value_type.unwrap(),
                }
            })
            .collect()
    }

    fn confirm_name_of_directories(&self, recipes: &mut HashMap<DictId, DictionaryInstanceRecipe>) {
        let mut confirmed_names: HashMap<String, DictId> = Default::default();
        let mut spare_name_index = 0;
        let name_candidates = recipes
            .iter()
            .map(|(id, r)| (id, &r.name_candidates))
            .collect::<HashMap<_, _>>();
        for (key, name_candidates) in name_candidates
            .into_iter()
            .sorted_by_key(|(_, candidates)| candidates.len())
        {
            let name = if !name_candidates.is_empty() {
                if let Some(mut unique_name) = name_candidates
                    .iter()
                    .find(|name| !confirmed_names.contains_key(name.as_str()))
                    .cloned()
                {
                    if self.var_definitions.contains_key(&unique_name) {
                        // alternative strategy 1: "_dict" suffix for already defined names
                        // e.g. eval "found_${var}=yes" -> Get a unique name: "found_dict"
                        unique_name.push_str("_dict");
                    }
                    unique_name
                } else {
                    // alternative strategy 2: "_0" suffix to avoid collisions b/w dictionaries
                    let prefix = name_candidates.first().unwrap();
                    let name = format!("{}_{}", prefix, spare_name_index);
                    spare_name_index += 1;
                    name
                }
            } else {
                // alternative strategy 3: default names for anonymous dictionaries
                let name = format!("dict_{}", spare_name_index);
                spare_name_index += 1;
                name
            };
            confirmed_names.insert(name, key.clone());
        }
        for (name, dict_id) in confirmed_names {
            recipes
                .get_mut(&dict_id)
                .unwrap()
                .confirmed_name
                .replace(name);
        }
        assert!(recipes.values().all(|r| r.confirmed_name.is_some()));
    }

    /// returns a map from location to accesses to variable as dictionary
    fn enumerate_dictionary_access(&self, recipes: &mut HashMap<DictId, DictionaryInstanceRecipe>) {
        for (full_name, divided) in self.divided_vars.iter() {
            let mut idents = divided
                .values()
                .map(|div| encode_identifier(&div.division))
                .collect::<Vec<_>>();
            // make sure that a divided variable corresponds to exactly one dictionary.
            assert!(idents.iter().all_equal());
            let dict_id = idents.pop().unwrap();
            assert!(!divided.is_empty());
            let keys_for_evals = divided
                .iter()
                .map(|(loc, div)| (loc, div.map.values().collect::<Vec<_>>()))
                .collect::<HashMap<&Location, Vec<&String>>>();
            assert!(!keys_for_evals.is_empty());
            let dict_keys = if !keys_for_evals.values().all_equal() {
                // Detected omission of keys. We need to find what keys are omitted.
                let accesses = &mut recipes.get_mut(&dict_id).unwrap().accesses;
                self.fill_up_omissions_of_dictionary_keys(accesses, keys_for_evals)
            } else {
                let keys = keys_for_evals.values().next().unwrap().clone();
                keys.into_iter()
                    .map(|v| DictionaryKey::Lit(v.to_owned()))
                    .collect::<Vec<_>>()
            };
            let def_locs = self.get_all_definition(full_name.as_str(), None);
            let use_locs = self.get_all_usages_before(full_name.as_str(), None);

            if let Some(def_locs) = def_locs {
                for loc in def_locs {
                    let accesses = &mut recipes.get_mut(&dict_id).unwrap().accesses;
                    accesses.insert(
                        loc,
                        DictionaryAccessRecipe {
                            operation: Some(DictionaryOperation::Read),
                            keys: Some(dict_keys.clone()),
                            raw_name: Some(full_name.to_owned()),
                            assigned_to: None,
                        },
                    );
                }
            }
            if let Some(use_locs) = use_locs {
                for loc in use_locs {
                    if let Some(access) = {
                        let mut loc_as_def = loc.clone();
                        loc_as_def.is_left = true;
                        let accesses = &mut recipes.get_mut(&dict_id).unwrap().accesses;
                        accesses.get_mut(&loc_as_def)
                    } {
                        access.operation.replace(DictionaryOperation::Append);
                    } else {
                        let accesses = &mut recipes.get_mut(&dict_id).unwrap().accesses;
                        accesses.insert(
                            loc,
                            DictionaryAccessRecipe {
                                operation: Some(DictionaryOperation::Write),
                                keys: Some(dict_keys.clone()),
                                raw_name: Some(full_name.to_owned()),
                                assigned_to: None,
                            },
                        );
                    }
                }
            }
        }
        assert!(recipes.values().all(|r| r
            .accesses
            .values()
            .all(|a| a.operation.is_some() && a.keys.is_some())));

        assert!(recipes.values().all(|r| r
            .accesses
            .values()
            .map(|a| a.keys.as_ref().unwrap().len())
            .all_equal()));
    }

    fn fill_up_omissions_of_dictionary_keys(
        &self,
        accesses: &mut HashMap<Location, DictionaryAccessRecipe>,
        keys_for_evals: HashMap<&Location, Vec<&String>>,
    ) -> Vec<DictionaryKey> {
        // The idea is that there must be a division where a key is evaluated to an empty string.
        let num_keys = keys_for_evals.values().map(|v| v.len()).max().unwrap();
        // take keys with maximum size as standard
        let keys_without_omission = keys_for_evals
            .values()
            .filter(|v| v.len() == num_keys)
            .next()
            .unwrap()
            .clone();
        let omitted_key_indexes = keys_without_omission
            .iter()
            .enumerate()
            .filter_map(|(pos, key)| key.is_empty().then_some(pos))
            .collect::<Vec<_>>();
        for (eval_loc, mut keys_with_omission) in keys_for_evals
            .into_iter()
            .filter(|(_, v)| v.len() < num_keys)
        {
            let mut filled_up_keys = Vec::new();
            for idx in 0..num_keys {
                let key = if omitted_key_indexes.contains(&idx) {
                    DictionaryKey::Lit("".into())
                } else {
                    DictionaryKey::Var(keys_with_omission.remove(0).clone())
                };
                filled_up_keys.push(key);
            }
            accesses
                .get_mut(eval_loc)
                .unwrap()
                .keys
                .replace(filled_up_keys);
        }
        keys_without_omission
            .into_iter()
            .map(|v| DictionaryKey::Lit(v.to_owned()))
            .collect::<Vec<_>>()
    }

    fn infer_dictionary_value_types(
        &self,
        recipes: &mut HashMap<DictId, DictionaryInstanceRecipe>,
    ) {
        for recipe in recipes.values_mut() {
            let mut value_type = None;
            for access in recipe.accesses.values_mut() {
                let inferred = self.infer_dictionary_value_type(access);
                if DataType::Literal != inferred {
                    // FIXME more refined type merging needed
                    value_type.replace(inferred);
                    break;
                }
            }
            let value_type = value_type.unwrap_or(DataType::Literal);
            recipe.value_type.replace(value_type);
        }
    }

    fn infer_dictionary_value_type(&self, access: &DictionaryAccessRecipe) -> DataType {
        if let Some(raw_name) = &access.raw_name {
            if let Some((_, ty)) = self.inferred_types.get(raw_name) {
                return ty.clone();
            }
        }

        if let Some(assigned_to) = &access.assigned_to {
            if let Some((_, ty)) = self.inferred_types.get(assigned_to) {
                return ty.clone();
            }
        }

        DataType::Literal
    }
}
