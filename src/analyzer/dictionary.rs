//! Structs & Methods for Making Dictionary Instances
use std::collections::HashMap;

use itertools::Itertools;

use super::{
    value_set_analysis::IdentifierDivision,
    location::Location,
    type_inference::DataType,
    variable::{Identifier, ValueExpr},
    Analyzer,
};

/// Represents the operation on the dictionary types
#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) enum DictionaryOperation {
    Read,
    Write,
}

/// Represents the operation on the dictionary types
#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) enum DictionaryKey {
    Lit(String),
    Var(String),
}

impl DictionaryKey {
    pub(crate) fn print(&self) -> String {
        use DictionaryKey::*;
        match self {
            Lit(lit) => format!("\"{}\".to_string()", lit),
            Var(var) => format!("{}.to_string()", var),
        }
    }
}

/// Represents the value assigned to the dictionary
#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) enum DictionaryValue {
    Lit(String),
    Var(String),
    Dict(String, Location),
}

/// Saving the result of dictionary type inference.
#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) struct DictionaryAccess {
    // Tells whether are we reading/writing to the dictionary.
    pub operation: DictionaryOperation,
    // The keys needed to access to the dictionary equivalently as the original script.
    pub keys: Vec<DictionaryKey>,
    // The variable name in the original script.
    pub raw_name: Option<String>,
    // Right-hand-side values writing to the dictionary.
    pub assigned_to: Option<String>,
    // Right-hand-side values writing to the dictionary.
    pub assigned_value: Option<Vec<DictionaryValue>>,
}

/// Represent the newly developped dictionary instance
#[derive(Debug, Clone)]
pub(crate) struct DictionaryInstance {
    // The name of the dictionary instance.
    // It should not collide with any other dictionary instances.
    pub name: String,
    // Represent the behaviors of access to the instance.
    pub accesses: HashMap<Location, DictionaryAccess>,
    // The inferred type of the values
    pub value_type: DataType,
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
    assigned_value: Option<Vec<DictionaryValue>>,
}

#[derive(Debug, Default)]
struct DictionaryInstanceRecipe {
    accesses: HashMap<Location, DictionaryAccessRecipe>,
    name_candidates: Vec<String>,
    confirmed_name: Option<String>,
    value_type: Option<DataType>,
    last_loc: Option<Location>,
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
    strip_underscore(s.replace("@", "").as_str())
}

fn strip_underscore(s: &str) -> String {
    s.split("_").filter(|s| !s.is_empty()).join("_")
}

fn make_dictionary_value(value_expr: &ValueExpr, eval_loc: &Location) -> Vec<DictionaryValue> {
    match value_expr {
        ValueExpr::Lit(lit) => vec![DictionaryValue::Lit(lit.clone())],
        ValueExpr::Var(var, _) => vec![DictionaryValue::Var(var.clone())],
        ValueExpr::Concat(value_exprs) => value_exprs
            .iter()
            .map(|v| make_dictionary_value(v, eval_loc))
            .flatten()
            .collect(),
        v @ ValueExpr::DynName(_) => {
            let ident: Option<Identifier> = v.into();
            let mut loc = eval_loc.clone();
            // FIXME: incorrect.
            loc.order_in_expr = loc.order_in_expr.saturating_sub(1);
            vec![DictionaryValue::Dict(
                // will be replaced with the dictionary name later
                encode_identifier(&ident.unwrap()).0,
                loc.clone(),
            )]
        }
        _ => todo!("Shell commands in eval statements are unsupported"),
    }
}

fn search_dictionary_from_eval_assignment_rhs(
    lhs: &Identifier,
    rhs: &Option<ValueExpr>,
) -> Option<(
    DictId,
    Vec<DictionaryKey>,
    DictionaryOperation,
    Vec<String>,
    Option<String>,
    Option<Vec<DictionaryValue>>,
)> {
    if let Some(rhs) = rhs {
        // FIXME: The cases where two differennt dicts used in a single eval are out of scope.
        // In other words, we are expecting all indirect identifiers in this eval assignment
        // refer to the same dictionary.
        let rhs_as_ident: Option<Identifier> = rhs.into();
        if rhs_as_ident
            .as_ref()
            .is_some_and(|ident| ident.is_indirect())
        {
            let rhs_as_ident = rhs_as_ident.unwrap();
            let dict_id = encode_identifier(&rhs_as_ident);
            let vars = rhs_as_ident.vars().unwrap();
            let keys = vars.into_iter().map(DictionaryKey::Var).collect();
            let op = DictionaryOperation::Read;
            let names = vec![
                // prefer the name created from rhs
                make_dictionary_variable_name(&dict_id),
                make_dictionary_variable_name(&encode_identifier(lhs)),
            ];
            let assigned_to = if let Identifier::Name(var) = lhs {
                Some(var.into())
            } else {
                dbg!(&lhs);
                None
            };

            return Some((dict_id, keys, op, names, assigned_to, None));
        }
    }
    None
}

fn search_dictionary_from_eval_assignment_lhs(
    lhs: &Identifier,
    rhs: &Option<ValueExpr>,
    eval_loc: &Location,
) -> Option<(
    DictId,
    Vec<DictionaryKey>,
    DictionaryOperation,
    Vec<String>,
    Option<String>,
    Option<Vec<DictionaryValue>>,
)> {
    let dict_id = encode_identifier(lhs);
    if lhs.is_indirect() {
        // the dictionary must be on lhs
        let vars = lhs.vars().unwrap();
        let keys = vars.into_iter().map(DictionaryKey::Var).collect();
        let op = DictionaryOperation::Write;
        let names = vec![make_dictionary_variable_name(&dict_id)];
        let assigned_value = if let Some(rhs) = rhs {
            Some(make_dictionary_value(rhs, eval_loc))
        } else {
            None
        };

        Some((dict_id, keys, op, names, None, assigned_value))
    } else {
        None
    }
}

impl Analyzer {
    pub(crate) fn make_dictionary_instances(&mut self) {
        self.dicts.replace(self._make_dictionary_instances());
    }

    fn inspect_eval_assignment(
        &self,
        recipes: &mut HashMap<DictId, DictionaryInstanceRecipe>,
        lhs: &Identifier,
        rhs: &Option<ValueExpr>,
        mut eval_loc: Location,
    ) {
        let _num_vars_in_lhs = lhs.vars().map(|v| v.len()).unwrap_or(0);
        let _num_vars_in_rhs = rhs
            .as_ref()
            .map(|r| r.vars().map(|v| v.len()))
            .flatten()
            .unwrap_or(0);

        // Currently this ordering is determined independently of what is
        // assigned to the non-dictionary variables in the node,
        // so there is a possibility that inconsistencies may arise in
        // situations where particular care must be taken
        // with regard to the order within a node.
        eval_loc.order_in_expr = 0; //num_vars_in_lhs + num_vars_in_rhs;
        for result in [
            search_dictionary_from_eval_assignment_rhs(lhs, rhs),
            search_dictionary_from_eval_assignment_lhs(lhs, rhs, &eval_loc),
        ] {
            if let Some((dict_id, keys, operation, name_candidates, assigned_to, assigned_value)) =
                result
            {
                //assert!(!dict_id.0.is_empty());
                let recipe = recipes.entry(dict_id.clone()).or_default();

                let access = recipe.accesses.entry(eval_loc.clone()).or_default();
                access.operation.replace(operation);
                access.keys.replace(keys);
                access.assigned_to = assigned_to;
                access.assigned_value = assigned_value;
                // add candidates of the dictionary name
                for name_candidate in name_candidates {
                    if !name_candidate.is_empty() {
                        if !recipe.name_candidates.contains(&name_candidate) {
                            recipe.name_candidates.push(name_candidate);
                        }
                    }
                }

                // record latest eval locations for the read-only dictionary
                if recipe
                    .accesses
                    .values()
                    .all(|a| matches!(a.operation, Some(DictionaryOperation::Read)))
                {
                    if let Some(old_loc) = &recipe.last_loc {
                        recipe.last_loc.replace(old_loc.max(&eval_loc).clone());
                    } else {
                        recipe.last_loc.replace(eval_loc.clone());
                    }
                } else {
                    recipe.last_loc = None;
                }
                eval_loc.order_in_expr += 1;
            }
        }
    }

    fn _make_dictionary_instances(&self) -> Vec<DictionaryInstance> {
        let mut recipes: HashMap<DictId, DictionaryInstanceRecipe> = Default::default();
        // inspect analyzed eval statements
        for (identifier, (expr, eval_loc)) in self
            .eval_assigns()
            .iter()
            .flat_map(|(ident, evals)| std::iter::repeat(ident).zip(evals.into_iter()))
        {
            self.inspect_eval_assignment(&mut recipes, identifier, expr, eval_loc.clone());
        }

        // confirm names of dictionaries
        let names = self.confirm_names_of_directories(&mut recipes);

        // enumerate dictionary access
        self.enumerate_dictionary_accesses(&mut recipes);

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
                                // unwrap all optional fields
                                operation: v.operation.unwrap(),
                                keys: v.keys.unwrap(),
                                raw_name: v.raw_name,
                                assigned_to: v.assigned_to,
                                assigned_value: v.assigned_value.map(|vals| {
                                    // replace dict_id with confirmed dictionary name
                                    vals.into_iter()
                                        .map(|v| match v {
                                            DictionaryValue::Dict(id, loc) => {
                                                DictionaryValue::Dict(
                                                    names[&id.into()].clone(),
                                                    loc,
                                                )
                                            }
                                            v => v,
                                        })
                                        .collect()
                                }),
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

    fn confirm_names_of_directories(
        &self,
        recipes: &mut HashMap<DictId, DictionaryInstanceRecipe>,
    ) -> HashMap<DictId, String> {
        let mut confirmed_names: HashMap<String, DictId> = Default::default();
        let mut spare_name_index = 0;
        let name_candidates = recipes
            .iter()
            .map(|(id, r)| (id, &r.name_candidates))
            .collect::<HashMap<_, _>>();
        for (dict_id, name_candidates) in name_candidates
            .into_iter()
            .sorted_by_key(|(_, candidates)| candidates.len())
        {
            let name = {
                let alternative_suffixes = ["", "_map", "_dict"];
                if let Some(unique_name) = alternative_suffixes.into_iter().find_map(|suffix| {
                    name_candidates
                        .iter()
                        .map(|name| {
                            // alternative strategy 1: put suffix for already defined names
                            // e.g. found=no; eval "found_${var}=yes" -> Get a unique name: "found_dict"
                            [name, suffix].concat()
                        })
                        .find(|name| {
                            !confirmed_names.contains_key(name.as_str())
                                && !self.has_definition(name.as_str())
                        })
                }) {
                    // unique dictionary name was found.
                    unique_name
                } else {
                    // alternative strategy 2: default names for anonymous dictionaries
                    // I guess we rarely use this strategy though.
                    let name = format!("dict_{}", spare_name_index);

                    // if such a weird name is already defined, just give up.
                    assert!(!self.has_definition(name.as_str()));

                    spare_name_index += 1;
                    name
                }
            };
            confirmed_names.insert(name, dict_id.clone());
        }
        for (name, dict_id) in confirmed_names.iter() {
            recipes
                .get_mut(dict_id)
                .unwrap()
                .confirmed_name
                .replace(name.to_owned());
        }
        assert!(recipes.values().all(|r| r.confirmed_name.is_some()));
        confirmed_names.into_iter().map(|(k, v)| (v, k)).collect()
    }

    /// returns a map from location to accesses to variable as dictionary
    fn enumerate_dictionary_accesses(
        &self,
        recipes: &mut HashMap<DictId, DictionaryInstanceRecipe>,
    ) {
        for (full_name, divided) in self.divided_vars.as_ref().unwrap().iter() {
            let dict_id = {
                let mut idents = divided
                    .eval_locs
                    .values()
                    .map(|div| encode_identifier(&div.division))
                    .collect::<Vec<_>>();
                // make sure that a divided variable corresponds to exactly one dictionary.
                assert!(idents.iter().all_equal());
                idents.pop().unwrap()
            };
            assert!(!divided.eval_locs.is_empty());
            let mut keys_for_evals = divided
                .eval_locs
                .iter()
                .map(|(_, div)| div.mapping.iter().map(|(_, v)| v).collect::<Vec<_>>());
            let dict_keys = if !keys_for_evals.clone().all_equal() {
                // Detected omission of keys. We need to find what keys are omitted.
                let accesses = &mut recipes.get_mut(&dict_id).unwrap().accesses;
                self.fill_up_omissions_of_dictionary_keys(accesses, &divided.eval_locs)
            } else {
                let keys = keys_for_evals.next().unwrap().clone();
                keys.into_iter()
                    .map(|v| DictionaryKey::Lit(strip_underscore(v)))
                    .collect::<Vec<_>>()
            };

            for def_loc in &divided.def_locs {
                let accesses = &mut recipes.get_mut(&dict_id).unwrap().accesses;
                accesses.insert(
                    def_loc.clone(),
                    DictionaryAccessRecipe {
                        operation: Some(DictionaryOperation::Write),
                        keys: Some(dict_keys.clone()),
                        raw_name: Some(full_name.to_owned()),
                        assigned_to: None,
                        assigned_value: None,
                    },
                );
            }

            for use_loc in &divided.use_locs {
                let accesses = &mut recipes.get_mut(&dict_id).unwrap().accesses;
                accesses.insert(
                    use_loc.clone(),
                    DictionaryAccessRecipe {
                        operation: Some(DictionaryOperation::Read),
                        keys: Some(dict_keys.clone()),
                        raw_name: Some(full_name.to_owned()),
                        assigned_to: None,
                        assigned_value: None,
                    },
                );
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
        division: &HashMap<Location, IdentifierDivision>,
    ) -> Vec<DictionaryKey> {
        // The idea is that there must be a division where a key is evaluated to an empty string.
        let num_keys = division.values().map(|d| d.mapping.len()).max().unwrap();
        // take keys with maximum size as standard
        let vals_without_omission = division
            .values()
            .filter_map(|d| {
                (d.mapping.len() == num_keys)
                    .then_some(d.mapping.iter().map(|(_, v)| v).collect::<Vec<_>>())
            })
            .next()
            .unwrap()
            .clone();
        let omitted_indexes = vals_without_omission
            .iter()
            .enumerate()
            .filter_map(|(pos, v)| v.is_empty().then_some(pos))
            .collect::<Vec<_>>();
        for (eval_loc, div) in division.iter().filter(|(_, d)| d.mapping.len() < num_keys) {
            let mut filled_up_keys = Vec::new();
            let mut div_idx = 0;
            for idx in 0..num_keys {
                let key = if omitted_indexes.contains(&idx) {
                    DictionaryKey::Lit("".into())
                } else {
                    let var = div.mapping[div_idx].0.clone();
                    div_idx += 1;
                    DictionaryKey::Var(var)
                };
                filled_up_keys.push(key);
            }
            accesses
                .get_mut(&eval_loc)
                .unwrap()
                .keys
                .replace(filled_up_keys);
        }
        vals_without_omission
            .into_iter()
            .map(|v| DictionaryKey::Lit(strip_underscore(v)))
            .collect::<Vec<_>>()
    }

    fn infer_dictionary_value_types(
        &self,
        recipes: &mut HashMap<DictId, DictionaryInstanceRecipe>,
    ) {
        for recipe in recipes.values_mut() {
            let mut value_type: Option<DataType> = None;
            for access in recipe.accesses.values_mut() {
                let inferred = self.infer_dictionary_value_type(access);
                if let Some(old) = value_type.clone() {
                    if old.priority() < inferred.priority() {
                        value_type.replace(inferred);
                    }
                } else {
                    value_type.replace(inferred);
                }
            }
            let value_type = value_type.unwrap_or(DataType::Literal);
            recipe.value_type.replace(value_type);
        }
    }

    fn infer_dictionary_value_type(&self, access: &DictionaryAccessRecipe) -> DataType {
        if let Some(raw_name) = &access.raw_name {
            if let Some((_, ty)) = self.get_type_inference_result(raw_name) {
                return ty.clone();
            }
        }

        if let Some(assigned_to) = &access.assigned_to {
            if let Some((_, ty)) = self.get_type_inference_result(assigned_to) {
                return ty.clone();
            }
        }

        DataType::Literal
    }

    pub(crate) fn get_dict(&self, name: &str) -> Option<&DictionaryInstance> {
        self.dicts.as_ref().unwrap().iter().find(|d| d.name == name)
    }

    pub(crate) fn print_dictionary_type(&self, name: &str) -> String {
        let dict = self.get_dict(name).unwrap();
        let num_keys = dict.accesses.values().next().map(|a| a.keys.len()).unwrap();
        let key_type = match num_keys {
            1 => "String".into(),
            _ => format!("({})", std::iter::repeat("String").take(num_keys).join(", ")),
        };
        let value_type = dict.value_type.print();
        format!("HashMap<{}, {}>", key_type, value_type)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn dicitionary_variable_name() {
        let ident = Identifier::Concat(vec![
            Identifier::Name("prefix_".into()),
            Identifier::Indirect("var1".into()),
            Identifier::Indirect("var2".into()),
            Identifier::Name("_suffix".into()),
        ]);
        let dict_id = encode_identifier(&ident);
        assert_eq!(dict_id, DictId("prefix_@_suffix".into()));
        let name = make_dictionary_variable_name(&dict_id);
        assert_eq!(name, "prefix_suffix".to_owned());
    }
}
