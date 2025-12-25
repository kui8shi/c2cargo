use itertools::Itertools;
use std::collections::HashSet;

pub fn enumerate_combinations<T: Clone>(combos: Vec<HashSet<T>>) -> Vec<Vec<T>> {
    combos
        .into_iter()
        .map(|hs| hs.into_iter().collect::<Vec<_>>().into_iter())
        .multi_cartesian_product()
        .collect()
}
