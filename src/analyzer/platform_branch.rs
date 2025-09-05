use std::collections::{HashMap, HashSet};

use itertools::Itertools;
use serde::{Deserialize, Serialize};

use super::{
    guard::{Atom, Guard},
    Analyzer,
};
use crate::utils::glob::glob_match;

const TARGET_TRIPLETS_JSON: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/reference/target-triplets.json"
));

#[derive(Debug, Serialize, Deserialize)]
struct Triplet {
    arch: String,
    os: String,
    env: Option<String>,
    abi: Option<String>,
}

#[derive(Debug)]
struct PlatformSupport {
    supported_arch: HashSet<String>,
    supported_os: HashSet<String>,
    alternative_os: HashMap<String, (String, Option<String>, Option<String>)>,
}

impl PlatformSupport {
    fn new() -> Self {
        let triplets = serde_json::from_str::<HashMap<String, Triplet>>(TARGET_TRIPLETS_JSON)
            .expect("Failed to parse Reference JSON: target-triplets.json");
        let mut supported_arch = HashSet::new();
        let mut supported_os = HashSet::new();
        for triplet in triplets.into_values() {
            supported_arch.insert(triplet.arch);
            supported_os.insert(triplet.os);
        }
        let alternative_os =
            HashMap::from([("mingw".into(), ("windows".into(), Some("gnu".into()), None))]);
        Self {
            supported_arch,
            supported_os,
            alternative_os,
        }
    }

    fn check_supported_platform(&self, guard: &Guard) -> Option<Guard> {
        match guard {
            Guard::N(negated, atom) => match atom {
                Atom::ArchGlob(arch_pattern) => self
                    .supported_arch
                    .iter()
                    .find(|arch| glob_match(arch_pattern, arch))
                    .map(|arch| Guard::N(*negated, Atom::Arch(arch.clone()))),
                Atom::OsAbiGlob(os_abi_pattern) => self
                    .supported_os
                    .iter()
                    .find(|os| glob_match(os_abi_pattern, os))
                    .map(|os| Guard::N(*negated, Atom::Os(os.clone())))
                    .or(self
                        .alternative_os
                        .keys()
                        .find(|os_abi| glob_match(os_abi_pattern, os_abi))
                        .map(|os_abi| {
                            let (os, environment, abi) = self.alternative_os[os_abi].clone();
                            let mut guards = vec![Guard::confirmed(Atom::Os(os))];
                            if let Some(e) = environment {
                                guards.push(Guard::confirmed(Atom::Env(e)));
                            }
                            if let Some(a) = abi {
                                guards.push(Guard::confirmed(Atom::Abi(a)));
                            }
                            let guard = if guards.len() > 1 {
                                Guard::make_and(guards)
                            } else {
                                guards.pop().unwrap()
                            };
                            if *negated {
                                guard.negate_whole()
                            } else {
                                guard
                            }
                        })),
                _ => None,
            },
            Guard::And(v) => {
                let mut v = v.iter().map(|g| self.check_supported_platform(g));
                v.all(|g| g.is_some())
                    .then_some(Guard::And(v.flatten().collect()))
            }
            Guard::Or(v) => {
                let v = v
                    .iter()
                    .flat_map(|g| self.check_supported_platform(g))
                    .collect::<Vec<_>>();
                (!v.is_empty()).then_some(Guard::Or(v))
            }
        }
    }
}

impl Analyzer {
    pub fn prune_platform_branch(&mut self) {
        self.blocks_guarded_by_variable("host");
        let blocks = self
            .blocks
            .clone()
            .into_iter()
            .filter(|(_, block)| block.guards.last().is_some_and(|g| is_platform_branch(g)))
            .sorted_by_key(|(_, block)| block.guards.len())
            .map(|(_, block)| block);
        let support = PlatformSupport::new();
        for block in blocks {
            if self.blocks.contains(block.block_id) {
                if self.pool.nodes.contains(block.parent) {
                    let guard = block.guards.last().unwrap();
                    if let Some(guard) = support.check_supported_platform(guard) {
                        let block_id = block.block_id;
                        let block = self.blocks.get_mut(block_id).unwrap();
                        block.guards.pop();
                        block.guards.push(guard);
                    } else {
                        for &child in block.children.iter() {
                            if self.pool.nodes.contains(child) {
                                self.remove_node(child);
                            }
                        }
                    }
                }
            }
        }
    }
}

fn is_platform_branch(guard: &Guard) -> bool {
    match guard {
        Guard::N(_, atom) => match atom {
            Atom::OsAbiGlob(_) | Atom::ArchGlob(_) => true,
            _ => false,
        },
        Guard::And(v) | Guard::Or(v) => v.iter().any(|g| is_platform_branch(g)),
    }
}
