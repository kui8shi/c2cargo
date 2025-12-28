use std::collections::{HashMap, HashSet};

use serde::{Deserialize, Serialize};

use super::guard::{Atom, Guard};
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
pub(crate) struct PlatformSupport {
    platform_cfg_vars: HashSet<String>,
    supported_arch: Vec<String>,
    supported_os: Vec<String>,
    alternative_arch: HashMap<String, String>,
    alternative_os: HashMap<String, (String, Option<String>, Option<String>)>,
}

impl Default for PlatformSupport {
    fn default() -> Self {
        Self::new()
    }
}

impl PlatformSupport {
    pub(crate) fn new() -> Self {
        let triplets = serde_json::from_str::<HashMap<String, Triplet>>(TARGET_TRIPLETS_JSON)
            .expect("Failed to parse Reference JSON: target-triplets.json");
        let mut supported_arch = HashSet::new();
        let mut supported_os = HashSet::new();
        for triplet in triplets.into_values() {
            supported_arch.insert(triplet.arch);
            supported_os.insert(triplet.os);
        }
        let supported_arch = {
            let mut v = supported_arch.into_iter().collect::<Vec<_>>();
            v.sort_by_key(|s| s.len());
            v
        };
        let supported_os = {
            let mut v = supported_os.into_iter().collect::<Vec<_>>();
            v.sort_by_key(|s| s.len());
            v
        };
        let alternative_arch = HashMap::from([("i386".into(), "x86".into())]);
        let alternative_os =
            HashMap::from([("mingw".into(), ("windows".into(), Some("gnu".into()), None))]);
        let platform_cfg_vars = HashSet::from([
            // "build".into(),
            // "build_alias".into(),
            // "build_cpu".into(),
            // "build_os".into(),
            // "build_vendor".into(),
            // "target".into(),
            // "target_cpu".into(),
            // "target_os".into(),
            // "target_vendor".into(),
            "host".into(),
            "host_alias".into(),
            // "host_cpu".into(),
            "host_os".into(),
            "host_vendor".into(),
        ]);
        Self {
            platform_cfg_vars,
            supported_arch,
            supported_os,
            alternative_arch,
            alternative_os,
        }
    }

    pub(crate) fn check_supported_platform(&self, guard: &Guard) -> Option<Guard> {
        match guard {
            Guard::N(negated, atom) => match atom {
                Atom::ArchGlob(arch_pattern) => {
                    if let Some(supported) = self
                        .supported_arch
                        .iter()
                        .find(|arch| glob_match(arch_pattern, arch))
                        .map(|arch| Guard::N(*negated, Atom::Arch(arch.clone())))
                    {
                        Some(supported)
                    } else {
                        self.alternative_arch
                            .keys()
                            .find(|arch| glob_match(arch_pattern, arch))
                            .map(|arch| {
                                let arch = self.alternative_arch[arch].clone();
                                Guard::N(*negated, Atom::Arch(arch))
                            })
                    }
                }
                Atom::OsAbiGlob(os_abi_pattern) => {
                    if let Some(supported) = self
                        .supported_os
                        .iter()
                        .find(|os| glob_match(os_abi_pattern, os))
                        .map(|os| Guard::N(*negated, Atom::Os(os.clone())))
                    {
                        Some(supported)
                    } else {
                        self.alternative_os
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
                            })
                    }
                }
                _ => None,
            },
            Guard::And(v) => {
                let v = v
                    .iter()
                    .map(|g| self.check_supported_platform(g))
                    .collect::<Vec<_>>();
                v.iter()
                    .all(|g| g.is_some())
                    .then_some(Guard::make_and(v.into_iter().flatten().collect()))
            }
            Guard::Or(v) => {
                let v = v
                    .iter()
                    .flat_map(|g| self.check_supported_platform(g))
                    .collect::<Vec<_>>();
                (!v.is_empty()).then_some(Guard::make_or(v))
            }
        }
    }

    pub(crate) fn platform_vars(&self) -> &HashSet<String> {
        &self.platform_cfg_vars
    }
}
