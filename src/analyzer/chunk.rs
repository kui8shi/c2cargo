use crate::analyzer::dictionary::DictionaryOperation;

use super::{
    dictionary::DictionaryAccess, type_inference::DataType, Analyzer, Location, MayM4, NodeId,
    ShellCommand,
};
use itertools::Itertools;
use slab::Slab;
use std::{
    collections::{HashMap, HashSet},
    ops::Not,
};

pub(crate) type ChunkId = usize;

#[derive(Clone, Debug, Default)]
pub(crate) struct ChunkTree {
    id: ChunkId,
    parent: Option<ChunkId>,
    children: Vec<ChunkTree>,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct Scope {
    /// parental chunk, None if global.
    pub parent: Option<ChunkId>,
    /// ID of the chunk that defines the variable first.
    /// None if the variable is environmental (can be given by user).
    pub owner: Option<ChunkId>,
    /// ID of the chunk that "bounds" the variable.
    /// e.g. for var in ...
    pub bound_by: Option<ChunkId>,
    /// IDs of the chunks that writes value to the variable
    pub writers: Vec<ChunkId>,
    /// IDs of the chunks that overwrites the variable
    pub overwriters: Vec<ChunkId>,
    /// IDs of the chunks that read the variable
    pub readers: Vec<ChunkId>,
    /// Record relationships between chunks to appear
    pub post_order: Vec<ChunkId>,
    /// Inferred type for this specific scope.
    /// Set after scope splitting for variables with multiple scopes.
    pub inferred_type: Option<DataType>,
}

impl Scope {
    fn is_global(&self) -> bool {
        self.parent.is_none() && self.owner.is_none() && self.bound_by.is_none()
    }

    fn is_empty(&self) -> bool {
        self.parent.is_none() && self.readers.is_empty() && self.has_no_writers()
    }

    fn has_no_writers(&self) -> bool {
        self.owner.is_none()
            && self.bound_by.is_none()
            && self.writers.is_empty()
            && self.overwriters.is_empty()
    }
}

#[derive(Clone, Debug, Default)]
pub(crate) struct Chunk {
    pub nodes: Vec<NodeId>,
    pub descendant_nodes: HashSet<NodeId>,
    pub chunk_id: ChunkId,
    pub parent: Option<ChunkId>,
    pub children: Vec<ChunkId>,
    pub range: (usize, usize),
    pub io: ChunkIO,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct ChunkIO {
    pub imported: HashMap<String, Vec<Location>>,
    pub exported: HashMap<String, Vec<Location>>,
    pub bound: HashSet<String>,
    pub dictionaries: HashMap<String, HashMap<Location, DictionaryAccess>>,
    pub arg_vars: HashMap<String, Vec<Location>>,
}

impl Analyzer {
    pub(crate) fn get_scopes(&self, var_name: &str) -> Option<&Vec<Scope>> {
        self.var_scopes.as_ref().unwrap().get(var_name)
    }

    pub(crate) fn get_chunk_id(&self, node_id: NodeId) -> Option<ChunkId> {
        self.get_node(node_id).and_then(|n| n.info.chunk_id)
    }

    /// Check if any node in a chunk is related to any node within a window of nodes.
    /// Return the index (not NodeId) of the last related window node.
    fn are_nodes_related_with_window(
        &self,
        chunk: &[NodeId],
        window_nodes: &[NodeId],
    ) -> Option<usize> {
        for &chunk_node in chunk {
            for (i, &window_node) in window_nodes.iter().enumerate().rev() {
                if self.are_nodes_related(chunk_node, window_node) {
                    return Some(i);
                }
            }
        }
        None
    }

    /// Check if two nodes are related for chunk fusing.
    /// Nodes are related if one depends on the other through variable dependencies.
    fn are_nodes_related(&self, node1_id: NodeId, node2_id: NodeId) -> bool {
        let node1_defs = self
            .collect_descendant_nodes_per_node(node1_id, true, true)
            .into_iter()
            .map(|nid| {
                let info = &self.get_node(nid).unwrap().info;
                // let parent = info.parent.clone();
                info.definitions
                    .keys()
                    .filter(|key| !self.fixed.contains_key(key.as_str()))
            })
            .flatten()
            .collect::<HashSet<_>>();
        let node2_uses = self
            .collect_descendant_nodes_per_node(node2_id, true, true)
            .into_iter()
            .map(|nid| {
                let info = &self.get_node(nid).unwrap().info;
                // let parent = info.parent.clone();
                info.usages.keys()
            })
            .flatten()
            .collect::<HashSet<_>>();
        !node1_defs.is_disjoint(&node2_uses)
    }

    /// Check if a node is an assignment statement.
    fn is_assignment(&self, node_id: NodeId) -> bool {
        if let Some(node) = self.pool.get(node_id) {
            matches!(node.cmd.0, MayM4::Shell(ShellCommand::Assignment(_, _)))
        } else {
            false
        }
    }

    /// Perform node fusing with speculative lookahead window.
    /// When window > 0, speculatively adds next `window` nodes and reverts if no relations found.
    /// When disrespect_assignment is true, assignment nodes are looked through without consuming window depth.
    pub(crate) fn construct_chunks(&mut self, window: Option<usize>, disrespect_assignment: bool) {
        self.chunks.clear();
        let window = window.unwrap_or(0);
        let mut current_chunk = Vec::new();
        let mut i = 0;
        while i < self.top_ids.len() {
            let next_id = self.top_ids[i];

            if current_chunk.is_empty() {
                // Start a new chunk
                current_chunk.push(next_id);
            } else {
                let is_flattened = self.get_node(next_id).unwrap().info.is_flattened_node();

                // Check if next node is related to any node in the current chunk
                let is_related_to_chunk = current_chunk
                    .iter()
                    .any(|&nid| self.are_nodes_related(nid, next_id));

                if is_flattened {
                    // Flattened - cut here and start new chunk
                    if !current_chunk.is_empty() {
                        self.add_chunk(current_chunk.clone());
                        current_chunk.clear();
                    }
                    current_chunk.push(next_id);
                } else if is_related_to_chunk {
                    // Fuse with current chunk
                    current_chunk.push(next_id);
                } else if window > 0 || disrespect_assignment {
                    // Try speculative lookahead with optional assignment skipping
                    let mut lookahead_nodes = Vec::new();
                    let mut j = i;
                    let mut remaining_window = window;
                    let chunk_parent = self
                        .pool
                        .get(*current_chunk.first().unwrap())
                        .map(|n| n.info.parent);

                    // Collect lookahead nodes, skipping assignments if disrespect_assignment is true
                    while j < self.top_ids.len()
                        && (remaining_window > 0
                            || (disrespect_assignment && self.is_assignment(self.top_ids[j])))
                    {
                        let node_id = self.top_ids[j];

                        // Check if this node has the same parent as the chunk
                        let node_parent = self.pool.get(node_id).map(|n| n.info.parent);
                        if chunk_parent != node_parent {
                            break; // Different parent, stop lookahead
                        }

                        lookahead_nodes.push(node_id);

                        // Only consume window depth for non-assignments or when not disrespecting assignments
                        if !(disrespect_assignment && self.is_assignment(node_id)) {
                            if remaining_window > 0 {
                                remaining_window -= 1;
                            } else {
                                break;
                            }
                        }

                        j += 1;
                    }

                    if let Some(last_related_idx) =
                        self.are_nodes_related_with_window(&current_chunk, &lookahead_nodes)
                    {
                        // Found relation within lookahead - add all lookahead nodes to chunk
                        current_chunk.extend(lookahead_nodes[..=last_related_idx].iter());
                        i += last_related_idx; // Skip ahead (will be incremented at loop end)
                    } else {
                        // No relation found in lookahead - cut here and start new chunk
                        if !current_chunk.is_empty() {
                            self.add_chunk(current_chunk.clone());
                            current_chunk.clear();
                        }
                        current_chunk.push(next_id);
                    }
                } else {
                    // No window - cut here and start new chunk
                    if !current_chunk.is_empty() {
                        self.add_chunk(current_chunk.clone());
                        current_chunk.clear();
                    }
                    current_chunk.push(next_id);
                }
            }
            i += 1;
        }

        // Add the last chunk if not empty
        if !current_chunk.is_empty() {
            self.add_chunk(current_chunk);
        }
    }

    fn add_chunk(&mut self, nodes: Vec<NodeId>) -> ChunkId {
        let parent = self
            .get_node(*nodes.first().unwrap())
            .unwrap()
            .info
            .parent
            .and_then(|parent| self.get_chunk_id(parent));
        let range = (
            self.get_node(*nodes.first().unwrap())
                .unwrap()
                .range_start()
                .unwrap(),
            self.get_node(*nodes.last().unwrap())
                .unwrap()
                .range_end()
                .unwrap(),
        );
        let descendant_nodes = nodes
            .iter()
            .flat_map(|id| self.collect_descendant_nodes_per_node(*id, true, true))
            .collect::<HashSet<_>>();
        let new_chunk_id = self.chunks.insert(Chunk {
            nodes: nodes.to_vec(),
            descendant_nodes: descendant_nodes.clone(),
            parent,
            range,
            ..Default::default()
        });
        self.chunks[new_chunk_id].chunk_id = new_chunk_id;
        self.examine_chunk_io(new_chunk_id);
        for id in descendant_nodes.iter() {
            let info = &mut self.get_node_mut(*id).unwrap().info;
            info.chunk_id.replace(new_chunk_id);
            info.is_chunk_top.replace(false);
        }
        for id in nodes.iter() {
            let info = &mut self.get_node_mut(*id).unwrap().info;
            info.is_chunk_top.replace(true);
        }
        if let Some(id) = parent {
            self.chunks[id].children.push(new_chunk_id)
        }
        debug_assert!(self.verify_relationships_between_chunk_and_top_nodes());
        new_chunk_id
    }

    fn verify_relationships_between_chunk_and_top_nodes(&self) -> bool {
        self.pool
            .nodes
            .iter()
            .filter_map(|(_, n)| {
                if n.info.is_chunk_top_node() {
                    Some((n.info.node_id, n.info.chunk_id.unwrap()))
                } else {
                    None
                }
            })
            .all(|(nid, cid)| self.chunks.get(cid).unwrap().nodes.contains(&nid))
    }

    /// enumerate out-of-scope variables
    fn examine_chunk_io(&mut self, chunk_id: ChunkId) {
        let chunk_start_loc = {
            let first_id = *self.chunks[chunk_id].nodes.first().unwrap();
            self.get_location_of_node_start(first_id)
        };
        let chunk_end_loc = {
            let last_id = *self.chunks[chunk_id].nodes.last().unwrap();
            self.get_location_of_node_end(last_id)
        };

        // Collect all variables defined within the chunk
        let mut chunk_defines = HashMap::new();
        let mut chunk_uses = HashMap::new();
        let mut bound = HashSet::new();

        for &id in &self.chunks[chunk_id].nodes {
            // Get variables from all descendant nodes in the chunk
            let (defines, uses) = self.collect_variables(id);
            self.extend_var_maps(&mut chunk_defines, defines.into_iter());
            self.extend_var_maps(&mut chunk_uses, uses.into_iter());

            bound.extend(
                self.collect_descendant_nodes_per_node(id, true, false)
                    .into_iter()
                    .filter(|id| {
                        self.get_children(*id).is_some_and(|children| {
                            children
                                .iter()
                                .any(|id| self.get_node(*id).is_some_and(|n| n.info.is_top_node()))
                        })
                    })
                    .flat_map(|id| self.get_node(id).unwrap().info.bounds.keys())
                    .cloned(),
            );
        }

        // Helper function to check if a variable is always defined inside this chunk
        let is_always_defined_inside_chunk = |var_name: &String, use_locs: &[Location]| -> bool {
            use_locs.iter().all(|use_loc| {
                self.get_dominant_definition(var_name.as_str(), use_loc.node_id)
                    .is_some_and(|dominant_loc| chunk_start_loc <= dominant_loc)
            })
        };

        // Imported variables: used in chunk but not defined in chunk
        let imported: HashMap<String, Vec<Location>> = chunk_uses
            .clone()
            .into_iter()
            .filter(|(var, locs)| {
                // dictionaries will be global but we don't handle here
                !self
                    .divided_vars
                    .as_ref()
                    .unwrap()
                    .get(var.as_str())
                    .is_some_and(|div| {
                        locs.iter()
                            .any(|loc| div.def_locs.contains(loc) || div.use_locs.contains(loc))
                    })
            })
            .filter(|(var, _)| {
                // build option related variables are not handled here
                !self
                    .build_option_info()
                    .arg_var_to_option_name
                    .contains_key(var)
            })
            .filter(|(var, _)| !self.platform_support.platform_vars().contains(var))
            .filter_map(|(var, use_locs)| {
                is_always_defined_inside_chunk(&var, &use_locs)
                    .not()
                    .then_some((var, use_locs))
            })
            .collect();

        // Helper function to check if a variable has been used outside this chunk
        let has_been_used_outside_chunk = |var_name: &String| -> bool {
            let is_used_directly = self.get_usage(var_name).is_some_and(|use_locs| {
                use_locs
                    .iter()
                    .sorted()
                    .filter(|use_loc| chunk_end_loc <= **use_loc)
                    .any(|use_loc| {
                        self.get_dominant_definition(var_name, use_loc.node_id)
                            .is_none_or(|dominant_loc| dominant_loc < chunk_end_loc)
                    })
            });

            let is_used_indirectly = self
                .get_indirect_usage(var_name)
                .is_some_and(|locs| locs.iter().any(|loc| *loc >= chunk_end_loc));

            let is_substitued = self.is_substituted(var_name);

            is_used_directly || is_used_indirectly || is_substitued
        };

        // Exported variables: defined in chunk and used outside the chunk
        let exported: HashMap<String, Vec<Location>> = chunk_defines
            .clone()
            .into_iter()
            .filter(|(var, locs)| {
                !self
                    .divided_vars
                    .as_ref()
                    .unwrap()
                    .get(var.as_str())
                    .is_some_and(|div| {
                        locs.iter()
                            .all(|loc| div.def_locs.contains(loc) || div.use_locs.contains(loc))
                    })
            })
            .filter(|(var, _)| {
                !self
                    .build_option_info()
                    .arg_var_to_option_name
                    .contains_key(var)
            })
            .filter(|(var, _)| !self.platform_support.platform_vars().contains(var))
            .filter_map(|(var_name, def_locs)| {
                has_been_used_outside_chunk(&var_name).then_some((var_name, def_locs))
            })
            .collect();

        let dictionaries = self
            .dicts
            .as_ref()
            .unwrap()
            .iter()
            .filter_map(|dictionary_instance| {
                let accesses = dictionary_instance
                    .accesses
                    .clone()
                    .into_iter()
                    .filter(|(loc, _)| {
                        self.chunks[chunk_id]
                            .descendant_nodes
                            .contains(&loc.node_id)
                    })
                    .collect::<HashMap<_, _>>();
                accesses
                    .is_empty()
                    .not()
                    .then_some((dictionary_instance.name.clone(), accesses))
            })
            .collect();

        let arg_vars = chunk_uses
            .into_iter()
            .filter(|(var, _)| {
                self.build_option_info()
                    .arg_var_to_option_name
                    .contains_key(var.as_str())
            })
            .collect();

        self.chunks.get_mut(chunk_id).unwrap().io = ChunkIO {
            imported,
            exported,
            bound,
            dictionaries,
            arg_vars,
        };
    }

    pub(crate) fn cut_variable_scopes_chunkwise(&mut self) {
        assert!(!self.chunks.is_empty());
        self.var_scopes.replace(Default::default());

        let visible_vars = self
            .chunks
            .iter()
            .flat_map(|(id, c)| {
                c.io.imported
                    .keys()
                    .chain(c.io.exported.keys())
                    .chain(c.io.bound.iter())
                    .zip(std::iter::repeat(id))
            })
            .fold(HashMap::new(), |mut acc, (k, v)| {
                acc.entry(k.to_owned())
                    .or_insert_with(HashSet::new)
                    .insert(v);
                acc
            });
        for (var, cids) in visible_vars.iter() {
            if self
                .build_option_info()
                .arg_var_to_option_name
                .contains_key(var.as_str())
            {
                continue;
            }
            if self
                .build_option_info()
                .arg_var_to_option_name
                .contains_key(var.as_str())
            {
                continue;
            }
            let cids = cids
                .iter()
                .sorted_by_key(|id| self.chunks[**id].range.0)
                .cloned()
                .collect::<Vec<_>>();
            let mut current_scope = Scope::default();
            for &cid in cids.iter().rev() {
                let chunk = &self.chunks[cid];
                let chunk_guards_size = self.get_guards(chunk.nodes[0]).len();
                let is_imported = chunk.io.imported.contains_key(var.as_str());
                let is_exported = chunk.io.exported.contains_key(var.as_str());
                let is_bound = chunk.io.bound.contains(var.as_str());

                match (is_imported, is_exported, is_bound) {
                    (true, true, false) => {
                        current_scope.overwriters.push(cid);
                    }
                    (true, false, false) => {
                        current_scope.readers.push(cid);
                    }
                    (false, true, false) => {
                        if chunk
                            .io
                            .exported
                            .get(var.as_str())
                            .unwrap()
                            .iter()
                            .all(|def_loc| {
                                let is_propagated = |loc: &Location| -> Option<&Location> {
                                    self.get_parent(loc.node_id).and_then(|parent| {
                                        self.get_propagated_definition(var.as_str()).and_then(
                                            |prop_locs| {
                                                prop_locs
                                                    .iter()
                                                    .find(|prop_loc| prop_loc.node_id == parent)
                                            },
                                        )
                                    })
                                };
                                // calculate the size of guards in the definition location
                                let mut cur = def_loc;
                                let mut def_loc_guards_size =
                                    self.get_guards(def_loc.node_id).len();
                                while let Some(propagated_loc) = is_propagated(cur) {
                                    // if the definition is propagated to the parent node,
                                    // we should recaluclate the size of guards.
                                    def_loc_guards_size =
                                        self.get_guards(propagated_loc.node_id).len();
                                    cur = propagated_loc;
                                }
                                def_loc_guards_size > chunk_guards_size
                            })
                        {
                            // Turns out the variable to be defined **conditionally** in the chunk.
                            current_scope.overwriters.push(cid);
                        } else if self.is_substituted(&var) {
                            // the variable will be exported to the outside of configure.ac,
                            // therefore it's scope is global.
                            current_scope.writers.push(cid);
                        } else {
                            // we try to minimize the scope by considering the common parental chunk.
                            let mut common_parent = self.get_parental_chunk_sequence(cid);
                            for other in current_scope
                                .overwriters
                                .iter()
                                .chain(current_scope.readers.iter())
                            {
                                common_parent = take_common_chunk_sequence(
                                    &common_parent,
                                    &self.get_parental_chunk_sequence(*other),
                                );
                            }
                            if common_parent.is_empty() {
                                current_scope.writers.push(cid);
                            } else {
                                current_scope.parent = common_parent.last().cloned();
                                current_scope.owner.replace(cid);
                                self.add_chunkwise_scope(var.as_str(), current_scope);
                                // the scope starts by global.
                                current_scope = Scope::default();
                            }
                        }
                    }
                    (false, false, true) => {
                        // bound in a loop and used exclusively within the chunk
                        let parents = self.get_parental_chunk_sequence(cid);
                        current_scope.bound_by.replace(cid);
                        current_scope.parent = parents.last().cloned();
                        self.add_chunkwise_scope(var, current_scope);
                        current_scope = Scope::default();
                    }
                    (false, true, true) => {
                        // bound in a loop and exported outside the chunk
                        // it's a strange but legal pattern seen in shell scripts
                        // where all variables including bound one are globally scoped.
                        current_scope.owner.replace(cid);
                        current_scope.bound_by.replace(cid);
                        // we try to minimize the scope by considering the common parental chunk.
                        let mut common_parent = self.get_parental_chunk_sequence(cid);
                        for other in current_scope
                            .overwriters
                            .iter()
                            .chain(current_scope.readers.iter())
                        {
                            common_parent = take_common_chunk_sequence(
                                &common_parent,
                                &self.get_parental_chunk_sequence(*other),
                            );
                        }
                        current_scope.parent = common_parent.last().cloned();
                        self.add_chunkwise_scope(var, current_scope);
                        current_scope = Scope::default();
                    }
                    _ => unimplemented!("unable to calculate scopes of variable: {}", var),
                }
            }
            if !current_scope.overwriters.is_empty()
                || !current_scope.readers.is_empty()
                || self.is_substituted(&var)
            {
                if let Some(may_first_def) = current_scope.writers.pop() {
                    if current_scope
                        .writers
                        .iter()
                        .chain(current_scope.readers.iter())
                        .chain(current_scope.overwriters.iter())
                        .all(|may_follow| {
                            self.chunks[may_first_def].range.0 < self.chunks[*may_follow].range.0
                        })
                    {
                        current_scope.owner.replace(may_first_def);
                    } else {
                        current_scope.writers.push(may_first_def);
                    }
                }
                self.add_chunkwise_scope(var.as_str(), current_scope);
            }
        }
        for scopes in self.var_scopes.as_mut().unwrap().values_mut() {
            scopes.reverse();
        }
        self.reinfer_types_for_multiscope_vars();
    }

    fn reinfer_types_for_multiscope_vars(&mut self) {
        let var_scopes = self.var_scopes.as_ref().unwrap();
        let multiscope_vars: Vec<String> = var_scopes
            .iter()
            .filter(|(_, scopes)| scopes.len() > 1)
            .map(|(name, _)| name.clone())
            .collect();

        for var_name in multiscope_vars {
            let scopes = self.var_scopes.as_ref().unwrap().get(&var_name).unwrap();
            let num_scopes = scopes.len();
            for scope_idx in 0..num_scopes {
                let scope = &self.var_scopes.as_ref().unwrap()[&var_name][scope_idx];
                let scope_type = self.infer_type_for_scope(&var_name, scope);
                self.var_scopes
                    .as_mut()
                    .unwrap()
                    .get_mut(&var_name)
                    .unwrap()[scope_idx]
                    .inferred_type = Some(scope_type);
            }
        }
    }

    fn infer_type_for_scope(&self, var_name: &str, scope: &Scope) -> DataType {
        let related_chunks: Vec<ChunkId> = [scope.owner, scope.bound_by, scope.parent]
            .into_iter()
            .flatten()
            .chain(scope.writers.iter().copied())
            .chain(scope.overwriters.iter().copied())
            .chain(scope.readers.iter().copied())
            .collect();

        for &cid in &related_chunks {
            let chunk = &self.chunks[cid];
            for (dict_name, accesses) in chunk.io.dictionaries.iter() {
                for (_loc, access) in accesses.iter() {
                    if access.assigned_to.as_deref() == Some(var_name) {
                        if let Some(dict_info) = self.get_dict(dict_name.as_str()) {
                            return dict_info.value_type.clone();
                        }
                    }
                }
            }
        }

        self.get_inferred_type(var_name)
    }

    fn add_chunkwise_scope(&mut self, var: &str, mut scope: Scope) {
        scope.writers.sort_by_key(|cid| self.chunks[*cid].range.0);
        scope
            .overwriters
            .sort_by_key(|cid| self.chunks[*cid].range.0);
        scope.readers.sort_by_key(|cid| self.chunks[*cid].range.0);
        scope.post_order = self.calculate_chunk_post_order(&scope);
        self.var_scopes
            .as_mut()
            .unwrap()
            .entry(var.to_owned())
            .or_default()
            .push(scope);
    }

    fn calculate_chunk_post_order(&self, scope: &Scope) -> Vec<ChunkId> {
        // Identify all relevant nodes (scope IDs + all their ancestors).
        let mut relevant_nodes = HashSet::new();
        let initial_cids = scope
            .owner
            .iter()
            .chain(scope.writers.iter())
            .chain(scope.overwriters.iter())
            .chain(scope.readers.iter())
            .chain(scope.bound_by.iter());

        for &cid in initial_cids {
            let mut curr = Some(cid);
            while let Some(id) = curr {
                // If we insert a node that was already present, we know its ancestors
                // are also already present, so we can stop climbing.
                if !relevant_nodes.insert(id) {
                    break;
                }
                curr = self.chunks[id].parent;
            }
        }

        if relevant_nodes.is_empty() {
            return Vec::new();
        }

        // Find the roots of the forest to start traversal.
        // Since we climbed to the very top, these are nodes in our set with no parent.
        let mut roots: Vec<ChunkId> = relevant_nodes
            .iter()
            .filter(|&&id| self.chunks[id].parent.is_none())
            .cloned()
            .collect();

        // Sort roots by range start to ensure processing order matches file order.
        roots.sort_by_key(|&id| self.chunks[id].range.0);

        // Perform DFS restricted to the relevant_nodes set.
        let mut result = Vec::with_capacity(relevant_nodes.len());

        // We use a recursive helper that utilizes the existing `chunk.children` structure.
        fn dfs(
            current_id: ChunkId,
            chunks: &Slab<Chunk>,
            relevant_mask: &HashSet<ChunkId>,
            result: &mut Vec<ChunkId>,
        ) {
            let chunk = &chunks[current_id];

            // Visit children first (Post-Order)
            for &child_id in &chunk.children {
                // Only traverse into children that are part of our relevant set.
                if relevant_mask.contains(&child_id) {
                    dfs(child_id, chunks, relevant_mask, result);
                }
            }

            // Visit self
            result.push(current_id);
        }

        for root in roots {
            dfs(root, &self.chunks, &relevant_nodes, &mut result);
        }

        result
    }
    fn get_parental_chunk_sequence(&self, chunk_id: ChunkId) -> Vec<ChunkId> {
        let mut ret = Vec::new();
        let mut current = chunk_id;
        while let Some(parent) = self.chunks[current].parent {
            ret.push(parent);
            current = parent;
        }
        ret.reverse();
        ret
    }

    pub(crate) fn construct_chunk_skeletons(&mut self) {
        let mut chunk_skeletons: HashMap<ChunkId, FunctionSkeleton> = self
            .chunks
            .iter()
            .map(|(cid, _)| (cid, Default::default()))
            .collect();
        for (var, scopes) in self.var_scopes.as_ref().unwrap().iter() {
            for scope in scopes {
                if let Some(cid) = scope.owner.as_ref() {
                    let pos = scope.post_order.iter().position(|id| id == cid).unwrap();
                    let is_mut = scope.post_order[pos..]
                        .iter()
                        .any(|id| scope.writers.contains(id) || scope.overwriters.contains(id));
                    let ty = self.get_inferred_type_for_scope(var, scope);
                    chunk_skeletons
                        .get_mut(cid)
                        .unwrap()
                        .return_to_bind
                        .entry(var.to_owned())
                        .and_modify(|(existing_mut, _)| *existing_mut = *existing_mut || is_mut)
                        .or_insert((is_mut, ty));
                } else if let Some(cid) = scope.bound_by.as_ref() {
                    let pos = scope.post_order.iter().position(|id| id == cid).unwrap();
                    let is_mut = scope.post_order[pos..]
                        .iter()
                        .any(|id| scope.writers.contains(id) || scope.overwriters.contains(id));
                    let ty = self.get_inferred_type_for_scope(var, scope);
                    chunk_skeletons
                        .get_mut(cid)
                        .unwrap()
                        .bound_in_loop
                        .entry(var.to_owned())
                        .and_modify(|(existing_mut, _)| *existing_mut = *existing_mut || is_mut)
                        .or_insert((is_mut, ty));
                } else if let Some(cid) = scope.parent.as_ref() {
                    let pos = scope.post_order.iter().position(|id| id == cid).unwrap();
                    let is_mut = scope.post_order[pos..]
                        .iter()
                        .any(|id| scope.writers.contains(id) || scope.overwriters.contains(id));
                    let ty = self.get_inferred_type_for_scope(var, scope);
                    chunk_skeletons
                        .get_mut(cid)
                        .unwrap()
                        .declared
                        .entry(var.to_owned())
                        .and_modify(|(existing_mut, _)| *existing_mut = *existing_mut || is_mut)
                        .or_insert((is_mut, ty));
                }
                for cid in scope.writers.iter() {
                    let current = chunk_skeletons.get_mut(cid).unwrap();
                    if !current.return_to_bind.is_empty() || current.return_to_overwrite.is_some() {
                        let ty = self.get_inferred_type_for_scope(var, scope);
                        current
                            .args
                            .entry(var.to_owned())
                            .and_modify(|(existing_mut, _)| *existing_mut = true)
                            .or_insert((true, ty));
                    } else {
                        current.return_to_overwrite.replace((
                            var.to_owned(),
                            self.get_inferred_type_for_scope(var, scope),
                        ));
                    }
                }
                for cid in scope.overwriters.iter() {
                    let ty = self.get_inferred_type_for_scope(var, scope);
                    chunk_skeletons
                        .get_mut(cid)
                        .unwrap()
                        .args
                        .entry(var.to_owned())
                        .and_modify(|(existing_mut, _)| *existing_mut = true)
                        .or_insert((true, ty));
                }
                for cid in scope.readers.iter() {
                    let ty = self.get_inferred_type_for_scope(var, scope);
                    chunk_skeletons
                        .get_mut(cid)
                        .unwrap()
                        .args
                        .entry(var.to_owned())
                        .and_modify(|(existing_mut, _)| *existing_mut = *existing_mut || false)
                        .or_insert((false, ty));
                }
            }
        }

        // rust's syntax limitation: return_to_bind and return_to_overwrite are mutually exclusive.
        // if both are not empty move return_to_overwrite to args
        for (_, sk) in chunk_skeletons.iter_mut() {
            if !sk.return_to_bind.is_empty() && sk.return_to_overwrite.is_some() {
                let (var, ty) = sk.return_to_overwrite.take().unwrap();
                sk.args
                    .entry(var)
                    .and_modify(|(existing_mut, _)| *existing_mut = true)
                    .or_insert((true, ty));
            }
        }

        for (cid, chunk) in self.chunks.iter() {
            for (name, accesses) in chunk.io.dictionaries.iter() {
                let is_mut = accesses
                    .values()
                    .any(|a| matches!(a.operation, DictionaryOperation::Write));
                chunk_skeletons
                    .get_mut(&cid)
                    .unwrap()
                    .maps
                    .entry(name.clone())
                    .and_modify(|existing_mut| *existing_mut = *existing_mut || is_mut)
                    .or_insert(is_mut);
            }
        }

        for (_, top_level_chunk) in self
            .chunks
            .iter()
            .filter(|(_, c)| c.parent.is_none() && !c.children.is_empty())
        {
            // collect children chunks in post order
            let mut stack = top_level_chunk.children.clone();
            let mut post_order = Vec::new();
            while let Some(child) = stack.pop() {
                stack.extend(self.chunks[child].children.clone());
                post_order.push(child);
            }
            // propagate variables from child to parent
            while let Some(child_cid) = post_order.pop() {
                if let Some(parent_cid) = self.chunks.get(child_cid).unwrap().parent {
                    let vars_within_parent_scope = self
                        .var_scopes
                        .as_ref()
                        .unwrap()
                        .iter()
                        .filter_map(|(var, scopes)| {
                            scopes
                                .iter()
                                .any(|s| {
                                    // check if the var is within the parent chunk's scope
                                    s.parent == Some(parent_cid)            // not used outside of the parent
                                        || s.bound_by == Some(parent_cid)   // 'for var in ...'
                                        || s.owner == Some(parent_cid) // defined by the parent and used outside later
                                })
                                .then_some(var.to_owned())
                        })
                        .collect::<HashSet<_>>();
                    let sk = chunk_skeletons.get(&child_cid).unwrap();
                    let parent = chunk_skeletons.get(&parent_cid).unwrap();
                    // check new propagation: collect args that need to pass through
                    let args_propagation: Vec<_> = sk
                        .args
                        .iter()
                        .chain(sk.pass_through_args.iter())
                        .filter(|(name, _)| {
                            !parent.return_to_bind.contains_key(*name)
                                && !vars_within_parent_scope.contains(*name)
                        })
                        .map(|(name, (is_mut, ty))| {
                            if parent.args.contains_key(name) {
                                // propagate mutability to the arg
                                (name.clone(), Some(*is_mut), None, ty.clone())
                            } else {
                                // propagate mutability to the pass through arg
                                (name.clone(), None, Some(*is_mut), ty.clone())
                            }
                        })
                        .collect();
                    let maps_propagation: Vec<_> = sk
                        .maps
                        .iter()
                        .chain(sk.pass_through_maps.iter())
                        .map(|(name, is_mut)| {
                            if parent.maps.contains_key(name) {
                                // propagate mutability to the map
                                (name.clone(), Some(*is_mut), None)
                            } else {
                                // propagate mutability to the pass through map
                                (name.clone(), None, Some(*is_mut))
                            }
                        })
                        .collect();
                    let return_propagation: Vec<_> = sk
                        .return_to_bind
                        .iter()
                        .filter(|(name, _)| !vars_within_parent_scope.contains(*name))
                        .map(|(name, (is_mut, ty))| (name.clone(), (*is_mut, ty.clone())))
                        .collect();
                    // update the parent with mutability OR-ing
                    let parent = chunk_skeletons.get_mut(&parent_cid).unwrap();
                    for (name, is_arg_mut, is_pass_through_arg_mut, ty) in args_propagation {
                        if let Some(is_mut) = is_arg_mut {
                            parent.args.entry(name).and_modify(|(existing_mut, _)| {
                                *existing_mut = *existing_mut || is_mut
                            });
                        } else if let Some(is_mut) = is_pass_through_arg_mut {
                            parent
                                .pass_through_args
                                .entry(name)
                                .and_modify(|(existing_mut, _)| {
                                    *existing_mut = *existing_mut || is_mut
                                })
                                .or_insert((is_mut, ty));
                        }
                    }
                    for (name, is_map_mut, is_pass_through_map_mut) in maps_propagation {
                        if let Some(is_mut) = is_map_mut {
                            parent
                                .maps
                                .entry(name)
                                .and_modify(|existing_mut| *existing_mut = *existing_mut || is_mut);
                        } else if let Some(is_mut) = is_pass_through_map_mut {
                            parent
                                .pass_through_maps
                                .entry(name)
                                .and_modify(|existing_mut| *existing_mut = *existing_mut || is_mut)
                                .or_insert(is_mut);
                        }
                    }
                    for (name, (is_mut, ty)) in return_propagation {
                        parent
                            .return_to_bind
                            .entry(name)
                            .and_modify(|(existing_mut, _)| *existing_mut = *existing_mut || is_mut)
                            .or_insert((is_mut, ty));
                    }
                }
            }
        }
        self.chunk_skeletons.replace(chunk_skeletons);
    }
}

#[derive(Debug, Clone, Default)]
pub(crate) struct FunctionSkeleton {
    /// map of argument name to (mutability, type)
    pub args: HashMap<String, (bool, DataType)>,
    /// map of dictionary name to mutability
    pub maps: HashMap<String, bool>,
    /// map of variable name to (mutability, type)
    pub declared: HashMap<String, (bool, DataType)>,
    /// map of variable name to (mutability, type)
    pub bound_in_loop: HashMap<String, (bool, DataType)>,
    /// map of variable name to (mutability, type)
    pub return_to_bind: HashMap<String, (bool, DataType)>,
    /// (variable name, type)
    pub return_to_overwrite: Option<(String, DataType)>,
    /// map of variable name to (mutability, type)
    pub pass_through_args: HashMap<String, (bool, DataType)>,
    /// map of dictionary name to mutability
    pub pass_through_maps: HashMap<String, bool>,
}

impl Analyzer {
    pub(crate) fn get_chunk_skeleton(&self, id: ChunkId) -> Option<&FunctionSkeleton> {
        self.chunk_skeletons.as_ref().unwrap().get(&id)
    }

    pub(crate) fn print_chunk_skeleton_signature(&self, id: ChunkId) -> String {
        let sk = self.chunk_skeletons.as_ref().unwrap().get(&id).unwrap();
        let print_mut = |is_mut: bool| -> &'static str {
            if is_mut {
                "mut "
            } else {
                ""
            }
        };
        let arguments = sk
            .args
            .iter()
            .chain(sk.pass_through_args.iter())
            .sorted_by_key(|(name, _)| (*name).clone())
            .map(|(name, (is_mut, ty))| format!("{}: &{}{}", name, print_mut(*is_mut), ty.print()))
            .chain(
                sk.maps
                    .iter()
                    .chain(sk.pass_through_maps.iter())
                    .sorted_by_key(|(name, _)| (*name).clone())
                    .map(|(name, is_mut)| {
                        format!(
                            "{}: &{}{}",
                            name,
                            print_mut(*is_mut),
                            self.print_dictionary_type(name)
                        )
                    }),
            )
            .join(", ");
        let return_elements = sk
            .return_to_bind
            .iter()
            .sorted_by_key(|(name, _)| (*name).clone())
            .map(|(_, (_, ty))| ty)
            .chain(sk.return_to_overwrite.iter().map(|(_, ty)| ty))
            .map(|ty| ty.print())
            .collect::<Vec<_>>();
        let return_signature = match return_elements.len() {
            0 => String::new(),
            1 => format!(" -> {}", return_elements.first().unwrap()),
            _ => format!(" -> ({})", return_elements.join(", ")),
        };
        format!("({}){}", arguments, return_signature)
    }

    pub(crate) fn print_chunk_skeleton_body_header(&self, id: ChunkId) -> Vec<String> {
        let sk = self.chunk_skeletons.as_ref().unwrap().get(&id).unwrap();
        sk.declared
            .iter()
            .sorted_by_key(|(name, _)| (*name).clone())
            .map(|(name, (is_mut, ty))| {
                let mutability = if *is_mut { "mut " } else { "    " };
                format!(
                    "let {}{}: {} = Default::default();",
                    mutability,
                    name,
                    ty.print()
                )
            })
            .collect::<Vec<_>>()
    }

    pub(crate) fn print_chunk_skeleton_body_footer(&self, id: ChunkId) -> String {
        let sk = self.chunk_skeletons.as_ref().unwrap().get(&id).unwrap();
        let return_elements = sk
            .return_to_bind
            .iter()
            .sorted_by_key(|(name, _)| (*name).clone())
            .map(|(name, _)| name.clone())
            .chain(sk.return_to_overwrite.iter().map(|(name, _)| name.clone()))
            .collect::<Vec<_>>();
        match return_elements.len() {
            0 => String::new(),
            1 => return_elements.first().unwrap().to_string(),
            _ => format!("({})", return_elements.join(", ")),
        }
    }

    pub(crate) fn print_chunk_skeleton_call_site(
        &self,
        caller: Option<ChunkId>,
        callee: ChunkId,
        func_name: &str,
    ) -> String {
        let caller_sk = caller
            .as_ref()
            .map(|cid| self.chunk_skeletons.as_ref().unwrap().get(cid).unwrap());
        let callee_sk = self.chunk_skeletons.as_ref().unwrap().get(&callee).unwrap();
        let print_mut = |is_mut: bool| -> &'static str {
            if is_mut {
                "mut "
            } else {
                ""
            }
        };
        let may_print_ref = |name: &str, is_mut: bool| {
            if caller_sk.is_some_and(|sk| {
                sk.args.contains_key(name)
                    || sk.pass_through_args.contains_key(name)
                    || sk.pass_through_maps.contains_key(name)
            }) {
                "".into()
            } else {
                format!("&{}", print_mut(is_mut))
            }
        };
        let arguments = callee_sk
            .args
            .iter()
            .chain(callee_sk.pass_through_args.iter())
            .sorted_by_key(|(name, _)| (*name).clone())
            .map(|(name, (is_mut, _))| may_print_ref(name, *is_mut) + name)
            .chain(
                callee_sk
                    .maps
                    .iter()
                    .chain(callee_sk.pass_through_maps.iter())
                    .sorted_by_key(|(name, _)| (*name).clone())
                    .map(|(name, is_mut)| may_print_ref(name, *is_mut) + name),
            )
            .join(", ");
        let retval_usage = if let Some((name, _)) = &callee_sk.return_to_overwrite {
            format!("{} = ", name)
        } else {
            match callee_sk.return_to_bind.len() {
                0 => "".into(),
                1 => {
                    let (name, (is_mut, _)) = callee_sk.return_to_bind.iter().next().unwrap();
                    format!("let {}{} = ", print_mut(*is_mut), name)
                }
                _ => format!(
                    "let ({}) = ",
                    callee_sk
                        .return_to_bind
                        .iter()
                        .sorted_by_key(|(name, _)| (*name).clone())
                        .map(|(name, (is_mut, _))| format!("{}{}", print_mut(*is_mut), name))
                        .join(", ")
                ),
            }
        };
        format!("{}{}({});", retval_usage, func_name, arguments)
    }

    /// Returns a vector of references to Chunks in topologically sorted order.
    /// In this context, children appear before their parents.
    pub(super) fn get_topologically_sorted_chunks(&self) -> Vec<&Chunk> {
        let mut sorted = Vec::with_capacity(self.chunks.len());
        let mut visited = HashSet::new();

        // Identify root chunks (those without a parent)
        let root_ids: Vec<usize> = self
            .chunks
            .iter()
            .filter(|(_, chunk)| chunk.parent.is_none())
            .map(|(id, _)| id)
            .collect();

        for id in root_ids {
            self.topo_sort_dfs(id, &mut visited, &mut sorted);
        }

        sorted
    }

    fn topo_sort_dfs<'a>(
        &'a self,
        current_id: ChunkId,
        visited: &mut HashSet<ChunkId>,
        sorted: &mut Vec<&'a Chunk>,
    ) {
        if visited.contains(&current_id) {
            return;
        }

        // Mark as visited
        visited.insert(current_id);

        // Retrieve the chunk from the Slab
        if let Some(chunk) = self.chunks.get(current_id) {
            for child_id in &chunk.children {
                // Assuming ChunkId is a wrapper around usize for the Slab index
                self.topo_sort_dfs(*child_id, visited, sorted);
            }

            // For a "bottom-up" topo sort (parents after children),
            // we push the current node after visiting its children.
            sorted.push(chunk);
        }
    }
}

fn take_common_chunk_sequence(seq_x: &[ChunkId], seq_y: &[ChunkId]) -> Vec<ChunkId> {
    let mut ret = Vec::new();
    for (x, y) in seq_x.iter().zip(seq_y.iter()) {
        if x == y {
            ret.push(*x);
        } else {
            break;
        }
    }
    ret
}
