use crate::analyzer::dictionary::DictionaryOperation;

use super::{
    dictionary::DictionaryAccess, type_inference::DataType, Analyzer, Location, MayM4, NodeId,
    ShellCommand,
};
use itertools::Itertools;
use std::{
    collections::{HashMap, HashSet},
    ops::Not,
};

pub(crate) type ChunkId = usize;

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
    pub bounded: HashSet<String>,
    pub dictionaries: HashMap<String, HashMap<Location, DictionaryAccess>>,
    pub features: HashMap<String, Vec<Location>>,
}

impl Analyzer {
    pub(crate) fn get_scopes(&self, var_name: &str) -> Option<&Vec<Scope>> {
        self.var_scopes.as_ref().unwrap().get(var_name)
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
        if let (Some(node1), Some(node2)) = (self.pool.get(node1_id), self.pool.get(node2_id)) {
            // Check if node2 depends on node1 or vice versa
            (node1.info.parent == node2.info.parent) && {
                // FIXME
                let defs = node1
                    .info
                    .definitions
                    .keys()
                    .filter(|key| !self.fixed.contains_key(key.as_str()))
                    .cloned()
                    .collect::<HashSet<_>>();
                let uses = node2.info.usages.keys().cloned().collect::<HashSet<_>>();
                !defs.is_disjoint(&uses)
            }
        } else {
            false
        }
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
            let current_id = self.top_ids[i];

            if current_chunk.is_empty() {
                // Start a new chunk
                current_chunk.push(current_id);
            } else {
                // Check if current node is related to any node in the current chunk
                let is_related_to_chunk = current_chunk
                    .iter()
                    .any(|&chunk_node_id| self.are_nodes_related(chunk_node_id, current_id));

                if is_related_to_chunk {
                    // Fuse with current chunk
                    current_chunk.push(current_id);
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
                        i = i + last_related_idx; // Skip ahead (will be incremented at loop end)
                    } else {
                        // No relation found in lookahead - cut here and start new chunk
                        if !current_chunk.is_empty() {
                            self.add_chunk(current_chunk.clone());
                            current_chunk.clear();
                        }
                        current_chunk.push(current_id);
                    }
                } else {
                    // No window - cut here and start new chunk
                    if !current_chunk.is_empty() {
                        self.add_chunk(current_chunk.clone());
                        current_chunk.clear();
                    }
                    current_chunk.push(current_id);
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
            .map(|parent| self.get_node(parent).unwrap().info.chunk_id)
            .flatten();
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
            .map(|id| self.collect_descendant_nodes_per_node(*id, true, true))
            .flatten()
            .collect();
        let new_chunk_id = self.chunks.insert(Chunk {
            nodes: nodes.to_vec(),
            descendant_nodes,
            parent,
            range,
            ..Default::default()
        });
        self.chunks[new_chunk_id].chunk_id = new_chunk_id;
        self.examine_chunk_io(new_chunk_id);
        for id in nodes.iter() {
            self.get_node_mut(*id)
                .unwrap()
                .info
                .chunk_id
                .replace(new_chunk_id);
        }
        parent.map(|id| self.chunks[id].children.push(new_chunk_id));

        new_chunk_id
    }

    /// enumerate out-of-scope variables
    fn examine_chunk_io(&mut self, chunk_id: ChunkId) {
        let chunk_start_loc = {
            let first_id = *self.chunks[chunk_id].nodes.first().unwrap();
            self.node_start_loc(first_id)
        };
        let chunk_end_loc = {
            let last_id = *self.chunks[chunk_id].nodes.last().unwrap();
            self.node_end_loc(last_id)
        };

        // Collect all variables defined within the chunk
        let mut chunk_defines = HashMap::new();
        let mut chunk_uses = HashMap::new();
        let mut bounded = HashSet::new();

        for &id in &self.chunks[chunk_id].nodes {
            // Get variables from all descendant nodes in the chunk
            let (defines, uses) = self.collect_variables(id);
            self.extend_var_maps(&mut chunk_defines, defines.into_iter());
            self.extend_var_maps(&mut chunk_uses, uses.into_iter());

            bounded.extend(
                self.collect_descendant_nodes_per_node(id, true, false)
                    .into_iter()
                    .filter(|id| {
                        self.get_children(*id).is_some_and(|children| {
                            children
                                .iter()
                                .any(|id| self.get_node(*id).is_some_and(|n| n.info.is_top_node()))
                        })
                    })
                    .map(|id| self.get_node(id).unwrap().info.bounds.keys())
                    .flatten()
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
                !self
                    .build_option_info
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
                    .build_option_info
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

        let features = chunk_uses
            .into_iter()
            .filter(|(var, _)| {
                self.build_option_info
                    .arg_var_to_option_name
                    .contains_key(var.as_str())
            })
            .collect();

        self.chunks.get_mut(chunk_id).unwrap().io = ChunkIO {
            imported,
            exported,
            bounded,
            dictionaries,
            features,
        };
    }

    pub(crate) fn cut_variable_scopes_chunkwise(&mut self) {
        assert!(!self.chunks.is_empty());
        self.var_scopes.replace(Default::default());

        let visible_vars = self
            .chunks
            .iter()
            .map(|(id, c)| {
                c.io.imported
                    .keys()
                    .chain(c.io.exported.keys())
                    .chain(c.io.bounded.iter())
                    .zip(std::iter::repeat(id))
            })
            .flatten()
            .fold(HashMap::new(), |mut acc, (k, v)| {
                acc.entry(k.to_owned())
                    .or_insert_with(HashSet::new)
                    .insert(v);
                acc
            });
        for (var, cids) in visible_vars.iter() {
            if self
                .build_option_info
                .arg_var_to_option_name
                .contains_key(var.as_str())
            {
                continue;
            }
            if self
                .build_option_info
                .arg_var_to_option_name
                .contains_key(var.as_str())
            {
                continue;
            }
            let cids = cids
                .into_iter()
                .sorted_by_key(|id| self.chunks[**id].range.0);
            let mut current_scope = Scope::default();
            for &cid in cids.rev() {
                let chunk = &self.chunks[cid];
                let chunk_guards_size = self
                    .get_node(chunk.nodes[0])
                    .unwrap()
                    .info
                    .block
                    .map(|bid| self.get_block(bid).guards.len())
                    .unwrap_or(0);
                let is_imported = chunk.io.imported.contains_key(var.as_str());
                let is_exported = chunk.io.exported.contains_key(var.as_str());
                let is_bounded = chunk.io.bounded.contains(var.as_str());

                match (is_imported, is_exported, is_bounded) {
                    (true, true, _) => {
                        current_scope.overwriters.push(cid);
                    }
                    (true, false, _) => {
                        current_scope.readers.push(cid);
                    }
                    (false, true, _) => {
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
                                let mut def_loc_guards_size = self.guard_of_location(def_loc).len();
                                while let Some(propagated_loc) = is_propagated(cur) {
                                    // if the definition is propagated to the parent node,
                                    // we should recaluclate the size of guards.
                                    def_loc_guards_size =
                                        self.guard_of_location(propagated_loc).len();
                                    cur = propagated_loc;
                                }
                                def_loc_guards_size > chunk_guards_size
                            })
                        {
                            // Turns out the variable to be defined **conditionally** in the chunk.
                            current_scope.overwriters.push(cid);
                        } else {
                            let mut common_parent = self.get_parental_chunk_sequence(cid);
                            for other in current_scope
                                .overwriters
                                .iter()
                                .chain(current_scope.readers.iter())
                            {
                                common_parent = self.take_common_chunk_sequence(
                                    &common_parent,
                                    &self.get_parental_chunk_sequence(*other),
                                );
                            }
                            if common_parent.is_empty() {
                                current_scope.writers.push(cid);
                            } else {
                                current_scope.owner.replace(cid);
                                current_scope.parent.replace(*common_parent.last().unwrap());
                                self.add_chunkwise_scope(var.as_str(), current_scope);
                                current_scope = Scope::default();
                            }
                        }
                    }
                    (false, false, true) => {
                        current_scope.bound_by.replace(cid);
                        self.add_chunkwise_scope(var, current_scope);
                        current_scope = Scope::default();
                    }
                    _ => unreachable!(),
                }
            }
            if !current_scope.overwriters.is_empty() || !current_scope.readers.is_empty() {
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
    }

    fn add_chunkwise_scope(&mut self, var: &str, mut scope: Scope) {
        if !self.input_vars.as_ref().unwrap().contains(var) && scope.has_no_writers() {
            return;
        }
        scope.writers.sort_by_key(|cid| self.chunks[*cid].range.0);
        scope
            .overwriters
            .sort_by_key(|cid| self.chunks[*cid].range.0);
        scope.readers.sort_by_key(|cid| self.chunks[*cid].range.0);
        self.var_scopes
            .as_mut()
            .unwrap()
            .entry(var.to_owned())
            .or_default()
            .push(scope);
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

    fn take_common_chunk_sequence(&self, seq_x: &[ChunkId], seq_y: &[ChunkId]) -> Vec<ChunkId> {
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

    pub(crate) fn make_chunk_skeletons(&mut self) {
        let mut chunk_skeletons: HashMap<ChunkId, FunctionSkelton> = self
            .chunks
            .iter()
            .map(|(cid, _)| (cid, Default::default()))
            .collect();
        for (var, scopes) in self.var_scopes.as_ref().unwrap().iter() {
            for scope in scopes {
                if let Some(cid) = scope.owner.as_ref() {
                    let is_mut = !scope.writers.is_empty() || !scope.overwriters.is_empty();
                    chunk_skeletons.get_mut(cid).unwrap().return_to_bind.push((
                        is_mut,
                        var.to_owned(),
                        self.get_inferred_type(var),
                    ));
                } else if let Some(cid) = scope.parent.as_ref() {
                    let is_mut = !scope.writers.is_empty() || !scope.overwriters.is_empty();
                    chunk_skeletons.get_mut(cid).unwrap().declared.push((
                        is_mut,
                        var.to_owned(),
                        self.get_inferred_type(var),
                    ));
                }
                for cid in scope.writers.iter() {
                    let current = chunk_skeletons.get_mut(cid).unwrap();
                    if !current.return_to_bind.is_empty() || current.return_to_subst.is_some() {
                        current
                            .args
                            .push((true, var.to_owned(), self.get_inferred_type(var)));
                    } else {
                        current
                            .return_to_subst
                            .replace((var.to_owned(), self.get_inferred_type(var)));
                    }
                }
                for cid in scope.overwriters.iter() {
                    chunk_skeletons.get_mut(cid).unwrap().args.push((
                        true,
                        var.to_owned(),
                        self.get_inferred_type(var),
                    ));
                }
                for cid in scope.readers.iter() {
                    chunk_skeletons.get_mut(cid).unwrap().args.push((
                        false,
                        var.to_owned(),
                        self.get_inferred_type(var),
                    ));
                }
            }
        }
        for (cid, chunk) in self.chunks.iter() {
            for (name, accesses) in chunk.io.dictionaries.iter() {
                if accesses
                    .values()
                    .any(|a| matches!(a.operation, DictionaryOperation::Write))
                {
                    chunk_skeletons
                        .get_mut(&cid)
                        .unwrap()
                        .maps
                        .push((true, name.clone()));
                } else {
                    chunk_skeletons
                        .get_mut(&cid)
                        .unwrap()
                        .maps
                        .push((false, name.clone()));
                }
            }
        }
        for (_, top_level_chunk) in self
            .chunks
            .iter()
            .filter(|(_, c)| c.parent.is_none() && !c.children.is_empty())
        {
            let mut stack = top_level_chunk.children.clone();
            let mut post_order = Vec::new();
            while let Some(child) = stack.pop() {
                stack.extend(self.chunks[child].children.clone());
                post_order.push(child);
            }
            while let Some(cid) = post_order.pop() {
                if let Some(parent_cid) = self.chunks.get(cid).unwrap().parent {
                    let parent_scope_vars = self
                        .var_scopes
                        .as_ref()
                        .unwrap()
                        .iter()
                        .filter_map(|(var, scopes)| {
                            scopes
                                .iter()
                                .any(|s| s.parent == Some(parent_cid))
                                .then_some(var.to_owned())
                        })
                        .collect::<HashSet<_>>();
                    let s = chunk_skeletons.get(&cid).unwrap();
                    let parent = chunk_skeletons.get(&parent_cid).unwrap();
                    // check inlet
                    let args = s.args.iter().chain(s.pass_through_args.iter());
                    let maps = s.maps.iter().chain(s.pass_through_maps.iter());
                    // calc difference
                    let pass_through_args = args
                        .filter(|t| {
                            !parent.args.contains(t)
                                && !parent.pass_through_args.contains(t)
                                && !parent_scope_vars.contains(&t.1)
                        })
                        .map(|t| (*t).clone())
                        .collect::<Vec<_>>();
                    let pass_through_maps = maps
                        .filter(|t| {
                            !parent.maps.contains(t) && !parent.pass_through_maps.contains(t)
                        })
                        .map(|t| (*t).clone())
                        .collect::<Vec<_>>();
                    // update the parent
                    let parent = chunk_skeletons.get_mut(&parent_cid).unwrap();
                    parent.pass_through_args.extend(pass_through_args);
                    parent.pass_through_maps.extend(pass_through_maps);
                }
            }
        }
        for s in chunk_skeletons.values_mut() {
            s.args
                .sort_by_key(|(is_mut, name, _)| (is_mut.clone(), name.clone()));
            s.maps.sort();
            s.declared
                .sort_by_key(|(is_mut, name, _)| (is_mut.clone(), name.clone()));
            s.return_to_bind
                .sort_by_key(|(is_mut, name, _)| (is_mut.clone(), name.clone()));
            s.pass_through_args
                .sort_by_key(|(is_mut, name, _)| (is_mut.clone(), name.clone()));
            s.pass_through_maps.sort();
        }
        self.chunk_skeletons.replace(chunk_skeletons);
    }
}

#[derive(Debug, Clone, Default)]
pub(crate) struct FunctionSkelton {
    args: Vec<(bool, String, DataType)>,
    maps: Vec<(bool, String)>,
    declared: Vec<(bool, String, DataType)>,
    return_to_bind: Vec<(bool, String, DataType)>,
    return_to_subst: Option<(String, DataType)>,
    pass_through_args: Vec<(bool, String, DataType)>,
    pass_through_maps: Vec<(bool, String)>,
}

impl Analyzer {
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
            .map(|(is_mut, name, ty)| format!("{}: &{}{}", name, print_mut(*is_mut), ty.print()))
            .chain(
                sk.maps
                    .iter()
                    .chain(sk.pass_through_maps.iter())
                    .map(|(is_mut, name)| {
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
            .map(|(_, _, ty)| ty)
            .chain(sk.return_to_subst.iter().map(|(_, ty)| ty))
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
            .map(|(is_mut, name, ty)| {
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
            .map(|(_, name, _)| name.clone())
            .chain(sk.return_to_subst.iter().map(|(name, _)| name.clone()))
            .collect::<Vec<_>>();
        match return_elements.len() {
            0 => String::new(),
            1 => format!("{}", return_elements.first().unwrap()),
            _ => format!("({})", return_elements.join(", ")),
        }
    }

    pub(crate) fn print_chunk_skeleton_call_site(&self, id: ChunkId, func_name: &str) -> String {
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
            .map(|(is_mut, name, _)| format!("&{}{}", print_mut(*is_mut), name))
            .chain(
                sk.maps
                    .iter()
                    .chain(sk.pass_through_maps.iter())
                    .map(|(is_mut, name)| format!("&{}{}", print_mut(*is_mut), name)),
            )
            .join(", ");
        let retval_usage = if let Some((name, _)) = &sk.return_to_subst {
            format!("{} = ", name)
        } else {
            match sk.return_to_bind.len() {
                0 => "".into(),
                1 => {
                    let (is_mut, name, _) = sk.return_to_bind.first().unwrap();
                    format!("let {}{} = ", print_mut(*is_mut), name)
                }
                _ => format!(
                    "let ({}) = ",
                    sk.return_to_bind
                        .iter()
                        .map(|(is_mut, name, _)| format!("{}{}", print_mut(*is_mut), name))
                        .join(", ")
                ),
            }
        };
        format!("{}{}({});", retval_usage, func_name, arguments)
    }
}
