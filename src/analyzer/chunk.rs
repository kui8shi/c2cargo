use super::{Analyzer, Location, MayM4, NodeId, ShellCommand};
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
        self.parent.is_none()
    }
}

#[derive(Clone, Debug, Default)]
pub(crate) struct Chunk {
    pub nodes: Vec<NodeId>,
    pub chunk_id: ChunkId,
    pub parent: Option<ChunkId>,
    pub children: Vec<ChunkId>,
    pub range: (usize, usize),
    pub imported: HashSet<String>,
    pub exported: HashSet<String>,
    pub bounded: HashSet<String>,
}

impl Analyzer {
    pub(crate) fn get_scopes(&self, var_name: &str) -> Option<&Vec<Scope>> {
        self.scopes.as_ref().unwrap().get(var_name)
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
        let (imported, exported, bounded) = self.examine_chunk_io(&nodes);
        let new_chunk_id = self.chunks.insert(Chunk {
            nodes: nodes.to_vec(),
            parent,
            range,
            imported,
            exported,
            bounded,
            ..Default::default()
        });
        self.chunks[new_chunk_id].chunk_id = new_chunk_id;
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
    fn examine_chunk_io(
        &self,
        nodes: &[NodeId],
    ) -> (HashSet<String>, HashSet<String>, HashSet<String>) {
        let chunk_start_loc = {
            let first_id = *nodes.first().unwrap();
            self.node_start_loc(first_id)
        };
        let chunk_end_loc = {
            let last_id = *nodes.last().unwrap();
            self.node_end_loc(last_id)
        };

        // Collect all variables defined within the chunk
        let mut chunk_defines = HashMap::new();
        let mut chunk_uses = HashMap::new();
        let mut bounded = HashSet::new();

        for &id in nodes {
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
        let is_defined_inside_chunk = |var_name: &String, use_locs: &[Location]| -> bool {
            use_locs.iter().all(|use_loc| {
                self.get_dominant_definition(var_name.as_str(), use_loc.node_id)
                    .is_some_and(|dominant_loc| chunk_start_loc <= dominant_loc)
            })
        };

        // Imported variables: used in chunk but not defined in chunk
        let imported: HashSet<String> = chunk_uses
            .into_iter()
            .filter_map(|(var, use_locs)| {
                is_defined_inside_chunk(&var, &use_locs)
                    .not()
                    .then_some(var)
            })
            .collect();

        // Helper function to check if a variable is used outside this chunk
        let is_used_outside_chunk = |var_name: &String| -> bool {
            let is_used_directly = self.get_usage(var_name).is_some_and(|use_locs| {
                use_locs
                    .iter()
                    .find(|loc| chunk_end_loc <= **loc)
                    .is_some_and(|loc| {
                        self.get_dominant_definition(var_name, loc.node_id)
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
        let exported: HashSet<String> = chunk_defines
            .keys()
            .filter(|var_name| is_used_outside_chunk(var_name))
            .cloned()
            .collect();

        (imported, exported, bounded)
    }

    pub(crate) fn cut_variable_scopes_chunkwise(&mut self) {
        assert!(!self.chunks.is_empty());
        self.scopes.replace(Default::default());

        let visible_vars = self
            .chunks
            .iter()
            .map(|(id, c)| {
                c.imported
                    .iter()
                    .chain(c.exported.iter())
                    .chain(c.bounded.iter())
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
            // if self.subst_vars.contains(var.as_str()) {
            //     continue;
            // }
            if self.divided_vars().contains_key(var.as_str()) {
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
                let is_imported = chunk.imported.contains(var.as_str());
                let is_exported = chunk.exported.contains(var.as_str());
                let is_bounded = chunk.bounded.contains(var.as_str());

                match (is_imported, is_exported, is_bounded) {
                    (true, true, _) => {
                        current_scope.overwriters.push(cid);
                    }
                    (true, false, _) => {
                        current_scope.readers.push(cid);
                    }
                    (false, true, _) => {
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
                            current_scope
                                .parent
                                .replace(*common_parent.first().unwrap());
                            self.add_chunkwise_scope(var.as_str(), current_scope);
                            current_scope = Scope::default();
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
        for scopes in self.scopes.as_mut().unwrap().values_mut() {
            scopes.reverse();
        }
    }

    fn add_chunkwise_scope(&mut self, var: &str, mut scope: Scope) {
        scope.writers.sort_by_key(|cid| self.chunks[*cid].range.0);
        scope
            .overwriters
            .sort_by_key(|cid| self.chunks[*cid].range.0);
        scope.readers.sort_by_key(|cid| self.chunks[*cid].range.0);
        self.scopes
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
            ret.push(chunk_id);
            current = parent;
        }
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
}
