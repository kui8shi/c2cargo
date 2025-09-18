use itertools::Itertools;

use super::{Analyzer, Location, MayM4, NodeId, ShellCommand};
use std::collections::HashSet;

pub(crate) type ChunkId = usize;

#[derive(Clone, Debug, Default)]
pub(crate) struct Scope {
    /// parental chunk, None if global.
    parent: Option<ChunkId>,
    /// ID of the chunk that defines the variable first.
    /// None if the variable is environmental (can be given by user).
    first_def: Option<ChunkId>,
    /// IDs of the chunks that overwrites the variable
    overwrites: Vec<ChunkId>,
    /// IDs of the chunks that read the variable
    reads: Vec<ChunkId>,
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
}

impl Analyzer {
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
                    .defines
                    .keys()
                    .filter(|key| !self.fixed.contains_key(key.as_str()))
                    .cloned()
                    .collect::<HashSet<_>>();
                let uses = node2.info.uses.keys().cloned().collect::<HashSet<_>>();
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
            .info
            .parent
            .map(|parent| self.get_node(parent).info.chunk_id)
            .flatten();
        let range = (
            self.get_node(*nodes.first().unwrap())
                .range_start()
                .unwrap(),
            self.get_node(*nodes.last().unwrap()).range_end().unwrap(),
        );
        let (imported, exported) = self.examine_chunk_io(&nodes);
        let new_chunk_id = self.chunks.insert(Chunk {
            nodes: nodes.to_vec(),
            parent,
            range,
            imported,
            exported,
            ..Default::default()
        });
        self.chunks[new_chunk_id].chunk_id = new_chunk_id;
        for id in nodes.iter() {
            self.get_node_mut(*id).info.chunk_id.replace(new_chunk_id);
        }
        parent.map(|id| self.chunks[id].children.push(new_chunk_id));

        new_chunk_id
    }

    /// enumerate out-of-scope variables
    fn examine_chunk_io(&self, nodes: &[NodeId]) -> (HashSet<String>, HashSet<String>) {
        let chunk_end_loc = nodes
            .iter()
            .map(|id| Location {
                node_id: *id,
                line: self.get_node(*id).range_end().unwrap(),
                is_left: true,
            })
            .max()
            .unwrap();

        // Collect all variables defined within the chunk
        let mut chunk_defines = HashSet::new();
        let mut chunk_uses = HashSet::new();

        for &id in nodes {
            // Get variables from all descendant nodes in the chunk
            let (defines, uses) = self.collect_variables(id);
            chunk_defines.extend(defines.into_keys());
            chunk_uses.extend(uses.into_keys());
        }

        // Imported variables: used in chunk but not defined in chunk
        let imported: HashSet<String> = chunk_uses.difference(&chunk_defines).cloned().collect();

        // Helper function to check if a variable is used outside this chunk
        let is_used_outside_chunk = |var_name: &String| -> bool {
            self.var_usages.get(var_name).is_some_and(|locs| {
                locs.iter()
                    .find(|loc| **loc > chunk_end_loc)
                    .is_some_and(|loc| {
                        self.get_dominant_definition(var_name, loc.node_id)
                            .is_none_or(|dominant_loc| dominant_loc <= chunk_end_loc)
                    })
            }) || self
                .var_indirect_usages
                .get(var_name)
                .is_some_and(|locs| locs.iter().any(|loc| *loc > chunk_end_loc))
                || self.subst_vars.contains(var_name)
        };

        // Exported variables: defined in chunk and used outside the chunk
        let exported: HashSet<String> = chunk_defines
            .iter()
            .filter(|var_name| is_used_outside_chunk(var_name))
            .cloned()
            .collect();

        (imported, exported)
    }

    pub(crate) fn init_scopes(&mut self) {}
}
