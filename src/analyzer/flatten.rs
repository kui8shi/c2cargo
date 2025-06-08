use super::{AstVisitor, Node, NodeId, Word};
use slab::Slab;

/// A visitor to flatten and collect AST nodes into a linear sequence.
#[derive(Debug)]
pub(super) struct Flattener {
    threshold: usize,
    nodes: Slab<Node>,
    top_ids: Vec<NodeId>,
    parent_stack: Vec<NodeId>,
    cursor: Option<NodeId>,
    flatten: bool,
    #[cfg(debug_assertions)]
    last_range_start: Option<usize>,
}

impl Flattener {
    pub fn flatten(
        nodes: Slab<Node>,
        initial_top_ids: Vec<NodeId>,
        threshold: usize,
    ) -> (Vec<NodeId>, Slab<Node>) {
        let mut s = Self {
            threshold,
            nodes,
            top_ids: initial_top_ids.clone(),
            parent_stack: vec![],
            cursor: None,
            flatten: false,
            #[cfg(debug_assertions)]
            last_range_start: None,
        };

        for id in initial_top_ids {
            s.visit_top(id);
        }

        (s.top_ids, s.nodes)
    }

    fn do_flatten(&mut self, node_id: NodeId) -> bool {
        // flatten commands with more than `self.threshold` lines.
        self.flatten = self.nodes[node_id]
            .ranges
            .first()
            .is_some_and(|(start, end)| end - start > self.threshold);
        self.flatten
    }
}

impl AstVisitor for Flattener {
    fn get_node(&self, node_id: NodeId) -> &Node {
        &self.nodes[node_id]
    }

    fn visit_top(&mut self, node_id: NodeId) {
        self.visit_node(node_id);
    }

    fn visit_node(&mut self, node_id: NodeId) {
        // initialize `parent` and `children` fields
        if let Some(parent) = self.parent_stack.last().copied() {
            let top_id = self.parent_stack.first().copied().unwrap();
            assert!(self.nodes[node_id].chunk_id.is_none());
            assert!(self.nodes[node_id].parent.is_none());
            self.nodes[node_id].chunk_id = Some(top_id);
            self.nodes[node_id].parent = Some(parent);
            self.nodes[parent].children.get_or_insert_default().push(node_id);
        } else {
            self.nodes[node_id].chunk_id = Some(node_id);
        }
        if self.do_flatten(node_id) {
            self.nodes[node_id].chunk_id = Some(node_id);
        }
        #[cfg(debug_assertions)]
        {
            self.last_range_start = self.nodes[node_id].ranges.first().map(|r| r.0);
        }
        self.cursor = Some(node_id);
        self.walk_node(node_id);
    }

    fn visit_for(&mut self, var: &str, words: &Vec<Word<String>>, body: &Vec<NodeId>) {
        let cur = self.cursor.unwrap();
        if self.flatten {
            #[cfg(debug_assertions)]
            {
                let start = self.nodes[cur].range_start().unwrap();
                if let Some(prev) = self.last_range_start {
                    if !(prev <= start) {
                        dbg!(
                            &self.nodes[cur].ranges,
                            self.cursor,
                            self.last_range_start
                        );
                        panic!();
                    }
                }
                self.last_range_start = Some(start);
            }
            let body_start = self.nodes[*body.first().unwrap()].range_start().unwrap();
            let body_end = self.nodes[*body.last().unwrap()].range_end().unwrap();
            self.nodes[cur].gap_range(vec![(body_start + 1, body_end)]);
            self.top_ids.extend_from_slice(body);
        }
        self.parent_stack.push(cur);
        self.walk_for(var, words, body);
        self.parent_stack.pop();
    }

    fn visit_case(
        &mut self,
        word: &Word<String>,
        arms: &Vec<autoconf_parser::ast::node::PatternBodyPair<String>>,
    ) {
        let cur = self.cursor.unwrap();
        if self.flatten {
            #[cfg(debug_assertions)]
            {
                let start = self.nodes[cur].range_start().unwrap();
                if let Some(prev) = self.last_range_start {
                    if !(prev <= start) {
                        dbg!(cur, self.last_range_start);
                        panic!();
                    }
                }
                self.last_range_start = Some(start);
            }
            let gaps = arms
                .iter()
                .map(|arm| {
                    let body_start = self.nodes[*arm.body.first().unwrap()]
                        .range_start()
                        .unwrap();
                    let body_end = self.nodes[*arm.body.last().unwrap()].range_end().unwrap();
                    (body_start, body_end)
                })
                .collect();
            self.nodes[cur].gap_range(gaps);
            self.top_ids
                .extend(arms.iter().flat_map(|arm| arm.body.iter()));
        }
        self.parent_stack.push(cur);
        self.walk_case(word, arms);
        self.parent_stack.pop();
    }

    fn visit_if(
        &mut self,
        conditionals: &Vec<autoconf_parser::ast::node::GuardBodyPair<String>>,
        else_branch: &Vec<NodeId>,
    ) {
        let cur = self.cursor.unwrap();
        if self.flatten {
            #[cfg(debug_assertions)]
            {
                let start = self.nodes[cur].range_start().unwrap();
                if let Some(prev) = self.last_range_start {
                    if !(prev <= start) {
                        dbg!(cur, self.last_range_start);
                        panic!();
                    }
                }
                self.last_range_start = Some(start);
            }
            let gaps = conditionals
                .iter()
                .map(|c| &c.body)
                .chain(std::iter::once(else_branch))
                .filter(|body| !body.is_empty())
                .map(|body| {
                    let body_start = self.nodes[*body.first().unwrap()].range_start().unwrap();
                    let body_end = self.nodes[*body.last().unwrap()].range_end().unwrap();
                    (body_start + 1, body_end)
                })
                .collect();

            self.nodes[cur].gap_range(gaps);
            self.top_ids.extend(
                conditionals
                    .iter()
                    .flat_map(|c| c.body.iter())
                    .chain(else_branch.iter()),
            );
        }
        self.parent_stack.push(cur);
        self.walk_if(conditionals, else_branch);
        self.parent_stack.pop();
    }
}

impl Node {
    /// Break a range into ranges by removing overlapping parts with `gaps`
    fn gap_range(&mut self, mut gaps: Vec<(usize, usize)>) {
        let range = self.ranges.pop().unwrap();
        let mut result = Vec::new();
        let mut current_start = range.0;
        let range_end = range.1;

        gaps.sort_unstable_by_key(|g| g.0);

        for &(gap_start, gap_end) in &gaps {
            if gap_end < current_start {
                continue;
            }
            if gap_start > range_end {
                break;
            }

            if gap_start > current_start {
                result.push((current_start, gap_start));
            }

            // update the position to look for next.
            current_start = current_start.max(gap_end);
        }
        if current_start <= range_end {
            result.push((current_start, range_end));
        }

        self.ranges = result;
    }
}
