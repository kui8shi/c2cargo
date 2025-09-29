use autotools_parser::ast::node::NodeId;

use super::Analyzer;

pub(super) type ExecId = usize;

#[derive(Debug, Clone, PartialEq, Eq, Ord, Hash)]
pub(crate) struct Location {
    pub node_id: NodeId,
    pub exec_id: ExecId,
    pub order: usize,
    pub line: usize,
}

impl PartialOrd for Location {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some((self.exec_id, self.order).cmp(&(other.exec_id, other.order)))
    }
}

impl Analyzer {
    pub(crate) fn node_start_loc(&self, node_id: NodeId) -> Location {
        Location {
            node_id,
            exec_id: self.get_node(node_id).unwrap().info.exec_id,
            order: 0,
            line: self.get_node(node_id).unwrap().range_start().unwrap(),
        }
    }

    pub(crate) fn node_end_loc(&self, node_id: NodeId) -> Location {
        Location {
            node_id,
            exec_id: self.get_node(node_id).unwrap().info.exit,
            order: 0,
            line: self.get_node(node_id).unwrap().range_end().unwrap(),
        }
    }
}
