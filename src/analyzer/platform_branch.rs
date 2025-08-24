use super::{MayM4, ShellCommand};

use super::{Analyzer, NodeId};

#[derive(Debug)]
pub(super) struct PlatformBranchPrunner<'a> {
    analyzer: &'a Analyzer,
    cursor: Option<NodeId>,
}

impl Analyzer {
    pub fn prune_platform_branch(&mut self) {
        for id in self.find_case_branches(&["host"]) {
            if let MayM4::Shell(ShellCommand::Case { word, arms }) = &self.get_node(id).cmd.0 {
                println!("============================");
                println!("{}:", self.display_word(&word));
                for arm in arms {
                    println!("\t[");
                    for pattern in &arm.patterns {
                        println!("\t\t{},", self.display_word(pattern))
                    }
                    println!("\t]");
                }
            }
        }
    }
}
