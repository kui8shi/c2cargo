use std::collections::HashSet;

use autotools_parser::ast::{node::ShellCommand, MayM4, Redirect};

use crate::analyzer::{as_literal, as_shell};

use super::Analyzer;

use MayM4::*;
use ShellCommand::*;

impl Analyzer {
    pub(super) fn filter_out_commands(&mut self) {
        let mut remove_nodes = HashSet::new();
        for (node_id, node) in self.pool.nodes.iter() {
            match &node.cmd.0 {
                Shell(Redirect(id, redirs)) => {
                    if redirs.iter().all(|r| {
                        use Redirect::*;
                        match r {
                            Heredoc(_, _) => true,
                            Write(_, w)
                            | ReadWrite(_, w)
                            | Append(_, w)
                            | Clobber(_, w)
                            | DupWrite(_, w) => as_shell(w)
                                .and_then(as_literal)
                                .is_some_and(|lit| lit.parse::<u8>().is_ok()),
                            _ => false,
                        }
                    }) {
                        match &self.get_node(*id).unwrap().cmd.0 {
                            Shell(Cmd(cmd_words)) => {
                                match as_shell(cmd_words.first().unwrap()).and_then(as_literal) {
                                    Some("cat" | "echo") => {
                                        remove_nodes.insert(node_id);
                                    }
                                    _ => (),
                                }
                            }
                            _ => (),
                        }
                    }
                }
                MayM4::Shell(ShellCommand::Cmd(cmd_words))
                    if node.info.parent.is_some_and(|parent| {
                        match &self.get_node(parent).unwrap().cmd.0 {
                            // we need to skip commands wrapped by these components.
                            Shell(And(_, _) | Or(_, _) | Pipe(_, _) | Redirect(_, _)) => false,
                            _ => true,
                        }
                    }) =>
                {
                    match as_shell(cmd_words.first().unwrap()).and_then(as_literal) {
                        Some("cat" | "echo") => {
                            remove_nodes.insert(node_id);
                        }
                        _ => (),
                    }
                }
                _ => (),
            }
        }
        for id in remove_nodes {
            self.remove_node(id);
        }
    }
}
