use itertools::Itertools;
use std::collections::HashSet;
use use_llm::{TranslationEvidence, TranslationInput};

use crate::{analyzer::type_inference::DataType, utils::llm_analysis::LLMAnalysis};

use super::Analyzer;

mod printer;
mod use_llm;

impl Analyzer {
    /// Analyze commands and build the dependency graph
    pub async fn translate(&mut self) {
        println!("=== TRANSLATE DEBUG: Starting translation analysis ===");
        let mut exported = HashSet::new();
        for (i, chunk) in self.chunks.iter() {
            exported.extend(chunk.io.exported.clone());
            let last_id = *chunk.nodes.last().unwrap();
            println!(
                "Chunk {}: parent: {:?}, nodes {:?} , exit {:?}",
                i,
                chunk.parent,
                chunk
                    .nodes
                    .iter()
                    .map(|id| (
                        *id,
                        self.collect_descendant_nodes_per_node(*id, true, false)
                    ))
                    .map(|(id, nodes)| (
                        id,
                        nodes
                            .into_iter()
                            .map(|i| self.get_node(i).unwrap().info.exec_id)
                            .sorted()
                            .collect::<Vec<_>>()
                    ))
                    .collect::<Vec<_>>(),
                self.get_node(last_id).unwrap().info.exit,
            );
            println!("signature: {}", self.print_chunk_skeleton_signature(i));
            println!("header: {:?}", self.print_chunk_skeleton_body_header(i));
            println!("footer: {}", self.print_chunk_skeleton_body_footer(i));
            println!(
                "callsite: {}",
                self.print_chunk_skeleton_call_site(i, &format!("func{}", i))
            );
            let printer = printer::TranslatingPrinter::new(&self);
            for &id in chunk.nodes.iter() {
                println!("{}", &printer.print_node(id));
            }
        }
        println!("======================");
        let _env_init = self
            .env_vars
            .as_ref()
            .unwrap()
            .iter()
            .sorted()
            .map(|name| {
                let data_type = self.get_inferred_type(name);
                let expression = match &data_type {
                    DataType::Bool => format!("option_env!(\"{}\").is_some()", &name),
                    DataType::Integer => {
                        format!("option_env!(\"{}\").map(|s| s.parse()).flatten().unwrap_or_default()", &name)
                    }
                    DataType::List(item) if matches!(item.as_ref(), DataType::Literal) => format!(
                        "option_env!(\"{}\").unwrap_or_default().split_whitespace().map(|s| s.to_owned()).collect()",
                        &name
                    ),
                    DataType::Literal | DataType::Either(_, _) => format!(
                        "option_env!(\"{}\").unwrap_or_default().to_owned()",
                        &name
                    ),
                    DataType::Path => format!("option_env!(\"{}\").unwrap_or(\"\").into()", &name),
                    _ => todo!(),
                };
                let write_exists =
                    self.get_scopes(name.as_str())
                        .unwrap()
                        .first()
                        .is_some_and(|scope| {
                            !scope.writers.is_empty() || !scope.overwriters.is_empty()
                        });
                let mutability = if write_exists { "mut " } else { "    " };
                format!(
                    "let {}{}: {} = {};",
                    mutability,
                    name,
                    data_type.print(),
                    expression
                )
            })
            .collect::<Vec<_>>();
        let _default_init = self
            .var_usages
            .as_ref()
            .unwrap()
            .keys()
            .filter(|var_name| !self.env_vars.as_ref().unwrap().contains(var_name.as_str()))
            .filter(|var_name| {
                self.get_scopes(var_name.as_str()).is_some_and(|scopes| {
                    scopes
                        .first()
                        .is_some_and(|s| s.owner.is_none() && s.bound_by.is_none())
                })
            })
            .sorted()
            .map(|name| {
                let data_type = self.get_inferred_type(name);
                let mutability = if self
                    .get_scopes(name.as_str())
                    .unwrap()
                    .first()
                    .is_some_and(|scope| !scope.writers.is_empty() || !scope.overwriters.is_empty())
                {
                    "mut "
                } else {
                    "    "
                };
                format!(
                    "let {}{}: {} = Default::default();",
                    mutability,
                    name,
                    data_type.print()
                )
            })
            .collect::<Vec<_>>();
        // self.translate_chunks().await;
    }

    /// Translate chunk using LLMs
    pub(crate) async fn translate_chunks(&self) {
        let mut user = use_llm::LLMUser::new();
        let mut inputs = Vec::new();
        for (chunk_id, _) in self.chunks.iter().skip(276).take(1) {
            // for chunk_id in [124] {
            // conduct llm analysis
            let printer = printer::TranslatingPrinter::new(self);
            let script = self
                .chunks
                .get(chunk_id)
                .unwrap()
                .nodes
                .iter()
                .map(|nid| format!("{}", &printer.print_node(*nid)))
                .join("\n");
            let header = format!(
                "{} {{{}\n  ",
                self.print_chunk_skeleton_signature(chunk_id),
                {
                    let header = self.print_chunk_skeleton_body_header(chunk_id).join("\n  ");
                    if header.is_empty() {
                        "".into()
                    } else {
                        format!("\n  {}", header)
                    }
                }
            );
            let footer = format!("{}\n}}", {
                let footer = self.print_chunk_skeleton_body_footer(chunk_id);
                if footer.is_empty() {
                    "".into()
                } else {
                    format!("\n  {}", footer)
                }
            });
            let skeleton = format!("{}{{body}}{}", header, footer);
            let required_funcs = printer.get_required_rust_funcs();
            println!("{}: {}", chunk_id, &skeleton);
            println!("Chunk {} (Before):\n{}", chunk_id, &script);
            let input = TranslationInput::new(chunk_id, script, skeleton.clone(), &required_funcs);
            let evidence = TranslationEvidence {
                fixed_values: printer.collect_translated_fragments(),
                header,
                footer,
            };
            inputs.push((input, evidence));
        }

        let results = user
            .run_llm_analysis(inputs.iter().map(|(i, e)| (i, e)))
            .await;
        for res in results {
            let func_def = format!(
                "fn {}{} {{\n  {}\n}}",
                res.rust_func_name,
                self.print_chunk_skeleton_signature(res.id),
                self.print_chunk_skeleton_body_header(res.id)
                    .into_iter()
                    .chain(res.rust_func_body.split("\n").map(|s| s.to_owned()))
                    .chain(std::iter::once(
                        self.print_chunk_skeleton_body_footer(res.id)
                    ))
                    .filter(|s| !s.is_empty())
                    .join("\n  "),
            );
            println!("Chunk {} (After):\n{}", res.id, func_def)
        }
    }
}
