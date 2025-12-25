use itertools::Itertools;
use std::collections::{HashMap, HashSet};
use use_llm::{TranslationEvidence, TranslationInput};

use crate::{
    analyzer::{
        chunk::ChunkId,
        translator::{printer::TranslatingPrinter, use_llm::TranslationOutput},
        type_inference::DataType,
    },
    utils::llm_analysis::LLMAnalysis,
};

use super::Analyzer;

mod printer;
mod use_llm;

impl Analyzer {
    /// Analyze commands and build the dependency graph
    pub async fn translate(&mut self) {
        // println!("=== TRANSLATE DEBUG: Starting translation analysis ===");
        // let mut exported = HashSet::new();
        // for (i, chunk) in self.chunks.iter() {
        //     exported.extend(chunk.io.exported.clone());
        //     let last_id = *chunk.nodes.last().unwrap();
        //     println!(
        //         "Chunk {}: parent: {:?}, nodes {:?} , exit {:?}",
        //         i,
        //         chunk.parent,
        //         chunk
        //             .nodes
        //             .iter()
        //             .map(|id| (
        //                 *id,
        //                 self.collect_descendant_nodes_per_node(*id, true, false)
        //             ))
        //             .map(|(id, nodes)| (
        //                 id,
        //                 nodes
        //                     .into_iter()
        //                     .map(|i| self.get_node(i).unwrap().info.exec_id)
        //                     .sorted()
        //                     .collect::<Vec<_>>()
        //             ))
        //             .collect::<Vec<_>>(),
        //         self.get_node(last_id).unwrap().info.exit,
        //     );
        //     println!("signature: {}", self.print_chunk_skeleton_signature(i));
        //     println!("header: {:?}", self.print_chunk_skeleton_body_header(i));
        //     println!("footer: {}", self.print_chunk_skeleton_body_footer(i));
        //     println!(
        //         "callsite: {}",
        //         self.print_chunk_skeleton_call_site(i, &format!("func{}", i))
        //     );
        //     let printer = TranslatingPrinter::new(self);
        //     for &id in chunk.nodes.iter() {
        //         println!("{}", &printer.print_node(id));
        //     }
        // }
        // println!("======================");
        let tab = " ".repeat(TranslatingPrinter::get_tab_width());
        let env_init = self
            .env_vars
            .as_ref()
            .unwrap()
            .iter()
            .sorted()
            .map(|name| {
                let data_type = self.get_inferred_type(name);
                let expression = match &data_type {
                    DataType::Boolean => format!("option_env!(\"{}\").is_some()", &name),
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
                    "{tab}let {}{}: {} = {};",
                    mutability,
                    name,
                    data_type.print(),
                    expression
                )
            })
            .join("\n");
        let default_init = self
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
                    "{tab}let {}{}: {} = Default::default();",
                    mutability,
                    name,
                    data_type.print()
                )
            })
            .join("\n");
        let top_func_calls = self
            .chunks
            .iter()
            .filter(|(_, chunk)| chunk.parent.is_none())
            .map(|(chunk_id, chunk)| {
                let call_site = self.print_chunk_skeleton_call_site(
                    chunk_id,
                    &rust_func_placeholder_name(chunk_id),
                );
                format!("{tab}{call_site}")
            })
            .join("\n");
        println!(
            "fn main() {{\n{}\n{}\n{}\n}}",
            &env_init, &default_init, &top_func_calls
        );
        // let translated = self.translate_chunks().await;
        // let func_defs = self
        //     .chunks
        //     .iter()
        //     .filter(|(chunk_id, _)| translated.contains_key(&chunk_id))
        //     .map(|(chunk_id, _)| {
        //         self.get_rust_func_definition(
        //             chunk_id,
        //             &rust_func_placeholder_name(chunk_id),
        //             &translated.get(&chunk_id).unwrap().rust_func_body,
        //         )
        //     })
        //     .join("\n\n");
        // println!("{}", func_defs);
    }

    /// Translate chunk using LLMs
    async fn translate_chunks(&self) -> HashMap<ChunkId, TranslationOutput> {
        let mut results: HashMap<ChunkId, TranslationOutput> = Default::default();
        let mut user = use_llm::LLMUser::new();
        let mut inputs = Vec::new();
        let mut depending_funcs = HashMap::new();
        for (chunk_id, _) in self.chunks.iter().skip(20).take(1) {
            // conduct llm analysis
            let printer = TranslatingPrinter::new(self);
            let script = self
                .chunks
                .get(chunk_id)
                .unwrap()
                .nodes
                .iter()
                .map(|nid| printer.print_node(*nid).to_string())
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
            depending_funcs.insert(chunk_id, printer.get_embedded_chunks());
            let input = TranslationInput::new(chunk_id, script, skeleton.clone(), &required_funcs);
            let evidence = TranslationEvidence {
                rust_snippets: printer.get_translated_fragments(),
                header,
                footer,
            };
            inputs.push((input, evidence));
        }

        let llm_analysis_results = user
            .run_llm_analysis(inputs.iter().map(|(i, e)| (i, e)))
            .await;

        results.extend(llm_analysis_results.into_iter().map(|res| (res.id, res)));

        for chunk_id in results.keys().cloned().collect::<Vec<_>>() {
            for (id, placeholder) in depending_funcs.get(&chunk_id).unwrap() {
                if let Some(new_name) = results.get(id).map(|o| o.rust_func_name.clone()) {
                    let out = results.get_mut(&chunk_id).unwrap();
                    out.rust_func_body = out.rust_func_body.replace(placeholder, &new_name);
                }
            }
        }

        results
    }

    fn get_translation_inputs(&self) -> Vec<(TranslationInput, TranslationEvidence)> {
        let mut inputs = Vec::new();
        for (chunk_id, _) in self.chunks.iter() {
            // conduct llm analysis
            let printer = TranslatingPrinter::new(self);
            let script = self
                .chunks
                .get(chunk_id)
                .unwrap()
                .nodes
                .iter()
                .map(|nid| printer.print_node(*nid).to_string())
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
                rust_snippets: printer.get_translated_fragments(),
                header,
                footer,
            };
            inputs.push((input, evidence));
        }
        inputs
    }

    fn get_rust_func_definition(
        &self,
        chunk_id: ChunkId,
        func_name: &str,
        func_body: &str,
    ) -> String {
        let func_def = format!(
            "fn {}{} {{\n  {}\n}}",
            func_name,
            self.print_chunk_skeleton_signature(chunk_id),
            self.print_chunk_skeleton_body_header(chunk_id)
                .into_iter()
                .chain(func_body.split("\n").map(|s| s.to_owned()))
                .chain(std::iter::once(
                    self.print_chunk_skeleton_body_footer(chunk_id)
                ))
                .filter(|s| !s.is_empty())
                .join("\n  "),
        );
        func_def
    }
}

fn rust_func_placeholder_name(chunk_id: ChunkId) -> String {
    format!("func{}", chunk_id)
}
