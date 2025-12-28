use itertools::Itertools;
use std::collections::HashMap;
use use_llm::{LLMTranslationInput, TranslationEvidence};

use crate::{
    analyzer::{
        chunk::ChunkId,
        translator::{printer::TranslatingPrinter, use_llm::LLMTranslationOutput},
        type_inference::DataType,
        MayM4, ShellCommand,
    },
    utils::llm_analysis::LLMAnalysis,
};

use super::{AcWord, Analyzer};
use autotools_parser::ast::{node::WordFragment, Parameter};

mod printer;
mod use_llm;

#[derive(Debug, Clone)]
struct InlinedTranslation {
    pub id: ChunkId,
    pub inline_rust_code: Vec<String>,
}

#[derive(Debug, Clone)]
enum TranslationResult {
    Inlined(InlinedTranslation),
    LLM(LLMTranslationOutput),
}

impl Analyzer {
    /// Check if a chunk can be handled as a inlined translation
    fn is_inlined_chunk(&self, chunk_id: ChunkId) -> bool {
        let chunk = match self.chunks.get(chunk_id) {
            Some(chunk) => chunk,
            None => return false,
        };

        // Node count: 1-2 nodes only
        if chunk.nodes.len() > 2 {
            return false;
        }

        // No embedded chunks
        if !chunk.children.is_empty() {
            return false;
        }

        // Check all nodes are assignments
        for &node_id in &chunk.nodes {
            if let Some(node) = self.get_node(node_id) {
                match &node.cmd.0 {
                    MayM4::Shell(ShellCommand::Assignment(_, _)) => continue,
                    _ => return false,
                }
            } else {
                return false;
            }
        }

        // No complex dictionary operations
        if !chunk.io.dictionaries.is_empty() {
            return false;
        }

        // Simple imported/exported variables only
        let has_complex_deps = chunk.io.imported.len() > 3 || chunk.io.exported.len() > 2;
        if has_complex_deps {
            return false;
        }

        true
    }

    /// Translate a inlined chunk - fail fast on any complexity
    fn translate_inlined_chunk(&self, chunk_id: ChunkId) -> Option<InlinedTranslation> {
        let chunk = self.chunks.get(chunk_id)?;
        let skeleton = self
            .chunk_skeletons
            .as_ref()
            .unwrap()
            .get(&chunk_id)
            .unwrap();
        let mut rust_lines = Vec::new();

        for &node_id in &chunk.nodes {
            let node = self.get_node(node_id)?;

            if let MayM4::Shell(ShellCommand::Assignment(var_name, word)) = &node.cmd.0 {
                let rust_assignment = self.translate_inlined_assignment(var_name, word)?;
                let may_binding_rust_assignment = if let Some(mutability) = skeleton
                    .return_to_bind
                    .iter()
                    .find_map(|(mutability, name, _)| (name == var_name).then_some(mutability))
                {
                    format!(
                        "let {}{}",
                        if *mutability { "mut " } else { "" },
                        rust_assignment
                    )
                } else {
                    rust_assignment
                };
                rust_lines.push(may_binding_rust_assignment);
            } else {
                return None; // Non-assignment node, fail fast!
            }
        }

        if rust_lines.is_empty() {
            return None;
        }

        Some(InlinedTranslation {
            id: chunk_id,
            inline_rust_code: rust_lines,
        })
    }

    /// Translate a inlined assignment - returns None if too complex
    fn translate_inlined_assignment(&self, var_name: &str, word: &AcWord) -> Option<String> {
        use autotools_parser::ast::minimal::Word;

        let data_type = self.get_inferred_type(var_name);

        match &word.0 {
            Word::Single(MayM4::Shell(fragment)) => {
                match fragment {
                    WordFragment::Literal(literal) => {
                        self.translate_literal_assignment(var_name, literal, &data_type)
                    }
                    WordFragment::Param(Parameter::Var(other_var)) => {
                        Some(format!("{} = {}.clone();", var_name, other_var))
                    }
                    WordFragment::DoubleQuoted(fragments) => {
                        self.translate_quoted_assignment(var_name, fragments, &data_type)
                    }
                    _ => None, // Too complex
                }
            }
            _ => None, // Too complex
        }
    }

    /// Translate literal assignment based on type
    fn translate_literal_assignment(
        &self,
        var_name: &str,
        literal: &str,
        data_type: &DataType,
    ) -> Option<String> {
        match data_type {
            DataType::Boolean => {
                let rust_value = match literal {
                    "yes" | "1" => "true",
                    "no" | "0" | "" => "false",
                    _ => return None,
                };
                Some(format!("{} = {};", var_name, rust_value))
            }

            DataType::Integer => {
                if literal.chars().all(|c| c.is_numeric()) {
                    Some(format!("{} = {};", var_name, literal))
                } else if literal.is_empty() {
                    Some(format!("{} = 0;", var_name))
                } else {
                    None
                }
            }

            DataType::Path => Some(format!("{} = PathBuf::from(\"{}\");", var_name, literal)),

            DataType::List(inner_type) if matches!(inner_type.as_ref(), DataType::Literal) => {
                if literal.is_empty() {
                    Some(format!("{} = Vec::new();", var_name))
                } else {
                    let items: Vec<String> = literal
                        .split_whitespace()
                        .map(|s| format!("\"{}\".to_string()", s))
                        .collect();
                    Some(format!("{} = vec![{}];", var_name, items.join(", ")))
                }
            }

            DataType::Literal | DataType::Either(_, _) => {
                Some(format!("{} = \"{}\".to_string();", var_name, literal))
            }

            _ => None,
        }
    }

    /// Translate quoted assignment (handles appends)
    fn translate_quoted_assignment(
        &self,
        var_name: &str,
        fragments: &[WordFragment<AcWord>],
        data_type: &DataType,
    ) -> Option<String> {
        let has_self_ref = fragments
            .iter()
            .any(|f| matches!(f, WordFragment::Param(Parameter::Var(v)) if v == var_name));

        if has_self_ref {
            let additional_literals: Vec<&str> = fragments
                .iter()
                .filter_map(|f| match f {
                    WordFragment::Literal(lit) if !lit.trim().is_empty() => Some(lit.as_str()),
                    _ => None,
                })
                .collect();

            if additional_literals.len() != 1 {
                return None;
            }

            let additional = additional_literals[0].trim();
            if additional.is_empty() {
                return None;
            }

            match data_type {
                DataType::List(inner_type) if matches!(inner_type.as_ref(), DataType::Literal) => {
                    let items: Vec<String> = additional
                        .split_whitespace()
                        .map(|s| format!("{}.push(\"{}\".to_string());", var_name, s))
                        .collect();
                    Some(items.join("\n"))
                }
                DataType::Literal | DataType::Either(_, _) => {
                    Some(format!("{}.push_str(\" {}\");", var_name, additional))
                }
                _ => None,
            }
        } else {
            None
        }
    }

    /// Translate the scripts
    pub async fn translate(&mut self) {
        let tab = " ".repeat(TranslatingPrinter::get_tab_width());
        let env_init = 
                self.env_vars
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
        let default_init = 
                self.var_usages
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
                        let mutability =
                            if self.get_scopes(name.as_str()).unwrap().first().is_some_and(
                                |scope| !scope.writers.is_empty() || !scope.overwriters.is_empty(),
                            ) {
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
        let subst_end = self
            .subst_vars
            .as_ref()
            .unwrap()
            .iter()
            .map(|var| format!("{}: {}", var, self.get_inferred_type(var).print()))
            .collect::<Vec<_>>();
        dbg!(&subst_end);
        let translated = self.translate_chunks().await;
        let main_function_body = 
                self.chunks
                    .iter()
                    .filter(|(_, chunk)| chunk.parent.is_none())
                    .filter(|(chunk_id, _)| translated.contains_key(&chunk_id))
                    .map(|(chunk_id, _)| match translated.get(&chunk_id).unwrap() {
                        TranslationResult::Inlined(res) => {
                            format!("{tab}{}", res.inline_rust_code.join(&format!("\n{tab}")))
                        }
                        TranslationResult::LLM(_) => {
                            let call_site = self.print_chunk_skeleton_call_site(
                                chunk_id,
                                &rust_func_placeholder_name(chunk_id),
                            );
                            format!("{tab}{call_site}")
                        }
                    })
            .join("\n");
        let footer = {
            let dummy = Default::default();
            let printer = TranslatingPrinter::new(self, &dummy, true);

            // Deduplicate by cfg_key
            let mut src_incl_conds: std::collections::HashMap<String, _> =
                std::collections::HashMap::new();

            for conds in self
                .conditional_compilation_map
                .as_ref()
                .unwrap()
                .src_incl_map
                .values()
            {
                for cond in conds {
                    src_incl_conds.entry(cond.cfg_key.clone()).or_insert(cond);
                }
            }

            src_incl_conds
                .values()
                .map(|cond| {
                    let guard = self
                        .automake()
                        .am_cond_to_guard
                        .get(&cond.am_conditional_name)
                        .unwrap();
                    let cargo_instruction = format!("\"cargo::rustc-cfg={}\"", cond.cfg_key);
                    let print_line = format!("println!({});", cargo_instruction);
                    format!(
                        "{tab}if {}{{\n{tab}{tab}{}\n{tab}}}",
                        printer.display_guard(&guard),
                        print_line
                    )
                })
                .join("\n")
        };
        println!(
            "fn main() {{
{tab}// import environmental variables
{}
{tab}// default variables initialization
{}
{tab}// translated fragments
{}
{tab}// export cfg
{}
}}",
            &env_init, &default_init, &main_function_body, &footer
        );
        let func_defs = self
            .chunks
            .iter()
            .filter(|(chunk_id, _)| translated.contains_key(&chunk_id))
            .filter_map(|(chunk_id, _)| match translated.get(&chunk_id).unwrap() {
                TranslationResult::Inlined(res) => None,
                TranslationResult::LLM(res) => Some(res),
            })
            .map(|res| {
                self.construct_rust_func_definition(
                    res.id,
                    &rust_func_placeholder_name(res.id),
                    &res.rust_func_body,
                )
            })
            .join("\n\n");
        println!("{}", func_defs);
    }

    /// Translate chunks using inlined translation or LLMs
    async fn translate_chunks(&self) -> HashMap<ChunkId, TranslationResult> {
        let mut results = HashMap::new();
        let mut llm_results: HashMap<ChunkId, LLMTranslationOutput> = HashMap::new();
        let mut user = use_llm::LLMUser::new();
        let mut inputs = Vec::new();
        let mut depending_funcs = HashMap::new();

        return results;
        // Collect rule-based translations for inlining during LLM processing
        let inlined_translations: HashMap<ChunkId, InlinedTranslation> = self
            .chunks
            .iter()
            .filter_map(|(chunk_id, _)| {
                if self.is_inlined_chunk(chunk_id) {
                    self.translate_inlined_chunk(chunk_id)
                        .map(|st| (chunk_id, st))
                } else {
                    None
                }
            })
            .collect();

        // Process all chunks: inlined ones go directly to results, complex ones go to LLM
        for (chunk_id, _) in self.chunks.iter() {
            if let Some(inlined_translation) = inlined_translations.get(&chunk_id) {
                results.insert(
                    chunk_id,
                    TranslationResult::Inlined(inlined_translation.clone()),
                );
                continue;
            }

            // Conduct LLM analysis with inlined translations available for inlining
            let printer = TranslatingPrinter::new(self, &inlined_translations, false);
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
            let input =
                LLMTranslationInput::new(chunk_id, script, skeleton.clone(), &required_funcs);
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

        llm_results.extend(llm_analysis_results.into_iter().map(|res| (res.id, res)));

        // Handle LLM function name dependencies
        for chunk_id in llm_results.keys().cloned().collect::<Vec<_>>() {
            for (id, placeholder) in depending_funcs.get(&chunk_id).unwrap() {
                if let Some(new_name) = llm_results.get(id).map(|o| o.rust_func_name.clone()) {
                    let out = llm_results.get_mut(&chunk_id).unwrap();
                    out.rust_func_body = out.rust_func_body.replace(placeholder, &new_name);
                }
            }
        }

        // Convert LLM results to ChunkTranslationResult and merge with inlined results
        for (chunk_id, llm_output) in llm_results {
            results.insert(chunk_id, TranslationResult::LLM(llm_output));
        }

        results
    }

    fn construct_rust_func_definition(
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
