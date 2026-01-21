use itertools::Itertools;
use std::{
    collections::{HashMap, HashSet},
    hash::{DefaultHasher, Hash, Hasher},
    path::{Path, PathBuf},
};
use use_llm::{LLMBasedTranslationEvidence, LLMBasedTranslationInput};

use std::time::Duration;

use crate::{
    analyzer::{
        chunk::ChunkId,
        conditional_compilation::CCMigrationType,
        pkg_config::get_function_definition_bindgen,
        record::TranslationType,
        translator::{
            printer::TranslatingPrinter,
            use_llm::{LLMBasedTranslationOutput, LLMUser, LLMValidationFunc},
        },
        type_inference::DataType,
        MayM4, ShellCommand,
    },
    utils::llm_analysis::LLMAnalysis,
};

use super::{AcWord, Analyzer};
use autotools_parser::ast::{node::WordFragment, Parameter};

mod pretranslation;
mod printer;
mod use_llm;

#[derive(Debug, Clone)]
struct InlinedTranslationOutput {
    pub id: ChunkId,
    pub inline_rust_code: Vec<String>,
}

#[derive(Debug, Clone)]
enum ChunkTranslationOutput {
    Inlined(InlinedTranslationOutput),
    LLM(LLMBasedTranslationOutput),
}

/// Metadata for recording chunk translation results
#[derive(Debug, Clone)]
struct ChunkTranslationMeta {
    chunk_size: usize,
    translation_type: TranslationType,
    success: bool,
    failure_reason: Option<String>,
    llm_cost: Option<f64>,
    duration: Duration,
    retry_count: usize,
}

impl ChunkTranslationMeta {
    fn empty(chunk_size: usize, retry_count: usize) -> Self {
        Self {
            chunk_size,
            translation_type: TranslationType::LLMAssisted,
            success: false,
            failure_reason: None,
            llm_cost: None,
            duration: Duration::ZERO,
            retry_count,
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) struct TranslationResult {
    env_init: String,
    default_init: String,
    main_function_body: String,
    subst_to_cpps: String,
    src_incl_conds: String,
    recording: String,
    bindgen: String,
    chunk_funcs: Vec<String>,
}

impl Analyzer {
    /// Check if a chunk can be handled as a inlined translation
    fn is_inlined_chunk(&self, chunk_id: ChunkId) -> bool {
        let chunk = match self.chunks.get(chunk_id) {
            Some(chunk) => chunk,
            None => return false,
        };

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
    fn translate_inlined_chunk(&self, chunk_id: ChunkId) -> Option<InlinedTranslationOutput> {
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
                    .get(var_name)
                    .map(|(is_mut, _)| is_mut)
                {
                    format!(
                        "let {}{}",
                        if *mutability { "mut " } else { "" },
                        rust_assignment
                    )
                } else if skeleton.return_to_overwrite.is_some() {
                    rust_assignment
                } else {
                    "".to_owned()
                };
                rust_lines.push(may_binding_rust_assignment);
            } else {
                return None; // Non-assignment node, fail fast!
            }
        }

        if rust_lines.is_empty() {
            return None;
        }

        Some(InlinedTranslationOutput {
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

    /// debug print of chunks that would be fed to LLMs
    pub(crate) fn debug_print_chunks(&mut self) {
        println!("=== TRANSLATE DEBUG: Starting translation analysis ===");
        for (i, chunk) in self.chunks.iter() {
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
                self.print_chunk_skeleton_call_site(None, i, &format!("func{}", i))
            );
            println!("=====body=====");
            let printer = TranslatingPrinter::new(&self, None, false);
            for &id in chunk.nodes.iter() {
                println!("{}", &printer.print_node(id));
            }
            println!(
                "\n[required_snippets]:\n{}",
                printer.get_required_snippets().join("\n")
            );
            println!("==============");
        }
    }

    /// Translate the scripts
    pub async fn translate(&mut self) -> TranslationResult {
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
                    DataType::List(item) if matches!(item.as_ref(), DataType::Literal) => if let Some(val) = has_known_value(name) {
                        format!("option_env!(\"{}\").unwrap_or(\"{}\").split_whitespace().map(|s| s.to_owned()).collect()", name, val)
                    } else {
                        format!("option_env!(\"{}\").unwrap_or_default().split_whitespace().map(|s| s.to_owned()).collect()", name)
                    },
                    DataType::Literal | DataType::Either(_, _) =>  if let Some(val) = has_known_value(name) {
                        format!("option_env!(\"{}\").unwrap_or(\"{}\").to_owned()", name, val)
                    } else {
                        format!("option_env!(\"{}\").unwrap_or_default().to_owned()", name)
                    },
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

        let unused_subst_vars = self.subst_vars.as_ref().unwrap().iter().filter(|var| {
            self.var_scopes
                .as_ref()
                .unwrap()
                .get(var.as_str())
                .is_none_or(|scopes| scopes.first().is_none_or(|scope| scope.owner.is_none()))
        });
        let default_init = self
            .var_scopes
            .as_ref()
            .unwrap()
            .iter()
            .filter(|(_, scopes)| {
                scopes
                    .first()
                    .is_some_and(|s| s.owner.is_none() && s.bound_by.is_none())
            })
            .map(|(var_name, _)| var_name)
            .chain(unused_subst_vars)
            .filter(|var_name| !self.env_vars.as_ref().unwrap().contains(var_name.as_str()))
            .collect::<HashSet<_>>()
            .into_iter()
            .sorted()
            .map(|name| {
                let data_type = self.get_inferred_type(name);
                let mutability = if self.get_scopes(name.as_str()).is_some_and(|scopes| {
                    scopes.first().is_some_and(|scope| {
                        !scope.writers.is_empty() || !scope.overwriters.is_empty()
                    })
                }) {
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
            .chain(self.dicts.as_ref().unwrap().iter().map(|dict| {
                let dict_type_str = self.print_dictionary_type(&dict.name);
                format!(
                    "{tab}let mut {}: {} = Default::default();",
                    dict.name, dict_type_str
                )
            }))
            .join("\n");
        let (translated, translation_cache_used) = self.translate_chunks().await;

        // Mark if translation cache was used
        if translation_cache_used {
            self.record_collector_mut().set_translation_cache_used();
        }

        // Record each chunk translation
        for (chunk_id, (_, meta)) in translated.iter() {
            self.record_collector_mut().add_chunk_record(
                *chunk_id,
                meta.chunk_size,
                meta.translation_type.clone(),
                meta.success,
                meta.failure_reason.clone(),
                meta.llm_cost,
                meta.duration,
                meta.retry_count,
            );
        }

        let main_function_body = self
            .chunks
            .iter()
            .filter(|(_, chunk)| chunk.parent.is_none())
            .filter(|(chunk_id, _)| translated.contains_key(&chunk_id))
            .map(
                |(chunk_id, _)| match translated.get(&chunk_id).unwrap().0.as_ref() {
                    Some(ChunkTranslationOutput::Inlined(res)) => {
                        format!("{tab}{}", res.inline_rust_code.join(&format!("\n{tab}")))
                    }
                    Some(ChunkTranslationOutput::LLM(output)) => {
                        let call_site = self.print_chunk_skeleton_call_site(
                            None,
                            chunk_id,
                            output.rust_func_name.as_str(),
                        );
                        format!("{tab}{call_site}")
                    }
                    None => {
                        let call_site = self.print_chunk_skeleton_call_site(
                            None,
                            chunk_id,
                            &rust_func_placeholder_name(chunk_id),
                        );
                        format!("{tab}{call_site}")
                    }
                },
            )
            .join("\n");

        let subst_to_cpps = {
            self.conditional_compilation_map
                .as_ref()
                .unwrap()
                .subst_to_cpp_map
                .iter()
                .sorted_by_key(|(k, _)| (*k).clone())
                .map(|(var, policy)| match &policy.mig_type {
                    CCMigrationType::Cfg => format!(
                        "{tab}if {} {{\n{tab}{tab}define_cfg({:?}, None);\n{tab}}}",
                        var,
                        policy.key.as_ref().unwrap()
                    ),
                    CCMigrationType::Env => {
                        let expression =
                            printer::display_var_as_rust_str(var, &self.get_inferred_type(var));
                        format!(
                            "{tab}define_env({:?}, {});",
                            policy.key.as_ref().unwrap(),
                            expression
                        )
                    }
                    _ => unreachable!(),
                })
                .join("\n")
        };

        let src_incl_conds = {
            let printer = TranslatingPrinter::new(self, None, true);

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
                    let define_cfg = format!("define_cfg({:?}, None);", cond.cfg_key);
                    format!(
                        "{tab}if {} {{\n{tab}{tab}{}\n{tab}}}",
                        printer.display_guard(&guard),
                        define_cfg
                    )
                })
                .join("\n")
        };

        // Generate evaluation output section
        let recording = {
            let mut output = Vec::new();

            // Output subst variables
            if let Some(subst_vars) = &self.subst_vars {
                for var_name in subst_vars.iter().sorted() {
                    let data_type = self.get_inferred_type(var_name);
                    let var_output = match data_type {
                        DataType::List(ty) if *ty == DataType::Literal => {
                            format!("{}.join(\" \")", var_name)
                        }
                        DataType::Boolean => format!("{}.to_string()", var_name),
                        DataType::Integer => format!("{}.to_string()", var_name),
                        DataType::Path => format!("{}.to_str().unwrap()", var_name),
                        DataType::Optional(ty) if *ty == DataType::Literal => format!(
                            "{}.as_ref().map(|v| v.as_str()).unwrap_or_default()",
                            var_name
                        ),
                        DataType::Literal | DataType::Either(_, _) => var_name.to_string(),
                        _ => todo!(),
                    };
                    output.push(format!(
                        "{tab}record(\"subst\", \"{}\", &{});",
                        var_name, var_output
                    ));
                }
            }

            output.join("\n")
        };

        let bindgen = if !self
            .pkg_config_analyzer()
            .pkg_check_modules_calls
            .is_empty()
        {
            let mut cflags_var_names = self.project_info.cflags_var_names.clone();
            if cflags_var_names.is_empty() {
                cflags_var_names.push("CFLAGS".into());
            }
            get_bindgen_callsite(&tab, &cflags_var_names)
        } else {
            Default::default()
        };

        let chunk_funcs = self
            .chunks
            .iter()
            .filter(|(chunk_id, _)| translated.contains_key(&chunk_id))
            .filter_map(
                |(chunk_id, _)| match translated.get(&chunk_id).unwrap().0.as_ref() {
                    Some(ChunkTranslationOutput::Inlined(_)) => None,
                    Some(ChunkTranslationOutput::LLM(output)) => {
                        Some(self.construct_rust_func_definition(
                            output.id,
                            &output.rust_func_name,
                            &output.rust_func_body,
                        ))
                    }
                    None => Some(self.construct_dummy_rust_func_definition(
                        chunk_id,
                        &rust_func_placeholder_name(chunk_id),
                    )),
                },
            )
            .collect();

        TranslationResult {
            env_init,
            default_init,
            main_function_body,
            subst_to_cpps,
            src_incl_conds,
            recording,
            bindgen,
            chunk_funcs,
        }
    }

    /// Translate chunks using inlined translation or LLMs
    /// Returns (translations, cache_used) where cache_used is true if translation cache was hit
    async fn translate_chunks(
        &self,
    ) -> (
        HashMap<ChunkId, (Option<ChunkTranslationOutput>, ChunkTranslationMeta)>,
        bool,
    ) {
        let mut results = HashMap::new();
        let mut cache_used = false;
        let mut user = LLMUser::new();
        let mut inputs = Vec::new();
        let mut depending_funcs = HashMap::new();

        // Collect rule-based translations for inlining during LLM processing
        let mut inlined_translations: HashMap<ChunkId, InlinedTranslationOutput> = self
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

        // Add inlined translations with metadata
        for (chunk_id, inlined_translation) in inlined_translations.iter() {
            let chunk_size = self
                .chunks
                .get(*chunk_id)
                .map(|c| c.nodes.len())
                .unwrap_or(0);
            let meta = ChunkTranslationMeta {
                chunk_size,
                translation_type: TranslationType::Inlined,
                success: true,
                failure_reason: None,
                llm_cost: None,
                duration: Duration::ZERO,
                retry_count: 0,
            };
            results.insert(
                *chunk_id,
                (
                    Some(ChunkTranslationOutput::Inlined(inlined_translation.clone())),
                    meta,
                ),
            );
        }

        let max_retries = 5;
        // Track LLM metadata separately since cache may not have it
        let mut llm_chunk_ids: Vec<ChunkId> = Vec::new();
        let mut llm_metadata: HashMap<ChunkId, ChunkTranslationMeta> = HashMap::new();

        let llm_translations = if let Some(cached) = self.load_translation_cache() {
            // For cached translations, we don't have the original metadata
            cache_used = true;
            for (chunk_id, _) in cached.iter() {
                llm_chunk_ids.push(*chunk_id);
                let chunk_size = self
                    .chunks
                    .get(*chunk_id)
                    .map(|c| c.nodes.len())
                    .unwrap_or(0);
                llm_metadata.insert(
                    *chunk_id,
                    ChunkTranslationMeta {
                        chunk_size,
                        translation_type: TranslationType::LLMAssisted,
                        success: true,
                        failure_reason: None,
                        llm_cost: None,           // Not available from cache
                        duration: Duration::ZERO, // Not available from cache
                        retry_count: 0,           // Not available from cache
                    },
                );
            }
            cached
        } else {
            if use_llm::get_rust_check_dir().exists() {
                // clean directory
                std::fs::remove_dir_all(use_llm::get_rust_check_dir())
                    .expect("Failed to remove a directory");
            }
            // Process all chunks: inlined ones go directly to results, complex ones go to LLM
            for chunk in self.get_topologically_sorted_chunks() {
                let chunk_id = chunk.chunk_id;
                if inlined_translations.contains_key(&chunk_id) {
                    // inlined chunk
                    continue;
                }

                // Conduct LLM analysis with inlined translations available for inlining
                let printer = TranslatingPrinter::new(self, Some(&inlined_translations), false);
                let script = self
                    .chunks
                    .get(chunk_id)
                    .unwrap()
                    .nodes
                    .iter()
                    .map(|nid| printer.print_node(*nid).to_string())
                    .join("\n");

                if script.trim().is_empty() {
                    // empty chunk
                    let inlined_output = InlinedTranslationOutput {
                        id: chunk_id,
                        inline_rust_code: Vec::new(),
                    };
                    let meta = ChunkTranslationMeta {
                        chunk_size: 0,
                        translation_type: TranslationType::Inlined,
                        success: true,
                        failure_reason: None,
                        llm_cost: None,
                        duration: Duration::ZERO,
                        retry_count: 0,
                    };
                    results.insert(
                        chunk_id,
                        (
                            Some(ChunkTranslationOutput::Inlined(inlined_output.clone())),
                            meta,
                        ),
                    );
                    inlined_translations.insert(chunk_id, inlined_output);
                    continue;
                }

                let signature = self.print_chunk_skeleton_signature(chunk_id);
                let body_header = format!("{}\n  ", {
                    let header = self.print_chunk_skeleton_body_header(chunk_id).join("\n  ");
                    if header.is_empty() {
                        "".into()
                    } else {
                        format!("\n  {}", header)
                    }
                });
                let body_footer = format!("{}\n", {
                    let footer = self.print_chunk_skeleton_body_footer(chunk_id);
                    if footer.is_empty() {
                        "".into()
                    } else {
                        format!("\n  {}", footer)
                    }
                });
                let skeleton = format!("{} {{{}{{body}}{}}}", signature, body_header, body_footer);
                let required_funcs = printer.get_rust_funcs_required_for_chunk();
                let embedded_chunks = printer.get_embedded_chunks();
                depending_funcs.insert(chunk_id, embedded_chunks.clone());

                // Generate dummy function definitions for all embedded/depending chunks
                let depending_func_defs = embedded_chunks
                    .iter()
                    .filter(|(_, placeholder)| *placeholder != "inlined")
                    .map(|(dep_chunk_id, placeholder)| {
                        self.construct_dummy_rust_func_definition(*dep_chunk_id, &placeholder)
                    })
                    .collect::<Vec<_>>()
                    .join("\n\n");

                let input = LLMBasedTranslationInput::new(
                    chunk_id,
                    script,
                    skeleton.clone(),
                    &required_funcs,
                );
                let extra_validation_funcs = if let Some(threshold) =
                    printer.get_max_num_consecutive_slashes()
                {
                    vec![Box::new(move |content: &str| -> Option<String> {
                        let mut consecutive_count = 0;
                        for c in content.chars() {
                            if c == '\\' {
                                consecutive_count += 1;
                                if consecutive_count > threshold {
                                    return Some(format!(
                                            "Detected excessive usage of slash characters: '{}', which must be invalid.",
                                            std::iter::repeat('\\').take(threshold).collect::<String>()
                                        ));
                                }
                            } else {
                                consecutive_count = 0;
                            }
                        }
                        None
                    }) as LLMValidationFunc]
                } else {
                    Default::default()
                };
                let evidence = LLMBasedTranslationEvidence {
                    id: chunk_id,
                    snippets: printer.get_required_snippets(),
                    extra_validation_funcs,
                    predefinition: use_llm::get_predefinition(&required_funcs),
                    features: printer.get_cargo_features(),
                    signature,
                    body_header,
                    body_footer,
                    depending_func_defs,
                    heredoc_placeholders: printer.get_heredoc_placeholders(),
                };
                inputs.push((input, evidence));
                llm_chunk_ids.push(chunk_id);
            }

            let mut res = HashMap::new();
            if self.options.use_llm {
                let llm_results = user
                    .run_llm_analysis(inputs.iter().map(|(i, e)| (i, e)), max_retries)
                    .await;

                // Process results and collect metadata
                for result in llm_results {
                    let chunk_id = result.output.id;
                    let chunk_size = self
                        .chunks
                        .get(chunk_id)
                        .map(|c| c.nodes.len())
                        .unwrap_or(0);
                    llm_metadata.insert(
                        chunk_id,
                        ChunkTranslationMeta {
                            chunk_size,
                            translation_type: TranslationType::LLMAssisted,
                            success: true,
                            failure_reason: None,
                            llm_cost: result.cost,
                            duration: result.duration,
                            retry_count: result.retry_count,
                        },
                    );
                    // Heredoc placeholder restoration is handled in validate()
                    res.insert(chunk_id, result.output);
                }

                if self.options.rename_rust_functions {
                    // Handle LLM function name dependencies
                    let collided_func_names: HashMap<ChunkId, String> = {
                        let mut func_names = HashSet::new();
                        let mut fallback_names = HashMap::new();
                        for (chunk_id, output) in res.iter() {
                            if func_names.contains(&output.rust_func_name) {
                                fallback_names
                                    .insert(*chunk_id, rust_func_placeholder_name(*chunk_id));
                            } else {
                                func_names.insert(output.rust_func_name.clone());
                            }
                        }
                        fallback_names
                    };
                    for (chunk_id, fallback_name) in collided_func_names {
                        res.get_mut(&chunk_id).unwrap().rust_func_name = fallback_name;
                    }
                    for chunk_id in res.keys().cloned().collect::<Vec<_>>() {
                        for (id, placeholder) in depending_funcs.get(&chunk_id).unwrap() {
                            if let Some(new_name) = res.get(id).map(|o| o.rust_func_name.clone()) {
                                let out = res.get_mut(&chunk_id).unwrap();
                                out.rust_func_body =
                                    out.rust_func_body.replace(placeholder, &new_name);
                            }
                        }
                    }
                } else {
                    for chunk_id in res.keys().cloned().collect::<Vec<_>>() {
                        res.get_mut(&chunk_id).unwrap().rust_func_name =
                            rust_func_placeholder_name(chunk_id);
                    }
                }
                self.save_translation_cache(&res);
            }
            res
        };

        // Convert LLM results to ChunkTranslationResult and merge with inlined results
        for chunk_id in llm_chunk_ids {
            let chunk_size = self
                .chunks
                .get(chunk_id)
                .map(|c| c.nodes.len())
                .unwrap_or(0);
            let output = llm_translations
                .get(&chunk_id)
                .cloned()
                .map(ChunkTranslationOutput::LLM);
            let meta = llm_metadata
                .remove(&chunk_id)
                .unwrap_or_else(|| ChunkTranslationMeta::empty(chunk_size, max_retries));
            results.insert(chunk_id, (output, meta));
        }

        (results, cache_used)
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

    fn construct_dummy_rust_func_definition(&self, chunk_id: ChunkId, func_name: &str) -> String {
        // Get skeleton to access return variables
        let sk = self.get_chunk_skeleton(chunk_id).unwrap();

        // Collect all declarations: declared + return_to_bind + return_to_overwrite
        let declarations: Vec<String> =
            sk.declared
                .iter()
                .chain(sk.return_to_bind.iter())
                .map(|(name, (is_mut, ty))| {
                    let mutability = if *is_mut { "mut " } else { "" };
                    format!(
                        "let {}{}: {} = Default::default();",
                        mutability,
                        name,
                        ty.print()
                    )
                })
                .chain(sk.return_to_overwrite.iter().map(|(name, ty)| {
                    format!("let {}: {} = Default::default();", name, ty.print())
                }))
                .collect();

        format!(
            "fn {}{} {{\n  {}\n}}",
            func_name,
            self.print_chunk_skeleton_signature(chunk_id),
            declarations
                .into_iter()
                .chain(std::iter::once(
                    self.print_chunk_skeleton_body_footer(chunk_id)
                ))
                .filter(|s| !s.is_empty())
                .collect::<Vec<_>>()
                .join("\n  ")
        )
    }
}

fn rust_func_placeholder_name(chunk_id: ChunkId) -> String {
    format!("func{}", chunk_id)
}

impl Analyzer {
    /// Load cached translation results for all chunks
    fn load_translation_cache(&self) -> Option<HashMap<ChunkId, LLMBasedTranslationOutput>> {
        if !self.options.use_translation_cache {
            return None;
        }

        let cache_path = self.get_translation_cache_path();
        if let Ok(content) = std::fs::read(&cache_path) {
            let config = bincode::config::standard();
            if let Ok((cached_results, _)) = bincode::decode_from_slice::<
                HashMap<ChunkId, LLMBasedTranslationOutput>,
                _,
            >(&content, config)
            {
                println!("Loaded translation cache from: {:?}", cache_path);
                return Some(cached_results);
            }
        }
        None
    }

    /// Save translation results to cache for all chunks
    fn save_translation_cache(&self, results: &HashMap<ChunkId, LLMBasedTranslationOutput>) {
        if !self.options.use_translation_cache {
            return;
        }

        let cache_path = self.get_translation_cache_path();
        let config = bincode::config::standard();
        if let Ok(content) = bincode::encode_to_vec(results, config) {
            if let Ok(()) = std::fs::write(&cache_path, content) {
                println!("Saved translation cache to: {:?}", cache_path);
            }
        }
    }

    /// Get cache file path for all translation results
    fn get_translation_cache_path(&self) -> PathBuf {
        let mut hasher = DefaultHasher::new();

        // Hash the script path
        self.path.to_str().unwrap().hash(&mut hasher);

        // Hash all chunks content to ensure cache validity
        for (chunk_id, chunk) in &self.chunks {
            chunk_id.hash(&mut hasher);

            // Hash the chunk's script content
            let script_content = chunk
                .nodes
                .iter()
                .map(|nid| self.display_node(*nid))
                .collect::<Vec<_>>()
                .join("\n");
            script_content.hash(&mut hasher);

            // Hash the function skeleton
            let signature = self.print_chunk_skeleton_signature(chunk_id);
            let header = self.print_chunk_skeleton_body_header(chunk_id).join("\n");
            let footer = self.print_chunk_skeleton_body_footer(chunk_id);

            signature.hash(&mut hasher);
            header.hash(&mut hasher);
            footer.hash(&mut hasher);
        }

        let h = hasher.finish();
        PathBuf::from(format!("/tmp/translation_cache.{:x}.bin", h))
    }
}

impl Analyzer {
    pub(crate) fn print_build_rs(&self, res: &TranslationResult, record_path: &Path) -> String {
        let tab = " ".repeat(TranslatingPrinter::get_tab_width());
        let predefinition = self.get_predefinition_with_recording(record_path.to_str().unwrap());
        let build_rs = format!(
            "#![allow(non_snake_case)]

// predefinition
{}

fn main() {{
{tab}// import environmental variables
{}
{tab}// default variables initialization
{}
{tab}// translated fragments
{}
{tab}// export cfg/env via subst
{}
{tab}// export cfg for am conditionals
{}
{tab}// bindgen
{}
{tab}// record subst vars for evaluation
{}
}}

// chunk functions
{}",
            &predefinition,
            &res.env_init,
            &res.default_init,
            &res.main_function_body,
            &res.subst_to_cpps,
            &res.src_incl_conds,
            &res.bindgen,
            &res.recording,
            &res.chunk_funcs.join("\n\n")
        );
        build_rs
    }

    fn get_predefinition_with_recording(&self, record_path: &str) -> String {
        use_llm::get_predefinition(&[
            "module_regex",
            "module_pkg_config",
            "write_file",
            "define_cfg_with_record",
            "define_env_with_record",
            "sanitize_rust_name",
            "check_header",
            "check_library",
            "check_decl",
            "check_compile",
            "check_func",
            "check_link",
            "pkg_config",
        ]) + &get_function_definition_record(record_path)
            + "\n"
            + &get_function_definition_bindgen()
    }
}

fn get_function_definition_record(record_path: &str) -> String {
    format!(
        r#"
fn record(category: &str, key: &str, value: &str) {{
  let path = PathBuf::from("{}");
  if !path.exists() {{
    write_file(&path, "category,key,value");
  }}
  let line = format!("{{}},{{}},\"{{}}\"", category, key, value.trim());
  write_file(&path, &line)
}}"#,
        record_path
    )
}

fn get_bindgen_callsite<S: std::fmt::Display>(tab: &str, cflags_var_names: &[S]) -> String {
    format!(
        r#"{tab}let mut cflags = Vec::new();
{tab}for v in [{}] {{
{tab}{tab}cflags.extend(v.iter().map(|flag| flag.split_whitespace()).flatten());
{tab}}}
{tab}run_bindgen(&cflags);
"#,
        cflags_var_names
            .iter()
            .map(|var_name| format!("&{}", var_name))
            .join(", ")
    )
}

lazy_static::lazy_static! {
    /// Predefined m4/autoconf macros
    static ref KNOWN_VALUES: HashMap<String, String> = known_values();
}

fn known_values() -> HashMap<String, String> {
    HashMap::from([("CC".into(), "cc".into()), ("AWK".into(), "awk".into())])
}

fn has_known_value(name: &str) -> Option<String> {
    KNOWN_VALUES.get(name).cloned()
}
