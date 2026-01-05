use itertools::Itertools;
use std::{
    collections::HashMap,
    hash::{DefaultHasher, Hash, Hasher},
    path::{Path, PathBuf},
};
use use_llm::{LLMBasedTranslationEvidence, LLMBasedTranslationInput};

use crate::{
    analyzer::{
        chunk::ChunkId,
        translator::{printer::TranslatingPrinter, use_llm::LLMBasedTranslationOutput},
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
struct InlinedTranslationOutput {
    pub id: ChunkId,
    pub inline_rust_code: Vec<String>,
}

#[derive(Debug, Clone)]
enum ChunkTranslationOutput {
    Inlined(InlinedTranslationOutput),
    LLM(LLMBasedTranslationOutput),
}

#[derive(Debug, Clone)]
pub(crate) struct TranslationResult {
    env_init: String,
    default_init: String,
    main_function_body: String,
    am_cond_to_cfg: String,
    recording: String,
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

    fn debug_print_chunks(&mut self) {
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
                self.print_chunk_skeleton_call_site(i, &format!("func{}", i))
            );
            let dummy = HashMap::new();
            let printer = TranslatingPrinter::new(&self, &dummy, false);
            for &id in chunk.nodes.iter() {
                println!("{}", &printer.print_node(id));
            }
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

        dbg!(&self.get_scopes("WITH_XPATH"));

        let default_init = self
            .var_scopes
            .as_ref()
            .unwrap()
            .iter()
            .filter(|(var_name, _)| !self.env_vars.as_ref().unwrap().contains(var_name.as_str()))
            .filter(|(_, scopes)| {
                scopes
                    .first()
                    .is_some_and(|s| s.owner.is_none() && s.bound_by.is_none())
            })
            .map(|(var_name, _)| var_name)
            .sorted()
            .map(|name| {
                dbg!(&name);
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
        let translated = self.translate_chunks().await;
        let main_function_body = self
            .chunks
            .iter()
            .filter(|(_, chunk)| chunk.parent.is_none())
            .filter(|(chunk_id, _)| translated.contains_key(&chunk_id))
            .map(|(chunk_id, _)| match translated.get(&chunk_id).unwrap() {
                ChunkTranslationOutput::Inlined(res) => {
                    format!("{tab}{}", res.inline_rust_code.join(&format!("\n{tab}")))
                }
                ChunkTranslationOutput::LLM(_) => {
                    let call_site = self.print_chunk_skeleton_call_site(
                        chunk_id,
                        &rust_func_placeholder_name(chunk_id),
                    );
                    format!("{tab}{call_site}")
                }
            })
            .join("\n");
        let am_cond_to_cfg = {
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
                        "{tab}if {} {{\n{tab}{tab}{}\n{tab}}}",
                        printer.display_guard(&guard),
                        print_line
                    )
                })
                .join("\n")
        };

        // Generate evaluation output section
        let recording = {
            let mut output = Vec::new();

            // Output subst variables
            output.push(format!("{tab}// recording subst vars"));
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
        let chunk_funcs = self
            .chunks
            .iter()
            .filter(|(chunk_id, _)| translated.contains_key(&chunk_id))
            .filter_map(|(chunk_id, _)| match translated.get(&chunk_id).unwrap() {
                ChunkTranslationOutput::Inlined(res) => None,
                ChunkTranslationOutput::LLM(res) => Some(res),
            })
            .map(|res| {
                self.construct_rust_func_definition(
                    res.id,
                    &rust_func_placeholder_name(res.id),
                    &res.rust_func_body,
                )
            })
            .collect();
        TranslationResult {
            env_init,
            default_init,
            main_function_body,
            am_cond_to_cfg,
            recording,
            chunk_funcs,
        }
    }

    /// Translate chunks using inlined translation or LLMs
    async fn translate_chunks(&self) -> HashMap<ChunkId, ChunkTranslationOutput> {
        let mut results = HashMap::new();
        let mut user = use_llm::LLMUser::new();
        let mut inputs = Vec::new();
        let mut depending_funcs = HashMap::new();

        // Collect rule-based translations for inlining during LLM processing
        let inlined_translations: HashMap<ChunkId, InlinedTranslationOutput> = self
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

        results.extend(
            inlined_translations
                .iter()
                .map(|(chunk_id, inlined_translation)| {
                    (
                        *chunk_id,
                        ChunkTranslationOutput::Inlined(inlined_translation.clone()),
                    )
                }),
        );

        let llm_translations = if let Some(cached) = self.load_translation_cache() {
            cached
        } else {
            // Process all chunks: inlined ones go directly to results, complex ones go to LLM
            for (chunk_id, _) in self.chunks.iter() {
                if inlined_translations.contains_key(&chunk_id) {
                    // inlined chunk
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

                if script.trim().is_empty() {
                    // empty chunk
                    continue;
                }

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
                let required_funcs = printer.get_rust_funcs_required_for_chunk();
                depending_funcs.insert(chunk_id, printer.get_embedded_chunks());
                let input = LLMBasedTranslationInput::new(
                    chunk_id,
                    script,
                    skeleton.clone(),
                    &required_funcs,
                );
                let evidence = LLMBasedTranslationEvidence {
                    id: chunk_id,
                    rust_snippets: printer.get_translated_fragments(),
                    predefinition: use_llm::get_predefinition(&required_funcs),
                    header,
                    footer,
                };
                inputs.push((input, evidence));
            }

            let mut res = user
                .run_llm_analysis(inputs.iter().map(|(i, e)| (i, e)))
                .await
                .into_iter()
                .map(|res| (res.id, res))
                .collect::<HashMap<_, _>>();

            // Handle LLM function name dependencies
            for chunk_id in res.keys().cloned().collect::<Vec<_>>() {
                for (id, placeholder) in depending_funcs.get(&chunk_id).unwrap() {
                    if let Some(new_name) = res.get(id).map(|o| o.rust_func_name.clone()) {
                        let out = res.get_mut(&chunk_id).unwrap();
                        out.rust_func_body = out.rust_func_body.replace(placeholder, &new_name);
                    }
                }
            }
            self.save_translation_cache(&res);
            res
        };

        // Convert LLM results to ChunkTranslationResult and merge with inlined results
        for (chunk_id, llm_output) in llm_translations {
            results.insert(chunk_id, ChunkTranslationOutput::LLM(llm_output));
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
        let predefinition =
            self.get_predefinition_with_record(record_path.to_str().unwrap_or("/tmp/record.txt"));
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
{tab}// export cfg
{}
{tab}// record
{}
}}
{}",
            &predefinition,
            &res.env_init,
            &res.default_init,
            &res.main_function_body,
            &res.am_cond_to_cfg,
            &res.recording,
            &res.chunk_funcs.join("\n\n")
        );
        build_rs
    }

    fn get_predefinition_with_record(&self, record_path: &str) -> String {
        let predefinitions_with_record = [
            (
                "define_cfg_with_record",
                r#"fn define_cfg(key: &str, value: Option<&str>) {
  println!("cargo:rustc-check-cfg=cfg({})", key);
  if let Some(value) = value {
    println!("cargo:rustc-cfg={}={}", key, value);
    record("cfg", key, value);
  } else {
    println!("cargo:rustc-cfg={}", key);
    record("cfg", key, "");
  }
}"#,
            ),
            (
                "define_env_with_record",
                r#"fn define_env(key: &str, value: &str) {
  println!("cargo:rustc-env={}={}", key, value);
  record("env", key, value);
}"#,
            ),
            (
                "record",
                &format!(
                    r#"fn record(category: &str, key: &str, value: &str) {{
  let line = format!("{{}}:{{}}={{}}\n", category, key, value);
  let path = PathBuf::from("{}");
  write_file(&path, &line)
}}"#,
                    record_path
                ),
            ),
        ];
        use_llm::get_predefinition(&["write_file"])
            + "\n"
            + &predefinitions_with_record.iter().map(|(_, s)| s).join("\n")
    }
}
