//! Analysis module for c2cargo.
//! Handles the main analysis pipeline for converting autoconf to Cargo.

use crate::analyzer::{record::AnalysisParameters, Analyzer, AnalyzerOptions};
use std::path::Path;

pub(crate) async fn analysis(
    configure_path: &Path,
    output_dir: &Path,
    options: Option<AnalyzerOptions>,
) -> Result<(), Box<dyn std::error::Error>> {
    // Read file contents
    let configure_path = std::path::absolute(configure_path).unwrap();
    let output_dir = std::path::absolute(output_dir).unwrap();

    // Use provided options or default
    let opts = options.unwrap_or_default();

    // Initialize record collector with parameters matching the options
    let parameters = AnalysisParameters {
        chunk_window_size: Some(opts.chunk_window_size),
        disrespect_assignment: opts.chunk_disrespect_assignment,
        type_inference_enabled: opts.type_inference,
        build_option_analysis_enabled: true,
    };

    // Initialize the lexer and parser with options
    let mut analyzer = Analyzer::new(&configure_path, Some(opts));
    analyzer.init_record_collector(parameters);
    analyzer.record_collector_mut().start_timing();

    // === Build Option Analysis ===
    analyzer.run_extra_build_option_analysis().await;

    // Collect project info before translation
    let (
        source_files,
        header_files,
        built_files,
        generated_files,
        config_files,
        subst_files,
        automake_files,
        total_commands,
        total_chunks,
    ) = analyzer.get_project_info_for_record();

    analyzer.record_collector_mut().collect_project_info(
        source_files,
        header_files,
        built_files,
        generated_files,
        config_files,
        subst_files,
        automake_files,
        total_commands,
        total_chunks,
    );

    // === Translation Analysis Debug ===
    println!("\n=== DEBUG: Testing Analyzer::translate ===");
    println!("Calling analyzer.translate()...");

    // Time the translation stage
    analyzer.record_collector_mut().start_stage();
    let res = analyzer.translate().await;
    analyzer.record_collector_mut().end_stage_translation();
    println!("translate() completed successfully");

    // Finish timing and export record results
    analyzer.record_collector_mut().finish_timing();

    // Export record data
    let target_name = analyzer
        .get_project_metadata()
        .map(|meta| meta.name.as_ref().map(|s| s.as_str()))
        .flatten()
        .unwrap_or("unknown");
    let project_name = format!("{}-rs", target_name);
    let record_dir = output_dir.join("record");
    std::fs::create_dir_all(&record_dir)?;

    analyzer
        .record_collector()
        .export_project_info_json(&record_dir.join("project_info.json"))?;
    // Only export build options CSV if cache wasn't used (otherwise data is incomplete)
    if !analyzer.record_collector().build_option_cache_used {
        analyzer
            .record_collector()
            .export_build_options_csv(&record_dir.join("build_options.csv"))?;
    }
    // Only export chunks CSV if cache wasn't used (otherwise data has placeholder values)
    if !analyzer.record_collector().translation_cache_used {
        analyzer
            .record_collector()
            .export_chunks_csv(&record_dir.join("chunks.csv"))?;
    }

    println!("Evaluation data exported to: {}", record_dir.display());

    let record_path = record_dir.join("record.csv");

    let crate_dir = output_dir.join(&project_name);
    std::process::Command::new("cargo")
        .arg("new")
        .arg(&project_name)
        .current_dir(&output_dir)
        .output()
        .expect("Failed to create a Rust crate.");

    let cargo_toml = analyzer.generate_cargo_toml();
    std::fs::write(crate_dir.join("Cargo.toml"), cargo_toml)?;

    let build_rs = analyzer.print_build_rs(&res, &record_path);
    std::fs::write(crate_dir.join("build.rs"), build_rs)?;

    if let Some(wrapper_h) = analyzer.generate_wrapper_header() {
        std::fs::write(crate_dir.join("wrapper.h"), wrapper_h)?;
    }

    let ccm = analyzer.print_conditional_compilation_map();
    std::fs::write(record_dir.join("conditinal_compilation_map.json"), ccm)?;

    Ok(())
}
