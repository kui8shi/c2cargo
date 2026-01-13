//! An example of how to use the DependencyAnalyzer to analyze variable dependencies
//! in a shell script or autoconf file.

use crate::analyzer::{record::AnalysisParameters, Analyzer, AnalyzerOptions};
use std::path::Path;

pub(crate) async fn analysis(
    configure_path: &Path,
    output_dir: &Path,
) -> Result<(), Box<dyn std::error::Error>> {
    // Read file contents
    let configure_path = std::path::absolute(configure_path).unwrap();
    let output_dir = std::path::absolute(output_dir).unwrap();

    let options = AnalyzerOptions::default();
    // Initialize the lexer and parser
    let mut analyzer = Analyzer::new(&configure_path, Some(options));
    analyzer.debug_print_chunks();
    return Ok(());

    // Initialize record collector
    let parameters = AnalysisParameters {
        chunk_window_size: Some(2),
        disrespect_assignment: false,
        type_inference_enabled: true,
        build_option_analysis_enabled: true,
    };
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
        .unwrap()
        .name
        .as_ref()
        .map(|s| s.as_str())
        .unwrap_or("unknown");
    let project_name = format!("{}-rs", target_name);
    let record_dir = output_dir.join("record");
    std::fs::create_dir_all(&record_dir)?;

    analyzer
        .record_collector()
        .export_record_json(&record_dir.join("record.json"))?;
    analyzer
        .record_collector()
        .export_build_options_csv(&record_dir.join("build_options.csv"))?;
    analyzer
        .record_collector()
        .export_chunks_csv(&record_dir.join("chunks.csv"))?;

    println!("Evaluation data exported to: {}", record_dir.display());

    let record_path = record_dir.join("record.txt");

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
