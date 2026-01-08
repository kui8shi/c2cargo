//! An example of how to use the DependencyAnalyzer to analyze variable dependencies
//! in a shell script or autoconf file.

use crate::analyzer::{record::AnalysisParameters, Analyzer, AnalyzerOptions};
use std::path::{Path, PathBuf};

pub(crate) async fn analysis(path: &Path) -> Result<(), Box<dyn std::error::Error>> {
    // Read file contents
    let path = std::path::absolute(path).unwrap();

    let options = AnalyzerOptions::default();
    // Initialize the lexer and parser
    let mut analyzer = Analyzer::new(&path, Some(options));

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
    let project_name = analyzer
        .get_project_metadata()
        .unwrap()
        .package_name
        .as_ref()
        .map(|s| s.as_str())
        .unwrap_or("unknown");
    let root_dir = PathBuf::from("/tmp");
    let output_dir = root_dir.join(format!("c2cargo_record_{}", project_name));
    std::fs::create_dir_all(&output_dir)?;

    analyzer
        .record_collector()
        .export_json(&output_dir.join("analysis_info.json"))?;
    analyzer
        .record_collector()
        .export_build_options_csv(&output_dir.join("build_options.csv"))?;
    analyzer
        .record_collector()
        .export_chunks_csv(&output_dir.join("chunks.csv"))?;

    println!("Evaluation data exported to: {}", output_dir.display());

    let record_path = output_dir.join("record.txt");

    let crate_dir = root_dir.join(&project_name);
    std::process::Command::new("cargo")
        .arg("new")
        .arg(&project_name)
        .current_dir(&root_dir)
        .output()?;

    let cargo_toml = analyzer.generate_cargo_toml();
    std::fs::write(crate_dir.join("Cargo.toml"), cargo_toml)?;

    let build_rs = analyzer.print_build_rs(&res, &record_path);
    std::fs::write(crate_dir.join("build.rs"), build_rs)?;

    if let Some(wrapper_h) = analyzer.generate_wrapper_header() {
        std::fs::write(crate_dir.join("wrapper.h"), wrapper_h)?;
    }

    Ok(())
}
