use clap::Parser;
use std::path::PathBuf;

mod analysis;
mod analyzer;
mod display;
mod utils;

use analyzer::AnalyzerOptions;

/// c2cargo: Convert autoconf build systems to Rust Cargo
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Output directory for generated files
    #[arg(short, long, value_name = "DIR", default_value = "/tmp/c2cargo")]
    output_dir: PathBuf,

    /// Path to configure.ac file
    #[arg(required = true, value_name = "path/to/configure.ac")]
    configure_path: PathBuf,

    /// Use full-script translation mode (no chunking)
    #[arg(long)]
    full_script: bool,

    /// Disable type inference
    #[arg(long)]
    no_type_inference: bool,

    /// Chunk window size (ignored if --full-script)
    #[arg(long, default_value = "2")]
    chunk_window_size: usize,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = Args::parse();

    let ac_path = &args.configure_path;
    // Check if file exists
    if !ac_path.exists() {
        eprintln!("Error: File '{}' does not exist", ac_path.to_str().unwrap());
        std::process::exit(1);
    }

    let output_dir = &args.output_dir;
    if output_dir.exists() {
        std::fs::remove_dir_all(output_dir)?;
    }
    std::fs::create_dir(output_dir)?;

    // Construct analyzer options from CLI arguments (if any were specified)
    let options = if args.full_script || args.no_type_inference || args.chunk_window_size != 2 {
        Some(AnalyzerOptions {
            chunk_window_size: if args.full_script {
                usize::MAX
            } else {
                args.chunk_window_size
            },
            type_inference: !args.no_type_inference,
            ..Default::default()
        })
    } else {
        None // Use default options
    };

    analysis::analysis(ac_path, output_dir, options).await?;
    Ok(())
}
