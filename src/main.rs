use clap::Parser;
use std::path::PathBuf;

mod analysis;
mod analyzer;
mod display;
mod utils;

/// Simple CLI argument parser
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    #[arg(short, long, value_name = "DIR", default_value = "/tmp/c2cargo")]
    output_dir: PathBuf,
    #[arg(required = true, value_name = "path/to/configure.ac")]
    configure_path: PathBuf,
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

    analysis::analysis(ac_path, output_dir).await?;
    // dbg!(analyzer.find_case_matches(&["host".into(), "host_cpu".into()]));
    // migrate(&analyzer)?;
    Ok(())
}
