use std::{env, path::Path};
mod analysis;
mod analyzer;
mod display;
mod utils;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<String> = env::args().collect();

    let path = match args.get(1) {
        Some(path) => path,
        None => {
            eprintln!("Usage: c2cargo <path>");
            std::process::exit(1);
        }
    };

    // Check if file exists
    if !Path::new(path).exists() {
        eprintln!("Error: File '{}' does not exist", path);
        std::process::exit(1);
    }

    analysis::analysis(Path::new(path)).await?;
    // dbg!(analyzer.find_case_matches(&["host".into(), "host_cpu".into()]));
    // migrate(&analyzer)?;
    Ok(())
}
