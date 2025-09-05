use serde::{Deserialize, Serialize};
use std::io::{stdin, Read};
mod analysis;
mod analyzer;
mod utils;

#[derive(Serialize)]
struct ClaudeRequest {
    model: String,
    max_tokens: usize,
    messages: Vec<Message>,
}

#[derive(Serialize)]
struct Message {
    role: String,
    content: String,
}

#[derive(Deserialize)]
struct ClaudeResponse {
    content: Vec<ClaudeContent>,
}

#[derive(Deserialize)]
struct ClaudeContent {
    text: String,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Read input from stdin
    let mut input = String::new();
    stdin().read_to_string(&mut input)?;
    analysis::analysis(input).await?;
    // dbg!(analyzer.find_case_matches(&["host".into(), "host_cpu".into()]));
    // migrate(&analyzer)?;
    Ok(())
}

/*
fn migrate(analyzer: &Analyzer) -> Result<(), Box<dyn std::error::Error>> {
    let mut fragments = Vec::new();
    for id in topological_sort(analyzer) {
        if let Some(content) = analyzer.get_content(id) {
            fragments.push(content.join("\n"));
        }
    }

    let prompt = "You are analyzing a fragment of a build script from a C project.

Your task:
Classify the following snippet into exactly one of the following categories:

1. Feature setting (e.g., setting compile-time flags based on environment)
2. Library checking (e.g., verifying if a library is available)
3. Library dependency setup (e.g., setting link options for a library)
4. Dynamic file generation (e.g., generating config headers or source files)
5. Other arbitrary actions (e.g., pure logic, unrelated processing)

If you need additional context (e.g., macro definitions or source code information), ask explicitly.

Here is the script fragment:
";

    for frag in fragments.iter().skip(20).take(2) {
        println!("Request: {}", frag);
        req(&format!("{}\n```\n{}\n```", prompt, frag))?;
    }

    // req(&prompt)?;

    Ok(())
}

fn topological_sort(analyzer: &Analyzer) -> Vec<usize> {
    let mut indegree = vec![0; analyzer.command_count()];
    let mut adj = vec![Vec::new(); analyzer.command_count()];

    // Build adjacency list and compute indegree
    for i in 0..analyzer.command_count() {
        if let Some(deps) = analyzer.get_dependencies(i) {
            for dep in deps {
                adj[dep].push(i); // dep -> i
                indegree[i] += 1;
            }
        }
    }

    let mut queue = std::collections::VecDeque::new();
    for (i, &deg) in indegree.iter().enumerate() {
        if deg == 0 {
            queue.push_back(i);
        }
    }

    let mut topo_order = Vec::new();
    while let Some(u) = queue.pop_front() {
        topo_order.push(u);
        for &v in &adj[u] {
            indegree[v] -= 1;
            if indegree[v] == 0 {
                queue.push_back(v);
            }
        }
    }
    topo_order
}

fn req(prompt: &str) -> Result<(), Box<dyn std::error::Error>> {
    // dotenv::dotenv().ok();
    let api_key = env::var("CLAUDE_API_KEY")?;

    let client = Client::new();
    let res = client
        .post("https://api.anthropic.com/v1/messages")
        .header("x-api-key", api_key)
        .header("anthropic-version", "2023-06-01")
        .json(&ClaudeRequest {
            model: "claude-3-5-haiku-latest".to_string(), // opus or sonnetなど
            max_tokens: 100,
            messages: vec![Message {
                role: "user".to_string(),
                content: prompt.to_string(),
            }],
        })
        .send()?
        .json::<ClaudeResponse>()?;

    for part in res.content {
        println!("Response:\n{}", part.text);
    }

    Ok(())
}
*/
