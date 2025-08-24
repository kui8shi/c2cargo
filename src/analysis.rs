//! An example of how to use the DependencyAnalyzer to analyze variable dependencies
//! in a shell script or autoconf file.

use autotools_parser::ast::MayM4;

use crate::analyzer::Analyzer;

pub(crate) fn analysis(input: String) -> Result<(), Box<dyn std::error::Error>> {
    let fixed = [(
        "srcdir".to_owned(),
        format!("{}/src/gmp-6.2.0", env!("HOME")),
    )];
    // Initialize the lexer and parser
    let mut analyzer = Analyzer::new(&input, None, Some(fixed.into()));
    let top_ids = analyzer.get_top_ids();

    /*

    // Print information about the analyzed script
    println!("Total commands: {}", top_ids.len());

    // Display all variables and their definitions
    let mut all_vars = std::collections::HashSet::new();
    for &i in &top_ids {
        if let Some(defines) = analyzer.get_defined_variables(i) {
            all_vars.extend(defines.clone());
        }
    }

    // Display dependency information for each command
    println!("\nCommand dependencies:");
    let mut chunk_file = File::create("/tmp/chunks.sh")?;
    for chunk in &analyzer.fuse_chunks(Some(3), true) {
        for &i in chunk {
            writeln!(
                chunk_file,
                "Command {}: {:?}",
                i,
                analyzer.get_ranges(i).unwrap()
            )?;
        }

        for &i in chunk {
            writeln!(chunk_file, "{}", analyzer.recover_content(i))?;
        }

        for &i in chunk {
            // if analyzer.get_node(i).ranges.first().is_none_or(|(s, e)| s == e) {
            //     continue;
            // }
            println!(
                "\x1b[33mCommand {}: {:?}\x1b[m",
                i,
                analyzer.get_ranges(i).unwrap()
            );
        }

        for &i in chunk {
            // Print the command (simplified)
            // if let Some(cmd) = analyzer.get_content(i) {
            //     print!(
            //         "{:?}\x1b[m\n{}",
            //         analyzer.get_ranges(i).unwrap(),
            //         cmd.join("\n")
            //     );
            //     // print!("{:?}\n{:?}", analyzer.get_ranges(i).unwrap(), cmd);
            // }

            // println!("\n===========when recovering==========");

            println!("{}", analyzer.recover_content(i));

            // Print defined variables
            if let Some(defines) = analyzer.get_defined_variables(i) {
                if !defines.is_empty() {
                    print!("  Defines: ");
                    for (idx, var) in defines.iter().enumerate() {
                        if idx > 0 {
                            print!(", ");
                        }
                        print!("{}", var);
                    }
                    println!();
                }
            }

            // Print used variables
            if let Some(uses) = analyzer.get_used_variables(i) {
                if !uses.is_empty() {
                    print!("  Uses: ");
                    for (idx, var) in uses.iter().enumerate() {
                        if idx > 0 {
                            print!(", ");
                        }
                        print!("{}", var);
                    }
                    println!();
                }
            }

            // Print dependencies
            if let Some(deps) = analyzer.get_dependencies(i) {
                if !deps.is_empty() {
                    print!("  Depends on commands: ");
                    for (idx, &dep) in deps.iter().enumerate() {
                        if idx > 0 {
                            print!(", ");
                        }
                        print!("{}", dep);
                    }
                    println!();
                }
            }
            if let Some((parent, branch_idx)) = analyzer.get_parent(i) {
                print!("  Parent : {}", parent);
                if let Some(b) = branch_idx {
                    print!(":{}", b);
                }
                println!();
            }

            // Print dependents
            if let Some(deps) = analyzer.get_dependents(i) {
                if !deps.is_empty() {
                    print!("  Commands that depend on this: ");
                    for (idx, &dep) in deps.iter().enumerate() {
                        if idx > 0 {
                            print!(", ");
                        }
                        print!("{}", dep);
                    }
                    println!();
                }
            }

            println!();
        }
    }

    // Example of finding all commands related to a specific variable
    println!("\nExample variable analysis:");
    if !all_vars.is_empty() {
        let example_var = all_vars.iter().next().unwrap();
        println!("Commands related to variable '{}': ", example_var);

        let related_cmds = analyzer.find_commands_with_variable(example_var);
        for cmd_idx in related_cmds {
            println!("  Command {}: {:?}", cmd_idx, analyzer.get_command(cmd_idx));
        }

        let mut groups = Vec::new();
        let mut belongs_to = std::collections::HashMap::new();
        for &i in &top_ids {
            if !belongs_to.contains_key(&i) {
                let grp_idx = groups.len();
                let mut group = std::collections::HashSet::new();
                let mut stack = vec![i];
                while let Some(cmd_idx) = stack.pop() {
                    if !belongs_to.contains_key(&cmd_idx) {
                        group.insert(cmd_idx);
                        belongs_to.insert(cmd_idx, grp_idx);
                        if let Some(deps) = analyzer.get_dependencies(cmd_idx) {
                            for dep in deps {
                                stack.push(dep);
                            }
                        }
                    }
                }
                groups.push(group);
            }
        }

        let (groups, belongs_to) = (groups, belongs_to);
        for (grp_idx, group) in groups.iter().enumerate() {
            println!("Group {}: ", grp_idx);
            for cmd_idx in group {
                if let Some(ranges) = analyzer.get_ranges(*cmd_idx) {
                    println!("  Command {}: {:?}", cmd_idx, ranges);
                }
            }
        }

        // println!("  Group {}: {:?}", group_idx, analyzer.get_command(cmd_idx));
    }

    // Export graph in DOT format
    let mut dot_file = File::create("/tmp/dependencies.dot")?;
    writeln!(dot_file, "digraph Dependencies {{")?;
    // writeln!(dot_file, "  rankdir=LR;")?;

    // Node definitions
    for &i in &top_ids {
        let label = format!("{}", i);
        writeln!(dot_file, r#"  {} [label="{}"];"#, i, label)?;
    }

    // Edges (dependencies)
    for &i in &top_ids {
        if let Some(deps) = analyzer.get_dependencies(i) {
            for dep in deps {
                writeln!(dot_file, "  {} -> {};", dep, i)?; // dep must come before i
            }
        }
    }
    writeln!(dot_file, "}}")?;
    println!("DOT graph written to dependencies.dot");

    // === Topological Sort ===
    println!("\n=== Topological Sort ===");

    let mut indegree = vec![0; analyzer.num_nodes()];
    let mut adj = vec![Vec::new(); analyzer.num_nodes()];

    // Build adjacency list and compute indegree
    for &i in &top_ids {
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

    if topo_order.len() != top_ids.len() {
        println!("Cycle detected! Cannot perform topological sort.");
    } else {
        println!("Topological order:");
        for (i, cmd_idx) in topo_order.iter().enumerate() {
            println!("  {}: Command {}", i, cmd_idx);
        }
    }
    */

    // === Variable dependency edge profiling ===
    // use std::collections::HashMap;

    // This map will count how many times each variable appears as a dependency edge
    // let mut edge_counter: HashMap<String, Vec<(usize, usize)>> = HashMap::new();

    // for &top_id in &top_ids {
    //     // Get variables used in the current command
    //     if let Some(uses) = analyzer.get_used_variables(top_id) {
    //         // Get the commands this one depends on
    //         if let Some(deps) = analyzer.get_dependencies(top_id) {
    //             for dep in deps {
    //                 // For each dependency command, get the variables it defines
    //                 if let Some(defs) = analyzer.get_defined_variables(dep) {
    //                     for var in defs {
    //                         // If the current command uses a variable defined in a dependency, count it
    //                         if uses.contains(&var) && top_id != dep {
    //                             edge_counter
    //                                 .entry(var.clone())
    //                                 .or_insert(Vec::new())
    //                                 .push((top_id, dep));
    //                         }
    //                     }
    //                 }
    //             }
    //         }
    //     }
    // }

    // Sort the variables by descending edge count
    // let mut edge_stats: Vec<(String, usize)> = edge_counter
    //     .iter()
    //     .map(|(k, v)| (k.clone(), v.len()))
    //     .collect();
    // edge_stats.sort_by(|a, b| b.1.cmp(&a.1)); // Sort by count (descending)

    // Print the top 50 variables with the most dependency edges
    // println!("\n=== Variable Edge Count Ranking ===");
    // for (var, count) in edge_stats.iter().take(1) {
    //     println!(
    //         "{:20} ({}): {:?}",
    //         var,
    //         count,
    //         edge_counter.get(var).unwrap()
    //     );
    // }

    // === Value Set Analysis for Eval ===
    // println!("\n=== Value Set Analysis for Eval ===");
    // analyzer.run_value_set_analysis();

    // === Variable Type Inference ===
    // dbg!(analyzer.run_type_analysis());

    // === Out-of-scope variables ===
    // for chunk in analyzer.fuse_chunks(Some(12), true) {
    //     println!("+++++++++++++++++++++++++++++++++++++++++++++");
    //     for &id in &chunk {
    //         // println!("{}", &analyzer.recover_content(id));
    //     }
    //     dbg!(analyzer.examine_chunk_io(&chunk));
    // }

    // === Platform Branch Prunning ===
    // analyzer.prune_platform_branch();

    Ok(())
}
