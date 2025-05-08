use std::env;
use std::fs::File;
use circom_witnesscalc::ffi::ParallelGraph;

struct Args {
    graph_file: String,
    optimized_graph_path: String,
    thread_count: Option<usize>,
}

fn parse_args() -> Args {
    let args: Vec<String> = env::args().collect();
    if args.len() != 3 && args.len() != 4 {
        eprintln!("Usage: {} <graph.bin> <output_graph_path> [#threads]", args[0]);
        std::process::exit(1);
    }

    let thread_count = if args.len() == 4 {
        Some(args[3].parse::<usize>().unwrap())
    } else {
        None
    };

    Args {
        graph_file: args[1].clone(),
        optimized_graph_path: args[2].clone(),
        thread_count,
    }
}

fn main() {
    let args = parse_args();

    let graph = if let Some(thread_count) = args.thread_count {
        ParallelGraph::new_with_nthreads(&args.graph_file, thread_count)
    } else {
        ParallelGraph::new(&args.graph_file)
    };

    graph.save_graph_to_disk(&args.optimized_graph_path);
}
