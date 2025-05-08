use std::env;
use std::io::Write;
use std::fs::File;
use wtns_file::FieldElement;
use circom_witnesscalc::field::U254;
use circom_witnesscalc::{ffi::ParallelGraph, wtns_from_witness2};

struct Args {
    optimized_graph_path: String,
    inputs_file: String,
    witness_file: String,
}

fn parse_args() -> Args {
    let args: Vec<String> = env::args().collect();
    if args.len() != 4 {
        eprintln!("Usage: {} <optimized_graph_path> <inputs.json> <witness.wtns>", args[0]);
        std::process::exit(1);
    }

    Args {
        optimized_graph_path: args[1].clone(),
        inputs_file: args[2].clone(),
        witness_file: args[3].clone(),
    }
}

fn main() {
    let args = parse_args();

    let mut graph = ParallelGraph::new_from_disk(&args.optimized_graph_path);
    let mut witness = vec![U254::default(); graph.get_witness_len()];

    graph.calc_witness(&args.inputs_file, &mut witness);

    let vec_witness: Vec<FieldElement<32>> = witness
        .iter()
        .map(|a| TryInto::<[u8; 32]>::try_into(a.as_le_slice()).unwrap().into())
        .collect();

    let wtns_bytes = wtns_from_witness2(vec_witness, graph.get_prime());

    let mut file = File::create(&args.witness_file).unwrap();
    file.write_all(&wtns_bytes).unwrap();
}
