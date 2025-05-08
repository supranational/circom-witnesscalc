use std::collections::HashMap;
use std::fs;
use std::fs::File;
use std::io::Write;
use std::sync::{LazyLock, Mutex};
use std::ffi::{c_char, CStr};
use rayon::prelude::*;
use crate::graph::{Node, TresOperation, tree_shake};
use crate::{Field, U254, Nodes, VecNodes, InputSignalsInfo, create_inputs, deserialize_inputs2};
use crate::field::{FieldOperations, FieldOps};
use crate::storage::proto_deserializer::deserialize_witnesscalc_graph_from_bytes_bn254;

static GRAPHS: LazyLock<Mutex<HashMap<String, ParallelGraph>>> = LazyLock::new(|| Mutex::new(HashMap::new()));

#[no_mangle]
pub extern "C" fn setup_parallel_graph(graph_path: *const c_char) -> usize {
    let graph_path = unsafe { CStr::from_ptr(graph_path).to_str().unwrap() };

    let graph = ParallelGraph::new_from_disk(graph_path);

    let witness_len = graph.witness_len;

    GRAPHS.lock().unwrap().insert(graph_path.to_string(), graph);

    witness_len
}

#[no_mangle]
pub extern "C" fn calc_witness_with_parallel_graph(
    graph_path: *const c_char,
    inputs_file: *const c_char,
    witness_data: *mut U254,
) {
    let graph_path = unsafe { CStr::from_ptr(graph_path).to_str().unwrap() };
    let mut graphs_lock = GRAPHS.lock().unwrap();
    let graph = graphs_lock.get_mut(graph_path).unwrap();

    let inputs_file = unsafe { CStr::from_ptr(inputs_file).to_str().unwrap() };

    let witness_slice = unsafe { std::slice::from_raw_parts_mut(witness_data, graph.get_witness_len()) };
    graph.calc_witness(inputs_file, witness_slice);
}

pub struct ParallelGraph {
    pub ff: Field<U254>,
    pub subgraphs: Vec<Vec<Node>>,
    pub constants: Vec<U254>,
    pub split_signals: Vec<Vec<usize>>,
    pub input_mapping: InputSignalsInfo,

    pub values: Vec<Vec<U254>>,

    witness_len: usize,
    thread_count: usize,
}

impl ParallelGraph {
    pub fn save_graph_to_disk(&self, graph_path: &str) {
        fs::create_dir_all(graph_path).unwrap();

        let graph_path = String::from(graph_path);

        let config = bincode::config::standard();

        let constants_limbs = self.constants.iter().map(|val| val.into_limbs()).collect::<Vec<[u64; U254::LIMBS]>>();
        let constants_bytes = bincode::encode_to_vec(&constants_limbs, config).unwrap();
        let mut constants_file = File::create(graph_path.clone() + "/constants").unwrap();
        constants_file.write_all(&constants_bytes).unwrap();

        let split_signals_bytes = bincode::encode_to_vec(&self.split_signals, config).unwrap();
        let mut split_signals_file = File::create(graph_path.clone() + "/split_signals").unwrap();
        split_signals_file.write_all(&split_signals_bytes).unwrap();

        let input_mapping_bytes = bincode::encode_to_vec(&self.input_mapping, config).unwrap();
        let mut input_mapping_file = File::create(graph_path.clone() + "/input_mapping").unwrap();
        input_mapping_file.write_all(&input_mapping_bytes).unwrap();

        for i in 0..self.subgraphs.len() {
            let subgraph_bytes = bincode::encode_to_vec(&self.subgraphs[i], config).unwrap();
            let mut subgraph_file = File::create(graph_path.clone() + "/subgraph_" + &i.to_string()).unwrap();
            subgraph_file.write_all(&subgraph_bytes).unwrap();
        }
    }

    pub fn new_from_disk(graph_path: &str) -> Self {
        let graph_path = String::from(graph_path);

        let config = bincode::config::standard();

        let constants_bytes = fs::read(graph_path.clone() + "/constants").unwrap();
        let (constants_limbs, _): (Vec<[u64; U254::LIMBS]>, usize) = bincode::decode_from_slice(&constants_bytes, config).unwrap();
        let constants = constants_limbs.iter().map(|limbs| U254::from_limbs(*limbs)).collect::<Vec<U254>>();

        let split_signals_bytes = fs::read(graph_path.clone() + "/split_signals").unwrap();
        let (split_signals, _): (Vec<Vec<usize>>, usize) = bincode::decode_from_slice(&split_signals_bytes, config).unwrap();

        let input_mapping_bytes = fs::read(graph_path.clone() + "/input_mapping").unwrap();
        let (input_mapping, _): (InputSignalsInfo, usize) = bincode::decode_from_slice(&input_mapping_bytes, config).unwrap();

        let thread_count = split_signals.len();

        let subgraphs: Vec<Vec<Node>> = (0..thread_count).into_par_iter().map(|i| {
            let subgraph_file = graph_path.clone() + "/subgraph_" + &i.to_string();
            let subgraph_bytes = fs::read(subgraph_file).unwrap();

            let (subgraph, _): (Vec<Node>, usize) = bincode::decode_from_slice(&subgraph_bytes, config).unwrap();

            subgraph
        }).collect();

        let prime = U254::from_str(
            "21888242871839275222246405745257275088548364400416034343698204186575808495617")
            .unwrap();
        let ff = Field::<U254>::new(prime);

        let mut values = vec![Vec::new(); subgraphs.len()];
        subgraphs.par_iter().zip(values.par_iter_mut()).for_each(|(subgraph, value)| {
            *value = vec![U254::default(); subgraph.len()];
        });

        let mut witness_len = 0usize;
        for signals in &split_signals {
            witness_len += signals.len();
        }

        Self {
            ff,
            subgraphs,
            constants,
            split_signals,
            input_mapping,
            values,
            witness_len,
            thread_count
        }
    }

    pub fn new_with_nthreads(graph_file: &str, thread_count: usize) -> Self {
        let graph_bytes = std::fs::read(graph_file).expect("Failed to read graph file");
        let (nodes, signals, input_mapping): (Nodes<U254, VecNodes>, Vec<usize>, InputSignalsInfo) =
            deserialize_witnesscalc_graph_from_bytes_bn254(&graph_bytes).unwrap();
        let witness_len = signals.len();
        println!("total nodes: {}, # threads: {}", nodes.len(), thread_count);

        let thread_count = {
            let max_threads = std::thread::available_parallelism().unwrap().get();
            if thread_count > 0 && thread_count <= max_threads {
                thread_count
            } else {
                max_threads
            }
        };

        let sz = (signals.len() + thread_count - 1) / thread_count;

        let mut split_signals = Vec::new();
        let mut subgraphs = Vec::new();

        for (i, chunk) in signals.chunks(sz).enumerate() {
            let mut nodes = nodes.clone();
            let mut chunk = Vec::from(chunk);
            tree_shake(&mut nodes, &mut chunk);
            println!("chunk #{}: {} nodes", i, nodes.len());

            split_signals.push(chunk);
            subgraphs.push(nodes.nodes.nodes);
        }

        let mut values = vec![Vec::new(); subgraphs.len()];
        subgraphs.par_iter().zip(values.par_iter_mut()).for_each(|(subgraph, value)| {
            *value = vec![U254::default(); subgraph.len()];
        });

        Self {
            ff: nodes.ff,
            subgraphs,
            constants: nodes.constants,
            split_signals,
            input_mapping,
            values,
            witness_len,
            thread_count
        }
    }

    pub fn new(graph_file: &str) -> Self {
        Self::new_with_nthreads(graph_file, 0usize)
    }

    pub fn calc_witness(&mut self, inputs_file: &str, witness: &mut [U254]) {
        let inputs_bytes = std::fs::read_to_string(inputs_file).expect("Failed to read input file");

        let inputs = deserialize_inputs2(inputs_bytes.as_bytes(), &self.ff).unwrap();
        let inputs = create_inputs(&inputs, &self.input_mapping).unwrap();
        self.evaluate_parallel(&inputs, witness);
    }

    pub fn get_witness_len(&self) -> usize {
        self.witness_len
    }

    pub fn get_thread_count(&self) -> usize {
        self.thread_count
    }

    pub fn get_prime(&self) -> U254 {
        self.ff.prime
    }

    pub fn evaluate_parallel(&mut self, inputs: &[U254], witness: &mut [U254]) {
        let ff = &self.ff;
        let constants = &self.constants;

        let subgraphs = self.subgraphs.as_slice();
        let values = self.values.as_mut_slice();
        let split_signals = self.split_signals.as_slice();

        let chunk_len = split_signals[0].len();

        subgraphs
            .par_iter()
            .zip(split_signals.par_iter()
            .zip(witness.par_chunks_mut(chunk_len)
            .zip(values.par_iter_mut())))
            .for_each(|(nodes, (outputs, (witness_chunk, values)))| {
            for i in 0..nodes.len() {
                let node = nodes[i];
                let value = match node {
                    Node::Unknown => panic!("Unknown node"),
                    Node::Constant(i) => constants[i],
                    Node::Input(i) => inputs[i],
                    Node::Op(op, a, b) => {
                        ff.op_duo(op, values[a], values[b])
                    },
                    Node::UnoOp(op, a) => {
                        ff.op_uno(op, values[a])
                    },
                    Node::TresOp(op, a, b, c) => {
                        match op {
                            TresOperation::TernCond => {
                                if values[a].is_zero() { values[c] } else { values[b] }
                            },
                        }
                    },
                };
                values[i] = value;
            }

            for i in 0..outputs.len() {
                witness_chunk[i] = values[outputs[i]];
            }
        });
    }
}
