use std::collections::HashMap;
use std::env;
use std::fs::File;
use core::str::FromStr;
use std::cell::RefCell;
use std::io::Write;
use std::rc::Rc;
use std::time::Instant;
use ark_bn254::Fr;
use code_producers::c_elements::TemplateInstanceIOMap;
use circom_witnesscalc::{Error};
use circom_witnesscalc::Error::InputsUnmarshal;
use circom_witnesscalc::storage::deserialize_witnesscalc_vm;
use circom_witnesscalc::vm::{build_component, execute};

struct Args {
    vm_file: String,
    inputs_file: String,
    witness_file: String,
}

fn parse_args() -> Args {
    let args: Vec<String> = env::args().collect();
    if args.len() != 4 {
        eprintln!("Usage: {} <graph.bin> <inputs.json> <witness.wtns>", args[0]);
        std::process::exit(1);
    }

    Args {
        vm_file: args[1].clone(),
        inputs_file: args[2].clone(),
        witness_file: args[3].clone(),
    }
}

fn calc_len(vs: &Vec<serde_json::Value>) -> usize {
    let mut len = vs.len();

    for v in vs {
        if let serde_json::Value::Array(arr) = v {
            len += calc_len(arr)-1;
        }
    }

    len
}

fn flatten_array(
    key: &str, vs: &Vec<serde_json::Value>) -> Result<Vec<Fr>, Error> {

    let mut vals: Vec<Fr> = Vec::with_capacity(calc_len(vs));

    for v in vs {
        match v {
            serde_json::Value::String(s) => {
                let i = Fr::from_str(s.as_str())
                    .map_err(
                        |_| {InputsUnmarshal(format!(
                            "can't convert to field number: {}",
                            s.as_str()))})?;
                vals.push( i);
            }
            serde_json::Value::Number(n) => {
                vals.push(Fr::from(
                    n.as_u64()
                        .ok_or(Error::InputsUnmarshal(format!(
                            "signal value is not a positive integer: {}",
                            key).to_string()))?));
            }
            serde_json::Value::Array(arr) => {
                vals.extend_from_slice(flatten_array(key, arr)?.as_slice());
            }
            _ => {
                return Err(Error::InputsUnmarshal(
                    format!("inputs must be a string: {}", key).to_string()));
            }
        };

    }
    Ok(vals)
}

pub fn deserialize_inputs(inputs_data: &[u8]) -> Result<HashMap<String, Vec<Fr>>, Error> {
    let v: serde_json::Value = serde_json::from_slice(inputs_data).unwrap();

    let map = v.as_object()
        .ok_or_else(
            || Error::InputsUnmarshal("inputs must be an object".to_string()))?;

    let mut inputs: HashMap<String, Vec<Fr>> = HashMap::new();
    for (k, v) in map {
        match v {
            serde_json::Value::String(s) => {
                let i = Fr::from_str(s.as_str())
                    .map_err(
                        |_| {InputsUnmarshal(format!(
                            "can't convert to field number: {}",
                            s.as_str()))})?;
                inputs.insert(k.clone(), vec![i]);
            }
            serde_json::Value::Number(n) => {
                if !n.is_u64() {
                    return Err(Error::InputsUnmarshal("signal value is not a positive integer".to_string()));
                }
                let i = Fr::from(n.as_u64().unwrap());
                inputs.insert(k.clone(), vec![i]);
            }
            serde_json::Value::Array(ss) => {
                let vals: Vec<Fr> = flatten_array(k.as_str(), &ss)?;
                inputs.insert(k.clone(), vals);
            }
            _ => {
                return Err(Error::InputsUnmarshal(format!(
                    "value for key {} must be an a number as a string, as a number of an array of strings of numbers",
                    k.clone())));
            }
        }
    }
    Ok(inputs)
}

fn main() {
    let args = parse_args();

    let inputs_data = std::fs::read_to_string(&args.inputs_file)
        .expect("Failed to read input file");

    let vm_data = std::fs::read(&args.vm_file).expect("Failed to read vm file");

    let start = Instant::now();

    let inputs = deserialize_inputs(inputs_data.as_bytes()).unwrap();
    println!("number of input keys {}", inputs.len());


    let (templates, functions, main_template_id, signals_num) =  deserialize_witnesscalc_vm(
        std::io::Cursor::new(vm_data)).unwrap();

    let main_component_signals_start = 1;
    let main_component = build_component(
        &templates, main_template_id, main_component_signals_start);
    let main_component = Rc::new(RefCell::new(main_component));

    // let (nodes, signals, input_mapping): (Vec<Node>, Vec<usize>, InputSignalsInfo) =
    //     deserialize_witnesscalc_graph(std::io::Cursor::new(graph_data)).unwrap();
    //
    // let mut inputs_buffer = get_inputs_buffer(get_inputs_size(&nodes));
    // populate_inputs(&inputs, &input_mapping, &mut inputs_buffer);
    //
    // let witness = graph::evaluate(&nodes, inputs_buffer.as_slice(), &signals);
    //
    // TODO
    let constants = vec![];
    // TODO
    let mut signals = Vec::with_capacity(signals_num);
    // TODO
    let io_map = TemplateInstanceIOMap::new();
    // TODO: pass expected signals
    execute(
        main_component, &templates, &functions, &constants, &mut signals,
        &io_map, None);
    //
    // let wtns_bytes = wtns_from_witness(witness);
    // TODO
    let wtns_bytes = vec![];
    //
    let duration = start.elapsed();
    println!("Witness generated in: {:?}", duration);
    //
    {
        let mut f = File::create(&args.witness_file).unwrap();
        f.write_all(&wtns_bytes).unwrap();
    }
    //
    // println!("witness saved to {}", &args.witness_file);
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_ok() {
        println!("OK");
    }
}