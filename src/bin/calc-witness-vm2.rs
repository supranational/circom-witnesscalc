use std::collections::HashMap;
use std::{env};
use std::fs::File;
use std::cell::RefCell;
use std::io::Write;
use std::rc::Rc;
use std::time::Instant;
use code_producers::c_elements::{InputList};
use ruint::aliases::U256;
use circom_witnesscalc::{wtns_from_witness, Error};
use circom_witnesscalc::Error::InputsUnmarshal;
use circom_witnesscalc::graph::u256_to_fr;
use circom_witnesscalc::storage::deserialize_witnesscalc_vm2;
use circom_witnesscalc::vm2::{build_component, execute};

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
    key: &str, vs: &Vec<serde_json::Value>) -> Result<Vec<U256>, Error> {

    let mut vals: Vec<U256> = Vec::with_capacity(calc_len(vs));

    for v in vs {
        match v {
            serde_json::Value::String(s) => {
                let i = U256::from_str_radix(s.as_str(), 10)
                    .map_err(
                        |_| {InputsUnmarshal(format!(
                            "can't convert to field number: {}",
                            s.as_str()))})?;
                vals.push( i);
            }
            serde_json::Value::Number(n) => {
                vals.push(U256::from(
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

pub fn deserialize_inputs(inputs_data: &[u8]) -> Result<HashMap<String, Vec<U256>>, Error> {
    let v: serde_json::Value = serde_json::from_slice(inputs_data).unwrap();

    let map = v.as_object()
        .ok_or_else(
            || Error::InputsUnmarshal("inputs must be an object".to_string()))?;

    let mut inputs: HashMap<String, Vec<U256>> = HashMap::new();
    for (k, v) in map {
        match v {
            serde_json::Value::String(s) => {
                let i = U256::from_str_radix(s.as_str(), 10)
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
                let i = U256::from(n.as_u64().unwrap());
                inputs.insert(k.clone(), vec![i]);
            }
            serde_json::Value::Array(ss) => {
                let vals: Vec<U256> = flatten_array(k.as_str(), ss)?;
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

    let start0 = Instant::now();

    let start = Instant::now();

    let inputs = deserialize_inputs(inputs_data.as_bytes()).unwrap();
    println!("Inputs loaded in {:?}, number of input keys {}.", start.elapsed(), inputs.len());


    let start = Instant::now();
    let cs =
        deserialize_witnesscalc_vm2(std::io::Cursor::new(&vm_data)).unwrap();
    println!(
        "VM file read and parsed in {:?}. Templates: {}, functions: {}.",
        start.elapsed(), cs.templates.len(), cs.functions.len());

    let start = Instant::now();
    let main_component_signals_start = 1;
    let main_component = build_component(
        &cs.templates, cs.main_template_id, main_component_signals_start);
    let main_component = Rc::new(RefCell::new(main_component));
    println!("Component tree built in {:?}.", start.elapsed());

    let start = Instant::now();
    let mut signals = Vec::new();
    signals.resize(cs.signals_num, None);
    init_input_signals(&cs.inputs, &inputs, &mut signals);
    println!("Signals initialized in {:?}.", start.elapsed());

    let start = Instant::now();
    // TODO: pass expected signals
    execute(
        main_component, &cs.templates, &cs.functions, &cs.constants,
        &mut signals, &cs.io_map, None);
    println!("VM execution done in {:?}.", start.elapsed());
    //

    let start = Instant::now();

    let mut witness = Vec::with_capacity(cs.witness_signals.len());
    for w in cs.witness_signals.iter() {
        witness.push(signals[*w].unwrap());
    }

    let witness = witness.iter()
        .map(|x| u256_to_fr(x)).collect::<Vec<_>>();
    let wtns_bytes = wtns_from_witness(witness);

    {
        let mut f = File::create(&args.witness_file).unwrap();
        f.write_all(&wtns_bytes).unwrap();
    }

    println!("Witness created from signals in {:?}", start.elapsed());

    println!("Total time {:?}", start0.elapsed());
}

fn init_input_signals(
    inputs_desc: &InputList,
    inputs: &HashMap<String, Vec<U256>>,
    signals: &mut [Option<U256>],
) {
    signals[0] = Some(U256::from(1u64));

    for (name, offset, len) in inputs_desc {
        match inputs.get(name) {
            Some(values) => {
                if values.len() != *len {
                    panic!(
                        "input signal {} has different length in inputs file, want {}, actual {}",
                        name, len, values.len());
                }
                for (i, v) in values.iter().enumerate() {
                    signals[*offset + i] = Some(*v);
                }
            }
            None => {
                panic!("input signal {} is not found in inputs file", name);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_ok() {
        println!("OK");
    }
}