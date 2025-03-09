#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
// #[allow(dead_code)]
pub mod field;
pub mod graph;
pub mod storage;
pub mod vm;

use std::collections::HashMap;
use std::ffi::{c_char, c_int, c_void, CStr};
use std::slice::from_raw_parts;
use ruint::aliases::U256;
use ruint::ParseError;
use crate::graph::Node;
use wtns_file::FieldElement;
use ark_bn254::Fr;
use ark_ff::{BigInteger, PrimeField};
use crate::storage::proto_deserializer::deserialize_witnesscalc_graph_from_bytes;

pub type InputSignalsInfo = HashMap<String, (usize, usize)>;

pub mod proto {
    include!(concat!(env!("OUT_DIR"), "/circom_witnesscalc.proto.rs"));

    pub mod vm {
        include!(concat!(env!("OUT_DIR"), "/circom_witnesscalc.proto.vm.rs"));
    }
}

include!(concat!(env!("OUT_DIR"), "/bindings.rs"));
// include!("bindings.rs");

fn prepare_status(status: *mut gw_status_t, code: GW_ERROR_CODE, error_msg: &str) {
    if !status.is_null() {
        let bs = error_msg.as_bytes();
        unsafe {
            (*status).code = code;
            (*status).error_msg = libc::malloc(bs.len()+1) as *mut c_char;
            libc::memcpy((*status).error_msg as *mut c_void, bs.as_ptr() as *mut c_void, bs.len());
            *((*status).error_msg.add(bs.len())) = 0;
        }
    }
}

/// # Safety
/// 
/// This function is unsafe because it dereferences raw pointers and can cause
/// undefined behavior if misused.
#[no_mangle]
pub unsafe extern "C" fn gw_calc_witness(
    inputs: *const c_char,
    graph_data: *const c_void, graph_data_len: usize,
    wtns_data: *mut *mut c_void, wtns_len: *mut usize,
    status: *mut gw_status_t) -> c_int {

    if inputs.is_null() {
        prepare_status(status, GW_ERROR_CODE_ERROR, "inputs is null");
        return 1;
    }

    if graph_data.is_null() {
        prepare_status(status, GW_ERROR_CODE_ERROR, "graph_data is null");
        return 1;
    }

    if graph_data_len == 0 {
        prepare_status(status, GW_ERROR_CODE_ERROR, "graph_data_len is 0");
        return 1;
    }

    let graph_data_r: &[u8];
    unsafe {
        graph_data_r = from_raw_parts(graph_data as *const u8, graph_data_len);
    }


    let inputs_str: &str;
    unsafe {
        let c = CStr::from_ptr(inputs);
        match c.to_str() {
            Ok(x) => {
                inputs_str = x;
            }
            Err(e) => {
                prepare_status(status, GW_ERROR_CODE_ERROR, format!("Failed to parse inputs: {}", e).as_str());
                return 1;
            }
        }
    }

    let witness = match calc_witness(inputs_str, graph_data_r) {
        Ok(witness) => witness,
        Err(e) => {
            prepare_status(status, GW_ERROR_CODE_ERROR, format!("Failed to calculate witness: {:?}", e).as_str());
            return 1;
        }
    };

    let witness_data = wtns_from_u256_witness(witness);

    unsafe {
        *wtns_len = witness_data.len();
        *wtns_data = libc::malloc(witness_data.len());
        if (*wtns_data).is_null() {
            prepare_status(status, GW_ERROR_CODE_ERROR, "Failed to allocate memory for wtns_data");
            return 1;
        }
        libc::memcpy(*wtns_data, witness_data.as_ptr() as *const c_void, witness_data.len());
    }

    prepare_status(status, GW_ERROR_CODE_ERROR, "test error");

    0
}

// create a wtns file bytes from witness (array of field elements)
pub fn wtns_from_u256_witness(witness: Vec<U256>) -> Vec<u8> {
    let vec_witness: Vec<FieldElement<32>> = witness
        .iter()
        .map(|a| TryInto::<[u8; 32]>::try_into(a.as_le_slice()).unwrap().into())
        .collect();
    wtns_from_witness(vec_witness)
}

fn wtns_from_witness(witness: Vec<FieldElement<32>>) -> Vec<u8> {
    let mut buf = Vec::new();
    let m: [u8; 32] = Fr::MODULUS.to_bytes_le().as_slice().try_into().unwrap();
    let mut wtns_f = wtns_file::WtnsFile::from_vec(witness, m.into());
    wtns_f.version = 2;
    // We write into the buffer, so we should not have any errors here.
    // Panic in case of out of memory is fine.
    wtns_f.write(&mut buf).unwrap();
    buf
}

pub fn calc_witness(inputs: &str, graph_data: &[u8]) -> Result<Vec<U256>, Error> {

    let start = std::time::Instant::now();
    let inputs = deserialize_inputs(inputs.as_bytes())?;
    println!("Inputs loaded in {:?}", start.elapsed());

    let start = std::time::Instant::now();
    let (nodes, signals, input_mapping): (Vec<Node>, Vec<usize>, InputSignalsInfo) =
        deserialize_witnesscalc_graph_from_bytes(graph_data).unwrap();
    println!("Graph loaded in {:?}", start.elapsed());

    let start = std::time::Instant::now();
    let mut inputs_buffer = get_inputs_buffer(get_inputs_size(&nodes));
    populate_inputs(&inputs, &input_mapping, &mut inputs_buffer);
    println!("Inputs populated in {:?}", start.elapsed());

    // graph::evaluate_parallel(&nodes, inputs_buffer.as_slice(), &signals);
    Ok(graph::evaluate(&nodes, inputs_buffer.as_slice(), &signals))
}

fn get_inputs_size(nodes: &[Node]) -> usize {
    let mut start = false;
    let mut max_index = 0usize;
    for &node in nodes.iter() {
        if let Node::Input(i) = node {
            if i > max_index {
                max_index = i;
            }
            start = true
        } else if start {
            break;
        }
    }
    max_index + 1
}

fn populate_inputs(
    input_list: &HashMap<String, Vec<U256>>, inputs_info: &InputSignalsInfo,
    input_buffer: &mut [U256]) {
    for (key, value) in input_list {
        let (offset, len) = inputs_info[key];
        if len != value.len() {
            panic!("Invalid input length for {}", key);
        }
        // println!("input {}, offset {}, len {}", key, offset, len);

        for (i, v) in value.iter().enumerate() {
            input_buffer[offset + i] = *v;
        }
    }
}

/// Allocates inputs vec with position 0 set to 1
fn get_inputs_buffer(size: usize) -> Vec<U256> {
    let mut inputs = vec![U256::ZERO; size];
    inputs[0] = U256::from(1);
    inputs
}

#[derive(Debug)]
pub enum Error {
    InputsUnmarshal(String),
    InputFieldNumberParseError(ParseError)
}

impl From<ParseError> for Error {
    fn from(e: ParseError) -> Self {
        Error::InputFieldNumberParseError(e)
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
                vals.push(U256::from_str_radix(s.as_str(),10)?);
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

    let map = if let serde_json::Value::Object(map) = v {
        map
    } else {
        return Err(Error::InputsUnmarshal("inputs must be an object".to_string()));
    };

    let mut inputs: HashMap<String, Vec<U256>> = HashMap::new();
    for (k, v) in map {
        match v {
            serde_json::Value::String(s) => {
                let i = U256::from_str_radix(s.as_str(),10)?;
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
                let vals: Vec<U256> = flatten_array(k.as_str(), &ss)?;
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

#[cfg(test)]
mod tests {
    use std::collections::HashMap;
    use prost::Message;
    use ruint::aliases::U256;
    use ruint::uint;
    use crate::flatten_array;
    use crate::proto::InputNode;

    #[test]
    fn test_ok() {
        let data = r#"
    {
        "key1": ["123", "456", 100500],
        "key2": "789",
        "key3": 123123
    }
    "#;
        let inputs = super::deserialize_inputs(data.as_bytes()).unwrap();
        let want: HashMap<String, Vec<U256>> = [
            ("key1".to_string(), vec![uint!(123_U256), uint!(456_U256), uint!(100500_U256)]),
            ("key2".to_string(), vec![uint!(789_U256)]),
            ("key3".to_string(), vec![uint!(123123_U256)]),
        ].iter().cloned().collect();

        // Check that both maps have the same length
        assert_eq!(inputs.len(), want.len(), "HashMaps do not have the same length");

        // Iterate and compare each key-value pair
        for (key, value) in &inputs {
            assert_eq!(want.get(key), Some(value), "Mismatch at key: {}", key);
        }
    }

    #[test]
    fn test_ok2() {
        let i: InputNode = InputNode {
            idx: 1,
        };
        let v = i.encode_to_vec();
        println!("{:?}", v.len());
    }

    #[test]
    fn test_flatten_array() {
        let data = r#"["123", "456", 100500, [1, 2]]"#;
        let v = serde_json::from_str(data).unwrap();
        let res = flatten_array("key1", &v).unwrap();

        let want = vec![uint!(123_U256), uint!(456_U256), uint!(100500_U256), uint!(1_U256), uint!(2_U256)];
        assert_eq!(want, res);
    }

    #[test]
    fn test_calc_len() {
        let data = r#"["123", "456", 100500]"#;
        let v = serde_json::from_str(data).unwrap();
        let l = super::calc_len(&v);
        assert_eq!(l, 3);

        let data = r#"["123", ["456", true], 100500]"#;
        let v = serde_json::from_str(data).unwrap();
        let l = super::calc_len(&v);
        assert_eq!(l, 4);
    }

}