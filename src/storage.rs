use std::collections::HashMap;
#[cfg(test)]
use std::fmt::{Debug, Formatter};
use std::io::{Error, ErrorKind, Read, Write};
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use code_producers::c_elements::InputList;
use code_producers::components::{IODef, TemplateInstanceIOMap};
use prost::Message;
use ruint::aliases::U256;
use crate::field::{FieldOps, U254};
use crate::graph::{Nodes, NodesInterface, Operation, TresOperation, UnoOperation};
use crate::InputSignalsInfo;
use crate::proto::SignalDescription;
use crate::proto::vm::{IoDef, IoDefs};
use crate::vm::{Function, Template};
// format of the wtns.graph file:
// + magic line: wtns.graph.001
// + 4 bytes unsigned LE 32-bit integer: number of nodes
// + series of protobuf serialized nodes. Each node prefixed by varint length
// + protobuf serialized GraphMetadata
// + 8 bytes unsigned LE 64-bit integer: offset of GraphMetadata message

pub mod proto_deserializer;

const WITNESSCALC_GRAPH_MAGIC: &[u8] = b"wtns.graph.001";
const WITNESSCALC_VM_MAGIC: &[u8] = b"wtns.vm.001";

const MAX_VARINT_LENGTH: usize = 10;

impl From<crate::proto::UnoOp> for UnoOperation {
    fn from(value: crate::proto::UnoOp) -> Self {
        match value {
            crate::proto::UnoOp::Neg => UnoOperation::Neg,
            crate::proto::UnoOp::Id => UnoOperation::Id,
            crate::proto::UnoOp::Lnot => UnoOperation::Lnot,
            crate::proto::UnoOp::Bnot => UnoOperation::Bnot,
        }
    }
}

impl From<crate::proto::DuoOp> for Operation {
    fn from(value: crate::proto::DuoOp) -> Self {
        match value {
            crate::proto::DuoOp::Mul => Operation::Mul,
            crate::proto::DuoOp::Div => Operation::Div,
            crate::proto::DuoOp::Add => Operation::Add,
            crate::proto::DuoOp::Sub => Operation::Sub,
            crate::proto::DuoOp::Pow => Operation::Pow,
            crate::proto::DuoOp::Idiv => Operation::Idiv,
            crate::proto::DuoOp::Mod => Operation::Mod,
            crate::proto::DuoOp::Eq => Operation::Eq,
            crate::proto::DuoOp::Neq => Operation::Neq,
            crate::proto::DuoOp::Lt => Operation::Lt,
            crate::proto::DuoOp::Gt => Operation::Gt,
            crate::proto::DuoOp::Leq => Operation::Leq,
            crate::proto::DuoOp::Geq => Operation::Geq,
            crate::proto::DuoOp::Land => Operation::Land,
            crate::proto::DuoOp::Lor => Operation::Lor,
            crate::proto::DuoOp::Shl => Operation::Shl,
            crate::proto::DuoOp::Shr => Operation::Shr,
            crate::proto::DuoOp::Bor => Operation::Bor,
            crate::proto::DuoOp::Band => Operation::Band,
            crate::proto::DuoOp::Bxor => Operation::Bxor,
        }
    }
}

impl From<crate::proto::TresOp> for TresOperation {
    fn from(value: crate::proto::TresOp) -> Self {
        match value {
            crate::proto::TresOp::TernCond => TresOperation::TernCond,
        }
    }
}

pub fn serialize_witnesscalc_graph<W: Write, T: FieldOps + 'static>(
    mut w: W, nodes: &Nodes<T>, witness_signals: &[usize],
    input_signals: &InputSignalsInfo) -> std::io::Result<()> {

    let mut ptr = 0usize;
    w.write_all(WITNESSCALC_GRAPH_MAGIC).unwrap();
    ptr += WITNESSCALC_GRAPH_MAGIC.len();

    w.write_u64::<LittleEndian>(nodes.nodes.len() as u64)?;
    ptr += 8;

    let metadata = crate::proto::GraphMetadata {
        witness_signals: witness_signals.iter().map(|x| *x as u32).collect::<Vec<u32>>(),
        inputs: input_signals.iter().map(|(k, v)| {
            let sig = crate::proto::SignalDescription {
                offset: v.0 as u32,
                len: v.1 as u32 };
            (k.clone(), sig)
        }).collect(),
        prime: Some(crate::proto::BigUInt {
            value_le: nodes.prime().to_le_bytes()
        }),
        prime_str: nodes.prime_str(),
    };

    // capacity of buf should be enough to hold the largest message + 10 bytes
    // of varint length
    let mut buf =
        Vec::with_capacity(metadata.encoded_len() + MAX_VARINT_LENGTH);

    for i in 0..nodes.len() {
        let node = nodes.to_proto(i).unwrap();
        let node_pb = crate::proto::Node{ node: Some(node) };

        assert_eq!(buf.len(), 0);
        node_pb.encode_length_delimited(&mut buf)?;
        ptr += buf.len();

        w.write_all(&buf)?;
        buf.clear();

    }

    metadata.encode_length_delimited(&mut buf)?;
    w.write_all(&buf)?;
    buf.clear();

    w.write_u64::<LittleEndian>(ptr as u64)?;

    Ok(())
}

pub struct CompiledCircuit {
    pub main_template_id: usize,
    pub templates: Vec<Template>,
    pub functions: Vec<Function>,
    pub signals_num: usize,
    pub constants: Vec<U256>,
    pub inputs: InputList,
    pub witness_signals: Vec<usize>,
    pub io_map: TemplateInstanceIOMap,
}

#[cfg(test)]
impl Debug for CompiledCircuit {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CompiledCircuit")
            .field("main_template_id", &self.main_template_id)
            .field("templates", &self.templates)
            .field("functions", &self.functions)
            .field("signals_num", &self.signals_num)
            .field("constants", &self.constants.iter().map(|x| x.to_string()).collect::<Vec<String>>())
            .field("inputs", &self.inputs)
            .field("witness_signals", &self.witness_signals)
            .field(
                "io_map",
                &self.io_map.iter()
                    .map( |(&x, y)|
                        (
                            x,
                            y.iter().map(|z| (z.code, z.offset, z.lengths.clone())).collect::<Vec<(usize, usize, Vec<usize>)>>(),
                        )
                    )
                    .collect::<Vec<(usize, Vec<(usize, usize, Vec<usize>)>)>>()
            )
            .finish()
    }
}

pub fn serialize_witnesscalc_vm(
    mut w: impl Write, cs: &CompiledCircuit) -> std::io::Result<()> {

    let inputs_desc = cs.inputs.iter()
        .map(|(name, offset, len)| {
            (
                name.clone(),
                SignalDescription {
                    offset: TryInto::<u32>::try_into(*offset)
                        .expect("signal offset is too large"),
                    len: TryInto::<u32>::try_into(*len)
                        .expect("signals length is too large"),
                },
            )
        }).collect::<HashMap<String, SignalDescription>>();

    w.write_all(WITNESSCALC_VM_MAGIC).unwrap();

    let io_map = cs.io_map.iter()
        .map(|(tmpl_idx, io_list)| {
            (
                TryInto::<u32>::try_into(*tmpl_idx)
                    .expect("io_map template index is too large"),
                IoDefs{
                    io_defs: io_list.iter()
                        .map(|x| IoDef{
                            code: x.code.try_into()
                                .expect("signal code is too large"),
                            offset: x.offset.try_into()
                                .expect("signal offset is too large"),
                            lengths: x.lengths.iter()
                                .map(|l| TryInto::<u32>::try_into(*l)
                                    .expect("signal length is too large"))
                                .collect::<Vec<u32>>(),
                        })
                        .collect()
                }
            )
        })
        .collect();

    let md = crate::proto::vm::VmMd {
        main_template_id: cs.main_template_id.try_into()
            .expect("main template id too large"),
        templates_num: TryInto::<u32>::try_into(cs.templates.len())
            .expect("too many templates"),
        functions_num: TryInto::<u32>::try_into(cs.functions.len())
            .expect("too many functions"),
        signals_num: TryInto::<u32>::try_into(cs.signals_num)
            .expect("too many signals"),
        constants_num: TryInto::<u32>::try_into(cs.constants.len())
            .expect("too many constants"),
        inputs: inputs_desc,
        witness_signals: cs.witness_signals.iter()
            .map(|x| TryInto::<u32>::try_into(*x)
                .expect("witness signal index is too large"))
            .collect(),
        io_map,
    };

    let mut buf = Vec::new();
    md.encode_length_delimited(&mut buf)?;
    w.write_all(&buf)?;
    buf.clear();

    for tmpl in &cs.templates {
        let tmpl_pb: crate::proto::vm::Template = tmpl.try_into().unwrap();
        assert_eq!(buf.len(), 0);
        tmpl_pb.encode_length_delimited(&mut buf)?;
        w.write_all(&buf)?;
        buf.clear();
    }

    for func in &cs.functions {
        let func_pb: crate::proto::vm::Function = func.try_into().unwrap();
        assert_eq!(buf.len(), 0);
        func_pb.encode_length_delimited(&mut buf)?;
        w.write_all(&buf)?;
        buf.clear();
    }

    for c in &cs.constants {
        w.write_all(c.as_le_slice())?;
    }

    Ok(())
}

fn read_message_length<R: Read>(rw: &mut WriteBackReader<R>) -> std::io::Result<usize> {
    let mut buf = [0u8; MAX_VARINT_LENGTH];
    let bytes_read = rw.read(&mut buf)?;
    if bytes_read == 0 {
        return Err(std::io::Error::new(
            std::io::ErrorKind::UnexpectedEof, "Unexpected EOF"));
    }

    let len_delimiter = prost::decode_length_delimiter(buf.as_ref())?;

    let lnln = prost::length_delimiter_len(len_delimiter);

    if lnln < bytes_read {
        rw.write_all(&buf[lnln..bytes_read])?;
    }

    Ok(len_delimiter)
}

fn read_message<R: Read, M: Message + Default>(rw: &mut WriteBackReader<R>) -> std::io::Result<M> {
    let ln = read_message_length(rw)?;
    let mut buf = vec![0u8; ln];
    let bytes_read = rw.read(&mut buf)?;
    if bytes_read != ln {
        return Err(std::io::Error::new(
            std::io::ErrorKind::UnexpectedEof, "Unexpected EOF"));
    }

    let msg = prost::Message::decode(&buf[..])?;

    Ok(msg)
}

pub fn deserialize_witnesscalc_vm(
    mut r: impl Read) -> std::io::Result<CompiledCircuit>{

    let mut br = WriteBackReader::new(&mut r);
    let mut magic = [0u8; WITNESSCALC_VM_MAGIC.len()];

    br.read_exact(&mut magic)?;

    if !magic.eq(WITNESSCALC_VM_MAGIC) {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            "vm file does not look like a witnesscalc vm file"));
    };

    let md: crate::proto::vm::VmMd = read_message(&mut br)?;

    let mut templates: Vec<Template> = Vec::with_capacity(md.templates_num as usize);
    for _ in 0..md.templates_num {
        let tmpl: crate::proto::vm::Template = read_message(&mut br)?;
        templates.push(Template::try_from(&tmpl).unwrap());
    }

    let mut functions: Vec<Function> = Vec::with_capacity(md.functions_num as usize);
    for _ in 0..md.functions_num {
        let func: crate::proto::vm::Function = read_message(&mut br)?;
        functions.push(Function::try_from(&func).unwrap());
    }

    let mut constants = Vec::with_capacity(md.constants_num as usize);
    for _ in 0 .. md.constants_num {
        let mut buf = [0u8; 32];
        br.read_exact(&mut buf)?;
        let c = U256::from_le_slice(&buf);
        constants.push(c);
    }

    Ok(CompiledCircuit {
        main_template_id: md.main_template_id.try_into()
            .expect("main template id too large for this architecture"),
        templates,
        functions,
        signals_num: md.signals_num.try_into()
            .expect("signals number too large for this architecture"),
        constants,
        inputs: md.inputs.iter()
            .map(|(sig_name, sig_desc)| (
                sig_name.clone(),
                TryInto::<usize>::try_into(sig_desc.offset)
                    .expect("signal offset is too large for this architecture"),
                TryInto::<usize>::try_into(sig_desc.len)
                    .expect("signals length is too large for this architecture"),
            ))
            .collect(),
        witness_signals: md.witness_signals.iter()
            .map(|x| TryInto::<usize>::try_into(*x)
                .expect("witness signal index is too large for this architecture"))
            .collect(),
        io_map: md.io_map
            .iter()
            .map(|(tmpl_id, io_defs)| (
                TryInto::<usize>::try_into(*tmpl_id)
                    .expect("template index is too large for this architecture"),
                io_defs.io_defs.iter()
                    .map(|d| IODef {
                        code: d.code.try_into()
                            .expect("signal code is too large for this architecture"),
                        offset: d.offset.try_into()
                            .expect("signal offset is too large for this architecture"),
                        lengths: d.lengths.iter()
                            .map(|l| TryInto::<usize>::try_into(*l)
                                .expect("signal length is too large for this architecture"))
                            .collect(),
                    })
                    .collect(),
            ))
            .collect(),
    })
}

// This function is unused, but it is a reference implementation of
// wtns.graph.001 file format deserialization. There is another replacement
// for this function — deserialize_witnesscalc_graph_from_bytes, but it
// implements custom protobuf deserialization and may be not fully compatible.
pub fn deserialize_witnesscalc_graph(
    r: impl Read) -> std::io::Result<(Box<dyn NodesInterface>, Vec<usize>, InputSignalsInfo)> {

    let mut br = WriteBackReader::new(r);
    let mut magic = [0u8; WITNESSCALC_GRAPH_MAGIC.len()];

    br.read_exact(&mut magic)?;

    if !magic.eq(WITNESSCALC_GRAPH_MAGIC) {
        return Err(Error::new(
            ErrorKind::InvalidData, "Invalid magic"));
    }

    let nodes_num = br.read_u64::<LittleEndian>()?;
    let mut nodes_pb = Vec::with_capacity(nodes_num as usize);
    for _ in 0..nodes_num {
        let n: crate::proto::Node = read_message(&mut br)?;
        nodes_pb.push(n);
        // let n2: Node = n.into();
        // nodes.push(n2);
    }

    let md: crate::proto::GraphMetadata = read_message(&mut br)?;

    let witness_signals = md.witness_signals
        .iter()
        .map(|x| *x as usize)
        .collect::<Vec<usize>>();

    let input_signals = md.inputs.iter()
        .map(|(k, v)| {
            (k.clone(), (v.offset as usize, v.len as usize))
        })
        .collect::<InputSignalsInfo>();

    let outer_nodes: Box<dyn NodesInterface> = if (md.prime.is_none() && md.prime_str.is_empty())
        || md.prime_str == "bn128" {

        let prime = U254::from_str_radix(
            "21888242871839275222246405745257275088548364400416034343698204186575808495617",
            10).unwrap();

        if md.prime.is_some() {
            let prime_pb = md.prime.unwrap();
            let prime2 = U254::from_le_slice(prime_pb.value_le.as_slice());
            if prime2 != prime {
                return Err(Error::new(
                    ErrorKind::InvalidData,
                    format!("prime mismatch, want {}, actual {}",
                            prime, prime2)));
            }
        }

        let mut nodes = Nodes::new(prime, "bn128");
        for n in nodes_pb.iter() {
            match &n.node {
                Some(n) => nodes.push_proto(n),
                None => {
                    return Err(Error::new(ErrorKind::InvalidData, "empty node"));
                }
            }
        }
        Box::new(nodes)
    } else {
        return Err(Error::new(
            ErrorKind::InvalidData,
            format!("unknown prime {}", md.prime_str)));
    };

    Ok((outer_nodes, witness_signals, input_signals))
}

struct WriteBackReader<R: Read> {
    reader: R,
    buffer: Vec<u8>,
}

impl <R: Read> WriteBackReader<R> {
    fn new(reader: R) -> Self {
        WriteBackReader {
            reader,
            buffer: Vec::new(),
        }
    }
}

impl<R: Read> Read for WriteBackReader<R> {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        if buf.is_empty() {
            return Ok(0)
        }

        let mut n = 0usize;

        if !self.buffer.is_empty() {
            n = std::cmp::min(buf.len(), self.buffer.len());
            self.buffer[self.buffer.len()-n..]
                .iter()
                .rev()
                .enumerate()
                .for_each(|(i, x)| {
                    buf[i] = *x;
                });
            self.buffer.truncate(self.buffer.len() - n);
        }

        while n < buf.len() {
            let m = self.reader.read(&mut buf[n..])?;
            if m == 0 {
                break;
            }
            n += m;
        }

        Ok(n)
    }
}

impl<R: Read> Write for WriteBackReader<R> {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.buffer.reserve(buf.len());
        self.buffer.extend(buf.iter().rev());
        Ok(buf.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

pub fn init_input_signals(
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
    use std::collections::HashMap;
    use crate::graph::{Node, Operation, TresOperation, UnoOperation};
    use byteorder::ByteOrder;
    use crate::vm::ComponentTmpl;
    use crate::field::{FieldOperations, U254};
    use crate::storage::proto_deserializer::deserialize_witnesscalc_graph_from_bytes;
    use super::*;

    #[test]
    fn test_read_message() {
        let mut buf = Vec::new();
        let n1 = crate::proto::Node {
            node: Some(crate::proto::node::Node::Input(
                crate::proto::InputNode { idx: 1 }))
        };
        n1.encode_length_delimited(&mut buf).unwrap();

        let n2 = crate::proto::Node {
            node: Some(crate::proto::node::Node::Input(
                crate::proto::InputNode { idx: 2 }))
        };
        n2.encode_length_delimited(&mut buf).unwrap();

        let mut reader = std::io::Cursor::new(&buf);

        let mut rw = WriteBackReader::new(&mut reader);

        let got_n1: crate::proto::Node = read_message(&mut rw).unwrap();
        assert!(n1.eq(&got_n1));

        let got_n2: crate::proto::Node = read_message(&mut rw).unwrap();
        assert!(n2.eq(&got_n2));

        assert_eq!(reader.position(), buf.len() as u64);
    }

    #[test]
    fn test_read_message_variant() {
        let prime = U254::from_str_radix(
            "21888242871839275222246405745257275088548364400416034343698204186575808495617",
            10).unwrap();
        let mut nodes = Nodes::new(prime, "bn128");
        nodes.push(Node::Input(0));
        let c = (&nodes.ff).parse_str("1").unwrap();
        nodes.push_constant(c);
        nodes.push(Node::UnoOp(UnoOperation::Id, 1));
        nodes.push(Node::Op(Operation::Add, 1, 2));
        nodes.push(Node::TresOp(TresOperation::TernCond, 1, 2, 2));
        let mut nodes_pb = Vec::new();
        let mut buf = Vec::new();
        for i in 0..nodes.len() {
            let n = nodes.to_proto(i).unwrap();
            let node_pb = crate::proto::Node{ node: Some(n) };
            node_pb.encode_length_delimited(&mut buf).unwrap();
            nodes_pb.push(node_pb);
        }
        let mut nodes_got: Vec<crate::proto::Node> = Vec::new();
        let mut reader = std::io::Cursor::new(&buf);
        let mut rw = WriteBackReader::new(&mut reader);
        for _ in 0..nodes.len() {
            nodes_got.push(read_message(&mut rw).unwrap());
        }
        assert_eq!(nodes_pb, nodes_got);
    }

    #[test]
    fn test_write_back_reader() {
        let data = [1u8, 2, 3, 4, 5, 6];
        let mut r = WriteBackReader::new(std::io::Cursor::new(&data));

        let buf = &mut [0u8; 5];
        r.read(buf).unwrap();
        assert_eq!(buf, &[1, 2, 3, 4, 5]);

        // return [4, 5] to reader
        r.write(&buf[3..]).unwrap();
        // return [2, 3] to reader
        r.write(&buf[1..3]).unwrap();

        buf.fill(0);

        // read 3 bytes, expect [2, 3, 4] after returns
        let mut n = r.read(&mut buf[..3]).unwrap();
        assert_eq!(n, 3);
        assert_eq!(buf, &[2, 3, 4, 0, 0]);

        buf.fill(0);

        // read everything left in reader
        n = r.read(buf).unwrap();
        assert_eq!(n, 2);
        assert_eq!(buf, &[5, 6, 0, 0, 0]);
    }

    #[test]
    fn test_deserialize_inputs() {
        let prime = <U254 as FieldOps>::from_str("21888242871839275222246405745257275088548364400416034343698204186575808495617").unwrap();
        let mut nodes = Nodes::new(prime, "bn128");
        nodes.push(Node::Input(0));
        let c = (&nodes.ff).parse_str("1").unwrap();
        nodes.push_constant(c);
        let c = (&nodes.ff).parse_str("0").unwrap();
        nodes.push_constant(c);
        nodes.push_noopt(Node::UnoOp(UnoOperation::Id, 0));
        nodes.push_noopt(Node::Op(Operation::Mul, 1, 2));
        nodes.push_noopt(Node::TresOp(TresOperation::TernCond, 1, 2, 3));

        let witness_signals = vec![4, 1];

        let mut input_signals: InputSignalsInfo = HashMap::new();
        input_signals.insert("sig1".to_string(), (1, 3));
        input_signals.insert("sig2".to_string(), (5, 1));

        let mut tmp = Vec::new();
        serialize_witnesscalc_graph(&mut tmp, &nodes, &witness_signals, &input_signals).unwrap();

        let mut reader = std::io::Cursor::new(&tmp);

        let (nodes_res, witness_signals_res, input_signals_res) =
            deserialize_witnesscalc_graph(&mut reader).unwrap();

        match nodes_res.as_any().downcast_ref::<Nodes<U254>>() {
            Some(t) => {
                assert_eq!(&nodes, t);
            },
            None => panic!(),
        }
        assert_eq!(input_signals, input_signals_res);
        assert_eq!(witness_signals, witness_signals_res);

        let (nodes_res, witness_signals_res, input_signals_res) =
            deserialize_witnesscalc_graph_from_bytes(&tmp).unwrap();
        match nodes_res.as_any().downcast_ref::<Nodes<U254>>() {
            Some(t) => {
                assert_eq!(&nodes, t);
            },
            None => panic!(),
        }

        assert_eq!(input_signals, input_signals_res);
        assert_eq!(witness_signals, witness_signals_res);

        let metadata_start = LittleEndian::read_u64(&tmp[tmp.len() - 8..]);

        let mt_reader = std::io::Cursor::new(&tmp[metadata_start as usize..]);
        let mut rw = WriteBackReader::new(mt_reader);
        let metadata: crate::proto::GraphMetadata = read_message(&mut rw).unwrap();

        let prime = nodes.prime();
        let prime_bytes: Vec<u8> = <U254 as FieldOps>::to_le_bytes(&prime);
        let metadata_want = crate::proto::GraphMetadata {
            witness_signals: vec![4, 1],
            inputs: input_signals.iter().map(|(k, v)| {
                (k.clone(), SignalDescription {
                    offset: v.0 as u32,
                    len: v.1 as u32
                })
            }).collect(),
            prime: Some(crate::proto::BigUInt {
                value_le: prime_bytes,
            }),
            prime_str: nodes.prime_str(),
        };

        assert_eq!(metadata, metadata_want);
    }

    #[test]
    fn test_serialization() {

        let mut buf: Vec<u8> = Vec::new();

        let mut io_map = TemplateInstanceIOMap::new();
        let io_list = vec![
            IODef {
                code: 1,
                offset: 2,
                lengths: vec![3, 4, 5],
            },
            IODef {
                code: 6,
                offset: 7,
                lengths: vec![8, 9, 10],
            },
        ];
        io_map.insert(100, io_list);

        let cs = CompiledCircuit {
            main_template_id: 2,
            templates: vec![
                Template{
                    name: "tmpl1".to_string(),
                    code: vec![1, 2, 3],
                    line_numbers: vec![10, 20, 30],
                    components: vec![
                        ComponentTmpl{
                            symbol: "sym1".to_string(),
                            sub_cmp_idx: 1,
                            number_of_cmp: 2,
                            name_subcomponent: "sub1".to_string(),
                            signal_offset: 3,
                            signal_offset_jump: 4,
                            template_id: 5,
                            has_inputs: true,
                        },
                        ComponentTmpl{
                            symbol: "sym2".to_string(),
                            sub_cmp_idx: 10,
                            number_of_cmp: 20,
                            name_subcomponent: "sub2".to_string(),
                            signal_offset: 30,
                            signal_offset_jump: 40,
                            template_id: 50,
                            has_inputs: false,
                        },
                    ],
                    var_stack_depth: 4,
                    number_of_inputs: 5,
                },
                Template{
                    name: "tmpl2".to_string(),
                    code: vec![10, 20, 30],
                    line_numbers: vec![100, 200, 300],
                    components: vec![],
                    var_stack_depth: 40,
                    number_of_inputs: 50,
                },
            ],
            functions: vec![
                Function{
                    name: "func1".to_string(),
                    symbol: "sym1".to_string(),
                    code: vec![1, 2, 3],
                    line_numbers: vec![10, 20, 30],
                },
            ],
            signals_num: 3,
            constants: vec![U256::from(100500)],
            inputs: vec![("inp1".to_string(), 5, 10)],
            witness_signals: vec![1, 2, 3],
            io_map,
        };
        serialize_witnesscalc_vm(&mut buf, &cs).unwrap();

        let cs2 = deserialize_witnesscalc_vm(&buf[..]).unwrap();

        // println!("{:?}", cs);
        // println!("{:?}", cs2);

        assert_eq!(format!("{:?}", cs), format!("{:?}", cs2));
    }
}