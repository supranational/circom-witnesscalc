use std::{env, fs};
use std::path::PathBuf;
use core::convert::TryInto;
use core::str::FromStr;
use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt::Display;
use std::fs::File;
use std::io::Write;
use std::rc::Rc;
use std::time::Instant;
use ark_bn254::Fr;
use ark_ff::BigInt;
use ark_ff::PrimeField;
use ark_ff::BigInteger;
use ark_ff::One;
use ark_ff::Zero;
use code_producers::c_elements::TemplateInstanceIOMap;
use compiler::circuit_design::function::FunctionCode;
use compiler::circuit_design::template::TemplateCode;
use compiler::compiler_interface::{run_compiler, Circuit, Config};
use compiler::intermediate_representation::InstructionList;
use compiler::intermediate_representation::ir_interface::{AddressType, ComputeBucket, CreateCmpBucket, InputInformation, Instruction, InstructionPointer, LoadBucket, LocationRule, ObtainMeta, OperatorType, ReturnType, StatusInput, ValueType};
use constraint_generation::{build_circuit, BuildConfig};
use program_structure::error_definition::Report;
use type_analysis::check_types::check_types;
use wtns_file::FieldElement;
use circom_witnesscalc::{deserialize_inputs};
use circom_witnesscalc::graph::{Operation, UnoOperation};

struct Args {
    circuit_file: String,
    inputs_file: Option<String>,
    graph_file: String,
    link_libraries: Vec<PathBuf>,
    print_debug: bool,
    witness_file: Option<String>,
    expected_signals: Option<Vec<Fr>>,
}

// An instance of a template
struct Component {
    vars: Vec<Option<Fr>>,
    signals_start: usize,
    template_id: usize,
    subcomponents: Vec<Rc<RefCell<Component>>>,
    number_of_inputs: usize,
}

struct Template {
    name: String,
    code: Vec<u8>,
    line_numbers: Vec<usize>,
    components: Vec<ComponentTmpl>,
}

struct Function {
    name: String,
    symbol: String,
    code: Vec<u8>,
    line_numbers: Vec<usize>,
}

struct VM<'a, 'b> {
    templates: &'a Vec<Template>,
    signals: &'a mut [Option<Fr>],
    constants: &'a Vec<Fr>,
    stack: Vec<Fr>,
    stack_u32: Vec<u32>,
    expected_signals: Option<&'a Vec<Fr>>,
    call_frames: Vec<Frame<'a, 'b>>,
}

impl<'a, 'b> VM<'a, 'b> {
    fn assert_signal(&self, sig_idx: usize) {
        if let Some(expected_signals) = self.expected_signals {
            let cmp = expected_signals[sig_idx].cmp(&self.signals[sig_idx].unwrap());
            match cmp {
                Ordering::Equal => return,
                _ => {
                    self.print_stack_trace();
                    panic!(
                        "Signal at {} want {}, got {}", sig_idx,
                        expected_signals[sig_idx],
                        self.signals[sig_idx].unwrap())
                },
            }
        }
    }

    /// Set the signal sig_idx to the value from the top of the stack
    fn set_signal(&mut self, sig_idx: usize) {
        if self.signals[sig_idx].is_some() {
            panic!("Signal already set");
        }
        self.signals[sig_idx] = Some(self.stack.pop().unwrap());
        self.assert_signal(sig_idx);
    }

    fn print_stack(&self) {
        for (i, s) in self.stack.iter().enumerate() {
            let s = if s.is_zero() { String:: from("0") } else { s.to_string() };
            println!("{:04x}: {}", i, s);
        }
    }
    fn print_stack_u32(&self) {
        for (i, s) in self.stack_u32.iter().enumerate() {
            println!("{:04x}: {}", i, s);
        }
    }

    fn print_stack_trace(&self) {
        for frame in self.call_frames.iter().rev() {
            match frame {
                Frame::Component { component, ip, .. } => {
                    let component = component.borrow();
                    let template_id = component.template_id;
                    let line_no = self.templates[template_id].line_numbers[*ip];
                    let tmpl_name = self.templates[template_id].name.clone();
                    println!("Component: {}:{}", tmpl_name, line_no);
                }
                Frame::Function { function, ip, .. } => {
                    let line_no = function.line_numbers[*ip];
                    println!("Function: {}:{}", function.name, line_no);
                }
            }
        }
    }
}

#[repr(u8)]
#[derive(Debug, Clone)]
enum InputStatus {
    Last    = 0,
    NoLast  = 1,
    Unknown = 2,
}

impl Display for InputStatus {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let str = match self {
            InputStatus::Last => "LAST".to_string(),
            InputStatus::NoLast => "NO_LAST".to_string(),
            InputStatus::Unknown => "UNKNOWN".to_string(),
        };
        write!(f, "{}", str)
    }
}

impl TryFrom<u8> for InputStatus {
    type Error = ();

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            0 => Ok(InputStatus::Last),
            1 => Ok(InputStatus::NoLast),
            2 => Ok(InputStatus::Unknown),
            _ => Err(()),
        }
    }
}

impl From<&StatusInput> for InputStatus {
    fn from(status: &StatusInput) -> Self {
        match status {
            StatusInput::Last => InputStatus::Last,
            StatusInput::NoLast => InputStatus::NoLast,
            StatusInput::Unknown => InputStatus::Unknown,
        }
    }
}

impl Into<u8> for InputStatus {
    fn into(self) -> u8 {
        self as u8
    }
}

#[repr(u8)]
#[derive(Debug)]
enum OpCode {
    NoOp = 0,
    GetConstant8   =  1, // pushes the value of a constant to the stack. Address of the constant is u64 little endian
    Push8          =  2, // pushes the value of the following 4 bytes as a little endian u64 to the stack
    Push4          =  3, // pushes the value of the following 4 bytes as a little endian u64 to the stack_u32
    GetVariable4   =  4,
    // Put variables to the stack
    // arguments:          variables number as u32 to put on stack
    // required stack_u32: variable index
    GetVariable    =  5,
    SetVariable4   =  6,
    // Set variables from the stack
    // arguments:          variables number u32
    // required stack_u32: variable index
    // required stack:     values to store equal to variables number from arguments
    SetVariable    =  7,
    // Put signals to the stack
    // arguments: signal index u32, signals number u32
    GetSelfSignal4 =  8,
    // Put signals to the stack
    // arguments:          signals number u32
    // required stack_u32: signal index
    GetSelfSignal  =  9,
    SetSelfSignal4 = 10,
    SetSelfSignal  = 11,
    // Put subcomponent signals to the stack
    // arguments:
    // - signals number u32;
    // - flags
    //   - 7th bit is set when it is a mapped signal index
    // - [optional: if flags' 7th bit is set] indexes number u32
    // - [optional: if flags' 7th bit is set] signal code u32
    // required stack_u32:
    // - if signal is not mapped:
    //   - first signal index;
    //   - subcomponent index
    // - if signal mapped:
    //   - mapped indexes (number of indexes passed from the arguments);
    //   - subcomponent index
    GetSubSignal   = 13,
    // arguments:
    // - signals number u32;
    // - flags
    //   - 0-1 bits is an InputStatus;
    //   - 7th bit is set when it is a mapped signal index
    // - [optional: if flags' 7th bit is set] indexes number u32
    // - [optional: if flags' 7th bit is set] signal code u32
    // required stack: values to store (equal to signals number)
    // required stack_u32:
    // - if signal is not mapped:
    //   - first signal index;
    //   - subcomponent index
    // - if signal mapped:
    //   - mapped indexes (number of indexes passed from the arguments);
    //   - subcomponent index
    SetSubSignal   = 14,
    JumpIfFalse    = 15, // Jump to the offset i32 if the value on the top of the stack is false
    Jump           = 16, // Jump to the offset i32
    OpMul          = 17,
    OpDiv          = 18,
    OpAdd          = 19,
    OpSub          = 20,
    OpIntDiv       = 21,
    OpMod          = 22,
    OpShL          = 23,
    OpShR          = 24,
    OpLtE          = 25,
    OpGtE          = 26,
    OpLt           = 27,
    OpGt           = 28,
    OpEq           = 29,
    OpNe           = 30,
    OpBoolAnd      = 31,
    OpBitOr        = 32,
    OpBitAnd       = 33,
    OpBitXor       = 34,
    OpNeg          = 35,
    OpToAddr       = 36,
    OpMulAddr      = 37,
    OpAddAddr      = 38,
    CmpCall        = 39,
    FnCall         = 40,
    FnReturn       = 41,
    // TODO: Assert should accept an index of the string to print
    Assert         = 42,
}

#[derive(Debug)]
enum CompilationError {
    ValueTooLarge,
    NotAnExpression(String),
}

enum U32OrExpression {
    U32(u32),
    BigInt(Fr),
    Expression,
}

fn u32_or_expression(inst: &InstructionPointer, constants: &[Fr]) -> Result<U32OrExpression, CompilationError> {

    match **inst {
        Instruction::Value(ref value) => {
            match value.parse_as {
                ValueType::U32 => {
                    // maybe remove this
                    // if value.value > u32::MAX as usize {
                    //     return Ok(U32OrExpression::Expression);
                    // }
                    let v: u32 = value.value.try_into().expect("value is too large for stack_u32");
                    Ok(U32OrExpression::U32(v))
                },
                ValueType::BigInt => {
                    return Ok(U32OrExpression::BigInt(constants[value.value]));
                },
            }
        }
        Instruction::Load(_) => Ok(U32OrExpression::Expression),
        Instruction::Compute(ref compute_bucket) => {

            let two_op_fn = |op: Operation| -> Result<U32OrExpression, CompilationError> {
                assert_eq!(2, compute_bucket.stack.len());
                let a = match u32_or_expression(&compute_bucket.stack[0], constants)? {
                    U32OrExpression::U32(v) => panic!("expected BigInt value"),
                    U32OrExpression::BigInt(v) => v,
                    U32OrExpression::Expression => { return Ok(U32OrExpression::Expression) }
                };
                let b = match u32_or_expression(&compute_bucket.stack[1], constants)? {
                    U32OrExpression::U32(v) => panic!("expected BigInt value"),
                    U32OrExpression::BigInt(v) => v,
                    U32OrExpression::Expression => { return Ok(U32OrExpression::Expression) }
                };
                Ok(U32OrExpression::BigInt(op.eval_fr(a, b)))
            };

            match compute_bucket.op {
                OperatorType::Mul => two_op_fn(Operation::Mul),
                OperatorType::Div => {todo!()}
                OperatorType::Add => two_op_fn(Operation::Add),
                OperatorType::Sub => two_op_fn(Operation::Sub),
                OperatorType::Pow => {todo!()}
                OperatorType::IntDiv => {todo!()}
                OperatorType::Mod => two_op_fn(Operation::Mod),
                OperatorType::ShiftL => {todo!()}
                OperatorType::ShiftR => {todo!()}
                OperatorType::LesserEq => {todo!()}
                OperatorType::GreaterEq => {todo!()}
                OperatorType::Lesser => {todo!()}
                OperatorType::Greater => {todo!()}
                OperatorType::Eq(_) => {todo!()}
                OperatorType::NotEq => {todo!()}
                OperatorType::BoolOr => {todo!()}
                OperatorType::BoolAnd => {todo!()}
                OperatorType::BitOr => {todo!()}
                OperatorType::BitAnd => {todo!()}
                OperatorType::BitXor => {todo!()}
                OperatorType::PrefixSub => {todo!()}
                OperatorType::BoolNot => {todo!()}
                OperatorType::Complement => {todo!()}
                OperatorType::ToAddress => {
                    assert_eq!(1, compute_bucket.stack.len());
                    match u32_or_expression(&compute_bucket.stack[0], constants)? {
                        U32OrExpression::U32(v) => panic!("expected big integer value"),
                        U32OrExpression::BigInt(v) => {
                            let v = bigint_to_u64(v.into_bigint())
                                .expect("value is too large for stack_u32");
                            let v: u32 = v.try_into()
                                .expect("value is too large for stack_u32");
                            Ok(U32OrExpression::U32(v))
                        },
                        U32OrExpression::Expression => Ok(U32OrExpression::Expression)
                    }
                }
                OperatorType::MulAddress => {
                    assert_eq!(2, compute_bucket.stack.len());
                    let a = match u32_or_expression(&compute_bucket.stack[0], constants)? {
                        U32OrExpression::U32(v) => v,
                        U32OrExpression::BigInt(v) => panic!("expected u32 value"),
                        U32OrExpression::Expression => { return Ok(U32OrExpression::Expression) }
                    };
                    let b = match u32_or_expression(&compute_bucket.stack[1], constants)? {
                        U32OrExpression::U32(v) => v,
                        U32OrExpression::BigInt(v) => panic!("expected u32 value"),
                        U32OrExpression::Expression => { return Ok(U32OrExpression::Expression) }
                    };
                    let (v, overflow) = a.overflowing_mul(b);
                    if overflow {
                        panic!("value is too large for stack_u32");
                    }
                    Ok(U32OrExpression::U32(v))
                }
                OperatorType::AddAddress => {
                    assert_eq!(2, compute_bucket.stack.len());
                    let a = match u32_or_expression(&compute_bucket.stack[0], constants)? {
                        U32OrExpression::U32(v) => v,
                        U32OrExpression::BigInt(v) => panic!("expected u32 value"),
                        U32OrExpression::Expression => { return Ok(U32OrExpression::Expression) }
                    };
                    let b = match u32_or_expression(&compute_bucket.stack[1], constants)? {
                        U32OrExpression::U32(v) => v,
                        U32OrExpression::BigInt(v) => panic!("expected u32 value"),
                        U32OrExpression::Expression => { return Ok(U32OrExpression::Expression) }
                    };
                    let (v, overflow) = a.overflowing_add(b);
                    if overflow {
                        panic!("value is too large for stack_u32");
                    }
                    Ok(U32OrExpression::U32(v))
                }
            }
        },
        _ => {
            Err(CompilationError::NotAnExpression(inst.to_string()))
        }
    }
}

fn parse_args() -> Args {
    let args: Vec<String> = env::args().collect();
    let mut i = 1;
    let mut circuit_file: Option<String> = None;
    let mut graph_file: Option<String> = None;
    let mut link_libraries: Vec<PathBuf> = Vec::new();
    let mut inputs_file: Option<String> = None;
    let mut witness_file: Option<String> = None;
    let mut print_debug = false;
    let mut expected_signals: Option<Vec<Fr>> = None;

    let usage = |err_msg: &str| -> String {
        eprintln!("{}", err_msg);
        eprintln!("Usage: {} <circuit_file> <graph_file> [-l <link_library>]* [-i <inputs_file.json>] [-print-unoptimized] [-v] [-wtns <output.wtns]", args[0]);
        std::process::exit(1);
    };

    while i < args.len() {
        if args[i] == "-l" {
            i += 1;
            if i >= args.len() {
                usage("missing argument for -l");
            }
            link_libraries.push(args[i].clone().into());
        } else if args[i].starts_with("-l") {
            link_libraries.push(args[i][2..].to_string().into())
        } else if args[i] == "-wtns" {
            i += 1;
            if i >= args.len() {
                usage("missing argument for -wtns");
            }
            if let None = witness_file {
                witness_file = Some(args[i].clone());
            } else {
                usage("multiple witness files");
            }
        } else if args[i] == "-i" {
            i += 1;
            if i >= args.len() {
                usage("missing argument for -i");
            }
            if let None = inputs_file {
                inputs_file = Some(args[i].clone());
            } else {
                usage("multiple inputs files");
            }
        } else if args[i].starts_with("-i") {
            if let None = inputs_file {
                inputs_file = Some(args[i][2..].to_string());
            } else {
                usage("multiple inputs files");
            }
        } else if args[i] == "-v" {
            print_debug = true;
        } else if args[i] == "-expected-signals" {
            i += 1;
            if i >= args.len() {
                usage("missing argument for -expected-signals");
            }
            expected_signals = Some(load_signals_txt(&args[i]));
        } else if args[i].starts_with("-") {
            let message = format!("unknown argument: {}", args[i]);
            usage(&message);
        } else if let None = circuit_file {
            circuit_file = Some(args[i].clone());
        } else if let None = graph_file {
            graph_file = Some(args[i].clone());
        } else {
            usage(format!("unexpected argument: {}", args[i]).as_str());
        }
        i += 1;
    };

    Args {
        circuit_file: circuit_file.unwrap_or_else(|| { usage("missing circuit file") }),
        inputs_file,
        graph_file: graph_file.unwrap_or_else(|| { usage("missing graph file") }),
        link_libraries,
        print_debug,
        witness_file,
        expected_signals,
    }
}


fn load_signals_txt(file_name: &str) -> Vec<Fr> {
    let content = fs::read_to_string(file_name)
        .expect("failed to read signals file");
    let mut signals = Vec::new();
    for line in content.lines() {
        let signal = Fr::from_str(line)
            .expect("failed to parse signal");
        signals.push(signal);
    }
    signals
}


fn main() {
    let args = parse_args();

    if let Some(ref expected_signals) = args.expected_signals {
        println!("Expected signals:");
        for (i, s) in expected_signals.iter().enumerate() {
            println!("{}: {}", i, s);
        }
    }

    let version = "2.1.9";

    let parser_result = parser::run_parser(
        args.circuit_file.clone(), version, args.link_libraries.clone());

    let mut program_archive = match parser_result {
        Err((file_library, report_collection)) => {
            Report::print_reports(&report_collection, &file_library);
            panic!("Parser error");
        }
        Ok((program_archive, warnings)) => {
            if !warnings.is_empty() {
                println!("Parser warnings:");
                for warning in warnings {
                    println!("{}", warning.get_message());
                }
            }
            program_archive
        }
    };

    match check_types(&mut program_archive) {
        Err(errs) => {
            println!("Type errors:");
            for err in errs {
                println!("{}", err.get_message());
            }
            std::process::exit(1);
        }
        Ok(warns) => {
            if !warns.is_empty() {
                println!("Type warnings:");
                for warn in warns {
                    println!("{}", warn.get_message());
                }
            }
        }
    }

    let build_config = BuildConfig {
        no_rounds: usize::MAX,
        flag_json_sub: false,
        json_substitutions: String::new(),
        flag_s: false,
        flag_f: false,
        flag_p: false,
        flag_verbose: false,
        flag_old_heuristics: false,
        inspect_constraints: false,
        prime: String::from("bn128"),
    };

    let (_, vcp) = build_circuit(program_archive, build_config).unwrap();

    let main_template_id = vcp.main_id;

    let witness_list = vcp.get_witness_list().clone();

    let circuit = run_compiler(
        vcp,
        Config {
            debug_output: true,
            produce_input_log: true,
            wat_flag: false,
        },
        version)
        .unwrap();
    println!("prime: {}", circuit.c_producer.prime);
    println!("prime_str: {}", circuit.c_producer.prime_str);
    println!("templates len: {}", circuit.templates.len());
    println!("functions len: {}", circuit.functions.len());
    println!("main header: {}", circuit.c_producer.main_header);

    // let (input_signals, input_signal_values): (InputSignalsInfo, Vec<U256>) = init_input_signals(
    //     &circuit, &mut nodes, &mut signal_node_idx, args.inputs_file);

    // assert that template id is equal to index in templates list
    for (i, t) in circuit.templates.iter().enumerate() {
        assert_eq!(i, t.id);
        // if args.print_debug {
        //     println!("Template #{}: {}", i, t.name);
        // }
    }

    let constants = get_constants(&circuit);
    let main_component_signal_start = 1usize;
    let start = Instant::now();
    let (compiled_templates, compiled_functions) =
        compile(&circuit.templates, &circuit.functions, &constants);


    // for (i, t) in compiled_templates.iter().enumerate() {
    //     println!("Compiled template #{}: {}", i, t.name);
    //     disassemble(
    //         &t.code, &t.line_numbers, t.name.as_str(), &compiled_functions);
    // }
    //
    // for (i, t) in compiled_functions.iter().enumerate() {
    //     println!("Compiled function #{}: {}", i, t.name);
    //     disassemble(&t.code, &t.line_numbers, &t.name, &compiled_functions);
    // }

    println!("Compilation time: {:?}", start.elapsed());

    if let Some(input_file) = args.inputs_file {

        let main_component = build_component(
            &compiled_templates, &circuit.templates, main_template_id,
            main_component_signal_start);
        let main_component = Rc::new(RefCell::new(main_component));

        let sigs_num = circuit.c_producer.get_total_number_of_signals();

        if let Some(ref expected_signals) = args.expected_signals {
            assert_eq!(expected_signals.len(), sigs_num);
        }

        let mut signals = Vec::new();
        signals.resize(sigs_num, None);
        init_input_signals(&circuit, input_file, &mut signals);

        println!("Run VM");
        let start = Instant::now();
        let io_map = circuit.c_producer.get_io_map();
        execute(
            main_component, &compiled_templates, &compiled_functions,
            &constants, &mut signals, io_map, args.expected_signals.as_ref());

        println!("Execution time: {:?}", start.elapsed());

        if let Some(witness_file) = args.witness_file {
            let mut witness = Vec::with_capacity(witness_list.len());
            for (i, w) in witness_list.iter().enumerate() {
                // println!("w: {}",
                //          signals[*w]
                //              .expect(
                //                  format!("signal at {} is not set", i).as_str())
                //              .to_string());
                witness.push(signals[*w].unwrap());
            }

            let wtns_bytes = wtns_from_witness(witness);

            {
                let mut f = File::create(witness_file).unwrap();
                f.write_all(&wtns_bytes).unwrap();
            }
        } else {
            println!("Witness file is not set. Witness was calculated but not saved.")
        }
    }
}

fn build_component(
    compiled_templates: &[Template], templates: &[TemplateCode],
    template_id: usize, signals_start: usize) -> Component {

    let mut subcomponents = Vec::with_capacity(
        compiled_templates[template_id].components.len());

    for c in &compiled_templates[template_id].components {
        let mut cmp_signal_offset = c.signal_offset;

        for _ in c.sub_cmp_idx..c.sub_cmp_idx+c.number_of_cmp {
            let subcomponent = build_component(
                compiled_templates, templates, c.template_id,
                signals_start + cmp_signal_offset);
            subcomponents.push(Rc::new(RefCell::new(subcomponent)));
            cmp_signal_offset += c.signal_offset_jump;
        }
    }

    Component {
        vars: vec![None; templates[template_id].var_stack_depth],
        signals_start,
        template_id,
        subcomponents,
        number_of_inputs: templates[template_id].number_of_inputs,
    }
}

fn get_constants(circuit: &Circuit) -> Vec<Fr> {
    let mut constants = Vec::new();
    for c in &circuit.c_producer.field_tracking {
        constants.push(Fr::from_str(c.as_str()).unwrap());
    }
    constants
}


fn read_instruction(code: &[u8], ip: usize) -> OpCode {
    unsafe { std::mem::transmute::<u8, OpCode>(code[ip]) }
}

fn read_usize(code: &[u8], ip: usize) -> usize {
    usize::from_le_bytes(code[ip..ip+size_of::<usize>()].try_into().unwrap())
}

fn read_u32(code: &[u8], ip: usize) -> u32 {
    u32::from_le_bytes(code[ip..ip+size_of::<u32>()].try_into().unwrap())
}

fn read_i32(code: &[u8], ip: usize) -> i32 {
    i32::from_le_bytes(code[ip..ip+size_of::<i32>()].try_into().unwrap())
}

enum Frame<'a, 'b> {
    Component {
        ip: usize,
        code: &'a [u8],
        component: Rc<RefCell<Component>>,
    },
    Function {
        ip: usize,
        vars: Vec<Option<Fr>>,
        code: &'a [u8],
        function: &'b Function,
        return_num: usize,
    }
}

impl Frame<'_, '_> {
    fn new_component(component: Rc<RefCell<Component>>, templates: &[Template]) -> Frame {
        let template_id = component.borrow().template_id;
        Frame::Component {
            ip: 0,
            code: &templates[template_id].code,
            component,
        }
    }

    fn new_function(
        fn_idx: usize, functions: &[Function], args_num: usize,
        return_num: usize) -> Frame {

        Frame::Function {
            ip: 0,
            vars: Vec::with_capacity(args_num),
            code: &functions[fn_idx].code,
            function: &functions[fn_idx],
            return_num,
        }
    }
}

fn calc_mapped_signal_idx(
    template_id: usize, io_map: &TemplateInstanceIOMap,
    signal_code: u32, indexes: &[u32]) -> u32 {

    let signals = io_map.get(&template_id).expect(format!("template not found: {}", template_id).as_str());
    let def = &signals[signal_code as usize];
    let mut sig_idx: u32 = def.offset.try_into()
        .expect("Signal index is too large");

    if indexes.is_empty() {
        return sig_idx;
    }

    assert_eq!(def.lengths.len(), indexes.len());

    // Compute strides
    let mut strides = vec![1u32; def.lengths.len()];
    for i in (0..def.lengths.len() - 1).rev() {
        let ln: u32 = def.lengths[i+1].try_into().expect("Length is too large");
        let (s, overflowed) = strides[i+1].overflowing_mul(ln);
        if overflowed {
            panic!("Stride is too large");
        }
        strides[i] = s;
    }

    for (i, idx_ip) in indexes.iter().enumerate() {
        let (x, mut overflow) = idx_ip.overflowing_mul(strides[i]);
        if overflow {
            panic!("Index is too large");
        }

        (sig_idx, overflow) = sig_idx.overflowing_add(x);
        if overflow {
            panic!("Signal index is too large");
        }
    };

    sig_idx
}

fn execute(
    component: Rc<RefCell<Component>>, templates: &Vec<Template>,
    functions: &[Function], constants: &Vec<Fr>,
    signals: &mut [Option<Fr>], io_map: &TemplateInstanceIOMap,
    expected_signals: Option<&Vec<Fr>>) {

    let mut vm = VM {
        templates,
        signals,
        constants,
        stack: vec![],
        stack_u32: vec![],
        expected_signals,
        call_frames: vec![],
    };

    vm.call_frames.push(Frame::new_component(component.clone(), templates));

    let mut ip = 0usize;
    let mut code: &[u8];
    let mut template_id: usize;
    let mut signals_start: usize;
    {
        match vm.call_frames.last().unwrap() {
            Frame::Component { code: code_local, component, .. } => {
                code = *code_local;
                template_id = component.borrow().template_id;
                signals_start = component.borrow().signals_start;
            }
            Frame::Function { .. } => {
                panic!("Function frame on top of the call stack");
            }
        }
    }


    'main: loop {
        while ip == code.len() {
            vm.call_frames.pop();
            if vm.call_frames.is_empty() {
                break 'main;
            }

            let last_frame = vm.call_frames.last().unwrap();
            match last_frame {
                Frame::Component { ip: ip_local, component, .. } => {
                    ip = *ip_local;
                    let component = component.borrow();
                    template_id = component.template_id;
                    code = &templates[template_id].code;
                    signals_start = component.signals_start;
                }
                Frame::Function { .. } => {
                    panic!("Suppose to exit from the function with the Return statement");
                }
            }
        }

        #[cfg(feature = "print_opcode")]
        {
            let (line_numbers, name) = match vm.call_frames.last().unwrap() {
                Frame::Component { .. } => {
                    (&templates[template_id].line_numbers, templates[template_id].name.as_str())
                }
                Frame::Function { function, .. } => {
                    (&(*function).line_numbers, function.name.as_str())
                }
            };
            disassemble_instruction(code, line_numbers, ip, name, functions);
        }

        let op = read_instruction(code, ip);
        ip += 1;

        match op {
            OpCode::NoOp => {
                // do nothing
            }
            OpCode::SetSelfSignal4 => {
                let sig_offset = read_u32(code, ip);
                ip += size_of::<u32>();

                let sigs_number = read_u32(code, ip);
                ip += size_of::<u32>();

                let sig_offset = usize::try_from(sig_offset)
                    .expect("Signal index is too large");

                let (sig_start, overflowed) = signals_start
                    .overflowing_add(sig_offset);

                if overflowed {
                    panic!("Signal index is too large");
                }

                let (sig_end, overflowed) = sig_start
                    .overflowing_add(sigs_number as usize);

                if overflowed || sig_end > vm.signals.len() {
                    panic!("Signal index is too large");
                }

                for sig_idx in (sig_start..sig_end).rev() {
                    vm.set_signal(sig_idx);
                }
            }
            OpCode::SetSelfSignal => {
                let cmp_signal_offset =
                    vm.stack_u32.pop().unwrap() as usize;

                let sigs_number = read_u32(code, ip);
                ip += size_of::<u32>();

                let (sig_start, overflowed) = signals_start
                    .overflowing_add(cmp_signal_offset);
                if overflowed {
                    panic!("Signal index is too large");
                }

                let (sig_end, overflowed) =
                    sig_start.overflowing_add(sigs_number as usize);
                if overflowed || sig_end > vm.signals.len() {
                    panic!("Signal index is too large");
                }

                for sig_idx in (sig_start..sig_end).rev() {
                    vm.set_signal(sig_idx);
                }
            }
            OpCode::GetConstant8 => {
                let const_idx = read_usize(code, ip);
                ip += size_of::<usize>();
                vm.stack.push(vm.constants[const_idx]);
            }
            OpCode::Push8 => {
                let val = read_usize(code, ip);
                ip += size_of::<usize>();
                let val = Fr::from(val as u64);
                vm.stack.push(val);
            }
            OpCode::Push4 => {
                let val = read_u32(code, ip);
                ip += size_of::<u32>();
                vm.stack_u32.push(val);
            }
            OpCode::GetVariable4 => {
                let var_idx = read_u32(code, ip);
                ip += size_of::<u32>();

                let var_start = var_idx as usize;

                let vars_number = read_u32(code, ip);
                ip += size_of::<u32>();

                let (var_end, overflow) = var_start.overflowing_add(vars_number as usize);
                if overflow {
                    panic!("Variable index is too large");
                }

                let last_frame = vm.call_frames.last().unwrap();
                let vars = match last_frame {
                    Frame::Component { component, .. } => {
                        &mut component.borrow_mut().vars
                    }
                    Frame::Function { vars, .. } => {
                        vars
                    }
                };

                if vars.len() < var_end {
                    panic!("Variable is not set as {}", var_end-1);
                }

                for var_idx in var_start..var_end {
                    if vars[var_idx].is_none() {
                        panic!("Variable not set");
                    }
                    vm.stack.push(vars[var_idx].unwrap());
                }
            }
            OpCode::GetVariable => {
                let var_idx = vm.stack_u32.pop().unwrap() as usize;

                let vars_number = read_u32(code, ip) as usize;
                ip += size_of::<u32>();

                let last_frame = vm.call_frames.last().unwrap();
                let vars = match last_frame {
                    Frame::Component { component, .. } => {
                        &mut component.borrow_mut().vars
                    }
                    Frame::Function { vars, .. } => {
                        vars
                    }
                };

                if var_idx + vars_number > vars.len() {
                    vm.print_stack_trace();
                    panic!(
                        "Variable not set. Total variables length: {}, var_idx: {}, vars_number: {}",
                        vars.len(), var_idx, vars_number);
                }

                for i in var_idx..var_idx+vars_number {
                    if vars[i].is_none() {
                        panic!("Variable not set");
                    }
                    vm.stack.push(vars[i].unwrap());
                }
            }
            OpCode::SetVariable4 => {
                let var_idx = read_u32(code, ip);
                ip += size_of::<u32>();

                let var_start = usize::try_from(var_idx).unwrap();

                let vars_number = read_u32(code, ip);
                ip += size_of::<u32>();

                if vars_number as usize > vm.stack.len() {
                    panic!("Number of variables is greater the stack depth");
                }

                let (var_end, overflow) =
                    var_start.overflowing_add(vars_number as usize);
                if overflow {
                    panic!("Variable index is too large");
                }

                let last_frame = vm.call_frames.last_mut().unwrap();
                let vars: &mut Vec<Option<Fr>> = match last_frame {
                    Frame::Component { component, .. } => {
                        &mut component.borrow_mut().vars
                    }
                    Frame::Function { ref mut vars, .. } => {
                        vars
                    }
                };

                if vars.len() < var_end {
                    vars.resize(var_end, None);
                }

                for var_idx in (var_start..var_end).rev() {
                    vars[var_idx] = Some(vm.stack.pop().unwrap());
                }
            }
            OpCode::SetVariable => {
                let var_start = vm.stack_u32.pop().unwrap() as usize;

                let vars_number = read_u32(code, ip);
                ip += size_of::<u32>();

                if vars_number as usize > vm.stack.len() {
                    panic!("Number of variables is greater the stack depth");
                }

                let (var_end, overflow) =
                    var_start.overflowing_add(vars_number as usize);
                if overflow {
                    panic!("Variable index is too large");
                }

                let mut last_frame = vm.call_frames.last_mut().unwrap();
                let vars: &mut Vec<Option<Fr>> = match last_frame {
                    Frame::Component { component, .. } => {
                        &mut component.borrow_mut().vars
                    }
                    Frame::Function { ref mut vars, .. } => {
                        vars
                    }
                };

                if vars.len() < var_end {
                    vars.resize(var_end, None);
                }

                for var_idx in (var_start..var_end).rev() {
                    vars[var_idx] = Some(vm.stack.pop().unwrap());
                }
            }
            OpCode::GetSubSignal => {
                let sigs_number = read_u32(code, ip);
                ip += size_of::<u32>();

                let flags = code[ip];
                ip += 1;
                let is_mapped_signal_idx = flags & 0b1000_0000 != 0;

                let cmp_idx = vm.stack_u32.pop().unwrap();

                let cmp = if let Frame::Component { component, .. } = vm.call_frames.last().unwrap() {
                    component
                } else {
                    panic!("GetSubSignal instruction inside a function");
                };

                let sig_idx = if is_mapped_signal_idx {
                    let indexes_number = read_u32(code, ip);
                    ip += size_of::<u32>();

                    let signal_code = read_u32(code, ip);
                    ip += size_of::<u32>();

                    let indexes = vm.stack_u32.split_off(indexes_number as usize);

                    let subcmp_template_id = cmp.borrow()
                        .subcomponents[cmp_idx as usize].borrow()
                        .template_id;

                    calc_mapped_signal_idx(subcmp_template_id, io_map, signal_code, &indexes)
                } else {
                    vm.stack_u32.pop().unwrap()
                };

                let subcmp_signals_start = cmp.borrow().subcomponents[cmp_idx as usize].borrow().signals_start;

                let (sig_start, overflowed) =
                    subcmp_signals_start.overflowing_add(sig_idx as usize);

                if overflowed {
                    panic!("Subcomponent signal index is too large");
                }

                let (sig_end, overflowed) = sig_start
                    .overflowing_add(sigs_number as usize);

                if overflowed || sig_end > vm.signals.len() {
                    panic!("Subcomponent signal index is too large");
                }

                for sig_idx in sig_start..sig_end {
                    vm.stack.push(vm.signals[sig_idx].expect("Subcomponent signal is not set"));
                }
            }
            OpCode::SetSubSignal => {
                let sigs_number = read_u32(code, ip);
                ip += size_of::<u32>();

                let flags = code[ip];
                ip += 1;

                let (input_status, is_mapped_signal_idx) = unpack_flags(flags);

                let cmp_idx = vm.stack_u32.pop().unwrap();

                let cmp = match vm.call_frames.last().unwrap() {
                    Frame::Component { component, .. } => {
                        component.clone()
                    }
                    Frame::Function { .. } => {
                        panic!("SetSubSignal instruction inside a function");
                    }
                };

                let sig_idx = if is_mapped_signal_idx {
                    let indexes_number = read_u32(code, ip);
                    ip += size_of::<u32>();

                    let signal_code = read_u32(code, ip);
                    ip += size_of::<u32>();

                    let indexes = vm.stack_u32.split_off(indexes_number as usize);

                    let subcmp_template_id = cmp.borrow()
                            .subcomponents[cmp_idx as usize].borrow()
                            .template_id;

                    calc_mapped_signal_idx(subcmp_template_id, io_map, signal_code, &indexes)
                } else {
                    vm.stack_u32.pop().unwrap()
                };

                if vm.stack.len() < sigs_number as usize {
                    panic!("Number of signals is greater than the stack depth");
                }

                let should_call_cmp = {
                    let cmp = cmp.borrow();
                    let mut subcmp = cmp
                        .subcomponents[cmp_idx as usize].borrow_mut();

                    let (sigs_start, overflowed) =
                        subcmp.signals_start.overflowing_add(sig_idx as usize);

                    if overflowed || sigs_start >= vm.signals.len() {
                        panic!("Subcomponent signal start index is too large");
                    }

                    let (sigs_end, overflowed) =
                        sigs_start.overflowing_add(sigs_number as usize);

                    if overflowed || sigs_end > vm.signals.len() {
                        panic!("Subcomponent signal end index is too large");
                    }

                    for sig_idx in (sigs_start..sigs_end).rev() {
                        vm.set_signal(sig_idx);
                    }

                    subcmp.number_of_inputs -= sigs_number as usize;

                    let should_call_cmp = match input_status {
                        InputStatus::Last => true,
                        InputStatus::NoLast => false,
                        InputStatus::Unknown => subcmp.number_of_inputs == 0,
                    };

                    should_call_cmp
                };

                if should_call_cmp {
                    match vm.call_frames.last_mut().unwrap() {
                        Frame::Component { ip: ip_local, .. } => {
                            *ip_local = ip;
                        }
                        Frame::Function { .. } => {
                            panic!("Does not expect to call a subcomponent from inside the function");
                        }
                    }

                    vm.call_frames.push(
                        Frame::new_component(
                            cmp.borrow().subcomponents[cmp_idx as usize].clone(),
                            templates));

                    ip = 0usize;
                    match vm.call_frames.last().unwrap() {
                        Frame::Component { code: code_local, component,  .. } => {
                            code = *code_local;
                            template_id = component.borrow().template_id;
                            signals_start = component.borrow().signals_start;
                        }
                        Frame::Function { .. } => {
                            panic!("No way, we just added a component frame");
                        }
                    }
                }
            }
            OpCode::JumpIfFalse => {
                let offset = read_i32(code, ip);
                ip += size_of::<i32>();

                let c = vm.stack.pop().unwrap();
                if c.is_zero() {
                    if offset < 0 {
                        ip = ip - offset.abs() as usize;
                    } else {
                        ip += offset as usize;
                    }
                }
            }
            OpCode::Jump => {
                let offset = read_i32(code, ip);
                ip += size_of::<i32>();
                if offset < 0 {
                    ip = ip - offset.abs() as usize;
                } else {
                    ip += offset as usize;
                }
            }
            OpCode::OpMul => {
                let b = vm.stack.pop().unwrap();
                let a = vm.stack.pop().unwrap();
                vm.stack.push(a * b);
            }
            OpCode::OpDiv => {
                let b = vm.stack.pop().unwrap();
                let a = vm.stack.pop().unwrap();
                if b.is_zero() {
                    panic!("Division by zero");
                }
                vm.stack.push(a / b);
            }
            OpCode::OpAdd => {
                let b = vm.stack.pop().unwrap();
                let a = vm.stack.pop().unwrap();
                vm.stack.push(a + b);
            }
            OpCode::OpSub => {
                let b = vm.stack.pop().unwrap();
                let a = vm.stack.pop().unwrap();
                vm.stack.push(Operation::Sub.eval_fr(a, b));
            }
            OpCode::OpIntDiv => {
                let b = vm.stack.pop().unwrap();
                let a = vm.stack.pop().unwrap();
                vm.stack.push(Operation::Idiv.eval_fr(a, b));
            }
            OpCode::OpMod => {
                let b = vm.stack.pop().unwrap();
                let a = vm.stack.pop().unwrap();
                vm.stack.push(Operation::Mod.eval_fr(a, b));
            }
            OpCode::OpShL => {
                let b = vm.stack.pop().unwrap();
                let a = vm.stack.pop().unwrap();
                vm.stack.push(Operation::Shl.eval_fr(a, b));
            }
            OpCode::OpShR => {
                let b = vm.stack.pop().unwrap();
                let a = vm.stack.pop().unwrap();
                vm.stack.push(Operation::Shr.eval_fr(a, b));
            }
            OpCode::OpLtE => {
                let b = vm.stack.pop().unwrap();
                let a = vm.stack.pop().unwrap();
                vm.stack.push(Operation::Leq.eval_fr(a, b));
            }
            OpCode::OpGtE => {
                let b = vm.stack.pop().unwrap();
                let a = vm.stack.pop().unwrap();
                vm.stack.push(Operation::Geq.eval_fr(a, b));
            }
            OpCode::OpLt => {
                let b = vm.stack.pop().unwrap();
                let a = vm.stack.pop().unwrap();
                vm.stack.push(u_lt(&a, &b));
            }
            OpCode::OpGt => {
                let b = vm.stack.pop().unwrap();
                let a = vm.stack.pop().unwrap();
                vm.stack.push(Operation::Gt.eval_fr(a, b));
            }
            OpCode::OpEq => {
                let b = vm.stack.pop().unwrap();
                let a = vm.stack.pop().unwrap();
                vm.stack.push(Operation::Eq.eval_fr(a, b));
            }
            OpCode::OpNe => {
                let b = vm.stack.pop().unwrap();
                let a = vm.stack.pop().unwrap();
                vm.stack.push(match a.cmp(&b) {
                    Ordering::Equal => Fr::zero(),
                    _ => Fr::one(),
                });
            }
            OpCode::OpBoolAnd => {
                let b = vm.stack.pop().unwrap();
                let a = vm.stack.pop().unwrap();
                vm.stack.push(Operation::Land.eval_fr(a, b));
            }
            OpCode::OpBitOr => {
                let b = vm.stack.pop().unwrap();
                let a = vm.stack.pop().unwrap();
                vm.stack.push(Operation::Bor.eval_fr(a, b));
            }
            OpCode::OpBitAnd => {
                let b = vm.stack.pop().unwrap();
                let a = vm.stack.pop().unwrap();
                vm.stack.push(Operation::Band.eval_fr(a, b));
            }
            OpCode::OpBitXor => {
                let b = vm.stack.pop().unwrap();
                let a = vm.stack.pop().unwrap();
                vm.stack.push(Operation::Bxor.eval_fr(a, b));
            }
            OpCode::OpNeg => {
                let a = vm.stack.pop().unwrap();
                vm.stack.push(UnoOperation::Neg.eval_fr(a));
            }
            OpCode::GetSelfSignal4 => {
                let sig_idx = read_u32(code, ip);
                ip += size_of::<u32>();

                let sigs_number = read_u32(code, ip);
                ip += size_of::<u32>();

                let (sig_start, overflow) = signals_start
                    .overflowing_add(sig_idx as usize);
                if overflow {
                    panic!("Signal index is too large");
                }

                let (sig_end, overflow) = sig_start
                    .overflowing_add(sigs_number as usize);

                if overflow || sig_end > vm.signals.len() {
                    panic!("Signal index is too large");
                }

                for sig_idx in sig_start..sig_end {
                    vm.stack.push(vm.signals[sig_idx].expect("Signal is not set"));
                }
            }
            OpCode::GetSelfSignal => {
                let cmp_signal_offset = vm.stack_u32.pop().unwrap();
                let (sig_start, overflow) =
                    signals_start.overflowing_add(cmp_signal_offset as usize);
                if overflow {
                    panic!(
                        "First signal index is too large: [{} + {}] = {}",
                        signals_start, cmp_signal_offset, sig_start);
                }

                let sigs_num = read_u32(code, ip);
                ip += size_of::<u32>();

                let (sig_end, overflow) = sig_start
                    .overflowing_add(sigs_num as usize);

                if overflow || sig_end > vm.signals.len() {
                    panic!(
                        "Last signal index is too large: [{} + {}] = {}",
                        sig_start, sigs_num, sig_end);
                }

                for sig_idx in sig_start..sig_end {
                    vm.stack.push(vm.signals[sig_idx].expect("Signal is not set"));
                }
            }
            OpCode::OpToAddr => {
                let f = vm.stack.pop().unwrap();
                let f = bigint_to_u64(f.into_bigint())
                    .expect("Value is too large for address");
                let f: u32 = f.try_into()
                    .expect("Value is too large for address");
                vm.stack_u32.push(f);
            }
            OpCode::OpMulAddr => {
                let b = vm.stack_u32.pop().unwrap();
                let a = vm.stack_u32.pop().unwrap();
                let (r, overflow) = a.overflowing_mul(b);
                if overflow {
                    panic!("Address multiplication overflow");
                }
                vm.stack_u32.push(r);
            }
            OpCode::OpAddAddr => {
                let b = vm.stack_u32.pop().unwrap();
                let a = vm.stack_u32.pop().unwrap();
                let (r, overflow) = a.overflowing_add(b);
                if overflow {
                    panic!("Address addition overflow");
                }
                vm.stack_u32.push(r);
            }
            OpCode::CmpCall => {
                let cmp_idx = read_u32(code, ip);
                ip += size_of::<u32>();

                let cmp = match vm.call_frames.last().unwrap() {
                    Frame::Component { component, .. } => {
                        component.clone()
                    }
                    Frame::Function { .. } => {
                        panic!("SetSubSignal instruction inside a function");
                    }
                };

                match vm.call_frames.last_mut().unwrap() {
                    Frame::Component { ip: ip_local, .. } => {
                        *ip_local = ip;
                    }
                    Frame::Function { .. } => {
                        panic!("Does not expect to call a subcomponent from inside the function");
                    }
                }

                vm.call_frames.push(
                    Frame::new_component(
                        cmp.borrow().subcomponents[cmp_idx as usize].clone(),
                        templates));

                ip = 0usize;
                match vm.call_frames.last().unwrap() {
                    Frame::Component { code: code_local, component,  .. } => {
                        code = *code_local;
                        template_id = component.borrow().template_id;
                        signals_start = component.borrow().signals_start;
                    }
                    Frame::Function { .. } => {
                        panic!("No way, we just added a component frame");
                    }
                }
            }
            OpCode::FnCall => {
                let fn_idx = read_u32(code, ip) as usize;
                ip += size_of::<u32>();

                let args_num = read_u32(code, ip) as usize;
                ip += size_of::<u32>();

                let return_num = read_u32(code, ip) as usize;
                ip += size_of::<u32>();

                match vm.call_frames.last_mut().unwrap() {
                    Frame::Component { ip: ip_local, .. } | Frame::Function { ip: ip_local, .. } => {
                        *ip_local = ip;
                    }
                }

                vm.call_frames.push(Frame::new_function(
                    fn_idx, functions, args_num, return_num));

                ip = 0usize;
                match vm.call_frames.last().unwrap() {
                    Frame::Component { code: code_local, component,  .. } => {
                        panic!("No way, we just added a function frame");
                    }
                    Frame::Function { code: code_local, .. } => {
                        code = *code_local;
                        template_id = usize::MAX;
                        signals_start = usize::MAX;
                    }
                }

                if let Frame::Function {vars, ..} = vm.call_frames.last_mut().unwrap() {
                    vars.resize(args_num, None);
                    for i in (0..args_num).rev() {
                        vars[i] = Some(vm.stack.pop().unwrap());
                    }
                } else {
                    panic!("No way, we just added a function frame")
                }
            }
            OpCode::FnReturn => {
                let return_num = read_u32(code, ip) as usize;
                ip += size_of::<u32>();

                match vm.call_frames.last().unwrap() {
                    Frame::Component { .. } => {
                        panic!("Return instruction inside the component");
                    }
                    Frame::Function { return_num: return_num_local, function, .. } => {
                        assert_eq!(
                            *return_num_local, return_num,
                            "Function {} is supposed to return {} values, but actually returned {}",
                            function.name, *return_num_local, return_num);
                    }
                }

                vm.call_frames.pop();
                if vm.call_frames.is_empty() {
                    panic!("We supposed to exit from the function to the component at least")
                }

                let last_frame = vm.call_frames.last().unwrap();
                match last_frame {
                    Frame::Component { ip: ip_local, component, .. } => {
                        ip = *ip_local;
                        let component = component.borrow();
                        template_id = component.template_id;
                        code = &templates[template_id].code;
                        signals_start = component.signals_start;
                    }
                    Frame::Function { ip: ip_local, code: code_local, .. } => {
                        ip = *ip_local;
                        code = *code_local;
                    }
                }
            }
            OpCode::Assert => {
                panic!("Assert instruction");
            }
        }

        #[cfg(feature = "print_opcode")]
        {
            println!("==[ Stack ]==");
            vm.print_stack();
            println!("==[ Stack32 ]==");
            vm.print_stack_u32();
        }
    }
}

fn calc_jump_offset(from: usize, to: usize) -> i32 {
    let from: i64 = from.try_into().expect("Jump from offset is too large");
    let to: i64 = to.try_into().expect("Jump to offset is too large");

    (to - from).try_into().expect("Jump offset is too large")
}

fn emit_jump(code: &mut Vec<u8>, to: usize) {
    code.push(OpCode::Jump as u8);

    let jump_offset_addr = code.len();
    let offset = calc_jump_offset(jump_offset_addr + 4, to);

    code.extend_from_slice(offset.to_le_bytes().as_ref());
}


fn pre_emit_jump_if_false(code: &mut Vec<u8>) -> usize {
    code.push(OpCode::JumpIfFalse as u8);
    for _ in 0..4 { code.push(0xffu8); }
    code.len() - 4
}

fn pre_emit_jump(code: &mut Vec<u8>) -> usize {
    code.push(OpCode::Jump as u8);
    for _ in 0..4 { code.push(0xffu8); }
    code.len() - 4
}

/// We expect the jump offset located at `jump_offset_addr` to be 4 bytes long.
/// The jump offset is calculated as `to - jump_offset_addr - 4`.
fn patch_jump(code: &mut [u8], jump_offset_addr: usize, to: usize) {
    let offset = calc_jump_offset(jump_offset_addr + 4, to);
    code[jump_offset_addr..jump_offset_addr+4].copy_from_slice(offset.to_le_bytes().as_ref());
}

fn store_subsignal(
    code: &mut Vec<u8>, dest: &LocationRule, constants: &[Fr],
    components: &mut Vec<ComponentTmpl>, line_numbers: &mut Vec<usize>,
    line_no: usize, cmp_address: &InstructionPointer,
    input_information: &InputInformation, signals_num: u32) {

    let mut indexes_number = 0u32;
    let mut signal_code = 0u32;
    let is_signal_idx_mapped = match dest {
        LocationRule::Indexed { ref location, .. } => {
            let sig_idx =
                u32_or_expression(location, constants).unwrap();

            match sig_idx {
                U32OrExpression::U32(sig_idx) => {
                    code.push(OpCode::Push4 as u8);
                    line_numbers.push(line_no);

                    code.extend_from_slice(sig_idx.to_le_bytes().as_ref());
                    for _ in 0..4 { line_numbers.push(usize::MAX); }
                }
                U32OrExpression::BigInt(_) => {
                    panic!("Signal index is not u32");
                }
                U32OrExpression::Expression => {
                    expression_u32(
                        location, code, constants, line_numbers,
                        components);
                }
            };

            false
        }
        LocationRule::Mapped { signal_code: ref signal_code_local, ref indexes } => {
            for idx_inst in indexes {
                expression_u32(
                    idx_inst, code, constants, line_numbers,
                    components)
            }

            indexes_number = indexes.len()
                .try_into().expect("Too many indexes");
            signal_code = (*signal_code_local).try_into()
                .expect("Too large signal code");

            true
        }
    };
    let cmp_idx =
        u32_or_expression(cmp_address, constants);
    match cmp_idx {
        Ok(ref cmp_idx) => {
            match cmp_idx {
                U32OrExpression::U32(cmp_idx) => {
                    code.push(OpCode::Push4 as u8);
                    line_numbers.push(line_no);

                    code.extend_from_slice(cmp_idx.to_le_bytes().as_ref());
                    for _ in 0..4 { line_numbers.push(usize::MAX); }
                },
                U32OrExpression::BigInt(_) => {
                    panic!("Component index is not u32");
                },
                U32OrExpression::Expression => {
                    expression_u32(
                        cmp_address, code, constants,
                        line_numbers, components);
                }
            }
        }
        Err(e) => {
            panic!("Error: {:?}", e);
        }
    };


    code.push(OpCode::SetSubSignal as u8);
    line_numbers.push(line_no);

    code.extend_from_slice(signals_num.to_le_bytes().as_ref());
    for _ in 0..4 { line_numbers.push(usize::MAX); }

    let input_status: InputStatus = if let InputInformation::Input{ status } = input_information {
        status.into()
    } else {
        panic!("Can't store signal to non-input subcomponent");
    };
    code.push(mk_flags(input_status, is_signal_idx_mapped));
    line_numbers.push(usize::MAX);

    if is_signal_idx_mapped {
        code.extend_from_slice(indexes_number.to_le_bytes().as_ref());
        for _ in 0..4 { line_numbers.push(usize::MAX); }

        code.extend_from_slice(signal_code.to_le_bytes().as_ref());
        for _ in 0..4 { line_numbers.push(usize::MAX); }
    }
}

// After statement execution, there should not be side-effect on the stack
fn statement(
    inst: &InstructionPointer, code: &mut Vec<u8>, constants: &[Fr],
    line_numbers: &mut Vec<usize>, components: &mut Vec<ComponentTmpl>,
    fn_registry: &mut FnRegistry) {

    // println!("statement: {}", inst.to_string());

    match **inst {
        Instruction::Store(ref store_bucket) => {

            expression(
                &store_bucket.src, code, constants, line_numbers, components);
            assert_eq!(line_numbers.len(), code.len());

            match store_bucket.dest_address_type {
                AddressType::Variable => {
                    let location = if let LocationRule::Indexed{ref location, ..} = store_bucket.dest {
                        location
                    } else {
                        panic!("Variable destination should be of Indexed type");
                    };

                    let var_idx =
                        u32_or_expression(location, constants).unwrap();

                    match var_idx {
                        U32OrExpression::U32(var_idx) => {
                            code.push(OpCode::SetVariable4 as u8);
                            line_numbers.push(store_bucket.line);
                            code.extend_from_slice(var_idx.to_le_bytes().as_ref());
                            for _ in 0..4 { line_numbers.push(usize::MAX); }
                        }
                        U32OrExpression::BigInt(_) => {
                            panic!("Variable index is not u32");
                        }
                        U32OrExpression::Expression => {
                            expression_u32(
                                location, code, constants, line_numbers,
                                components);
                            code.push(OpCode::SetVariable as u8);
                            line_numbers.push(store_bucket.line);
                        }
                    }

                    let signals_num: u32 = store_bucket.context.size
                        .try_into().expect("Too many signals");
                    code.extend_from_slice(signals_num.to_le_bytes().as_ref());
                    for _ in 0..4 { line_numbers.push(usize::MAX); }
                }

                AddressType::Signal => {
                    let location = if let LocationRule::Indexed{ref location, ..} = store_bucket.dest {
                        location
                    } else {
                        panic!("Signal destination should be of Indexed type");
                    };

                    let sig_idx =
                        u32_or_expression(location, constants).unwrap();

                    match sig_idx {
                        U32OrExpression::U32(sig_idx) => {
                            code.push(OpCode::SetSelfSignal4 as u8);
                            line_numbers.push(store_bucket.line);
                            code.extend_from_slice(sig_idx.to_le_bytes().as_ref());
                            for _ in 0..4 { line_numbers.push(usize::MAX); }
                        }
                        U32OrExpression::BigInt(_) => {
                            panic!("Signal index is not u32");
                        }
                        U32OrExpression::Expression => {
                            expression_u32(
                                location, code, constants, line_numbers,
                                components);
                            code.push(OpCode::SetSelfSignal as u8);
                            line_numbers.push(store_bucket.line);
                        }
                    }

                    let signals_num: u32 = store_bucket.context.size
                        .try_into().expect("Too many signals");
                    code.extend_from_slice(signals_num.to_le_bytes().as_ref());
                    for _ in 0..4 { line_numbers.push(usize::MAX); }
                }

                AddressType::SubcmpSignal { ref cmp_address, ref input_information, .. } => {
                    let signals_num: u32 = store_bucket.context.size
                        .try_into().expect("Too many signals");

                    store_subsignal(
                        code, &store_bucket.dest, constants, components,
                        line_numbers, store_bucket.get_line(), cmp_address,
                        input_information, signals_num);
                }
            }
            assert_eq!(line_numbers.len(), code.len());
        }
        Instruction::Loop(ref loop_bucket) => {
            let loop_start = code.len();

            expression(
                &loop_bucket.continue_condition, code, constants, line_numbers,
                components);

            let loop_end_jump_offset = pre_emit_jump_if_false(code);
            line_numbers.push(loop_bucket.line);
            line_numbers.push(usize::MAX);
            line_numbers.push(usize::MAX);
            line_numbers.push(usize::MAX);
            line_numbers.push(usize::MAX);

            block(
                &loop_bucket.body, code, constants, line_numbers, components,
                fn_registry);

            emit_jump(code, loop_start);
            line_numbers.push(loop_bucket.line);
            line_numbers.push(usize::MAX);
            line_numbers.push(usize::MAX);
            line_numbers.push(usize::MAX);
            line_numbers.push(usize::MAX);

            let to = code.len();

            patch_jump(code, loop_end_jump_offset, to);
            assert_eq!(line_numbers.len(), code.len());
        }
        Instruction::CreateCmp(ref cmp_bucket) => {
            let sub_cmp_idx = u32_or_expression(
                &cmp_bucket.sub_cmp_id, constants).unwrap();

            let sub_cmp_idx = if let U32OrExpression::U32(sub_cmp_idx) = sub_cmp_idx {
                sub_cmp_idx
            } else {
                panic!("Subcomponent index suppose to be a constant");
            };

            // let want_defined_positions: Vec<(usize, bool)> = vec![(0, false)];
            // assert_eq!(cmp_bucket.defined_positions, want_defined_positions); // TODO

            if cmp_bucket.is_part_mixed_array_not_uniform_parallel {
                todo!();
            }

            // TODO
            assert!(matches!(cmp_bucket.uniform_parallel, Some(false)));

            // if cmp_bucket.dimensions.len() > 0 {
            //     todo!("{:?}: {}", cmp_bucket.dimensions, cmp_bucket.to_string());
            // }
            // if cmp_bucket.component_offset != 0 {
            //     todo!();
            // }
            // if cmp_bucket.component_offset_jump != 1 {
            //     todo!("{:?}: {}", cmp_bucket.component_offset_jump, cmp_bucket.to_string());
            // }
            // if cmp_bucket.number_of_cmp != 1 {
            //     todo!();
            // }

            components.push(ComponentTmpl {
                symbol: cmp_bucket.symbol.clone(),
                sub_cmp_idx: sub_cmp_idx as usize,
                number_of_cmp: cmp_bucket.number_of_cmp,
                name_subcomponent: cmp_bucket.name_subcomponent.clone(),
                signal_offset: cmp_bucket.signal_offset,
                signal_offset_jump: cmp_bucket.signal_offset_jump,
                template_id: cmp_bucket.template_id,
                has_inputs: cmp_bucket.has_inputs,
            });

            // println!("{}", fmt_create_cmp_bucket(cmp_bucket, sub_cmp_idx));

            if !cmp_bucket.has_inputs {
                let components_number: u32 = cmp_bucket.number_of_cmp
                    .try_into().expect("Too many components");

                for i in 0..components_number {
                    code.push(OpCode::CmpCall as u8);
                    line_numbers.push(cmp_bucket.line);

                    let (sub_cmp_idx2, overflowed) = sub_cmp_idx.overflowing_add(i);
                    if overflowed {
                        panic!("Subcomponent index is too large");
                    }
                    code.extend_from_slice(sub_cmp_idx2.to_le_bytes().as_ref());
                    for _ in 0..4 { line_numbers.push(usize::MAX); }
                }
            }
        }
        Instruction::Call(ref call_bucket) => {
            // println!("call bucket: {}", _call_bucket.to_string());
            // println!("[3, component] {} {:?}", call_bucket.symbol, call_bucket.argument_types.iter().map(|x| format!("{}", x.size)).collect::<Vec<String>>());

            let args_num: usize = call_bucket.arguments.iter().map(
                |arg| {
                    expression(arg, code, constants, line_numbers, components)
                }).sum();

            let fn_idx = fn_registry.get(&call_bucket.symbol);
            let fn_idx: u32 = fn_idx.try_into().expect("Such a lot of functions?");
            code.push(OpCode::FnCall as u8);
            line_numbers.push(call_bucket.line);

            code.extend_from_slice(fn_idx.to_le_bytes().as_ref());
            for _ in 0..4 { line_numbers.push(usize::MAX); }

            let args_num: u32 = args_num.try_into().expect("Too many arguments");
            code.extend_from_slice(args_num.to_le_bytes().as_ref());
            for _ in 0..4 { line_numbers.push(usize::MAX); }

            match call_bucket.return_info {
                ReturnType::Intermediate { .. } => todo!(),
                ReturnType::Final(ref final_data) => {
                    let return_num: u32 = final_data.context.size.try_into()
                        .expect("Too many return values");
                    code.extend_from_slice(return_num.to_le_bytes().as_ref());
                    for _ in 0..4 { line_numbers.push(usize::MAX); }

                    match final_data.dest_address_type {
                        AddressType::Variable => {
                            let location = if let LocationRule::Indexed{ref location, ..} = final_data.dest {
                                location
                            } else {
                                panic!("Variable destination should be of Indexed type");
                            };
                            expression_u32(
                                location, code, constants, line_numbers,
                                components);

                            code.push(OpCode::SetVariable as u8);
                            line_numbers.push(location.get_line());

                            code.extend_from_slice(return_num.to_le_bytes().as_ref());
                            for _ in 0..4 { line_numbers.push(usize::MAX); }
                        }
                        AddressType::Signal => {todo!()}
                        AddressType::SubcmpSignal { ref cmp_address, ref input_information, .. } => {
                            store_subsignal(
                                code, &final_data.dest, constants, components,
                                line_numbers, call_bucket.get_line(), cmp_address,
                                input_information, return_num);
                        }
                    }
                }
            }

        }
        Instruction::Value(_) => {
            panic!("An expression instruction Value found where statement expected");
        }
        Instruction::Load(_) => {
            panic!("An expression instruction Load found where statement expected");
        }
        Instruction::Compute(_) => {
            panic!("An expression instruction Compute found where statement expected");
        }
        Instruction::Branch(ref branch_bucket) => {
            expression(
                &branch_bucket.cond, code, constants, line_numbers, components);

            let else_jump_offset = pre_emit_jump_if_false(code);
            line_numbers.push(branch_bucket.line);
            for _ in 0..4 { line_numbers.push(usize::MAX); }

            block(
                &branch_bucket.if_branch, code, constants, line_numbers,
                components, fn_registry);

            let end_jump_offset = pre_emit_jump(code);
            line_numbers.push(branch_bucket.line);
            for _ in 0..4 { line_numbers.push(usize::MAX); }

            let to = code.len();
            patch_jump(code, else_jump_offset, to);

            block(
                &branch_bucket.else_branch, code, constants, line_numbers,
                components, fn_registry);

            let to = code.len();
            patch_jump(code, end_jump_offset, to);

            assert_eq!(line_numbers.len(), code.len());
        }
        Instruction::Return(_) => {
            todo!();
        }
        Instruction::Assert(_) => {
            // TODO: maybe implement asserts at runtime
            // todo!();
        }
        Instruction::Log(_) => {
            todo!();
        }
    }
}

fn fn_statement(
    inst: &InstructionPointer, code: &mut Vec<u8>, constants: &[Fr],
    line_numbers: &mut Vec<usize>, fn_registry: &mut FnRegistry) {

    // println!("function statement: {}", inst.to_string());

    match **inst {
        Instruction::Store(ref store_bucket) => {

            let ln = fn_expression(&store_bucket.src, code, constants, line_numbers);
            assert_eq!(ln, store_bucket.context.size);
            assert!(matches!(store_bucket.dest_address_type, AddressType::Variable));

            let location = if let LocationRule::Indexed{ref location, ..} = store_bucket.dest {
                location
            } else {
                panic!("Variable destination should be of Indexed type");
            };

            let var_idx =
                u32_or_expression(location, constants).unwrap();

            match var_idx {
                U32OrExpression::U32(var_idx) => {
                    code.push(OpCode::SetVariable4 as u8);
                    line_numbers.push(store_bucket.line);
                    code.extend_from_slice(var_idx.to_le_bytes().as_ref());
                    for _ in 0..4 { line_numbers.push(usize::MAX); }
                }
                U32OrExpression::BigInt(_) => {
                    panic!("Variable index is not u32");
                }
                U32OrExpression::Expression => {
                    fn_expression_u32(location, code, constants, line_numbers);
                    code.push(OpCode::SetVariable as u8);
                    line_numbers.push(store_bucket.line);
                }
            }

            let values_num: u32 = store_bucket.context.size
                .try_into().expect("Too many values");
            code.extend_from_slice(values_num.to_le_bytes().as_ref());
            for _ in 0..4 { line_numbers.push(usize::MAX); }

            assert_eq!(line_numbers.len(), code.len());
        }
        Instruction::Loop(ref loop_bucket) => {
            let loop_start = code.len();

            let ln = fn_expression(
                &loop_bucket.continue_condition, code, constants, line_numbers);
            assert_eq!(ln, 1);

            let loop_end_jump_offset = pre_emit_jump_if_false(code);
            line_numbers.push(loop_bucket.line);
            for _ in 0..4 { line_numbers.push(usize::MAX); }

            fn_block(
                &loop_bucket.body, code, constants, line_numbers, fn_registry);

            emit_jump(code, loop_start);
            line_numbers.push(loop_bucket.line);
            for _ in 0..4 { line_numbers.push(usize::MAX); }

            let to = code.len();
            patch_jump(code, loop_end_jump_offset, to);
            assert_eq!(line_numbers.len(), code.len());
        }
        Instruction::CreateCmp(ref cmp_bucket) => {
            panic!("`CreateCmp` instruction is not allowed in function body");
        }
        Instruction::Call(ref call_bucket) => {
            // println!("[3, function] {} {:?}", call_bucket.symbol, call_bucket.argument_types.iter().map(|x| format!("{}", x.size)).collect::<Vec<String>>());
            let args_num: usize = call_bucket.arguments.iter().map(
                |arg| {
                    fn_expression(arg, code, constants, line_numbers)
                }).sum();

            let fn_idx = fn_registry.get(&call_bucket.symbol);
            let fn_idx: u32 = fn_idx.try_into().expect("Such a lot of functions?");
            code.push(OpCode::FnCall as u8);
            line_numbers.push(call_bucket.line);

            code.extend_from_slice(fn_idx.to_le_bytes().as_ref());
            for _ in 0..4 { line_numbers.push(usize::MAX); }

            let args_num: u32 = args_num.try_into().expect("Too many arguments");
            code.extend_from_slice(args_num.to_le_bytes().as_ref());
            for _ in 0..4 { line_numbers.push(usize::MAX); }

            match call_bucket.return_info {
                ReturnType::Intermediate { .. } => todo!(),
                ReturnType::Final(ref final_data) => {
                    let return_num: u32 = final_data.context.size.try_into()
                        .expect("Too many return values");
                    code.extend_from_slice(return_num.to_le_bytes().as_ref());
                    for _ in 0..4 { line_numbers.push(usize::MAX); }

                    match final_data.dest_address_type {
                        AddressType::Variable => {
                            let location = if let LocationRule::Indexed{ref location, ..} = final_data.dest {
                                location
                            } else {
                                panic!("Variable destination should be of Indexed type");
                            };
                            fn_expression_u32(
                                location, code, constants, line_numbers);

                            code.push(OpCode::SetVariable as u8);
                            line_numbers.push(location.get_line());

                            code.extend_from_slice(return_num.to_le_bytes().as_ref());
                            for _ in 0..4 { line_numbers.push(usize::MAX); }
                        }
                        AddressType::Signal => {todo!()}
                        AddressType::SubcmpSignal { .. } => {todo!()}
                    }
                }
            }
        }
        Instruction::Value(_) => {
            panic!("An expression instruction Value found where statement expected");
        }
        Instruction::Load(_) => {
            panic!("An expression instruction Load found where statement expected");
        }
        Instruction::Compute(_) => {
            panic!("An expression instruction Compute found where statement expected");
        }
        Instruction::Branch(ref branch_bucket) => {
            let ln = fn_expression(
                &branch_bucket.cond, code, constants, line_numbers);
            assert_eq!(ln, 1);

            let else_jump_offset = pre_emit_jump_if_false(code);
            line_numbers.push(branch_bucket.line);
            for _ in 0..4 { line_numbers.push(usize::MAX); }

            fn_block(
                &branch_bucket.if_branch, code, constants, line_numbers,
                fn_registry);

            let end_jump_offset = pre_emit_jump(code);
            line_numbers.push(branch_bucket.line);
            for _ in 0..4 { line_numbers.push(usize::MAX); }

            let to = code.len();
            patch_jump(code, else_jump_offset, to);

            fn_block(
                &branch_bucket.else_branch, code, constants, line_numbers,
                fn_registry);

            let to = code.len();
            patch_jump(code, end_jump_offset, to);

            assert_eq!(line_numbers.len(), code.len());
        }
        Instruction::Return(ref return_bucket) => {

            let return_num = fn_expression(&return_bucket.value, code, constants, line_numbers);
            let return_num: u32 = return_num.try_into().expect("Too many return values");

            code.push(OpCode::FnReturn as u8);
            line_numbers.push(return_bucket.line);

            code.extend_from_slice(return_num.to_le_bytes().as_ref());
            for _ in 0..4 { line_numbers.push(usize::MAX); }

            assert_eq!(line_numbers.len(), code.len());
        }
        Instruction::Assert(_) => {
            // TODO: maybe implement asserts at runtime
            // todo!();
        }
        Instruction::Log(_) => {
            todo!();
        }
    }
}

fn fmt_create_cmp_bucket(
    cmp_bucket: &CreateCmpBucket,
    sub_cmp_id: u32,
) -> String {
    format!(
        r#"CreateCmpBucket: template_id: {}
                 cmp_unique_id: {}
                 symbol: {}
                 sub_cmp_id: {}
                 name_subcomponent: {}
                 defined_positions: {:?}
                 dimensions: {:?}
                 signal_offset: {}
                 signal_offset_jump: {}
                 component_offset: {}
                 component_offset_jump: {}
                 number_of_cmp: {}
                 has_inputs: {}"#,
        cmp_bucket.template_id,
        cmp_bucket.cmp_unique_id,
        cmp_bucket.symbol,
        sub_cmp_id,
        cmp_bucket.name_subcomponent,
        cmp_bucket.defined_positions,
        cmp_bucket.dimensions,
        cmp_bucket.signal_offset,
        cmp_bucket.signal_offset_jump,
        cmp_bucket.component_offset,
        cmp_bucket.component_offset_jump,
        cmp_bucket.number_of_cmp,
        cmp_bucket.has_inputs,
    )
}


fn assert_64() {
    assert!(cfg!(target_pointer_width = "64"), "Need a fix for non-64-bit architecture.");
}

fn expression_load(
    lb: &LoadBucket, code: &mut Vec<u8>, constants: &[Fr],
    line_numbers: &mut Vec<usize>,
    components: &mut Vec<ComponentTmpl>) -> usize {

    match lb.address_type {
        AddressType::Signal => {
            let location = if let LocationRule::Indexed{ref location, ..} = lb.src {
                location
            } else {
                panic!("Signal source location should be of Indexed type");
            };

            let idx = u32_or_expression(location, constants)
                .unwrap();

            match idx {
                U32OrExpression::U32(idx) => {
                    code.push(OpCode::GetSelfSignal4 as u8);
                    line_numbers.push(lb.line);
                    code.extend_from_slice(idx.to_le_bytes().as_ref());
                    for _ in 0..4 { line_numbers.push(usize::MAX); }
                }
                U32OrExpression::BigInt(_) => {
                    panic!("Signal index is not u32");
                }
                U32OrExpression::Expression => {
                    expression_u32(
                        location, code, constants, line_numbers, components);
                    code.push(OpCode::GetSelfSignal as u8);
                    line_numbers.push(lb.line);
                }
            }

            let signals_num: u32 = lb.context.size
                .try_into().expect("Too many signals");
            code.extend_from_slice(signals_num.to_le_bytes().as_ref());
            for _ in 0..4 { line_numbers.push(usize::MAX); }
        }
        AddressType::SubcmpSignal { ref cmp_address, ref input_information, .. } => {

            let mut indexes_number = 0u32;
            let mut signal_code = 0u32;

            let is_mapped_signal = match lb.src {
                LocationRule::Indexed { ref location, .. } => {
                    let sig_idx =
                        u32_or_expression(location, constants).unwrap();

                    match sig_idx {
                        U32OrExpression::U32(sig_idx) => {
                            code.push(OpCode::Push4 as u8);
                            line_numbers.push(lb.line);

                            code.extend_from_slice(sig_idx.to_le_bytes().as_ref());
                            for _ in 0..4 { line_numbers.push(usize::MAX); }
                        }
                        U32OrExpression::BigInt(_) => {
                            panic!("Signal index is not u32");
                        }
                        U32OrExpression::Expression => {
                            expression_u32(
                                location, code, constants, line_numbers,
                                components);
                        }
                    };
                    false
                }
                LocationRule::Mapped { signal_code: ref signal_code_local, ref indexes } => {
                    for idx_inst in indexes {
                        expression_u32(idx_inst, code, constants, line_numbers, components)
                    }

                    indexes_number = indexes.len()
                        .try_into().expect("Too many indexes");
                    signal_code = (*signal_code_local).try_into()
                        .expect("Too large signal code");

                    true
                }

            };

            // Put component idx to the u32 stack
            match u32_or_expression(cmp_address, constants) {
                Ok(ref cmp_idx) => {
                    match cmp_idx {
                        U32OrExpression::U32(cmp_idx) => {
                            code.push(OpCode::Push4 as u8);
                            line_numbers.push(lb.line);

                            code.extend_from_slice(cmp_idx.to_le_bytes().as_ref());
                            for _ in 0..4 { line_numbers.push(usize::MAX); }
                        }
                        U32OrExpression::BigInt(_) => {
                            panic!("Component index is not u32");
                        }
                        U32OrExpression::Expression => {
                            expression_u32(
                                cmp_address, code, constants, line_numbers,
                                components);
                        }
                    }
                }
                Err(e) => {
                    panic!("Error: {:?}", e);
                }
            };

            // Put opcode
            code.push(OpCode::GetSubSignal as u8);
            line_numbers.push(lb.line);

            // Put signals number argument
            let signals_num: u32 = lb.context.size.try_into()
                .expect("Too many signals");
            code.extend_from_slice(signals_num.to_le_bytes().as_ref());
            for _ in 0..4 { line_numbers.push(usize::MAX); }

            // Put flags argument
            let flags = if is_mapped_signal {
                0b1000_0000
            } else {
                0
            };
            code.push(flags);
            line_numbers.push(usize::MAX);

            if is_mapped_signal {
                // Put mapping indexes number
                code.extend_from_slice(indexes_number.to_le_bytes().as_ref());
                for _ in 0..4 { line_numbers.push(usize::MAX); }

                // Put signal code
                code.extend_from_slice(signal_code.to_le_bytes().as_ref());
                for _ in 0..4 { line_numbers.push(usize::MAX); }
            }
        }
        AddressType::Variable => {
            let location = if let LocationRule::Indexed{ref location, ..} = lb.src {
                location
            } else {
                panic!("Variable source location should be of Indexed type");
            };

            let idx = u32_or_expression(location, constants)
                .unwrap();

            match idx {
                U32OrExpression::U32(idx) => {
                    code.push(OpCode::GetVariable4 as u8);
                    line_numbers.push(lb.line);
                    code.extend_from_slice(idx.to_le_bytes().as_ref());
                    for _ in 0..4 { line_numbers.push(usize::MAX); }
                }
                U32OrExpression::BigInt(_) => {
                    panic!("Variable index is not u32");
                }
                U32OrExpression::Expression => {
                    expression_u32(
                        location, code, constants, line_numbers, components);
                    code.push(OpCode::GetVariable as u8);
                    line_numbers.push(lb.line);
                }
            }

            let signals_num: u32 = lb.context.size
                .try_into().expect("Too many signals");
            code.extend_from_slice(signals_num.to_le_bytes().as_ref());
            for _ in 0..4 { line_numbers.push(usize::MAX); }
        }
    }

    lb.context.size
}

fn fn_expression_load(
    lb: &LoadBucket, code: &mut Vec<u8>, constants: &[Fr],
    line_numbers: &mut Vec<usize>) -> usize {

    assert!(matches!(lb.address_type, AddressType::Variable));

    let location = if let LocationRule::Indexed{ref location, ..} = lb.src {
        location
    } else {
        panic!("Variable source location should be of Indexed type");
    };

    let idx = u32_or_expression(location, constants).unwrap();

    match idx {
        U32OrExpression::U32(idx) => {
            code.push(OpCode::GetVariable4 as u8);
            line_numbers.push(lb.line);
            code.extend_from_slice(idx.to_le_bytes().as_ref());
            for _ in 0..4 { line_numbers.push(usize::MAX); }
        }
        U32OrExpression::BigInt(_) => {
            panic!("Variable index is not u32");
        }
        U32OrExpression::Expression => {
            fn_expression_u32(location, code, constants, line_numbers);
            code.push(OpCode::GetVariable as u8);
            line_numbers.push(lb.line);
        }
    }

    let values_num: u32 = lb.context.size
        .try_into().expect("Too many signals");
    code.extend_from_slice(values_num.to_le_bytes().as_ref());
    for _ in 0..4 { line_numbers.push(usize::MAX); }

    lb.context.size
}

fn expression_compute(
    cb: &ComputeBucket, code: &mut Vec<u8>, constants: &[Fr],
    line_numbers: &mut Vec<usize>,
    components: &mut Vec<ComponentTmpl>) -> usize {

    // two operand operations
    let mut op2 = |oc: OpCode| {
        assert_eq!(2, cb.stack.len());
        expression(&cb.stack[0], code, constants, line_numbers, components);
        expression(&cb.stack[1], code, constants, line_numbers, components);
        code.push(oc as u8);
        line_numbers.push(cb.line);
    };

    match cb.op {
        OperatorType::Mul => {
            op2(OpCode::OpMul);
        }
        OperatorType::Div => {
            op2(OpCode::OpDiv);
        }
        OperatorType::Add => {
            op2(OpCode::OpAdd);
        }
        OperatorType::Sub => {
            op2(OpCode::OpSub);
        }
        OperatorType::IntDiv => {
            op2(OpCode::OpIntDiv);
        }
        OperatorType::Mod => {
            op2(OpCode::OpMod);
        }
        OperatorType::ShiftL => {
            op2(OpCode::OpShL);
        }
        OperatorType::ShiftR => {
            op2(OpCode::OpShR);
        }
        OperatorType::LesserEq => {
            op2(OpCode::OpLtE);
        }
        OperatorType::GreaterEq => {
            op2(OpCode::OpGtE);
        }
        OperatorType::Lesser => {
            op2(OpCode::OpLt);
        }
        OperatorType::Greater => {
            op2(OpCode::OpGt);
        }
        OperatorType::Eq( x ) => {
            if x != 1 {
                todo!();
            }
            op2(OpCode::OpEq);
        }
        OperatorType::NotEq => {
            op2(OpCode::OpNe);
        }
        OperatorType::BoolAnd => {
            op2(OpCode::OpBoolAnd);
        }
        OperatorType::BitOr => {
            op2(OpCode::OpBitOr);
        }
        OperatorType::BitAnd => {
            op2(OpCode::OpBitAnd);
        }
        OperatorType::BitXor => {
            op2(OpCode::OpBitXor);
        }
        OperatorType::PrefixSub => {
            assert_eq!(1, cb.stack.len());
            expression(&cb.stack[0], code, constants, line_numbers, components);
            code.push(OpCode::OpNeg as u8);
            line_numbers.push(cb.line);
        }
        OperatorType::ToAddress | OperatorType::MulAddress | OperatorType::AddAddress => {
            panic!("Unexpected address operator: {}", cb.op.to_string());
        }
        _ => {
            todo!("not implemented expression operator {}: {}",
                cb.op.to_string(), cb.to_string());
        }
    };
    1
}

fn fn_expression_compute(
    cb: &ComputeBucket, code: &mut Vec<u8>, constants: &[Fr],
    line_numbers: &mut Vec<usize>) -> usize {

    // two operand operations
    let mut op2 = |oc: OpCode| {
        assert_eq!(2, cb.stack.len());
        let ln = fn_expression(&cb.stack[0], code, constants, line_numbers);
        assert_eq!(1, ln);
        let ln = fn_expression(&cb.stack[1], code, constants, line_numbers);
        assert_eq!(1, ln);
        code.push(oc as u8);
        line_numbers.push(cb.line);
    };

    match cb.op {
        OperatorType::Mul => {
            op2(OpCode::OpMul);
        }
        OperatorType::Div => {
            op2(OpCode::OpDiv);
        }
        OperatorType::Add => {
            op2(OpCode::OpAdd);
        }
        OperatorType::Sub => {
            op2(OpCode::OpSub);
        }
        OperatorType::Mod => {
            op2(OpCode::OpMod);
        }
        OperatorType::ShiftL => {
            op2(OpCode::OpShL);
        }
        OperatorType::ShiftR => {
            op2(OpCode::OpShR);
        }
        OperatorType::LesserEq => {
            op2(OpCode::OpLtE);
        }
        OperatorType::GreaterEq => {
            op2(OpCode::OpGtE);
        }
        OperatorType::Lesser => {
            op2(OpCode::OpLt);
        }
        OperatorType::Greater => {
            op2(OpCode::OpGt);
        }
        OperatorType::Eq( x ) => {
            if x != 1 {
                todo!();
            }
            op2(OpCode::OpEq);
        }
        OperatorType::NotEq => {
            op2(OpCode::OpNe);
        }
        OperatorType::BoolAnd => {
            op2(OpCode::OpBoolAnd);
        }
        OperatorType::BitOr => {
            op2(OpCode::OpBitOr);
        }
        OperatorType::BitAnd => {
            op2(OpCode::OpBitAnd);
        }
        OperatorType::BitXor => {
            op2(OpCode::OpBitXor);
        }
        OperatorType::PrefixSub => {
            assert_eq!(1, cb.stack.len());
            let ln = fn_expression(&cb.stack[0], code, constants, line_numbers);
            assert_eq!(1, ln);
            code.push(OpCode::OpNeg as u8);
            line_numbers.push(cb.line);
        }
        OperatorType::ToAddress | OperatorType::MulAddress | OperatorType::AddAddress => {
            panic!("Unexpected address operator: {}", cb.op.to_string());
        }
        _ => {
            todo!("not implemented function expression operator {}: {}",
                cb.op.to_string(), cb.to_string());
        }
    };
    1
}

fn expression_compute_u32(
    cb: &ComputeBucket, code: &mut Vec<u8>, constants: &[Fr],
    line_numbers: &mut Vec<usize>, components: &mut Vec<ComponentTmpl>) {

    match cb.op {
        OperatorType::ToAddress => {
            assert_eq!(1, cb.stack.len());
            expression(&cb.stack[0], code, constants, line_numbers, components);
            code.push(OpCode::OpToAddr as u8);
            line_numbers.push(cb.line);
        }
        OperatorType::MulAddress => {
            assert_eq!(2, cb.stack.len());
            expression_u32(
                &cb.stack[0], code, constants, line_numbers, components);
            expression_u32(
                &cb.stack[1], code, constants, line_numbers, components);
            code.push(OpCode::OpMulAddr as u8);
            line_numbers.push(cb.line);
        }
        OperatorType::AddAddress => {
            assert_eq!(2, cb.stack.len());
            expression_u32(
                &cb.stack[0], code, constants, line_numbers, components);
            expression_u32(
                &cb.stack[1], code, constants, line_numbers, components);
            code.push(OpCode::OpAddAddr as u8);
            line_numbers.push(cb.line);
        }
        _ => {
            todo!("not implemented expression operator {}: {}",
                cb.op.to_string(), cb.to_string());
        }
    };
}

fn fn_expression_compute_u32(
    cb: &ComputeBucket, code: &mut Vec<u8>, constants: &[Fr],
    line_numbers: &mut Vec<usize>) {

    match cb.op {
        OperatorType::ToAddress => {
            assert_eq!(1, cb.stack.len());
            let ln = fn_expression(&cb.stack[0], code, constants, line_numbers);
            assert_eq!(1, ln);
            code.push(OpCode::OpToAddr as u8);
            line_numbers.push(cb.line);
        }
        OperatorType::MulAddress => {
            assert_eq!(2, cb.stack.len());
            fn_expression_u32(&cb.stack[0], code, constants, line_numbers);
            fn_expression_u32(&cb.stack[1], code, constants, line_numbers);
            code.push(OpCode::OpMulAddr as u8);
            line_numbers.push(cb.line);
        }
        OperatorType::AddAddress => {
            assert_eq!(2, cb.stack.len());
            fn_expression_u32(&cb.stack[0], code, constants, line_numbers);
            fn_expression_u32(&cb.stack[1], code, constants, line_numbers);
            code.push(OpCode::OpAddAddr as u8);
            line_numbers.push(cb.line);
        }
        _ => {
            todo!("not implemented function expression operator {}: {}",
                cb.op.to_string(), cb.to_string());
        }
    };
}

// After expression execution, the value of the expression should be on the stack.
// Return the number of values put on the stack.
fn expression(
    inst: &InstructionPointer, code: &mut Vec<u8>, constants: &[Fr],
    line_numbers: &mut Vec<usize>,
    components: &mut Vec<ComponentTmpl>) -> usize {

    // println!("expression: {}", inst.to_string());
    match **inst {
        Instruction::Value(ref value_bucket) => {
            match value_bucket.parse_as {
                ValueType::U32 => {
                    code.push(OpCode::Push8 as u8);
                    line_numbers.push(value_bucket.line);
                    assert_64();
                    code.extend_from_slice(value_bucket.value.to_le_bytes().as_ref());
                    for _ in 0..8 { line_numbers.push(usize::MAX); }
                }
                ValueType::BigInt => {
                    code.push(OpCode::GetConstant8 as u8);
                    line_numbers.push(value_bucket.line);
                    assert_64();
                    code.extend_from_slice(value_bucket.value.to_le_bytes().as_ref());
                    for _ in 0..8 { line_numbers.push(usize::MAX); }
                }
            }
            assert_eq!(line_numbers.len(), code.len());
            1
        }
        Instruction::Load(ref load_bucket) => {
            let n = expression_load(
                load_bucket, code, constants, line_numbers, components);
            assert_eq!(line_numbers.len(), code.len());
            n
        }
        Instruction::Compute(ref compute_bucket) => {
            let n = expression_compute(
                compute_bucket, code, constants, line_numbers, components);
            assert_eq!(line_numbers.len(), code.len());
            n
        }
        _ => {
            panic!("Expression does not supported: {}", inst.to_string());
        }
    }
}

fn fn_expression(
    inst: &InstructionPointer, code: &mut Vec<u8>, constants: &[Fr],
    line_numbers: &mut Vec<usize>) -> usize {

    match **inst {
        Instruction::Value(ref value_bucket) => {
            match value_bucket.parse_as {
                ValueType::U32 => {
                    code.push(OpCode::Push8 as u8);
                    line_numbers.push(value_bucket.line);
                    assert_64();
                    code.extend_from_slice(value_bucket.value.to_le_bytes().as_ref());
                    for _ in 0..8 { line_numbers.push(usize::MAX); }
                }
                ValueType::BigInt => {
                    code.push(OpCode::GetConstant8 as u8);
                    line_numbers.push(value_bucket.line);
                    assert_64();
                    code.extend_from_slice(value_bucket.value.to_le_bytes().as_ref());
                    for _ in 0..8 { line_numbers.push(usize::MAX); }
                }
            }
            assert_eq!(line_numbers.len(), code.len());
            1
        }
        Instruction::Load(ref load_bucket) => {
            let ln =
                fn_expression_load(load_bucket, code, constants, line_numbers);
            assert_eq!(line_numbers.len(), code.len());
            ln
        }
        Instruction::Compute(ref compute_bucket) => {
            let ln = fn_expression_compute(
                compute_bucket, code, constants, line_numbers);
            assert_eq!(line_numbers.len(), code.len());
            ln
        }
        _ => {
            panic!("Expression does not supported: {}", inst.to_string());
        }
    }
}

// After expression execution_u32, the value of the expression should be on the stack_u32
fn expression_u32(
    inst: &InstructionPointer, code: &mut Vec<u8>, constants: &[Fr],
    line_numbers: &mut Vec<usize>, components: &mut Vec<ComponentTmpl>) {

    // println!("expression: {}", inst.to_string());
    match **inst {
        Instruction::Value(ref value_bucket) => {
            match value_bucket.parse_as {
                ValueType::U32 => {
                    code.push(OpCode::Push4 as u8);
                    line_numbers.push(value_bucket.line);
                    let value: u32 = value_bucket.value.try_into().expect("Value is too large");
                    code.extend_from_slice(value.to_le_bytes().as_ref());
                    for _ in 0..4 { line_numbers.push(usize::MAX); }
                }
                ValueType::BigInt => {
                    todo!("convert to u32 and check this");
                    code.push(OpCode::GetConstant8 as u8);
                    line_numbers.push(value_bucket.line);
                    assert_64();
                    code.extend_from_slice(value_bucket.value.to_le_bytes().as_ref());
                    for _ in 0..8 { line_numbers.push(usize::MAX); }
                }
            }
            assert_eq!(line_numbers.len(), code.len());
        }
        Instruction::Compute(ref compute_bucket) => {
            expression_compute_u32(
                compute_bucket, code, constants, line_numbers, components);
            assert_eq!(line_numbers.len(), code.len());
        }
        _ => {
            panic!("U32 expression does not supported: {}", inst.to_string());
        }
    }
}

fn fn_expression_u32(
    inst: &InstructionPointer, code: &mut Vec<u8>, constants: &[Fr],
    line_numbers: &mut Vec<usize>) {

    match **inst {
        Instruction::Value(ref value_bucket) => {
            match value_bucket.parse_as {
                ValueType::U32 => {
                    code.push(OpCode::Push4 as u8);
                    line_numbers.push(value_bucket.line);
                    let value: u32 = value_bucket.value.try_into().expect("Value is too large");
                    code.extend_from_slice(value.to_le_bytes().as_ref());
                    for _ in 0..4 { line_numbers.push(usize::MAX); }
                }
                ValueType::BigInt => {
                    todo!("convert to u32 and check this");
                    code.push(OpCode::GetConstant8 as u8);
                    line_numbers.push(value_bucket.line);
                    assert_64();
                    code.extend_from_slice(value_bucket.value.to_le_bytes().as_ref());
                    for _ in 0..8 { line_numbers.push(usize::MAX); }
                }
            }
            assert_eq!(line_numbers.len(), code.len());
        }
        Instruction::Compute(ref compute_bucket) => {
            fn_expression_compute_u32(
                compute_bucket, code, constants, line_numbers);
            assert_eq!(line_numbers.len(), code.len());
        }
        _ => {
            panic!(
                "U32 function expression does not supported: {}",
                inst.to_string());
        }
    }
}

struct ComponentTmpl {
    symbol: String,
    sub_cmp_idx: usize,
    number_of_cmp: usize,
    name_subcomponent: String,
    signal_offset: usize,
    signal_offset_jump: usize,
    template_id: usize,
    has_inputs: bool,
}

fn block(
    inst_list: &InstructionList, code: &mut Vec<u8>, constants: &[Fr],
    line_numbers: &mut Vec<usize>, components: &mut Vec<ComponentTmpl>,
    fn_registry: &mut FnRegistry) {

    for inst in inst_list {
        statement(inst, code, constants, line_numbers, components, fn_registry);
        assert_eq!(line_numbers.len(), code.len());
    }
}

fn fn_block(
    inst_list: &InstructionList, code: &mut Vec<u8>, constants: &[Fr],
    line_numbers: &mut Vec<usize>, fn_registry: &mut FnRegistry) {

    for inst in inst_list {
        fn_statement(inst, code, constants, line_numbers, fn_registry);
        assert_eq!(line_numbers.len(), code.len());
    }
}

fn compile_template(
    tmpl_code: &TemplateCode, constants: &[Fr],
    fn_registry: &mut FnRegistry) -> Template {

    // println!("Compile template {}", tmpl_code.name);

    let mut code = vec![];
    let mut line_numbers = vec![];
    let mut components = Vec::new();
    block(
        &tmpl_code.body, &mut code, constants, &mut line_numbers,
        &mut components, fn_registry);

    assert_eq!(line_numbers.len(), code.len());

    Template {
        name: tmpl_code.name.clone(),
        code,
        line_numbers,
        components: components,
    }
}

fn compile_function(
    fn_code: &FunctionCode, constants: &[Fr],
    fn_registry: &mut FnRegistry) -> Function {

    // println!("Compile function {}", fn_code.name);

    let mut code = vec![];
    let mut line_numbers = vec![];
    fn_block(
        &fn_code.body, &mut code, constants, &mut line_numbers, fn_registry);

    assert_eq!(line_numbers.len(), code.len());

    Function {
        name: fn_code.name.clone(),
        symbol: fn_code.header.clone(),
        code,
        line_numbers,
    }
}

struct FnRegistry (HashMap<String, usize>);

impl FnRegistry {
    fn new() -> Self {
        FnRegistry(HashMap::new())
    }

    fn sort(&self, fns: &mut [Function]) {
        fns.sort_by_key(|f| {
            match self.0.get(&f.symbol) {
                Some(idx) => *idx,
                None => {
                    println!("Function {} not found in registry", f.name);
                    usize::MAX
                },
            }
        });
    }

    fn get(&mut self, name: &str) -> usize {
        match self.0.get(name) {
            Some(idx) => *idx,
            None => {
                self.0.insert(name.to_string(), self.0.len());
                self.0.len() - 1
            },
        }
    }
}

fn compile(
    templates: &Vec<TemplateCode>,
    functions: &Vec<FunctionCode>,
    constants: &[Fr],
) -> (Vec<Template>, Vec<Function>) {

    let mut fn_registry = FnRegistry::new();

    let mut compiled_functions = Vec::with_capacity(functions.len());

    for fun in functions {
        compiled_functions.push(
            compile_function(fun, constants, &mut fn_registry));
    }

    let mut compiled_templates = Vec::with_capacity(templates.len());
    for tmpl in templates.iter() {
        compiled_templates.push(
            compile_template(tmpl, constants, &mut fn_registry));
    }

    fn_registry.sort(&mut compiled_functions);

    // Assert all components created has has_inputs field consistent with
    // the number of inputs in the templates
    for (i, tmpl) in compiled_templates.iter().enumerate() {
        // println!("Template #{}: {}", i, tmpl.name);
        for c in tmpl.components.iter() {
            let has_inputs = templates[c.template_id].number_of_inputs > 0;
            assert_eq!(c.has_inputs, has_inputs);
            // println!("Component: {} {}", c.symbol, c.template_id);
        }
    }

    (compiled_templates, compiled_functions)
}

fn init_input_signals(
    circuit: &Circuit,
    input_file: String,
    signals: &mut [Option<Fr>],
) {
    signals[0] = Some(Fr::from(1u32));

    let inputs_data = fs::read(input_file).expect("Failed to read input file");
    let inputs = deserialize_inputs(&inputs_data).unwrap();

    let input_list = circuit.c_producer.get_main_input_list();
    for (name, offset, len) in input_list {
        match inputs.get(name) {
            Some(values) => {
                if values.len() != *len {
                    panic!(
                        "input signal {} has different length in inputs file, want {}, actual {}",
                        name, *len, values.len());
                }
                for (i, v) in values.iter().enumerate() {
                    signals[offset + i] = Some(Fr::from_str(v.to_string().as_str()).unwrap());
                }
            }
            None => {
                panic!("input signal {} is not found in inputs file", name);
            }
        }
    }
}

fn fr_to_field_element(a: &Fr) -> FieldElement<32> {
    let x: [u8; 32] = a.into_bigint().to_bytes_le().as_slice().try_into().unwrap();
    x.into()
}


pub fn wtns_from_witness(witness: Vec<Fr>) -> Vec<u8> {
    let vec_witness: Vec<FieldElement<32>> = witness.iter().map(fr_to_field_element).collect();
    let mut buf = Vec::new();

    let m: [u8; 32] = Fr::MODULUS.to_bytes_le().as_slice().try_into().unwrap();

    let mut wtns_f = wtns_file::WtnsFile::from_vec(vec_witness, m.into());
    wtns_f.version = 2;
    // We write into the buffer, so we should not have any errors here.
    // Panic in case of out of memory is fine.
    wtns_f.write(&mut buf).unwrap();
    buf
}

fn bigint_to_u64<const N: usize>(i: BigInt<N>) -> Option<u64> {
    let z = BigInt::<N>::from(0u32);
    let max = BigInt::<N>::from(u64::MAX);

    if i < z || i > max {
        return None;
    }

    Some(i.0[0])
}

fn u_lt(a: &Fr, b: &Fr) -> Fr {
    let half_m = Fr::from_str("10944121435919637611123202872628637544274182200208017171849102093287904247808").unwrap();
    let a_neg = &half_m < a;
    let b_neg = &half_m < b;

    match (a_neg, b_neg) {
        (false, false) => Fr::from(a < b),
        (true, false) => Fr::one(),
        (false, true) => Fr::zero(),
        (true, true) => Fr::from(a < b),
    }
}

fn disassemble(
    code: &[u8], line_numbers: &[usize], name: &str, functions: &[Function]) {

    let mut ip = 0usize;
    while ip < code.len() {
        ip = disassemble_instruction(code, line_numbers, ip, &name, functions);
    }
}

fn disassemble_instruction(
    code: &[u8], line_numbers: &[usize], ip: usize, name: &str,
    functions: &[Function]) -> usize {

    print!("{:08x} [{:10}:{:4}] ", ip, name, line_numbers[ip]);

    let op = unsafe { std::mem::transmute::<u8, OpCode>(code[ip]) };
    let mut ip = ip + 1;


    match op {
        OpCode::NoOp => {
            println!("NoOp")
        }
        OpCode::SetSelfSignal4 => {
            let sig_idx = read_u32(&code, ip);
            ip += size_of::<u32>();

            let sigs_number = read_u32(&code, ip);
            ip += size_of::<u32>();

            println!("SetSelfSignal4 [{},{}]", sig_idx, sigs_number);
        }
        OpCode::SetSelfSignal => {
            let sigs_number = read_u32(&code, ip);
            ip += size_of::<u32>();

            println!("SetSelfSignal [{}]", sigs_number);
        }
        OpCode::GetConstant8 => {
            let const_idx = read_usize(&code, ip);
            ip += size_of::<usize>();

            println!("GetConstant8 [{}]", const_idx);
        }
        OpCode::Push8 => {
            let val = read_usize(&code, ip);
            ip += size_of::<usize>();

            println!("Push8 [{}]", val);
        }
        OpCode::Push4 => {
            let val = read_u32(&code, ip);
            ip += size_of::<u32>();

            println!("Push4 [{}]", val);
        }
        OpCode::GetVariable4 => {
            let var_idx = read_u32(&code, ip);
            ip += size_of::<u32>();

            let vars_number = read_u32(&code, ip);
            ip += size_of::<u32>();

            println!("GetVariable4 [{},{}]", var_idx, vars_number);
        }
        OpCode::GetVariable => {
            let vars_number = read_u32(&code, ip);
            ip += size_of::<u32>();

            println!("GetVariable [{}]", vars_number);
        }
        OpCode::SetVariable4 => {
            let var_idx = read_u32(&code, ip);
            ip += size_of::<u32>();

            let vars_num = read_u32(&code, ip);
            ip += size_of::<u32>();

            println!("SetVariable4 [{},{}]", var_idx, vars_num);
        }
        OpCode::SetVariable => {
            let vars_num = read_u32(&code, ip);
            ip += size_of::<u32>();

            println!("SetVariable [{}]", vars_num);
        }
        OpCode::GetSubSignal => {
            let sigs_number = read_u32(&code, ip);
            ip += size_of::<u32>();

            let flags: u8 = code[ip];
            ip += 1;

            if flags & 0b1000_0000 != 0 {
                let indexes_number = read_u32(&code, ip);
                ip += size_of::<u32>();

                let signal_code = read_u32(&code, ip);
                ip += size_of::<u32>();

                println!(
                    "GetSubSignal mapped [M,{},{},{}]",
                    sigs_number, indexes_number, signal_code);
            } else {
                println!(
                    "GetSubSignal [NM,{}]", sigs_number);
            }
        }
        OpCode::SetSubSignal => {
            let sigs_number = read_u32(&code, ip);
            ip += size_of::<u32>();

            let flags = code[ip];
            ip += 1;

            let (input_status, is_mapped_signal_idx) = unpack_flags(flags);

            if is_mapped_signal_idx {
                let indexes_number = read_u32(&code, ip);
                ip += size_of::<u32>();

                let signal_code = read_u32(&code, ip);
                ip += size_of::<u32>();

                println!(
                    "SetSubSignal [M,{},{},{},{}]",
                    sigs_number, input_status, indexes_number, signal_code);
            } else {
                println!(
                    "SetSubSignal [NM,{},{}]", sigs_number, input_status);
            }
        }
        OpCode::JumpIfFalse => {
            let offset = read_i32(&code, ip);
            ip += size_of::<i32>();

            println!("JumpIfFalse [{} -> {:x}]", offset, ip as i64 + offset as i64);
        }
        OpCode::Jump => {
            let offset = read_i32(&code, ip);
            ip += size_of::<i32>();

            println!("Jump [{} -> {:x}]", offset, ip as i64 + offset as i64);
        }
        OpCode::OpMul => {
            println!("OpMul");
        }
        OpCode::OpDiv => {
            println!("OpDiv");
        }
        OpCode::OpAdd => {
            println!("OpAdd");
        }
        OpCode::OpSub => {
            println!("OpSub");
        }
        OpCode::OpIntDiv => {
            println!("OpIntDiv");
        }
        OpCode::OpMod => {
            println!("OpMod");
        }
        OpCode::OpShL => {
            println!("OpShL");
        }
        OpCode::OpShR => {
            println!("OpShR");
        }
        OpCode::OpLtE => {
            println!("OpLtE");
        }
        OpCode::OpGtE => {
            println!("OpGtE");
        }
        OpCode::OpLt => {
            println!("OpLt");
        }
        OpCode::OpGt => {
            println!("OpGt");
        }
        OpCode::OpEq => {
            println!("OpEq");
        }
        OpCode::OpNe => {
            println!("OpNe");
        }
        OpCode::OpBoolAnd => {
            println!("OpBoolAnd");
        }
        OpCode::OpBitOr => {
            println!("OpBitOr");
        }
        OpCode::OpBitAnd => {
            println!("OpBitAnd");
        }
        OpCode::OpBitXor => {
            println!("OpBitXor");
        }
        OpCode::OpNeg => {
            println!("OpNeg");
        }
        OpCode::GetSelfSignal4 => {
            let sig_idx = read_u32(&code, ip);
            ip += size_of::<u32>();

            let sigs_number = read_u32(&code, ip);
            ip += size_of::<u32>();

            println!("GetSelfSignal4 [{},{}]", sig_idx, sigs_number);
        }
        OpCode::GetSelfSignal => {
            let sigs_number = read_u32(&code, ip);
            ip += size_of::<u32>();

            println!("GetSelfSignal [{}]", sigs_number);
        }
        OpCode::OpToAddr => {
            println!("OpToAddr");
        }
        OpCode::OpMulAddr => {
            println!("OpMulAddr");
        }
        OpCode::OpAddAddr => {
            println!("OpAddAddr");
        }
        OpCode::CmpCall => {
            let cmp_idx = read_u32(&code, ip);
            ip += size_of::<u32>();

            println!("CmpCall [{}]", cmp_idx);
        }
        OpCode::FnCall => {
            let fn_idx = read_u32(&code, ip);
            ip += size_of::<u32>();

            let args_num = read_u32(&code, ip);
            ip += size_of::<u32>();

            let return_num = read_u32(&code, ip);
            ip += size_of::<u32>();

            let fn_name = &functions[fn_idx as usize].name;

            println!(
                "FnCall [{}:{},{},{}]", fn_idx, fn_name, args_num, return_num);
        }
        OpCode::FnReturn => {
            let return_num = read_u32(&code, ip);
            ip += size_of::<u32>();

            println!("FnReturn [{}]", return_num);
        }
        OpCode::Assert => {
            println!("Assert");
        }
    }

    ip
}

fn mk_flags(input_status: InputStatus, is_mapped_signal_idx: bool) -> u8 {
    let mut flags: u8 = input_status as u8;

    if is_mapped_signal_idx {
        flags |= 0b1000_0000
    }

    flags
}

fn unpack_flags(flags: u8) -> (InputStatus, bool) {
    let is_mapped_signal_idx = flags & 0b1000_0000 != 0;
    let input_status = InputStatus::try_from(flags & 0b0000_0011).unwrap();
    (input_status, is_mapped_signal_idx)
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap};
    use ark_ff::BigInteger256;
    use compiler::intermediate_representation::ir_interface::{InstrContext, StoreBucket, ValueBucket};
    use super::*;

    fn assert_u64_value(inst: &InstructionPointer) -> u64 {
        let value = if let Instruction::Value(ref value) = **inst {
            value
        } else {
            panic!("Expected value instruction, got: {}", inst.to_string());
        };

        assert!(matches!(value.parse_as, ValueType::U32));
        value.value.try_into().expect("value is not u64")
    }

    #[test]
    fn test_parse_args() {
        let o = OpCode::SetSelfSignal4;
        println!("OK: {:?}", o);
        let i = o as u8;
        println!("OK: {:?}", i);
        let o2 = unsafe { std::mem::transmute::<u8, OpCode>(i) };
        println!("OK: {:?}", o2);
    }

    #[test]
    fn test_assert_u32() {
        let inst = Box::new(Instruction::Value(ValueBucket {
            line: 0,
            message_id: 0,
            parse_as: ValueType::U32,
            op_aux_no: 0,
            value: 42,
        }));
        let val: u64 = assert_u64_value(&inst);
        assert_eq!(val, 42);
    }

    #[test]
    #[should_panic(expected = "assertion failed: matches!(value.parse_as, ValueType::U32)")]
    fn test_assert_u32_not_u32() {
        let inst = Box::new(Instruction::Value(ValueBucket {
            line: 0,
            message_id: 0,
            parse_as: ValueType::BigInt,
            op_aux_no: 0,
            value: 42,
        }));
        let val: u64 = assert_u64_value(&inst);
    }

    #[test]
    fn test_expression_value_u32() {
        let mut code = vec![];
        let constants = vec![];
        let inst = Box::new(Instruction::Value(ValueBucket {
            line: 0,
            message_id: 0,
            parse_as: ValueType::U32,
            op_aux_no: 0,
            value: 42,
        }));
        expression(
            &inst, &mut code, &constants, &mut vec![],
            &mut vec![]);
        assert_eq!(code, vec![OpCode::Push8 as u8, 42, 0, 0, 0, 0, 0, 0, 0]);
    }

    #[test]
    fn test_expression_value_bigint() {
        let mut code = vec![];
        let constants = vec![];
        let inst = Box::new(Instruction::Value(ValueBucket {
            line: 0,
            message_id: 0,
            parse_as: ValueType::BigInt,
            op_aux_no: 0,
            value: 42,
        }));
        expression(&inst, &mut code, &constants, &mut vec![], &mut vec![]);
        assert_eq!(code, vec![OpCode::GetConstant8 as u8, 42, 0, 0, 0, 0, 0, 0, 0]);
    }

    #[test]
    fn statement_1() {
        /*
        STORE(
  line:8,
  template_id:0,
  dest_type:VARIABLE,
  dest:INDEXED:(
    VALUE(
	  line:8,
	  template_id:0,
	  as:U32,
	  op_number:0,
	  value:0),
	NONE),
  src:VALUE(
    line:8,
	template_id:0,
	as:BigInt,
	op_number:0,
	value:0)
)
         */
        let mut code = vec![];
        let inst = Box::new(Instruction::Store(StoreBucket {
            line: 8,
            message_id: 0,
            context: InstrContext { size: 1 },
            dest_is_output: false,
            dest_address_type: AddressType::Variable,
            dest: LocationRule::Indexed {
                location: Box::new(Instruction::Value(ValueBucket {
                    line: 8,
                    message_id: 0,
                    parse_as: ValueType::U32,
                    op_aux_no: 0,
                    value: 555,
                })),
                template_header: None,
            },
            src: Box::new(Instruction::Value(ValueBucket {
                line: 8,
                message_id: 0,
                parse_as: ValueType::BigInt,
                op_aux_no: 0,
                value: 234,
            })),
        }));

        let constants = vec![];
        let mut line_numbers = vec![];
        let mut components = vec![];
        let mut fn_registry = FnRegistry::new();
        statement(
            &inst, &mut code, &constants, &mut line_numbers, &mut components,
            &mut fn_registry);
        assert_eq!(code,
                   vec![
                       OpCode::GetConstant8 as u8, 0xea, 0, 0, 0, 0, 0, 0, 0,
                       OpCode::SetVariable4 as u8, 0x2b, 0x2, 0, 0, 1, 0, 0, 0]);
    }

    #[test]
    fn statement_2() {
        /*
		STORE(
			line:12,
			template_id:0,
			dest_type:VARIABLE,
			dest:INDEXED:(VALUE(line:10,template_id:0,as:U32,op_number:0,value:1), NONE),
			src:COMPUTE(
				line:12,
				template_id:0,
				op_number:0,
				op:ADD,
				stack:
					LOAD(
						line:12,
						template_id:0,
						address_type:VARIABLE,
						src:INDEXED:(VALUE(line:10,template_id:0,as:U32,op_number:0,value:1),NONE)
					);
					LOAD(
						line:12,
						template_id:0,
						address_type:SIGNAL,
						src:INDEXED:(COMPUTE(
							line:0,
							template_id:0,
							op_number:0,
							op:ADD_ADDRESS,
							stack:
								COMPUTE(
									line:0,
									template_id:0,
									op_number:0,
									op:MUL_ADDRESS,
									stack:
										VALUE(line:0,template_id:0,as:U32,op_number:0,value:1);
										COMPUTE(
											line:12,
											template_id:0,
											op_number:0,
											op:TO_ADDRESS,
											stack:
												LOAD(line:12,template_id:0,address_type:VARIABLE,src:INDEXED: (VALUE(line:11,template_id:0,as:U32,op_number:0,value:2), NONE));
										);
								);
								VALUE(line:0,template_id:0,as:U32,op_number:0,value:1);
						), NONE)
					);
			)
		);
         */
        let mut code = vec![];
        let inst = Box::new(Instruction::Store(StoreBucket {
            line: 12,
            message_id: 0,
            context: InstrContext { size: 1 },
            dest_is_output: false,
            dest_address_type: AddressType::Variable,
            dest: LocationRule::Indexed {
                location: Box::new(Instruction::Value(ValueBucket {
                    line: 8,
                    message_id: 0,
                    parse_as: ValueType::U32,
                    op_aux_no: 0,
                    value: 1,
                })),
                template_header: None,
            },
            src: Box::new(Instruction::Compute(ComputeBucket{
                line: 12,
                message_id: 0,
                op: OperatorType::Add,
                op_aux_no: 0,
                stack: vec![
                    Box::new(Instruction::Load(LoadBucket{
                        line: 0,
                        message_id: 0,
                        address_type: AddressType::Variable,
                        src: LocationRule::Indexed {
                            location: Box::new(Instruction::Value(ValueBucket {
                                line: 10,
                                message_id: 0,
                                parse_as: ValueType::U32,
                                op_aux_no: 0,
                                value: 1,
                            })),
                            template_header: None,
                        },
                        context: InstrContext { size: 1 },
                    })),
                    Box::new(Instruction::Load(LoadBucket{
                        line: 12,
                        message_id: 0,
                        address_type: AddressType::Signal,
                        src: LocationRule::Indexed {
                            location: Box::new(Instruction::Compute(ComputeBucket{
                                line: 0,
                                message_id: 0,
                                op: OperatorType::AddAddress,
                                op_aux_no: 0,
                                stack: vec![
                                    Box::new(Instruction::Compute(ComputeBucket{
                                        line: 0,
                                        message_id: 0,
                                        op: OperatorType::MulAddress,
                                        op_aux_no: 0,
                                        stack: vec![
                                            Box::new(Instruction::Value(ValueBucket{
                                                line: 0,
                                                message_id: 0,
                                                parse_as: ValueType::U32,
                                                op_aux_no: 0,
                                                value: 1,
                                            })),
                                            Box::new(Instruction::Compute(ComputeBucket{
                                                line: 12,
                                                message_id: 0,
                                                op: OperatorType::ToAddress,
                                                op_aux_no: 0,
                                                stack: vec![
                                                    Box::new(Instruction::Load(LoadBucket{
                                                        line: 12,
                                                        message_id: 0,
                                                        address_type: AddressType::Variable,
                                                        src: LocationRule::Indexed {
                                                            location: Box::new(Instruction::Value(ValueBucket {
                                                                line: 11,
                                                                message_id: 0,
                                                                parse_as: ValueType::U32,
                                                                op_aux_no: 0,
                                                                value: 2,
                                                            })),
                                                            template_header: None,
                                                        },
                                                        context: InstrContext { size: 1 },
                                                    })),
                                                ],
                                            })),
                                        ],
                                    })),
                                    Box::new(Instruction::Value(ValueBucket{
                                        line: 0,
                                        message_id: 0,
                                        parse_as: ValueType::U32,
                                        op_aux_no: 0,
                                        value: 1,
                                    })),
                                ],
                            })),
                            template_header: None,
                        },
                        context: InstrContext { size: 1 },
                    })),
                ],
            })),
        }));

        let constants = vec![];
        let mut line_numbers = vec![];
        let mut components = vec![];
        statement(
            &inst, &mut code, &constants, &mut line_numbers, &mut components,
            &mut FnRegistry::new());

        let var1 = Some(Fr::from(2));
        let var2 = Some(Fr::from(1));
        let c = Component{
            vars: vec![None, var1, var2],
            signals_start: 0,
            template_id: 0,
            subcomponents: vec![],
            number_of_inputs: 0,
        };
        let component = Rc::new(RefCell::new(c));
        let templates = vec![Template{
            name: "test".to_string(),
            code: code,
            line_numbers,
            components,
        }];

        let mut signals = vec![None, None, Some(Fr::from(8))];

        let functions = vec![];

        disassemble(
            &templates[0].code, &templates[0].line_numbers, "test",
            &functions);

        let io_map = BTreeMap::new();

        println!("execute");
        execute(
            component.clone(), &templates, &functions, &constants,
            &mut signals, &io_map, None);
        println!("{:?}", component.borrow().vars);
        assert_eq!(
            &vec![None, Some(Fr::from(10u64)), var2],
            &component.borrow().vars);
    }

    #[test]
    fn statement_3() {
        /*
STORE(
	line:207,
	template_id:69,
	dest_type:SIGNAL,
	dest:INDEXED:(VALUE(line:0,template_id:69,as:U32,op_number:0,value:0),NONE),
	src:LOAD(
		line:207,
		template_id:69,
		address_type:SUBCOMPONENT:VALUE(line:0,template_id:69,as:U32,op_number:0,value:0):NO_INPUT,
		src:INDEXED:(VALUE(line:0,template_id:68,as:U32,op_number:0,value:0),PoseidonEx_68),
		size:1
	),
	size:1
)
         */
        let inst = Box::new(Instruction::Store(StoreBucket {
            line: 207,
            message_id: 0,
            context: InstrContext { size: 1 },
            dest_is_output: false,
            dest_address_type: AddressType::Signal,
            dest: LocationRule::Indexed {
                location: Box::new(Instruction::Value(ValueBucket {
                    line: 0,
                    message_id: 0,
                    parse_as: ValueType::U32,
                    op_aux_no: 0,
                    value: 0,
                })),
                template_header: None,
            },
            src: Box::new(Instruction::Load(LoadBucket {
                line: 207,
                message_id: 0,
                address_type: AddressType::SubcmpSignal {
                    cmp_address: Box::new(Instruction::Value(ValueBucket {
                        line: 0,
                        message_id: 0,
                        parse_as: ValueType::U32,
                        op_aux_no: 0,
                        value: 0,
                    })),
                    uniform_parallel_value: None,
                    is_output: false,
                    input_information: InputInformation::NoInput,
                },
                src: LocationRule::Indexed {
                    location: Box::new(Instruction::Value(ValueBucket {
                        line: 0,
                        message_id: 0,
                        parse_as: ValueType::U32,
                        op_aux_no: 0,
                        value: 0,
                    })),
                    template_header: None },
                context: InstrContext { size: 1 },
            })),
        }));

        let mut code = vec![];
        let constants = vec![];
        let mut line_numbers = vec![];
        let mut components = vec![];
        let functions = vec![];
        statement(
            &inst, &mut code, &constants, &mut line_numbers, &mut components,
            &mut FnRegistry::new());
        disassemble(&code, &line_numbers, "test", &functions);
    }

    #[test]
    fn ok() {
        type B = BigInteger256;

        let a = Fr::from(5u64);

        let b: B = a.into_bigint();
        let x = a.into_bigint().to_bytes_le();
        let a2: Fr = b.try_into().unwrap();
        println!("{:?}", x);
        println!("{:?}", b.0);
        println!("{}", a2 - a2);
        println!("{}", B::NUM_LIMBS);

        let x = B::from(3u32);
        let y = B::from(5u32);
        let x2: Fr = x.try_into().unwrap();
        let y2: Fr = y.try_into().unwrap();
        println!("{:?}", x.to_bytes_le());
    }

    #[test]
    fn test_bigint_to_u64() {
        let mut i = BigInteger256::from(u64::MAX);
        let j = bigint_to_u64(i);
        assert!(matches!(j, Some(u64::MAX)));

        i.mul2();
        let j = bigint_to_u64(i);
        assert!(matches!(j, None));
    }

    #[test]
    fn test_jump_if_false_backward() {
        let noop = OpCode::NoOp as u8;
        let mut code = vec![];
        code.push(noop);
        let to = code.len();
        code.push(noop);
        let jump_offset = pre_emit_jump_if_false(&mut code);

        assert_eq!(code, vec![noop, noop, OpCode::JumpIfFalse as u8, 0xff, 0xff, 0xff, 0xff]);
        assert_eq!(jump_offset, 3);

        patch_jump(&mut code, jump_offset, to);
        assert_eq!(code, vec![noop, noop, OpCode::JumpIfFalse as u8, 0xfa, 0xff, 0xff, 0xff]);
        assert_eq!(-6, i32::from_le_bytes(code[jump_offset..jump_offset+4].try_into().unwrap()));
    }
    #[test]
    fn test_jump_if_false_forward() {
        let noop = OpCode::NoOp as u8;
        let jmp = OpCode::JumpIfFalse as u8;
        let mut code = vec![];
        code.push(noop);
        let jump_offset = pre_emit_jump_if_false(&mut code);
        assert_eq!(code, vec![noop, jmp, 0xff, 0xff, 0xff, 0xff]);
        assert_eq!(jump_offset, 2);

        code.push(noop);
        code.push(noop);
        let to = code.len();
        assert_eq!(8, to);
        code.push(noop);

        patch_jump(&mut code, jump_offset, to);
        assert_eq!(code, vec![noop, jmp, 0x02, 0x00, 0x00, 0x00, noop, noop, noop, ]);
        assert_eq!(2, i32::from_le_bytes(code[jump_offset..jump_offset+4].try_into().unwrap()));
    }

    // TODO: useless test for printing purposes. Maybe remove it.
    #[test]
    fn test_set_variable() {
        let noop = OpCode::NoOp as u8;
        let code = vec![
            OpCode::Push8 as u8, 0, 0, 0, 0, 0, 0, 0, 0,
            OpCode::JumpIfFalse as u8, 9*2, 0x00, 0x00, 0x00,
            OpCode::Push8 as u8, 0x01, 0, 0, 0, 0, 0, 0, 0,
            OpCode::SetVariable4 as u8, 0, 0, 0, 0, 1, 0, 0, 0,
            OpCode::Push8 as u8, 0x02, 0, 0, 0, 0, 0, 0, 0,
            OpCode::SetVariable4 as u8, 1, 0, 0, 0, 1, 0, 0, 0,
            OpCode::NoOp as u8,
        ];
        let mut line_numbers = Vec::with_capacity(code.len());
        for (i, _) in code.iter().enumerate() {
            line_numbers.push(i);
        }

        let functions = vec![];

        disassemble(&code, &line_numbers, "test", &functions);
        println!("execute");

        let c = Component{
            vars: vec![],
            signals_start: 0,
            template_id: 0,
            subcomponents: vec![],
            number_of_inputs: 0,
        };
        let component = Rc::new(RefCell::new(c));
        let templates = vec![Template {
            name: "test".to_string(),
            code: code.clone(),
            line_numbers,
            components: vec![],
        }];
        let constants = vec![];
        let mut signals = vec![None; 10];
        let io_map = BTreeMap::new();
        execute(
            component.clone(), &templates, &functions, &constants,
            &mut signals, &io_map, None);
        println!("{:?}", &component.borrow().vars);
    }

    #[test]
    fn test_dump() {
        let noop = OpCode::NoOp as u8;
        let mut code = vec![];
        code.push(noop);
        let c = Component{
            vars: vec![],
            signals_start: 0,
            template_id: 0,
            subcomponents: vec![],
            number_of_inputs: 0,
        };
        let component = Rc::new(RefCell::new(c));
        let templates = vec![Template{
            name: "test".to_string(),
            code: code.clone(),
            line_numbers: vec![0],
            components: vec![],
        }];
        let constants = vec![];
        let mut signals = vec![None; 10];
        let io_map = BTreeMap::new();
        execute(
            component, &templates, &vec![], &constants, &mut signals,
            &io_map, None);
    }

    fn names_from_fn_vec(fns: &Vec<Function>) -> Vec<String> {
        fns.iter().map(|f| f.name.clone()).collect()
    }

    fn mk_empty_fun(name: &str, symbol: &str) -> Function {
        Function {
            name: name.to_string(),
            symbol: symbol.to_string(),
            code: vec![],
            line_numbers: vec![],
        }
    }

    #[test]
    fn test_fn_registry_sort() {
        let mut reg = FnRegistry::new();
        assert_eq!(0, reg.get("ssigma1_1"));
        assert_eq!(1, reg.get("ssigma0_2"));
        assert_eq!(2, reg.get("bsigma1_3"));
        assert_eq!(3, reg.get("Ch_4"));
        assert_eq!(4, reg.get("sha256K_5"));
        assert_eq!(5, reg.get("bsigma0_6"));
        assert_eq!(6, reg.get("Maj_7"));
        assert_eq!(7, reg.get("rrot_8"));
        assert_eq!(8, reg.get("sha256compression_0"));

        let mut fns: Vec<Function> = vec![
            mk_empty_fun("sha256compression", "sha256compression_0"),
            mk_empty_fun("ssigma1", "ssigma1_1"),
            mk_empty_fun("ssigma0", "ssigma0_2"),
            mk_empty_fun("bsigma1", "bsigma1_3"),
            mk_empty_fun("Ch", "Ch_4"),
            mk_empty_fun("sha256K", "sha256K_5"),
            mk_empty_fun("bsigma0", "bsigma0_6"),
            mk_empty_fun("Maj", "Maj_7"),
            mk_empty_fun("rrot", "rrot_8"),
        ];

        let want = vec![
            "ssigma1".to_string(),
            "ssigma0".to_string(),
            "bsigma1".to_string(),
            "Ch".to_string(),
            "sha256K".to_string(),
            "bsigma0".to_string(),
            "Maj".to_string(),
            "rrot".to_string(),
            "sha256compression".to_string(),
        ];

        reg.sort(&mut fns);
        assert_eq!(want, names_from_fn_vec(&fns));
    }
}