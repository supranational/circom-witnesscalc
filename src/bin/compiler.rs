use std::{env, fs};
use std::path::PathBuf;
use core::convert::TryInto;
use core::str::FromStr;
use std::cell::RefCell;
use std::cmp::Ordering;
use std::fmt::Display;
use std::fs::File;
use std::io::Write;
use std::rc::Rc;
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
use compiler::intermediate_representation::ir_interface::{AddressType, ComputeBucket, CreateCmpBucket, InputInformation, Instruction, InstructionPointer, LoadBucket, LocationRule, ObtainMeta, OperatorType, StatusInput, ValueType};
use constraint_generation::{build_circuit, BuildConfig};
use program_structure::error_definition::Report;
use type_analysis::check_types::check_types;
use wtns_file::FieldElement;
use circom_witnesscalc::{deserialize_inputs};
use circom_witnesscalc::graph::Operation;

struct Args {
    circuit_file: String,
    inputs_file: Option<String>,
    graph_file: String,
    link_libraries: Vec<PathBuf>,
    print_debug: bool,
    witness_file: Option<String>,
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

struct VM<'a> {
    templates: Vec<Template>,
    signals: &'a mut [Option<Fr>],
    constants: &'a Vec<Fr>,
    stack: Vec<Fr>,
    stack_u32: Vec<u32>,
}

impl VM<'_> {
    fn print_stack(&self) {
        for (i, s) in self.stack.iter().enumerate() {
            let s = if s.is_zero() { String:: from("0") } else { s.to_string() };
            println!("{:04x}: {}", i, s);
        }
    }
}

#[repr(u8)]
#[derive(Debug)]
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
    GetVariable4   =  3,
    GetVariable    =  4,
    SetVariable4   =  5,
    SetVariable    =  6,
    // Put signals to the stack
    // arguments: signal index u32, signals number u32
    GetSelfSignal4 =  7,
    // Put signals to the stack
    // arguments:      signals number u32
    // required stack: signal index
    GetSelfSignal  =  8,
    SetSelfSignal4 =  9,
    SetSelfSignal  = 10,
    // arguments:      subcomponent index u32; signal index u32
    GetSubSignal4  = 11,
    // arguments:      subcomponent index u32
    // required stack: signal index
    GetSubSignal   = 12,
    // arguments:      subcomponent index u32; signal index u32; signals number u32; InputStatus
    // required stack: value to store
    SetSubSignal4  = 13,
    // arguments:      subcomponent index u32, signals number u32; InputStatus
    // required stack: signal index; value to store
    SetSubSignal   = 14,
    JumpIfFalse    = 15, // Jump to the offset i32 if the value on the top of the stack is false
    Jump           = 16, // Jump to the offset i32
    OpMul          = 17,
    OpDiv          = 18,
    OpAdd          = 19,
    OpShR          = 20,
    OpLt           = 21,
    OpGt           = 22,
    OpEq           = 23,
    OpNe           = 24,
    OpBAnd         = 25,
    OpNeg          = 26,
}

#[derive(Debug)]
enum CompilationError {
    ValueTooLarge,
    NotAnExpression(String),
}

enum U32OrExpression {
    U32(u32),
    Expression,
}

fn u32_or_expression(inst: &InstructionPointer, constants: &[Fr], max: Option<Fr>) -> Result<U32OrExpression, CompilationError> {
    match **inst {
        Instruction::Value(ref value) => {
            match value.parse_as {
                ValueType::U32 => {
                    if let Some(max) = max {
                        if Fr::from(value.value as u64) > max {
                            return Err(CompilationError::ValueTooLarge);
                        }
                    }
                    if value.value > u32::MAX as usize {
                        return Ok(U32OrExpression::Expression);
                    }
                    Ok(U32OrExpression::U32(value.value as u32))
                },
                ValueType::BigInt => {
                    let v = constants[value.value];
                    if let Some(max) = max {
                        if v > max {
                            return Err(CompilationError::ValueTooLarge);
                        }
                    }
                    let v64 = match bigint_to_u64(v.into_bigint()) {
                        Some(v) => v,
                        None => return Ok(U32OrExpression::Expression),
                    };
                    if v64 > u32::MAX as u64 {
                        return Ok(U32OrExpression::Expression);
                    }
                    Ok(U32OrExpression::U32(v64 as u32))
                },
            }
        }
        Instruction::Load(_) => Ok(U32OrExpression::Expression),
        Instruction::Compute(ref compute_bucket) => {
            let r = match compute_bucket.op {
                OperatorType::Mul => {todo!()}
                OperatorType::Div => {todo!()}
                OperatorType::Add => {todo!()}
                OperatorType::Sub => {todo!()}
                OperatorType::Pow => {todo!()}
                OperatorType::IntDiv => {todo!()}
                OperatorType::Mod => {todo!()}
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
                    let a = match u32_or_expression(&compute_bucket.stack[0], constants, max)? {
                        U32OrExpression::U32(v) => v,
                        U32OrExpression::Expression => { return Ok(U32OrExpression::Expression) }
                    };
                    a as u64
                }
                OperatorType::MulAddress => {
                    assert_eq!(2, compute_bucket.stack.len());
                    let a = match u32_or_expression(&compute_bucket.stack[0], constants, max)? {
                        U32OrExpression::U32(v) => v,
                        U32OrExpression::Expression => { return Ok(U32OrExpression::Expression) }
                    };
                    let b = match u32_or_expression(&compute_bucket.stack[1], constants, max)? {
                        U32OrExpression::U32(v) => v,
                        U32OrExpression::Expression => { return Ok(U32OrExpression::Expression) }
                    };
                    a as u64 * b as u64
                }
                OperatorType::AddAddress => {
                    assert_eq!(2, compute_bucket.stack.len());
                    let a = match u32_or_expression(&compute_bucket.stack[0], constants, max)? {
                        U32OrExpression::U32(v) => v,
                        U32OrExpression::Expression => { return Ok(U32OrExpression::Expression) }
                    };
                    let b = match u32_or_expression(&compute_bucket.stack[1], constants, max)? {
                        U32OrExpression::U32(v) => v,
                        U32OrExpression::Expression => { return Ok(U32OrExpression::Expression) }
                    };
                    a as u64 + b as u64
                }
            };

            if let Some(max) = max {
                if Fr::from(r) > max {
                    return Err(CompilationError::ValueTooLarge);
                }
            }

            if r > u32::MAX as u64 {
                return Ok(U32OrExpression::Expression);
            }

            Ok(U32OrExpression::U32(r as u32))
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
    }
}


fn main() {
    let args = parse_args();

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
        if args.print_debug {
            println!("Template #{}: {}", i, t.name);
        }
    }

    let constants = get_constants(&circuit);

    let main_component_signal_start = 1usize;
    let compiled_templates = compile(
        &circuit.templates, &circuit.functions,
        circuit.c_producer.get_io_map(), &constants);

    for (i, t) in compiled_templates.iter().enumerate() {
        println!("Compiled template #{}: {}", i, t.name);

        // for c in &t.code {
        //     println!("{:02x} ", c);
        // }

        disassemble(&t.code, &t.line_numbers);
    }


    if let Some(input_file) = args.inputs_file {

        let main_component = build_component(
            &compiled_templates, &circuit.templates, main_template_id,
            main_component_signal_start);
        let main_component = Rc::new(RefCell::new(main_component));

        let sigs_num = circuit.c_producer.get_total_number_of_signals();
        let mut signals = Vec::new();
        signals.resize(sigs_num, None);
        init_input_signals(&circuit, input_file, &mut signals);

        println!("Run VM");
        execute(
            main_component, &compiled_templates, &constants,
            &mut signals);

        if let Some(witness_file) = args.witness_file {
            let mut witness = Vec::with_capacity(witness_list.len());
            for (i, w) in witness_list.iter().enumerate() {
                println!("w: {}",
                         signals[*w]
                             .expect(
                                 format!("signal at {} is not set", i).as_str())
                             .to_string());
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

struct Frame<'a> {
    ip: usize,
    code: &'a [u8],
    component: Rc<RefCell<Component>>,
}

impl Frame<'_> {
    fn new(component: Rc<RefCell<Component>>, templates: &[Template]) -> Frame {
        let template_id = component.borrow().template_id;
        Frame {
            ip: 0,
            code: &templates[template_id].code,
            component,
        }
    }
}

fn execute(
    component: Rc<RefCell<Component>>, templates: &Vec<Template>, constants: &Vec<Fr>,
    signals: &mut [Option<Fr>]) {

    let mut vm = VM {
        templates: vec![],
        signals,
        constants,
        stack: vec![],
        stack_u32: vec![],
    };

    let mut call_frames: Vec<Frame> =
        vec![Frame::new(component.clone(), templates)];

    let mut ip = 0usize;
    let mut code: &[u8] = call_frames.last().unwrap().code;
    let mut template_id: usize = call_frames.last().unwrap().component.borrow().template_id;
    let mut signals_start = call_frames.last().unwrap().component.borrow().signals_start;

    loop {
        if ip == code.len() {
            call_frames.pop();
            if call_frames.is_empty() {
                break;
            }

            let last_frame = call_frames.last().unwrap();
            ip = last_frame.ip;
            template_id = last_frame.component.borrow().template_id;
            code = &templates[template_id].code;
            signals_start = last_frame.component.borrow().signals_start;
        }

        {
            // TODO wrap into `if debug` condition
            let line_numbers =
                &templates[template_id].line_numbers;
            disassemble_instruction(code, line_numbers, ip);
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
                    if vm.signals[sig_idx].is_some() {
                        panic!("Signal already set");
                    }
                    vm.signals[sig_idx] = Some(vm.stack.pop().unwrap());
                }
            }
            OpCode::SetSelfSignal => {
                let cmp_signal_offset = vm.stack.pop().unwrap();
                let cmp_signal_offset = bigint_to_u64(
                    cmp_signal_offset.into_bigint())
                    .expect("Signal index is too large");
                let cmp_signal_offset = usize::try_from(cmp_signal_offset)
                    .expect("Signal index is too large");

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
                    if vm.signals[sig_idx].is_some() {
                        panic!("Signal already set");
                    }
                    vm.signals[sig_idx] = Some(vm.stack.pop().unwrap());
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

                let last_frame = call_frames.last().unwrap();
                let vars = &mut last_frame.component.borrow_mut().vars;

                if vars.len() < var_end {
                    panic!("Variable is not set as {}", var_end-1);
                }

                for var_idx in (var_start..var_end).rev() {
                    if vars[var_idx].is_none() {
                        panic!("Variable not set");
                    }
                    vm.stack.push(vars[var_idx].unwrap());
                }
            }
            OpCode::GetVariable => {
                let var_idx = vm.stack.pop().unwrap();
                let var_idx = bigint_to_u64(
                    var_idx.into_bigint())
                    .expect("Variable index is too large");
                let var_idx = usize::try_from(var_idx).unwrap();

                let vars_number = read_u32(code, ip);
                ip += size_of::<u32>();

                let last_frame = call_frames.last().unwrap();
                let vars = &mut last_frame.component.borrow_mut().vars;

                if vars.len() <= var_idx+vars_number as usize {
                    panic!("Variable not set")
                }

                for i in var_idx..var_idx+vars_number as usize {
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

                let last_frame = call_frames.last().unwrap();
                let vars = &mut last_frame.component.borrow_mut().vars;

                if vars.len() < var_end {
                    vars.resize(var_end, None);
                }

                for var_idx in (var_start..var_end).rev() {
                    println!("Set variable {}", var_idx);
                    vars[var_idx] = Some(vm.stack.pop().unwrap());
                }
            }
            OpCode::SetVariable => {
                let var_start = vm.stack.pop().unwrap();
                let var_start = bigint_to_u64(
                    var_start.into_bigint())
                    .expect("Variable index is too large");
                let var_start = usize::try_from(var_start).unwrap();

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

                let last_frame = call_frames.last().unwrap();
                let vars =
                    &mut last_frame.component.borrow_mut().vars;

                if vars.len() < var_end {
                    vars.resize(var_end, None);
                }

                for var_idx in (var_start..var_end).rev() {
                    vars[var_idx] = Some(vm.stack.pop().unwrap());
                }
            }
            OpCode::GetSubSignal4 => {
                let cmp_idx = read_u32(code, ip);
                ip += size_of::<u32>();

                let sig_idx = read_u32(code, ip);
                ip += size_of::<u32>();

                let sigs_number = read_u32(code, ip);
                ip += size_of::<u32>();

                let subcmp_signals_start = call_frames.last().unwrap()
                    .component.borrow()
                    .subcomponents[cmp_idx as usize].borrow()
                    .signals_start;
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
            OpCode::GetSubSignal => {
                todo!();
            }
            OpCode::SetSubSignal4 => {
                let cmp_idx = read_u32(code, ip);
                ip += size_of::<u32>();

                let sig_idx = read_u32(code, ip);
                ip += size_of::<u32>();

                let sigs_number = read_u32(code, ip);
                ip += size_of::<u32>();

                if sigs_number as usize > vm.stack.len() {
                    panic!("Number of signals is greater than the stack depth");
                }

                let input_status =
                    InputStatus::try_from(code[ip]).unwrap();
                ip += 1;

                let cmp = call_frames.last().unwrap()
                    .component.clone();
                let should_call_cmp = {
                    let cmp = cmp.borrow();
                    let mut subcmp = cmp
                        .subcomponents[cmp_idx as usize].borrow_mut();

                    if sigs_number as usize > subcmp.number_of_inputs {
                        panic!("Number of signals is greater than the number of inputs left");
                    }

                    let (sig_start, overflowed) =
                        subcmp.signals_start.overflowing_add(sig_idx as usize);

                    if overflowed {
                        panic!("Subcomponent signal index is too large");
                    }

                    let (sig_end, overflowed) =
                        sig_start.overflowing_add(sigs_number as usize);

                    if overflowed || sig_end > vm.signals.len() {
                        panic!("Subcomponent signal index is too large");
                    }

                    for sig_idx in (sig_start..sig_end).rev() {
                        if vm.signals[sig_idx].is_some() {
                            panic!("Subcomponent signal is already set");
                        }

                        vm.signals[sig_idx] = Some(vm.stack.pop().unwrap());
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
                    call_frames.last_mut().unwrap().ip = ip;
                    call_frames.push(
                        Frame::new(
                            cmp.borrow().subcomponents[cmp_idx as usize].clone(),
                            templates));

                    ip = 0usize;
                    code = call_frames.last().unwrap().code;
                    template_id = call_frames.last().unwrap().component.borrow().template_id;
                    signals_start = call_frames.last().unwrap().component.borrow().signals_start;
                }
            }
            OpCode::SetSubSignal => {

                let cmp_idx = read_u32(code, ip);
                ip += size_of::<u32>();

                let sigs_number = read_u32(code, ip);
                ip += size_of::<u32>();

                let input_status =
                    InputStatus::try_from(code[ip]).unwrap();
                ip += 1;

                let sig_idx = vm.stack.pop().unwrap();
                let sig_idx = bigint_to_u64(
                    sig_idx.into_bigint())
                    .expect("Signal index does not fits into u64");
                let sig_idx = usize::try_from(sig_idx).unwrap();

                let cmp = call_frames.last().unwrap()
                    .component.clone();
                let should_call_cmp = {
                    let cmp = cmp.borrow();
                    let mut subcmp = cmp
                        .subcomponents[cmp_idx as usize].borrow_mut();

                    let (sigs_start, overflowed) =
                        subcmp.signals_start.overflowing_add(sig_idx);

                    if overflowed || sigs_start >= vm.signals.len() {
                        panic!("Subcomponent signal start index is too large");
                    }

                    let (sigs_end, overflowed) =
                        sigs_start.overflowing_add(sigs_number as usize);

                    if overflowed || sigs_end > vm.signals.len() {
                        panic!("Subcomponent signal end index is too large");
                    }

                    for sig_idx in sigs_start..sigs_end {
                        if vm.signals[sig_idx].is_some() {
                            panic!("Subcomponent signal is already set");
                        }

                        vm.signals[sig_idx] = Some(vm.stack.pop().unwrap());
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
                    call_frames.last_mut().unwrap().ip = ip;
                    call_frames.push(
                        Frame::new(
                            cmp.borrow().subcomponents[cmp_idx as usize].clone(),
                            templates));

                    ip = 0usize;
                    code = call_frames.last().unwrap().code;
                    template_id = call_frames.last().unwrap().component.borrow().template_id;
                    signals_start = call_frames.last().unwrap().component.borrow().signals_start;
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
            OpCode::OpShR => {
                let b = vm.stack.pop().unwrap();
                let a = vm.stack.pop().unwrap();
                vm.stack.push(Operation::Shr.eval_fr(a, b));
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
            OpCode::OpBAnd => {
                let b = vm.stack.pop().unwrap();
                let a = vm.stack.pop().unwrap();
                let ai = b.into_bigint();
                let bi = b.into_bigint();
                let mut r: BigInt<4> = BigInt!("0");
                for i in 0..r.0.len() {
                    r.0[i] = ai.0[i] & bi.0[i];
                }
                if r > Fr::MODULUS {
                    r.sub_with_borrow(&Fr::MODULUS);
                }
                vm.stack.push(Fr::from(r));
            }
            OpCode::OpNeg => {
                let a = vm.stack.pop().unwrap();
                let mut x = Fr::MODULUS;
                x.sub_with_borrow(&a.into_bigint());
                vm.stack.push(Fr::from(x));
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
                let cmp_signal_offset = vm.stack.pop().unwrap();
                let cmp_signal_offset = bigint_to_u64(
                    cmp_signal_offset.into_bigint())
                    .expect("Signal index is too large");
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
        }

        println!("==[ Stack ]==");
        vm.print_stack();
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

// After statement execution, there should not be side-effect on the stack
fn statement(
    inst: &InstructionPointer, code: &mut Vec<u8>, constants: &[Fr],
    line_numbers: &mut Vec<usize>, components: &mut Vec<ComponentTmpl>,
    io_map: &TemplateInstanceIOMap) {

    println!("statement: {}", inst.to_string());

    match **inst {
        Instruction::Store(ref store_bucket) => {

            expression(
                &store_bucket.src, code, constants, line_numbers, components,
                io_map);
            assert_eq!(line_numbers.len(), code.len());

            match store_bucket.dest_address_type {
                AddressType::Variable => {
                    let location = if let LocationRule::Indexed{ref location, ..} = store_bucket.dest {
                        location
                    } else {
                        panic!("Variable destination should be of Indexed type");
                    };

                    let var_idx = u32_or_expression(
                        location, constants, Some(Fr::from(u32::MAX)))
                        .unwrap();

                    match var_idx {
                        U32OrExpression::U32(var_idx) => {
                            code.push(OpCode::SetVariable4 as u8);
                            line_numbers.push(store_bucket.line);
                            code.extend_from_slice(var_idx.to_le_bytes().as_ref());
                            for _ in 0..4 { line_numbers.push(usize::MAX); }
                        }
                        U32OrExpression::Expression => {
                            expression(
                                location, code, constants, line_numbers,
                                components, io_map);
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

                    let sig_idx = u32_or_expression(
                        location, constants, Some(Fr::from(u32::MAX)))
                        .unwrap();

                    match sig_idx {
                        U32OrExpression::U32(sig_idx) => {
                            code.push(OpCode::SetSelfSignal4 as u8);
                            line_numbers.push(store_bucket.line);
                            code.extend_from_slice(sig_idx.to_le_bytes().as_ref());
                            for _ in 0..4 { line_numbers.push(usize::MAX); }
                        }
                        U32OrExpression::Expression => {
                            expression(
                                location, code, constants, line_numbers,
                                components, io_map);
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
                    println!("calc expression: {}", cmp_address.to_string()); // TODO remove
                    let cmp_idx = u32_or_expression(
                        cmp_address, constants, Some(Fr::from(u32::MAX)));
                    let cmp_idx = match cmp_idx {
                        Ok(ref cmp_idx) => {
                            match cmp_idx {
                                U32OrExpression::U32(cmp_idx) => cmp_idx,
                                U32OrExpression::Expression => {
                                    panic!(
                                        "Subcomponent index suppose to be \
                                        a constant");
                                }
                            }
                        }
                        Err(e) => {
                            panic!("Error: {:?}", e);
                        }
                    };

                    match store_bucket.dest {
                        LocationRule::Indexed { ref location, .. } => {
                            let sig_idx = u32_or_expression(
                                location, constants, Some(Fr::from(u32::MAX)))
                                .unwrap();

                            match sig_idx {
                                U32OrExpression::U32(sig_idx) => {
                                    code.push(OpCode::SetSubSignal4 as u8);
                                    line_numbers.push(store_bucket.line);

                                    code.extend_from_slice(cmp_idx.to_le_bytes().as_ref());
                                    for _ in 0..4 { line_numbers.push(usize::MAX); }

                                    code.extend_from_slice(sig_idx.to_le_bytes().as_ref());
                                    for _ in 0..4 { line_numbers.push(usize::MAX); }
                                }
                                U32OrExpression::Expression => {
                                    expression(
                                        location, code, constants, line_numbers,
                                        components, io_map);

                                    code.push(OpCode::SetSubSignal as u8);
                                    line_numbers.push(store_bucket.line);

                                    code.extend_from_slice(cmp_idx.to_le_bytes().as_ref());
                                    for _ in 0..4 { line_numbers.push(usize::MAX); }
                                }
                            };
                        }
                        LocationRule::Mapped { ref signal_code, ref indexes } => {
                            // copy the logic of calc_mapped_signal_idx

                            let sig_idx = calc_mapped_signal_idx(
                                *signal_code, indexes, *cmp_idx as usize,
                                io_map, components);

                            match sig_idx {
                                U32OrExpression::U32(sig_idx) => {
                                    code.push(OpCode::SetSubSignal4 as u8);
                                    line_numbers.push(store_bucket.line);

                                    code.extend_from_slice(cmp_idx.to_le_bytes().as_ref());
                                    for _ in 0..4 { line_numbers.push(usize::MAX); }

                                    code.extend_from_slice(sig_idx.to_le_bytes().as_ref());
                                    for _ in 0..4 { line_numbers.push(usize::MAX); }
                                }
                                U32OrExpression::Expression => {
                                    expression_mapped_signal_idx(
                                        code, constants, line_numbers, *signal_code,
                                        indexes, *cmp_idx as usize, io_map, components);

                                    code.push(OpCode::SetSubSignal as u8);
                                    line_numbers.push(store_bucket.line);

                                    code.extend_from_slice(cmp_idx.to_le_bytes().as_ref());
                                    for _ in 0..4 { line_numbers.push(usize::MAX); }
                                }
                            };
                        }
                    };

                    let signals_num: u32 = store_bucket.context.size
                        .try_into().expect("Too many signals");
                    code.extend_from_slice(signals_num.to_le_bytes().as_ref());
                    for _ in 0..4 { line_numbers.push(usize::MAX); }

                    let input_status = if let InputInformation::Input{ status } = input_information {
                        status
                    } else {
                        panic!("Can't store signal to non-input subcomponent");
                    };

                    let ii: InputStatus = input_status.into();
                    code.push(ii.into());
                    line_numbers.push(usize::MAX);
                }
            }
            assert_eq!(line_numbers.len(), code.len());
        }
        Instruction::Loop(ref loop_bucket) => {
            let loop_start = code.len();

            expression(
                &loop_bucket.continue_condition, code, constants, line_numbers,
                components, io_map);

            let loop_end_jump_offset = pre_emit_jump_if_false(code);
            line_numbers.push(loop_bucket.line);
            line_numbers.push(usize::MAX);
            line_numbers.push(usize::MAX);
            line_numbers.push(usize::MAX);
            line_numbers.push(usize::MAX);

            block(
                &loop_bucket.body, code, constants, line_numbers, components,
                io_map);

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
                &cmp_bucket.sub_cmp_id, constants, Some(Fr::from(u32::MAX)))
                .unwrap();

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

            println!("{}", fmt_create_cmp_bucket(cmp_bucket, sub_cmp_idx));

            if !cmp_bucket.has_inputs {
                todo!("We should insert here a direct instruction to call this component")
            }
        }
        Instruction::Call(ref _call_bucket) => {
            // pass
            todo!()
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
                &branch_bucket.cond, code, constants, line_numbers, components,
                io_map);

            let else_jump_offset = pre_emit_jump_if_false(code);
            line_numbers.push(branch_bucket.line);
            for _ in 0..4 { line_numbers.push(usize::MAX); }

            block(
                &branch_bucket.if_branch, code, constants, line_numbers,
                components, io_map);

            let end_jump_offset = pre_emit_jump(code);
            line_numbers.push(branch_bucket.line);
            for _ in 0..4 { line_numbers.push(usize::MAX); }

            let to = code.len();
            patch_jump(code, else_jump_offset, to);

            block(
                &branch_bucket.else_branch, code, constants, line_numbers,
                components, io_map);

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

fn calc_mapped_signal_idx(
    signal_code: usize, indexes: &[InstructionPointer], sub_cmp_idx: usize,
    io_map: &TemplateInstanceIOMap,
    components: &mut Vec<ComponentTmpl>) -> U32OrExpression {

    let mut template_id = components[0].template_id;
    for e in &components[1..] {
        if e.sub_cmp_idx > sub_cmp_idx {
            break;
        }
        template_id = e.template_id;
    }

    let signals = io_map.get(&template_id).unwrap();
    let def = &signals[signal_code];
    let mut sig_idx: u32 = def.offset.try_into()
        .expect("Signal index is too large");

    if indexes.is_empty() {
        panic!("test this");
        return U32OrExpression::U32(sig_idx);
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
        let idx_value = u32_or_expression(
            idx_ip, &[], Some(Fr::from(u32::MAX)))
            .unwrap();
        let idx_value = match idx_value {
            U32OrExpression::U32(idx_value) => idx_value,
            U32OrExpression::Expression => {
                return U32OrExpression::Expression;
            }
        };

        let (s, mut overflow) = idx_value.overflowing_mul(strides[i]);
        if overflow {
            panic!("Index is too large");
        }
        (sig_idx, overflow) = sig_idx.overflowing_add(s);
        if overflow {
            panic!("Signal index is too large");
        }
    }

    return U32OrExpression::U32(sig_idx);
}

fn expression_mapped_signal_idx(
    code: &mut Vec<u8>, constants: &[Fr], line_numbers: &mut Vec<usize>,
    signal_code: usize, indexes: &[InstructionPointer], sub_cmp_idx: usize,
    io_map: &TemplateInstanceIOMap,
    components: &mut Vec<ComponentTmpl>) {

    let mut template_id = components[0].template_id;
    for e in &components[1..] {
        if e.sub_cmp_idx > sub_cmp_idx {
            break;
        }
        template_id = e.template_id;
    }

    let signals = io_map.get(&template_id).unwrap();
    let def = &signals[signal_code];
    let mut sig_idx: u32 = def.offset.try_into()
        .expect("Signal index is too large");

    // TODO replace with short push to stack_u32
    code.push(OpCode::Push8 as u8);
    line_numbers.push(usize::MAX);
    assert_64();
    code.extend_from_slice(def.offset.to_le_bytes().as_ref());
    for _ in 0..8 { line_numbers.push(usize::MAX); }

    if indexes.is_empty() {
        return
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
        expression(
            idx_ip, code, constants, line_numbers, components, io_map);

        code.push(OpCode::Push8 as u8);
        line_numbers.push(idx_ip.get_line());
        assert_64();
        code.extend_from_slice((strides[i] as usize).to_le_bytes().as_ref());
        for _ in 0..8 { line_numbers.push(usize::MAX); }

        // TODO: replace with Address multiply
        code.push(OpCode::OpMul as u8);
        line_numbers.push(idx_ip.get_line());

        // TODO: replace with Address add
        code.push(OpCode::OpAdd as u8);
        line_numbers.push(idx_ip.get_line());
    }
}

fn expression_load(
    lb: &LoadBucket, code: &mut Vec<u8>, constants: &[Fr],
    line_numbers: &mut Vec<usize>, components: &mut Vec<ComponentTmpl>,
    io_map: &TemplateInstanceIOMap) {

    match lb.address_type {
        AddressType::Signal => {
            let location = if let LocationRule::Indexed{ref location, ..} = lb.src {
                location
            } else {
                panic!("Signal source location should be of Indexed type");
            };

            let idx = u32_or_expression(
                location, constants, Some(Fr::from(u32::MAX)))
                .unwrap();

            match idx {
                U32OrExpression::U32(idx) => {
                    code.push(OpCode::GetSelfSignal4 as u8);
                    line_numbers.push(lb.line);
                    code.extend_from_slice(idx.to_le_bytes().as_ref());
                    for _ in 0..4 { line_numbers.push(usize::MAX); }
                }
                U32OrExpression::Expression => {
                    expression(
                        location, code, constants, line_numbers, components,
                        io_map);
                    code.push(OpCode::GetSelfSignal as u8);
                    line_numbers.push(lb.line);
                }
            }
        }
        AddressType::SubcmpSignal { ref cmp_address, ref input_information, .. } => {

            let cmp_idx = u32_or_expression(
                cmp_address, constants, Some(Fr::from(u32::MAX)));
            let cmp_idx = match cmp_idx {
                Ok(ref cmp_idx) => {
                    match cmp_idx {
                        U32OrExpression::U32(cmp_idx) => cmp_idx,
                        U32OrExpression::Expression => {
                            panic!(
                                "Subcomponent index suppose to be a constant");
                        }
                    }
                }
                Err(e) => {
                    panic!("Error: {:?}", e);
                }
            };

            match lb.src {
                LocationRule::Indexed { ref location, .. } => {
                    let sig_idx = u32_or_expression(
                        location, constants, Some(Fr::from(u32::MAX)))
                        .unwrap();

                    match sig_idx {
                        U32OrExpression::U32(sig_idx) => {
                            code.push(OpCode::GetSubSignal4 as u8);
                            line_numbers.push(lb.line);

                            code.extend_from_slice(cmp_idx.to_le_bytes().as_ref());
                            for _ in 0..4 { line_numbers.push(usize::MAX); }

                            code.extend_from_slice(sig_idx.to_le_bytes().as_ref());
                            for _ in 0..4 { line_numbers.push(usize::MAX); }
                        }
                        U32OrExpression::Expression => {
                            expression(
                                location, code, constants, line_numbers,
                                components, io_map);

                            code.push(OpCode::GetSubSignal as u8);
                            line_numbers.push(lb.line);

                            code.extend_from_slice(cmp_idx.to_le_bytes().as_ref());
                            for _ in 0..4 { line_numbers.push(usize::MAX); }
                        }
                    };
                }
                LocationRule::Mapped { ref signal_code, ref indexes } => {
                    // copy the logic of calc_mapped_signal_idx
                    let sig_idx = calc_mapped_signal_idx(
                        *signal_code, indexes, *cmp_idx as usize,
                        io_map, components);

                    match sig_idx {
                        U32OrExpression::U32(sig_idx) => {
                            code.push(OpCode::GetSubSignal4 as u8);
                            line_numbers.push(lb.line);

                            code.extend_from_slice(cmp_idx.to_le_bytes().as_ref());
                            for _ in 0..4 { line_numbers.push(usize::MAX); }

                            code.extend_from_slice(sig_idx.to_le_bytes().as_ref());
                            for _ in 0..4 { line_numbers.push(usize::MAX); }
                        }
                        U32OrExpression::Expression => {
                            expression_mapped_signal_idx(
                                code, constants, line_numbers, *signal_code,
                                indexes, *cmp_idx as usize, io_map, components);

                            code.push(OpCode::GetSubSignal as u8);
                            line_numbers.push(lb.line);

                            code.extend_from_slice(cmp_idx.to_le_bytes().as_ref());
                            for _ in 0..4 { line_numbers.push(usize::MAX); }
                        }
                    };
                }
            };
        }
        AddressType::Variable => {
            let location = if let LocationRule::Indexed{ref location, ..} = lb.src {
                location
            } else {
                panic!("Variable source location should be of Indexed type");
            };

            let idx = u32_or_expression(
                location, constants, Some(Fr::from(u32::MAX)))
                .unwrap();

            match idx {
                U32OrExpression::U32(idx) => {
                    code.push(OpCode::GetVariable4 as u8);
                    line_numbers.push(lb.line);
                    code.extend_from_slice(idx.to_le_bytes().as_ref());
                    for _ in 0..4 { line_numbers.push(usize::MAX); }
                }
                U32OrExpression::Expression => {
                    expression(
                        location, code, constants, line_numbers, components,
                        io_map);
                    code.push(OpCode::GetVariable as u8);
                    line_numbers.push(lb.line);
                }
            }
        }
    }

    let signals_num: u32 = lb.context.size
        .try_into().expect("Too many signals");
    code.extend_from_slice(signals_num.to_le_bytes().as_ref());
    for _ in 0..4 { line_numbers.push(usize::MAX); }
}

fn expression_compute(
    cb: &ComputeBucket, code: &mut Vec<u8>, constants: &[Fr],
    line_numbers: &mut Vec<usize>, components: &mut Vec<ComponentTmpl>,
    io_map: &TemplateInstanceIOMap) {

    // two operand operations
    let mut op2 = |oc: OpCode| {
        assert_eq!(2, cb.stack.len());
        expression(
            &cb.stack[0], code, constants, line_numbers, components,
            io_map);
        expression(
            &cb.stack[1], code, constants, line_numbers, components,
            io_map);
        code.push(oc as u8);
        line_numbers.push(cb.line);
    };

    match cb.op {
        OperatorType::Mul | OperatorType::MulAddress => {
            op2(OpCode::OpMul);
        }
        OperatorType::Div => {
            op2(OpCode::OpDiv);
        }
        OperatorType::Add | OperatorType::AddAddress => {
            op2(OpCode::OpAdd);
        }
        OperatorType::ShiftR => {
            op2(OpCode::OpShR);
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
        OperatorType::BitAnd => {
            op2(OpCode::OpBAnd);
        }
        OperatorType::PrefixSub => {
            assert_eq!(1, cb.stack.len());
            expression(
                &cb.stack[0], code, constants, line_numbers, components,
                io_map);
            code.push(OpCode::OpNeg as u8);
            line_numbers.push(cb.line);
        }
        OperatorType::ToAddress => {
            assert_eq!(1, cb.stack.len());
            expression(
                &cb.stack[0], code, constants, line_numbers, components,
                io_map);

            // do not add instruction as the value on the stack after previous
            // expression compilation should be stayed as is.
        }
        _ => {
            todo!("not implemented expression operator {}: {}",
                cb.op.to_string(), cb.to_string());
        }
    };
}

// After expression execution, the value of the expression should be on the stack
fn expression(
    inst: &InstructionPointer, code: &mut Vec<u8>, constants: &[Fr],
    line_numbers: &mut Vec<usize>, components: &mut Vec<ComponentTmpl>,
    io_map: &TemplateInstanceIOMap) {

    println!("expression: {}", inst.to_string());
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
        }
        Instruction::Load(ref load_bucket) => {
            expression_load(
                load_bucket, code, constants, line_numbers, components, io_map);
            assert_eq!(line_numbers.len(), code.len());
        }
        Instruction::Compute(ref compute_bucket) => {
            expression_compute(
                compute_bucket, code, constants, line_numbers, components,
                io_map);
            assert_eq!(line_numbers.len(), code.len());
        }
        _ => {
            panic!("Expression does not supported: {}", inst.to_string());
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
    io_map: &TemplateInstanceIOMap) {

    for inst in inst_list {
        statement(inst, code, constants, line_numbers, components, io_map);
        assert_eq!(line_numbers.len(), code.len());
    }
}

fn compile_template(
    tmpl_code: &TemplateCode, constants: &[Fr],
    io_map: &TemplateInstanceIOMap) -> Template {

    println!("Compile template {}", tmpl_code.name);

    let mut code = vec![];
    let mut line_numbers = vec![];
    let mut components = Vec::new();
    block(
        &tmpl_code.body, &mut code, constants, &mut line_numbers,
        &mut components, io_map);

    assert_eq!(line_numbers.len(), code.len());

    Template {
        name: tmpl_code.name.clone(),
        code,
        line_numbers,
        components: components,
    }
}

fn compile(
    templates: &Vec<TemplateCode>,
    functions: &Vec<FunctionCode>,
    io_map: &TemplateInstanceIOMap,
    constants: &[Fr],
) -> Vec<Template>{

    let mut compiled_templates = Vec::with_capacity(templates.len());
    for tmpl in templates.iter() {
        compiled_templates.push(compile_template(tmpl, constants, io_map));
    }

    // Assert all components created has has_inputs field consistent with
    // the number of inputs in the templates
    for tmpl in compiled_templates.iter() {
        println!("Template: {}", tmpl.name);
        for c in tmpl.components.iter() {
            let has_inputs = templates[c.template_id].number_of_inputs > 0;
            assert_eq!(c.has_inputs, has_inputs);
            println!("Component: {} {}", c.symbol, c.template_id);
        }
    }

    compiled_templates
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

fn disassemble(code: &[u8], line_numbers: &[usize]) {
    let mut ip = 0usize;
    while ip < code.len() {
        ip = disassemble_instruction(code, line_numbers, ip);
    }
}

fn disassemble_instruction(code: &[u8], line_numbers: &[usize], ip: usize) -> usize {

    print!("{:08x} [{:4}] ", ip, line_numbers[ip]);

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

            println!("StoreSelfSignal8 [{},{}]", sig_idx, sigs_number);
        }
        OpCode::SetSelfSignal => {
            let sigs_number = read_u32(&code, ip);
            ip += size_of::<u32>();

            println!("StoreSelfSignal [{}]", sigs_number);
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
        OpCode::GetSubSignal4 => {
            let cmp_idx = read_u32(&code, ip);
            ip += size_of::<u32>();

            let sig_idx = read_u32(&code, ip);
            ip += size_of::<u32>();

            let sigs_number = read_u32(&code, ip);
            ip += size_of::<u32>();

            println!(
                "GetSubSignal4 [{},{},{}]", cmp_idx, sig_idx, sigs_number);
        }
        OpCode::GetSubSignal => {
            let cmp_idx = read_u32(&code, ip);
            ip += size_of::<u32>();

            let sigs_number = read_u32(&code, ip);
            ip += size_of::<u32>();

            println!(
                "GetSubSignal [{},{}]", cmp_idx, sigs_number);
        }
        OpCode::SetSubSignal4 => {
            let cmp_idx = read_u32(&code, ip);
            ip += size_of::<u32>();

            let sig_idx = read_u32(&code, ip);
            ip += size_of::<u32>();

            let sigs_number = read_u32(&code, ip);
            ip += size_of::<u32>();

            let input_status = InputStatus::try_from(code[ip]).unwrap();
            ip += 1;

            println!(
                "StoreSubSignal4 [{},{},{},{}]",
                cmp_idx, sig_idx, sigs_number, input_status);
        }
        OpCode::SetSubSignal => {
            let cmp_idx = read_u32(&code, ip);
            ip += size_of::<u32>();

            let sigs_number = read_u32(&code, ip);
            ip += size_of::<u32>();

            let input_status = InputStatus::try_from(code[ip]).unwrap();
            ip += 1;

            println!(
                "StoreSubSignal [{},{},{}]",
                cmp_idx, sigs_number, input_status);
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
        OpCode::OpShR => {
            println!("OpShR");
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
        OpCode::OpBAnd => {
            println!("OpAnd");
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
    }

    ip
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, HashMap};
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
        let io_map: TemplateInstanceIOMap = BTreeMap::new();
        expression(
            &inst, &mut code, &constants, &mut vec![],
            &mut vec![], &io_map);
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
        expression(&inst, &mut code, &constants, &mut vec![], &mut vec![], &BTreeMap::new());
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
        statement(&inst, &mut code, &constants, &mut line_numbers, &mut components, &BTreeMap::new());
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
        statement(&inst, &mut code, &constants, &mut line_numbers, &mut components, &BTreeMap::new());

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

        disassemble(&templates[0].code, &templates[0].line_numbers);

        println!("execute");
        execute(component.clone(), &templates, &constants, &mut signals);
        println!("{:?}", component.borrow().vars);
        assert_eq!(
            &vec![None, Some(Fr::from(10u64)), var2],
            &component.borrow().vars);
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

        disassemble(&code, &line_numbers);
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
        execute(component.clone(), &templates, &constants, &mut signals);
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
        execute(component, &templates, &constants, &mut signals);
    }
}