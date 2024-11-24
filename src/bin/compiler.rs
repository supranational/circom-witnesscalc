use std::{env, fs};
use std::path::PathBuf;
use core::convert::TryInto;
use core::str::FromStr;
use std::fs::File;
use std::io::Write;
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
use compiler::intermediate_representation::ir_interface::{AddressType, ComputeBucket, Instruction, InstructionPointer, LoadBucket, LocationRule, OperatorType, ValueType};
use constraint_generation::{build_circuit, BuildConfig};
use program_structure::error_definition::Report;
use type_analysis::check_types::check_types;
use wtns_file::FieldElement;
use circom_witnesscalc::{deserialize_inputs};

struct Args {
    circuit_file: String,
    inputs_file: Option<String>,
    graph_file: String,
    link_libraries: Vec<PathBuf>,
    print_debug: bool,
    witness_file: Option<String>,
}

// An instance of a template
struct Component<'a> {
    vars: Vec<Option<Fr>>,
    signals_start: usize,
    template: &'a Template,
}

struct Template {
    name: String,
    code: Vec<u8>,
    line_numbers: Vec<usize>,
}

struct VM<'a, 'b> {
    component: &'a mut Component<'b>,
    templates: Vec<Template>,
    signals: &'a mut [Option<Fr>],
    constants: &'a Vec<Fr>,
    stack: Vec<Fr>,
}

impl VM<'_, '_> {
    fn print_stack(&self) {
        for (i, s) in self.stack.iter().enumerate() {
            let s = if s.is_zero() { String:: from("0") } else { s.to_string() };
            println!("{:04x}: {}", i, s);
        }
    }
}

#[repr(u8)]
#[derive(Debug)]
enum OpCode {
    NoOp = 0,
    StoreSelfSignal8 = 1,
    GetConstant8 = 2, // pushes the value of a constant to the stack. Address of the constant is u64 little endian
    Push8 = 3, // pushes the value of the following 4 bytes as a little endian u64 to the stack
    GetVariable4 = 4,
    GetVariable = 5,
    SetVariable4 = 6,
    SetVariable = 7,
    JumpIfFalse = 8, // Jump to the offset i32 if the value on the top of the stack is false
    Jump = 9, // Jump to the offset i32
    OpMul = 10,
    OpAdd = 11,
    OpLt = 12,
    GetSelfSignal4 = 13, // next following 4 bytes is the signal index as le u32
    GetSelfSignal = 14, // the address of the signal is a value on the stack
}

fn assert_u64_value(inst: &InstructionPointer) -> u64 {
    let value = if let Instruction::Value(ref value) = **inst {
        value
    } else {
        panic!("Expected value instruction, got: {}", inst.to_string());
    };

    assert!(matches!(value.parse_as, ValueType::U32));
    value.value.try_into().expect("value is not u64")
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

    let mut component = Component {
        vars: vec![],
        signals_start: main_component_signal_start,
        template: &compiled_templates[main_template_id],
    };

    if let Some(input_file) = args.inputs_file {
        let sigs_num = circuit.c_producer.get_total_number_of_signals();
        let mut signals = Vec::new();
        signals.resize(sigs_num, None);
        init_input_signals(&circuit, input_file, &mut signals);

        execute(&mut component, &constants, &mut signals);

        if let Some(witness_file) = args.witness_file {
            let mut witness = Vec::with_capacity(witness_list.len());
            for (i, w) in witness_list.iter().enumerate() {
                println!("w: {}", signals[*w].unwrap().to_string());
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

fn execute(component: &mut Component, constants: &Vec<Fr>, signals: &mut [Option<Fr>]) {
    let mut vm = VM {
        component,
        templates: vec![],
        signals,
        constants,
        stack: vec![],
    };
    let mut ip = 0usize;
    loop {
        if ip == vm.component.template.code.len() {
            break;
        }

        disassemble_instruction(
            &vm.component.template.code, &vm.component.template.line_numbers,
            ip);

        let op = read_instruction(&vm.component.template.code, ip);
        ip += 1;

        match op {
            OpCode::NoOp => {
                // do nothing
            }
            OpCode::StoreSelfSignal8 => {
                let sig_idx = read_usize(&vm.component.template.code, ip);
                ip += size_of::<usize>();

                if let Some(_) = vm.signals[vm.component.signals_start + sig_idx] {
                    panic!("Signal already set");
                }

                vm.signals[vm.component.signals_start + sig_idx] = Some(vm.stack.pop().unwrap());
            }
            OpCode::GetConstant8 => {
                let const_idx = read_usize(&vm.component.template.code, ip);
                ip += size_of::<usize>();
                vm.stack.push(vm.constants[const_idx]);
            }
            OpCode::Push8 => {
                let val = read_usize(&vm.component.template.code, ip);
                ip += size_of::<usize>();
                let val = Fr::from(val as u64);
                vm.stack.push(val);
            }
            OpCode::GetVariable4 => {
                let var_idx = read_u32(&vm.component.template.code, ip);
                ip += size_of::<u32>();
                let var_idx = usize::try_from(var_idx).unwrap();
                if vm.component.vars.len() <= var_idx || vm.component.vars[var_idx].is_none() {
                    panic!("Variable not set");
                }
                vm.stack.push(vm.component.vars[var_idx].unwrap());
            }
            OpCode::GetVariable => {
                let var_idx = vm.stack.pop().unwrap();
                let var_idx = bigint_to_u64(
                    var_idx.into_bigint())
                    .expect("Variable index is too large");
                let var_idx = usize::try_from(var_idx).unwrap();
                if vm.component.vars.len() <= var_idx || vm.component.vars[var_idx].is_none() {
                    panic!("Variable not set");
                }
                vm.stack.push(vm.component.vars[var_idx].unwrap());
            }
            OpCode::SetVariable4 => {
                let var_idx = read_u32(&vm.component.template.code, ip);
                ip += size_of::<u32>();

                let var_idx = usize::try_from(var_idx).unwrap();

                if vm.component.vars.len() <= var_idx {
                    vm.component.vars.resize(var_idx + 1, None);
                }

                vm.component.vars[var_idx] = Some(vm.stack.pop().unwrap());
            }
            OpCode::SetVariable => {
                let var_idx = vm.stack.pop().unwrap();
                let var_idx = bigint_to_u64(
                    var_idx.into_bigint())
                    .expect("Variable index is too large");
                let var_idx = usize::try_from(var_idx).unwrap();

                if vm.component.vars.len() <= var_idx {
                    vm.component.vars.resize(var_idx + 1, None);
                }

                vm.component.vars[var_idx] = Some(vm.stack.pop().unwrap());
            }
            OpCode::JumpIfFalse => {
                let offset = read_i32(&vm.component.template.code, ip);
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
                let offset = read_i32(&vm.component.template.code, ip);
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
            OpCode::OpAdd => {
                let b = vm.stack.pop().unwrap();
                let a = vm.stack.pop().unwrap();
                vm.stack.push(a + b);
            }
            OpCode::OpLt => {
                let b = vm.stack.pop().unwrap();
                let a = vm.stack.pop().unwrap();
                vm.stack.push(u_lt(&a, &b));
            }
            OpCode::GetSelfSignal4 => {
                let sig_idx = read_u32(&vm.component.template.code, ip);
                ip += size_of::<u32>();
                vm.stack.push(vm.signals[vm.component.signals_start + sig_idx as usize].unwrap());
            }
            OpCode::GetSelfSignal => {
                let cmp_signal_offset = vm.stack.pop().unwrap();
                let cmp_signal_offset = bigint_to_u64(
                    cmp_signal_offset.into_bigint())
                    .expect("Signal index is too large");
                let sig_idx = vm.component.signals_start + cmp_signal_offset as usize;
                assert_64();
                if sig_idx >= vm.signals.len() {
                    panic!(
                        "Signal index is too large: [{} + {}] = {}",
                        vm.component.signals_start, cmp_signal_offset, sig_idx);
                }
                let v = match vm.signals[sig_idx] {
                    Some(v) => v,
                    None => panic!(
                        "Signal is not set: [{} + {}] = {}",
                        vm.component.signals_start, cmp_signal_offset, sig_idx),
                };
                vm.stack.push(v);
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


fn pre_emit_jump(code: &mut Vec<u8>) -> usize {
    code.push(OpCode::JumpIfFalse as u8);
    code.push(0xffu8);
    code.push(0xffu8);
    code.push(0xffu8);
    code.push(0xffu8);
    code.len() - 4
}

/// We expect the jump offset located at `jump_offset_addr` to be 4 bytes long.
/// The jump offset is calculated as `to - jump_offset_addr - 4`.
fn patch_jump(code: &mut [u8], jump_offset_addr: usize, to: usize) {
    let offset = calc_jump_offset(jump_offset_addr + 4, to);
    code[jump_offset_addr..jump_offset_addr+4].copy_from_slice(offset.to_le_bytes().as_ref());
}

// After statement execution, there should not be side-effect on the stack
fn statement(inst: &InstructionPointer, code: &mut Vec<u8>, constants: &[Fr], line_numbers: &mut Vec<usize>) {
    println!("statement: {}", inst.to_string());

    match **inst {
        Instruction::Store(ref store_bucket) => {
            if store_bucket.context.size != 1 {
                todo!();
            }

            expression(&store_bucket.src, code, constants, line_numbers);
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
                            expression(location, code, constants, line_numbers);
                            code.push(OpCode::SetVariable as u8);
                            line_numbers.push(store_bucket.line);
                        }
                    }
                }

                AddressType::Signal => {
                    let location = if let LocationRule::Indexed{ref location, ..} = store_bucket.dest {
                        location
                    } else {
                        panic!("Signal destination should be of Indexed type");
                    };

                    code.push(OpCode::StoreSelfSignal8 as u8);
                    line_numbers.push(store_bucket.line);

                    let sig_idx = assert_u64_value(location);
                    assert_64();
                    code.extend_from_slice(sig_idx.to_le_bytes().as_ref());
                    for _ in 0..8 { line_numbers.push(usize::MAX); }
                }

                AddressType::SubcmpSignal { .. } => {
                    todo!()
                }
            }
            assert_eq!(line_numbers.len(), code.len());
        }
        Instruction::Loop(ref loop_bucket) => {
            let loop_start = code.len();

            expression(&loop_bucket.continue_condition, code, constants, line_numbers);

            let loop_end_jump_offset = pre_emit_jump(code);
            line_numbers.push(loop_bucket.line);
            line_numbers.push(usize::MAX);
            line_numbers.push(usize::MAX);
            line_numbers.push(usize::MAX);
            line_numbers.push(usize::MAX);

            block(&loop_bucket.body, code, constants, line_numbers);

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
        _ => {
            todo!("instruction not supported: {}", inst.to_string());
        }
    }
}

fn assert_64() {
    assert!(cfg!(target_pointer_width = "64"), "Need a fix for non-64-bit architecture.");
}

fn expression_load(lb: &LoadBucket, code: &mut Vec<u8>, constants: &[Fr], line_numbers: &mut Vec<usize>) {
    if lb.context.size != 1 {
        todo!()
    }

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
                    expression(location, code, constants, line_numbers);
                    code.push(OpCode::GetSelfSignal as u8);
                    line_numbers.push(lb.line);
                }
            }
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
                    expression(location, code, constants, line_numbers);
                    code.push(OpCode::GetVariable as u8);
                    line_numbers.push(lb.line);
                }
            }
        }
        _ => {
            todo!("Unsupported load expression: {}", lb.to_string());
        }
    }
}

fn expression_compute(cb: &ComputeBucket, code: &mut Vec<u8>, constants: &[Fr], line_numbers: &mut Vec<usize>) {
    match cb.op {
        OperatorType::Mul | OperatorType::MulAddress => {
            assert_eq!(2, cb.stack.len());
            expression(&cb.stack[0], code, constants, line_numbers);
            expression(&cb.stack[1], code, constants, line_numbers);
            code.push(OpCode::OpMul as u8);
            line_numbers.push(cb.line);
        }
        OperatorType::Add | OperatorType::AddAddress => {
            assert_eq!(2, cb.stack.len());
            expression(&cb.stack[0], code, constants, line_numbers);
            expression(&cb.stack[1], code, constants, line_numbers);
            code.push(OpCode::OpAdd as u8);
            line_numbers.push(cb.line);
        }
        OperatorType::Lesser => {
            assert_eq!(2, cb.stack.len());
            expression(&cb.stack[0], code, constants, line_numbers);
            expression(&cb.stack[1], code, constants, line_numbers);
            code.push(OpCode::OpLt as u8);
            line_numbers.push(cb.line);
        }
        OperatorType::ToAddress => {
            assert_eq!(1, cb.stack.len());
            expression(&cb.stack[0], code, constants, line_numbers);

            // do not add instruction as the value on the stack after previous
            // expression compilation should be stayed as is.
        }
        _ => {
            todo!("not implemented expression: {}", cb.to_string());
        }
    };
}

// After expression execution, the value of the expression should be on the stack
fn expression(inst: &InstructionPointer, code: &mut Vec<u8>, constants: &[Fr], line_numbers: &mut Vec<usize>) {
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
            expression_load(load_bucket, code, constants, line_numbers);
            assert_eq!(line_numbers.len(), code.len());
        }
        Instruction::Compute(ref compute_bucket) => {
            expression_compute(compute_bucket, code, constants, line_numbers);
            assert_eq!(line_numbers.len(), code.len());
        }
        _ => {
            panic!("Expression does not supported: {}", inst.to_string());
        }
    }
}

fn block(inst_list: &InstructionList, code: &mut Vec<u8>, constants: &[Fr], line_numbers: &mut Vec<usize>) {
    for inst in inst_list {
        statement(inst, code, constants, line_numbers);
        assert_eq!(line_numbers.len(), code.len());
    }
}

fn compile_template(tmpl_code: &TemplateCode, constants: &[Fr]) -> Template {
    println!("Compile template {}", tmpl_code.name);

    let mut code = vec![];
    let mut line_numbers = vec![];
    block(&tmpl_code.body, &mut code, constants, &mut line_numbers);

    assert_eq!(line_numbers.len(), code.len());

    Template {
        name: tmpl_code.name.clone(),
        code,
        line_numbers,
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
        compiled_templates.push(compile_template(tmpl, constants));
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
        OpCode::StoreSelfSignal8 => {
            let sig_idx = read_usize(&code, ip);
            ip += size_of::<usize>();

            println!("StoreSelfSignal8 [{}]", sig_idx);
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

            println!("GetVariable4 [{}]", var_idx);
        }
        OpCode::GetVariable => {
            println!("GetVariable");
        }
        OpCode::SetVariable4 => {
            let var_idx = read_u32(&code, ip);
            ip += size_of::<u32>();

            println!("SetVariable4 [{}]", var_idx);
        }
        OpCode::SetVariable => {
            println!("SetVariable");
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
        OpCode::OpAdd => {
            println!("OpAdd");
        }
        OpCode::OpLt => {
            println!("OpLt");
        }
        OpCode::GetSelfSignal4 => {
            let sig_idx = read_u32(&code, ip);
            ip += size_of::<u32>();

            println!("GetSelfSignal4 [{}]", sig_idx);
        }
        OpCode::GetSelfSignal => {
            println!("GetSelfSignal");
        }
    }

    ip
}

#[cfg(test)]
mod tests {
    use ark_ff::BigInteger256;
    use compiler::intermediate_representation::ir_interface::{InstrContext, StoreBucket, ValueBucket};
    use super::*;

    #[test]
    fn test_parse_args() {
        let o = OpCode::StoreSelfSignal8;
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
        expression(&inst, &mut code, &constants, &mut vec![]);
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
        expression(&inst, &mut code, &constants, &mut vec![]);
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
        statement(&inst, &mut code, &constants, &mut line_numbers);
        assert_eq!(code,
                   vec![
                       OpCode::GetConstant8 as u8, 0xea, 0, 0, 0, 0, 0, 0, 0,
                       OpCode::SetVariable4 as u8, 0x2b, 0x2, 0, 0]);
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
        statement(&inst, &mut code, &constants, &mut line_numbers);

        let var1 = Some(Fr::from(2));
        let var2 = Some(Fr::from(1));
        let mut c = Component{
            vars: vec![None, var1, var2],
            signals_start: 0,
            template: &Template {
                name: "test".to_string(),
                code: code,
                line_numbers,
            },
        };

        let mut signals = vec![None, None, Some(Fr::from(8))];

        disassemble(&c.template.code, &c.template.line_numbers);

        println!("execute");
        execute(&mut c, &constants, &mut signals);
        println!("{:?}", &c.vars);
        assert_eq!(&vec![None, Some(Fr::from(10u64)), var2], &c.vars);
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
        let jump_offset = pre_emit_jump(&mut code);

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
        let jump_offset = pre_emit_jump(&mut code);
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
            OpCode::JumpIfFalse as u8, 5*2, 0x00, 0x00, 0x00,
            OpCode::Push8 as u8, 0x01, 0, 0, 0, 0, 0, 0, 0,
            OpCode::SetVariable4 as u8, 0, 0, 0, 0,
            OpCode::Push8 as u8, 0x02, 0, 0, 0, 0, 0, 0, 0,
            OpCode::SetVariable4 as u8, 1, 0, 0, 0,
            OpCode::NoOp as u8,
        ];
        let mut line_numbers = Vec::with_capacity(code.len());
        for (i, _) in code.iter().enumerate() {
            line_numbers.push(i);
        }

        disassemble(&code, &line_numbers);
        println!("execute");

        let mut c = Component{
            vars: vec![],
            signals_start: 0,
            template: &Template {
                name: "test".to_string(),
                code: code.clone(),
                line_numbers,
            },
        };
        let constants = vec![];
        let mut signals = vec![None; 10];
        execute(&mut c, &constants, &mut signals);
        println!("{:?}", &c.vars);
    }

    #[test]
    fn test_dump() {
        let noop = OpCode::NoOp as u8;
        let mut code = vec![];
        code.push(noop);
        let mut c = Component{
            vars: vec![],
            signals_start: 0,
            template: &Template {
                name: "test".to_string(),
                code: code.clone(),
                line_numbers: vec![0],
            },
        };
        let constants = vec![];
        let mut signals = vec![None; 10];
        execute(&mut c, &constants, &mut signals);
    }
}