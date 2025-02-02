use std::cell::RefCell;
use std::cmp::Ordering;
use std::fmt::{Debug, Display};
use std::num::TryFromIntError;
use std::rc::Rc;
use std::str::FromStr;
use ark_bn254::Fr;
use ark_ff::{BigInt, One, PrimeField, Zero};
use code_producers::c_elements::TemplateInstanceIOMap;
use compiler::intermediate_representation::ir_interface::StatusInput;
use crate::graph::{Operation, UnoOperation};

pub struct Component {
    pub vars: Vec<Option<Fr>>,
    pub signals_start: usize,
    pub template_id: usize,
    pub subcomponents: Vec<Rc<RefCell<Component>>>,
    pub number_of_inputs: usize,
}

#[cfg_attr(test, derive(Debug))]
pub struct ComponentTmpl {
    pub symbol: String,
    pub sub_cmp_idx: usize,
    pub number_of_cmp: usize,
    pub name_subcomponent: String,
    pub signal_offset: usize,
    pub signal_offset_jump: usize,
    pub template_id: usize,
    pub has_inputs: bool,
}

impl TryInto<crate::proto::vm::ComponentTmpl> for &ComponentTmpl {
    type Error = TryFromIntError;

    fn try_into(self) -> Result<crate::proto::vm::ComponentTmpl, Self::Error> {
        Ok(crate::proto::vm::ComponentTmpl{
            symbol: self.symbol.clone(),
            sub_cmp_idx: self.sub_cmp_idx.try_into()?,
            number_of_cmp: self.number_of_cmp.try_into()?,
            name_subcomponent: self.name_subcomponent.clone(),
            signal_offset: self.signal_offset.try_into()?,
            signal_offset_jump: self.signal_offset_jump.try_into()?,
            template_id: self.template_id.try_into()?,
            has_inputs: self.has_inputs,
        })
    }
}

impl TryFrom<&crate::proto::vm::ComponentTmpl> for ComponentTmpl {
    type Error = ();

    fn try_from(value: &crate::proto::vm::ComponentTmpl) -> Result<Self, Self::Error> {
        Ok(ComponentTmpl {
            symbol: value.symbol.clone(),
            sub_cmp_idx: value.sub_cmp_idx.try_into()
                .expect("sub_cmp_idx is too large for this platform"),
            number_of_cmp: value.number_of_cmp.try_into()
                .expect("number_of_cmp is too large for this platform"),
            name_subcomponent: value.name_subcomponent.clone(),
            signal_offset: value.signal_offset.try_into()
                .expect("signal_offset is too large for this platform"),
            signal_offset_jump: value.signal_offset_jump.try_into()
                .expect("signal_offset_jump is too large for this platform"),
            template_id: value.template_id.try_into()
                .expect("template_id is too large for this platform"),
            has_inputs: value.has_inputs,
        })
    }
}

#[cfg_attr(test, derive(Debug))]
pub struct Template {
    pub name: String,
    pub code: Vec<u8>,
    pub line_numbers: Vec<usize>,
    pub components: Vec<ComponentTmpl>,
    pub var_stack_depth: usize,
    pub number_of_inputs: usize,
}

impl TryInto<crate::proto::vm::Template> for &Template {
    type Error = TryFromIntError;

    fn try_into(self) -> Result<crate::proto::vm::Template, Self::Error> {
        Ok(crate::proto::vm::Template{
            name:self.name.clone(),
            code: self.code.clone(),
            line_numbers: self.line_numbers.iter()
                .map(|x| TryInto::try_into(*x))
                .collect::<Result<Vec<u64>, TryFromIntError>>()?,
            components: self.components.iter()
                .map(TryInto::<crate::proto::vm::ComponentTmpl>::try_into)
                .collect::<Result<Vec<_>, _>>()?,
            var_stack_depth: self.var_stack_depth.try_into()?,
            number_of_inputs: self.number_of_inputs.try_into()?,
        })
    }
}

impl TryFrom<&crate::proto::vm::Template> for Template {
    type Error = TryFromIntError;

    fn try_from(value: &crate::proto::vm::Template) -> Result<Self, Self::Error> {
        Ok(Template{
            name: value.name.clone(),
            code: value.code.clone(),
            line_numbers: value.line_numbers
                .iter()
                .map(|x| TryInto::<usize>::try_into(*x))
                .collect::<Result<Vec<usize>, TryFromIntError>>()?,
            components: value.components.iter()
                .map(|x| ComponentTmpl::try_from(x).unwrap())
                .collect::<Vec<ComponentTmpl>>(),
            var_stack_depth: value.var_stack_depth.try_into()?,
            number_of_inputs: value.number_of_inputs.try_into()?,
        })
    }
}

#[cfg_attr(test, derive(Debug))]
pub struct Function {
    pub name: String,
    pub symbol: String,
    pub code: Vec<u8>,
    pub line_numbers: Vec<usize>,
}

impl TryInto<crate::proto::vm::Function> for &Function {
    type Error = TryFromIntError;

    fn try_into(self) -> Result<crate::proto::vm::Function, Self::Error> {
        Ok(crate::proto::vm::Function{
            name: self.name.clone(),
            symbol: self.symbol.clone(),
            code: self.code.clone(),
            line_numbers: self.line_numbers.iter()
                .map(|x| TryInto::try_into(*x))
                .collect::<Result<Vec<u64>, TryFromIntError>>()?,
        })
    }
}

impl TryFrom<&crate::proto::vm::Function> for Function {
    type Error = TryFromIntError;

    fn try_from(value: &crate::proto::vm::Function) -> Result<Self, Self::Error> {
        Ok(Function{
            name: value.name.clone(),
            symbol: value.symbol.clone(),
            code: value.code.clone(),
            line_numbers: value.line_numbers
                .iter()
                .map(|x| TryInto::<usize>::try_into(*x))
                .collect::<Result<Vec<usize>, TryFromIntError>>()?,
        })
    }
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

    #[cfg(feature = "print_opcode")]
    fn print_stack(&self) {
        for (i, s) in self.stack.iter().enumerate() {
            let s = if s.is_zero() { String:: from("0") } else { s.to_string() };
            println!("{:04x}: {}", i, s);
        }
    }
    #[cfg(feature = "print_opcode")]
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
#[derive(Debug)]
pub enum OpCode {
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

#[repr(u8)]
#[derive(Debug, Clone)]
pub enum InputStatus {
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

fn unpack_flags(flags: u8) -> (InputStatus, bool) {
    let is_mapped_signal_idx = flags & 0b1000_0000 != 0;
    let input_status = InputStatus::try_from(flags & 0b0000_0011).unwrap();
    (input_status, is_mapped_signal_idx)
}

pub fn disassemble_instruction(
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

pub fn u_lt(a: &Fr, b: &Fr) -> Fr {
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

fn bigint_to_u64<const N: usize>(i: BigInt<N>) -> Option<u64> {
    let z = BigInt::<N>::from(0u32);
    let max = BigInt::<N>::from(u64::MAX);

    if i < z || i > max {
        return None;
    }

    Some(i.0[0])
}

pub fn build_component(
    compiled_templates: &[Template],
    template_id: usize, signals_start: usize) -> Component {

    let mut subcomponents = Vec::with_capacity(
        compiled_templates[template_id].components.len());

    for c in &compiled_templates[template_id].components {
        let mut cmp_signal_offset = c.signal_offset;

        for _ in c.sub_cmp_idx..c.sub_cmp_idx+c.number_of_cmp {
            let subcomponent = build_component(
                compiled_templates, c.template_id,
                signals_start + cmp_signal_offset);
            subcomponents.push(Rc::new(RefCell::new(subcomponent)));
            cmp_signal_offset += c.signal_offset_jump;
        }
    }

    Component {
        vars: vec![None; compiled_templates[template_id].var_stack_depth],
        signals_start,
        template_id,
        subcomponents,
        number_of_inputs: compiled_templates[template_id].number_of_inputs,
    }
}

// pub fn print_component_tree(c: &Component, indent: usize, templates: &[Template]) {
//     if indent == 0 {
//         println!("Component tree:");
//     }
//     let indent_str = " ".repeat(indent);
//     println!("{}{}", indent_str, templates[c.template_id].name);
//     for sc in &c.subcomponents {
//         print_component_tree(&sc.borrow(), indent + 2, templates);
//     }
// }

pub fn execute(
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
    #[cfg(feature = "print_opcode")]
    let mut template_id: usize;
    let mut signals_start: usize;
    {
        match vm.call_frames.last().unwrap() {
            Frame::Component { code: code_local, component, .. } => {
                code = *code_local;
                #[cfg(feature = "print_opcode")]
                {
                    template_id = component.borrow().template_id;
                }
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
                    #[cfg(feature = "print_opcode")]
                    {
                        template_id = component.template_id;
                    }
                    code = &templates[component.template_id].code;
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

                    match input_status {
                        InputStatus::Last => true,
                        InputStatus::NoLast => false,
                        InputStatus::Unknown => subcmp.number_of_inputs == 0,
                    }
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
                            #[cfg(feature = "print_opcode")]
                            {
                                template_id = component.borrow().template_id;
                            }
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
                        ip -= offset.unsigned_abs() as usize;
                    } else {
                        ip += offset as usize;
                    }
                }
            }
            OpCode::Jump => {
                let offset = read_i32(code, ip);
                ip += size_of::<i32>();
                if offset < 0 {
                    ip -= offset.unsigned_abs() as usize;
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
                        #[cfg(feature = "print_opcode")]
                        {
                            template_id = component.borrow().template_id;
                        }
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
                    Frame::Component { .. } => {
                        panic!("No way, we just added a function frame");
                    }
                    Frame::Function { code: code_local, .. } => {
                        code = *code_local;
                        #[cfg(feature = "print_opcode")]
                        {
                            template_id = usize::MAX;
                        }
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
                // ip += size_of::<u32>(); // no need to increment ip, it would be changed to where we return

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
                        #[cfg(feature = "print_opcode")]
                        {
                            template_id = component.template_id;
                        }
                        code = &templates[component.template_id].code;
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
