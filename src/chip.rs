
use petgraph::prelude::*;
use std::fmt;
use std::slice::Iter;
use graph_algorithms::*;
use utils::*;

macro_rules! chip_kinds {
    ($( $variant:tt ),*) => {
        #[derive(PartialEq, Eq, Copy, Clone, Debug, Hash)]
        pub enum ChipKind {
            $($variant,)*
        }

        impl ChipKind {
            pub fn iter() -> Iter<'static, ChipKind> {
                use ChipKind::*;
                static CHIP_KINDS: &'static [ChipKind] = &[
                    $($variant,)*
                ];
                CHIP_KINDS.into_iter()
            }
        }
    }
}

chip_kinds!(
    Nand, Not, Or, And, Xor, Mux, DMux, Not16, Or16, And16, Mux16,
    Or8Way, HalfAdder, FullAdder, Adder8);

impl fmt::Display for ChipKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

pub fn create_chip(chip: ChipKind) -> Composite {
    let mut factory = ChipFactory::new();
    match chip {
        ChipKind::Nand      => nand_composite(&mut factory),
        ChipKind::Not       => not(&mut factory),
        ChipKind::Or        => or(&mut factory),
        ChipKind::And       => and(&mut factory),
        ChipKind::Xor       => xor(&mut factory),
        ChipKind::Mux       => mux(&mut factory),
        ChipKind::DMux      => dmux(&mut factory),
        ChipKind::Not16     => not16(&mut factory),
        ChipKind::Or16      => or16(&mut factory),
        ChipKind::And16     => and16(&mut factory),
        ChipKind::Mux16     => mux16(&mut factory),
        ChipKind::Or8Way    => or8way(&mut factory),
        ChipKind::HalfAdder => halfadder(&mut factory),
        ChipKind::FullAdder => fulladder(&mut factory),
        ChipKind::Adder8    => adder8(&mut factory)
    }
}

macro_rules! wire {
    ($graph:expr, $( $n1:expr;$p1:tt -> $n2:expr;$p2:tt ), *) => {{
        $( $graph.add_edge($n1, $n2,
                Wire::new(stringify!($p1).into(), stringify!($p2).into())); )*
    }}
}

macro_rules! gate {
    ($graph:expr, $gate:expr) => {{
        $graph.add_node(Box::new($gate))
    }}
}

macro_rules! inputs {
    ($( $input:tt -> $n:expr;$p:tt ),*) => {{
        let mut map = HashMapFnv::default();
        $( map.entry(stringify!($input).into())
              .or_insert(Vec::<(NodeIndex, String)>::new())
              .push(($n, stringify!($p).into())); )*
        map
    }}
}

macro_rules! input {
    ($inputs:expr, $( $input:tt[$index:expr] -> $n:expr;$p:tt ),*) => {{
        $( $inputs.entry(format!("{}_{}", stringify!($input), $index))
                  .or_insert(Vec::<(NodeIndex, String)>::new())
                  .push(($n, stringify!($p).into())); )*
    }}
}

macro_rules! outputs {
    ($( $output:tt <- $n:expr;$p:tt ),*) => {{
        let mut map = HashMapFnv::default();
        $( map.insert(stringify!($output).into(), ($n, stringify!($p).into())); )*
        map
    }}
}

macro_rules! output {
    ($outputs:expr, $( $output:tt[$index:expr] <- $n:expr;$p:tt ),*) => {{
        $( $outputs.insert(
            format!("{}_{}", stringify!($output), $index),
             ($n, stringify!($p).into())); )*
    }}
}


pub type ChipGraph = Graph<Box<Chip>, Wire>;

pub trait Chip {
    /// Unique identifier.
    fn id(&self) -> u32;
    /// Human-readable name.
    fn name(&self) -> String;
    fn run(&mut self);
    fn set_input(&mut self, pin: &str, state: bool);
    fn read_output(&self, pin: &str) -> bool;
    fn input_pins(&self) -> Vec<String>;
    fn output_pins(&self) -> Vec<String>;
}

/// Nand gates are always treated as primitive.
/// We could use instances of Primitive to represent them, but
/// that would make emulation even slower.
pub struct Nand {
    id: u32,
    a: bool,
    b: bool,
    out: bool
}

pub struct Primitive {
    pub id: u32,
    pub name: String,
    pub inputs: HashMapFnv<String, bool>,
    pub outputs: HashMapFnv<String, bool>,
    pub runner: Box<FnMut(&HashMapFnv<String, bool>, &mut HashMapFnv<String, bool>)>
}

impl Chip for Primitive {
    fn id(&self) -> u32 {
        self.id
    }

    fn name(&self) -> String {
        self.name.clone()
    }

    // Assumes that inputs have already been set.
    fn run(&mut self) {
        (self.runner)(&self.inputs, &mut self.outputs);
    }

    fn set_input(&mut self, pin: &str, state: bool) {
        *self.inputs.get_mut(pin).unwrap() = state;
    }

    fn read_output(&self, pin: &str) -> bool {
        *self.outputs.get(pin).unwrap()
    }

    fn input_pins(&self) -> Vec<String> {
        self.inputs.keys().map(|x| x.clone()).collect()
    }

    fn output_pins(&self) -> Vec<String> {
        self.outputs.keys().map(|x| x.clone()).collect()
    }
}

// Dummy composite chip, so that we can render something for each chip kind.
pub fn nand_composite(f: &mut ChipFactory) -> Composite {
    let mut g = ChipGraph::new();
    let nand = gate!(g, nand(f));

    f.composite("NAND", g,
        inputs!(a -> nand;a, b -> nand;b),
        outputs!(out <- nand;out))
}

pub struct ChipFactory {
    chip_count: u32
}

impl ChipFactory {
    pub fn new() -> ChipFactory {
        ChipFactory { chip_count: 0}
    }

    pub fn nand(&mut self) -> Nand {
        let n = Nand::new(self.chip_count);
        self.chip_count += 1;
        n
    }

    pub fn composite(&mut self,
                 name: &str,
                 graph: ChipGraph,
                 inputs: HashMapFnv<String, Vec<(NodeIndex, String)>>,
                 outputs: HashMapFnv<String, (NodeIndex, String)>
        ) -> Composite {
        let sorted_nodes = topological_sort(&graph);
        let composite = Composite {
            id: self.chip_count,
            name: name.into(),
            graph: graph,
            inputs: inputs,
            outputs: outputs,
            sorted_nodes: sorted_nodes
        };
        self.chip_count += 1;
        composite
    }

    pub fn primitive(&mut self, name: &str,
        inputs: HashMapFnv<String, bool>,
        outputs: HashMapFnv<String, bool>,
        runner: Box<FnMut(&HashMapFnv<String, bool>, &mut HashMapFnv<String, bool>)>
        ) -> Primitive {
        let primitive = Primitive {
            id: self.chip_count,
            name: name.into(),
            inputs: inputs,
            outputs: outputs,
            runner: runner
        };
        self.chip_count += 1;
        primitive
    }
}

impl Nand {
    pub fn new(id: u32) -> Nand {
        Nand {
            id: id,
            a: false,
            b: false,
            out: false
        }
    }
}

/// The 'weight' of an edge connecting two pins.
/// The edge connects two chips, and its 'weights' determine
/// which ports on those chips are connected.
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct Wire {
    pub from_port: String,
    pub to_port: String,
}

impl Wire {
    pub fn new(from_port: &str, to_port: &str) -> Wire {
        Wire {
            from_port: from_port.into(),
            to_port: to_port.into()
        }
    }
}

pub struct Composite {
    pub id: u32,
    pub name: String,
    pub graph: ChipGraph,
    pub inputs: HashMapFnv<String, Vec<(NodeIndex, String)>>,
    pub outputs: HashMapFnv<String, (NodeIndex, String)>,

    sorted_nodes: Vec<NodeIndex>,
}

impl Chip for Nand {
    fn id(&self) -> u32 {
        self.id
    }

    fn name(&self) -> String {
        "NAND".into()
    }

    fn run(&mut self) {
        log_running(&self.name());
        self.out = !(self.a && self.b);
    }

    fn set_input(&mut self, pin: &str, state: bool) {
        log_input_set(&self.name(), pin, state);
        match pin {
            "a" => self.a = state,
            "b" => self.b = state,
            s => invalid_pin_write("nand", s, vec!["a", "b"])
        };
    }

    fn read_output(&self, pin: &str) -> bool {
        let out = match pin {
            "out" => self.out,
            s => invalid_pin_read("nand", s, vec!["out"])
        };
        log_output_read(&self.name(), pin, out);
        out
    }

    fn input_pins(&self) -> Vec<String> {
        vec!["a".into(), "b".into()]
    }

    fn output_pins(&self) -> Vec<String> {
        vec!["out".into()]
    }
}

impl Chip for Composite {
    fn id(&self) -> u32 {
        self.id
    }

    fn name(&self) -> String {
        self.name.clone()
    }

    // Assumes that inputs have already been set.
    fn run(&mut self) {
        log_running(&self.name());
        for u in &self.sorted_nodes {
            self.graph.node_weight_mut(*u).unwrap().run();

            let mut neighbours = self.graph
                .neighbors_directed(*u, Direction::Outgoing)
                .detach();

            while let Some((e, v)) = neighbours.next(&self.graph) {
                let wire = self.graph.edge_weight(e).unwrap().clone();
                let state = self.graph.node_weight(*u).unwrap().read_output(&wire.from_port);
                self.graph.node_weight_mut(v).unwrap().set_input(&wire.to_port, state);
            }
        }
    }

    fn set_input(&mut self, pin: &str, state: bool) {
        log_input_set(&self.name(), pin, state);
        if !self.inputs.contains_key(&pin.to_string()) {
            invalid_pin_write(&self.name, pin, self.inputs.keys().map(|a| &**a).collect::<Vec<_>>())
        }
        let node_pins = self.inputs.get(pin).unwrap();
        for &(node, ref inner_pin) in node_pins.into_iter() {
            let mut chip = self.graph.node_weight_mut(node).unwrap();
            chip.set_input(&inner_pin, state);
        }
    }

    fn read_output(&self, pin: &str) -> bool {
        if !self.outputs.contains_key(&pin.to_string()) {
            invalid_pin_read(&self.name, pin, self.outputs.keys().map(|a| &**a).collect::<Vec<_>>())
        }
        let &(node, ref inner_pin) = self.outputs.get(pin).unwrap();
        let chip = self.graph.node_weight(node).unwrap();
        let out = chip.read_output(&inner_pin);
        log_output_read(&self.name(), pin, out);
        out
    }

    fn input_pins(&self) -> Vec<String> {
        self.inputs.keys().map(|x| x.clone()).collect()
    }

    fn output_pins(&self) -> Vec<String> {
        self.outputs.keys().map(|x| x.clone()).collect()
    }
}

fn invalid_pin_read(chip_name: &str, pin_name: &str, available: Vec<&str>) -> ! {
    panic!(format!(
        "Attempting to read invalid pin {} on chip {}. The available output pins are: {}",
        pin_name, chip_name, join(available.iter(), ", ")));
}

fn invalid_pin_write(chip_name: &str, pin_name: &str, available: Vec<&str>) -> ! {
    panic!(format!(
        "Attempting to write invalid pin {} on chip {}. The available input pins are: {}",
        pin_name, chip_name, join(available.iter(), ", ")));
}

const DEBUG_CHIPS: bool = false;

fn log_running(name: &str) {
    if DEBUG_CHIPS {
        println!("Running {}", name);
    }
}

fn log_input_set(name: &str, pin: &str, state: bool) {
    if DEBUG_CHIPS {
        println!("Setting {}:{} to {}", name, pin, state);
    }
}

fn log_output_read(name: &str, pin: &str, state: bool) {
    if DEBUG_CHIPS {
        println!("Read {}:{} and got {}", name, pin, state);
    }
}


pub fn nand(f: &mut ChipFactory) -> Nand {
    f.nand()
}

pub fn not(f: &mut ChipFactory) -> Composite {
    let mut g = ChipGraph::new();
    let nand = gate!(g, nand(f));

    f.composite("NOT", g,
        inputs!(in -> nand;a, in -> nand;b),
        outputs!(out <- nand;out))
}

pub fn not_primitive(f: &mut ChipFactory) -> Primitive {
    f.primitive("NOT",
        hashmap!["in".into() => false],
        hashmap!["out".into() => false],
        Box::new(|i, o| {
            o.insert("out".into(), !i["in"]);
        })
    )
}

pub fn not16(f: &mut ChipFactory) -> Composite {
    let mut inputs = HashMapFnv::default();
    let mut outputs = HashMapFnv::default();
    let mut g = ChipGraph::new();

    for i in 0..16 {
        let nand = gate!(g, nand(f));
        input!(inputs, in[i] -> nand;a, in[i] -> nand;b);
        output!(outputs, out[i] <- nand;out);
    }

    f.composite("NOT16", g, inputs, outputs)
}

pub fn or(f: &mut ChipFactory) -> Composite {
    let mut g = ChipGraph::new();

    let nand = gate!(g, nand(f));
    let not1 = gate!(g, not(f));
    let not2 = gate!(g, not(f));
    wire!(g, not1;out -> nand;a, not2;out -> nand;b);

    f.composite("OR", g,
        inputs!(a -> not1;in, b -> not2;in),
        outputs!(out <- nand;out))
}

pub fn or8way(f: &mut ChipFactory) -> Composite {
    let mut g = ChipGraph::new();

    let mut ors = vec![];
    for _ in 0..7 {
        ors.push(gate!(g, or(f)));
    }

    wire!(g,
        ors[0];out -> ors[4];a, ors[1];out -> ors[4];b,
        ors[2];out -> ors[5];a, ors[3];out -> ors[5];b,
        ors[4];out -> ors[6];a, ors[5];out -> ors[6];b);

    f.composite("OR8WAY", g,
        inputs!(in0 -> ors[0];a, in1 -> ors[0];b,
                in2 -> ors[1];a, in3 -> ors[1];b,
                in4 -> ors[2];a, in5 -> ors[2];b,
                in6 -> ors[3];a, in7 -> ors[3];b),
        outputs!(out <- ors[6];out))
}

pub fn or16(f: &mut ChipFactory) -> Composite {
    let mut inputs = HashMapFnv::default();
    let mut outputs = HashMapFnv::default();
    let mut g = ChipGraph::new();

    for i in 0..16 {
        let not1 = gate!(g, not(f));
        let not2 = gate!(g, not(f));
        let nand = gate!(g, nand(f));
        wire!(g, not1;out -> nand;a, not2;out -> nand;b);
        input!(inputs, a[i] -> not1;in, b[i] -> not2;in);
        output!(outputs, out[i] <- nand;out);
    }

    f.composite("OR16", g, inputs, outputs)
}

pub fn and(f: &mut ChipFactory) -> Composite {
    let mut g = ChipGraph::new();

    let not = gate!(g, not(f));
    let nand = gate!(g, nand(f));
    wire!(g, nand;out -> not;in);

    f.composite("AND", g,
        inputs!(a -> nand;a, b -> nand;b),
        outputs!(out <- not;out))
}

pub fn and16(f: &mut ChipFactory) -> Composite {
    let mut inputs = HashMapFnv::default();
    let mut outputs = HashMapFnv::default();
    let mut g = ChipGraph::new();

    for i in 0..16 {
        let not = gate!(g, not(f));
        let nand = gate!(g, nand(f));
        wire!(g, nand;out -> not;in);
        input!(inputs, a[i] -> nand;a, b[i] -> nand;b);
        output!(outputs, out[i] <- not;out);
    }

    f.composite("AND16", g, inputs, outputs)
}

pub fn mux(f: &mut ChipFactory) -> Composite {
    let mut g = ChipGraph::new();

    let not = gate!(g, not(f));
    let and1 = gate!(g, and(f));
    let and2 = gate!(g, and(f));
    let or = gate!(g, or(f));
    wire!(g, not;out -> and2;b, and1;out -> or;b, and2;out -> or;a);

    f.composite("MUX", g,
        inputs!(sel -> not;in, sel -> and1;a, a -> and2;a, b -> and1;b),
        outputs!(out <- or;out))
}

// TODO: MUX4WAY16 (16-bit bus, 2 sel bits)
// TODO: MUX8WAY16 (16-bit bus, 3 sel bits)
// TODO: DMUX4WAY (2 sel bits)
// TODO: DMUX8WAY (3 sel bits)

pub fn mux16(f: &mut ChipFactory) -> Composite {
    let mut inputs = HashMapFnv::default();
    let mut outputs = HashMapFnv::default();
    let mut g = ChipGraph::new();

    for i in 0..16 {
        let not = gate!(g, not(f));
        let and1 = gate!(g, and(f));
        let and2 = gate!(g, and(f));
        let or = gate!(g, or(f));
        wire!(g, not;out -> and2;b, and1;out -> or;b, and2;out -> or;a);
        input!(inputs, sel[i] -> not;in, sel[i] -> and1;a, a[i] -> and2;a, b[i] -> and1;b);
        output!(outputs, out[i] <- or;out);
    }

    f.composite("MUX16", g, inputs, outputs)
}

pub fn xor(f: &mut ChipFactory) -> Composite {
    let mut g = ChipGraph::new();

    let nand = gate!(g, nand(f));
    let and = gate!(g, and(f));
    let or = gate!(g, or(f));
    wire!(g, or;out -> and;a, nand;out -> and;b);

    f.composite("XOR", g,
        inputs!(a -> or;a, a -> nand;a, b -> or;b, b -> nand;b),
        outputs!(out <- and;out))
}

pub fn dmux(f: &mut ChipFactory) -> Composite {
    let mut g = ChipGraph::new();

    let not = gate!(g, not(f));
    let and1 = gate!(g, and(f));
    let and2 = gate!(g, and(f));
    wire!(g, not;out -> and1;b);

    f.composite("DMUX", g,
        inputs!(sel -> not;in, sel -> and2;b, in -> and1;a, in -> and2; a),
        outputs!(a <- and1;out, b <- and2;out))
}

pub fn halfadder(f: &mut ChipFactory) -> Composite {
    let mut g = ChipGraph::new();

    let xor = gate!(g, xor(f));
    let and = gate!(g, and(f));

    f.composite("HALFADDER", g,
        inputs!(a -> xor;a, b -> xor;b, a -> and;a, b -> and;b),
        outputs!(sum <- xor;out, carry <- and;out))
}

pub fn fulladder(f: &mut ChipFactory) -> Composite {
    let mut g = ChipGraph::new();

    let half1 = gate!(g, halfadder(f));
    let half2 = gate!(g, halfadder(f));
    let or = gate!(g, or(f));

    wire!(g, half1;carry -> or;a, half1;sum -> half2;a, half2;carry -> or;b);

    f.composite("FULLADDER", g,
        inputs!(a -> half1;a, b -> half1;b, c -> half2;b),
        outputs!(sum <- half2;sum, carry <- or;out))
}

pub fn adder8(f: &mut ChipFactory) -> Composite {
    let mut inputs = HashMapFnv::default();
    let mut outputs = HashMapFnv::default();
    let mut g = ChipGraph::new();

    let half = gate!(g, halfadder(f));
    input!(inputs, a[0] -> half;a, b[0] -> half;b);
    output!(outputs, out[0] <- half;sum);

    let mut prev = half;
    for i in 0..7 {
        let full = gate!(g, fulladder(f));
        input!(inputs, a[i + 1] -> full;a, b[i + 1] -> full;b);
        output!(outputs, out[i + 1] <- full;sum);
        wire!(g, prev;carry -> full;c);
        prev = full;
    }

    f.composite("ADDER8", g, inputs, outputs)
}

#[cfg(test)]
mod tests {
    use super::*;

    const PRINT_TRUTH_TABLES: bool = false;

    fn test_against_reference<F>(chip: &mut Chip,
                                 input_names: Vec<&str>,
                                 output_names: Vec<&str>,
                                 reference: F)
         where F: Fn(&Vec<bool>) -> Vec<bool>
    {
        let num_inputs = input_names.len();
        let num_outputs = output_names.len();
        // TODO: better testing when the input space is large
        // TODO: this will presumably involve doing random rather than exhaustive
        // TODO: testing, but we first hit issues when enumerating the 2^16 inputs
        // TODO: to adder8, which really shouldn't be a performance issue. remove
        // TODO: the most gratuitous time sinks
        let max_tests = 1000;
        let test_cases = enumerate_bool_vecs(num_inputs, max_tests);

        if PRINT_TRUTH_TABLES {
            let columns = input_names.iter()
                .chain(output_names.iter())
                .map(|n| format!("{name:>width$}", name=n, width=3));

            let header = join(columns, "|");
            println!("{}", header);
            for _ in 0..header.len() {
                print!("-");
            }
            println!();
        }

        for input in &test_cases {
            let expected = reference(input);
            for i in 0..num_inputs {
                chip.set_input(input_names[i], input[i]);
            }
            chip.run();
            let mut actual = vec![];
            for i in 0..num_outputs {
                actual.push(chip.read_output(output_names[i]));
            }

            assert_eq!(actual, expected, "input: {:?}", input);

            if PRINT_TRUTH_TABLES {
                let row = input.iter()
                    .chain(actual.iter())
                    .map(|b| format!("{val:>width$}", val=if *b { "T" } else { "F" }, width=3));

                println!("{}", join(row, "|"));
            }
        }
    }

    fn test_against_primitive(composite: &mut Composite,
                              primitive: &mut Primitive,
                              input_names: Vec<&str>,
                              output_names: Vec<&str>)
    {
        // TODO: check compositive and primitive have the same inputs and outputs

        let num_inputs = input_names.len();
        let num_outputs = output_names.len();
        // TODO: better testing when the input space is large
        // TODO: this will presumably involve doing random rather than exhaustive
        // TODO: testing, but we first hit issues when enumerating the 2^16 inputs
        // TODO: to adder8, which really shouldn't be a performance issue. remove
        // TODO: the most gratuitous time sinks
        let max_tests = 1000;
        let test_cases = enumerate_bool_vecs(num_inputs, max_tests);

        if PRINT_TRUTH_TABLES {
            let columns = input_names.iter()
                .chain(output_names.iter())
                .map(|n| format!("{name:>width$}", name=n, width=3));

            let header = join(columns, "|");
            println!("{}", header);
            for _ in 0..header.len() {
                print!("-");
            }
            println!();
        }

        for input in &test_cases {
            for i in 0..num_inputs {
                composite.set_input(input_names[i], input[i]);
                primitive.set_input(input_names[i], input[i]);
            }

            composite.run();
            primitive.run();

            let mut composite_result = vec![];
            let mut primitive_result = vec![];

            for i in 0..num_outputs {
                composite_result.push(composite.read_output(output_names[i]));
                primitive_result.push(primitive.read_output(output_names[i]));
            }

            assert_eq!(composite_result, primitive_result, "input: {:?}", input);

            if PRINT_TRUTH_TABLES {
                let composite_rows = input.iter()
                    .chain(composite_result.iter())
                    .map(|b| format!("{val:>width$}", val=if *b { "T" } else { "F" }, width=3));

                println!("Composite");
                println!("{}", join(composite_rows, "|"));

                let primitive_rows = input.iter()
                    .chain(primitive_result.iter())
                    .map(|b| format!("{val:>width$}", val=if *b { "T" } else { "F" }, width=3));

                println!("Primitive");
                println!("{}", join(primitive_rows, "|"));
            }
        }
    }

    fn not_ref(inputs: &Vec<bool>) -> Vec<bool> {
        assert_eq!(inputs.len(), 1);
        vec![!inputs[0]]
    }

    #[test]
    fn run_not() {
        let mut f = ChipFactory::new();
        let mut c = not(&mut f);
        assert_eq!("NOT", c.name());
        test_against_reference(&mut c, vec!["in"], vec!["out"], not_ref);
        let mut p = not_primitive(&mut f);
        test_against_primitive(&mut c, &mut p, vec!["in"], vec!["out"]);
    }

    fn or_ref(inputs: &Vec<bool>) -> Vec<bool> {
        assert_eq!(inputs.len(), 2);
        vec![inputs[0] || inputs[1]]
    }

    #[test]
    fn run_or() {
        let mut f = ChipFactory::new();
        let mut c = or(&mut f);
        assert_eq!("OR", c.name());
        test_against_reference(&mut c, vec!["a", "b"], vec!["out"], or_ref);
    }

    fn xor_ref(inputs: &Vec<bool>) -> Vec<bool> {
        assert_eq!(inputs.len(), 2);
        vec![(inputs[0] || inputs[1]) && !(inputs[0] && inputs[1])]
    }

    #[test]
    fn run_xor() {
        let mut f = ChipFactory::new();
        let mut c = xor(&mut f);
        assert_eq!("XOR", c.name());
        test_against_reference(&mut c, vec!["a", "b"], vec!["out"], xor_ref);
    }

    fn or8way_ref(inputs: &Vec<bool>) -> Vec<bool> {
        assert_eq!(inputs.len(), 8);
        vec![inputs.iter().any(|x| *x)]
    }

    #[test]
    fn run_or8way() {
        let mut f = ChipFactory::new();
        let mut c = or8way(&mut f);
        assert_eq!("OR8WAY", c.name());
        test_against_reference(&mut c,
            vec!["in0", "in1", "in2", "in3", "in4", "in5", "in6", "in7"],
            vec!["out"],
            or8way_ref);
    }

    fn and_ref(inputs: &Vec<bool>) -> Vec<bool> {
        assert_eq!(inputs.len(), 2);
        vec![inputs[0] && inputs[1]]
    }

    #[test]
    fn run_and() {
        let mut f = ChipFactory::new();
        let mut c = and(&mut f);
        assert_eq!("AND", c.name());
        test_against_reference(&mut c, vec!["a", "b"], vec!["out"], and_ref);
    }

    fn mux_ref(inputs: &Vec<bool>) -> Vec<bool> {
        assert_eq!(inputs.len(), 3);
        let sel = inputs[0];
        let a = inputs[1];
        let b = inputs[2];
        vec![(!sel && a) || (sel && b)]
    }

    #[test]
    fn run_mux() {
        let mut f = ChipFactory::new();
        let mut c = mux(&mut f);
        assert_eq!("MUX", c.name());
        test_against_reference(&mut c, vec!["sel", "a", "b"], vec!["out"], mux_ref);
    }

    fn halfadder_ref(inputs: &Vec<bool>) -> Vec<bool> {
        assert_eq!(inputs.len(), 2);
        let sum = xor_ref(inputs)[0];
        let carry = and_ref(inputs)[0];
        vec![sum, carry]
    }

    #[test]
    fn run_halfadder() {
        let mut f = ChipFactory::new();
        let mut c = halfadder(&mut f);
        assert_eq!("HALFADDER", c.name());
        test_against_reference(&mut c, vec!["a", "b"], vec!["sum", "carry"], halfadder_ref);
    }

    fn fulladder_ref(inputs: &Vec<bool>) -> Vec<bool> {
        assert_eq!(inputs.len(), 3);
        let total = inputs.iter().filter(|x| **x).count();
        let sum = total & 1 > 0;
        let carry = total & 2 > 0;
        vec![sum, carry]
    }

    #[test]
    fn run_fulladder() {
        let mut f = ChipFactory::new();
        let mut c = fulladder(&mut f);
        assert_eq!("FULLADDER", c.name());
        test_against_reference(&mut c, vec!["a", "b", "c"], vec!["sum", "carry"], fulladder_ref);
    }

    // LSB first
    fn to_i8(bits: &[bool]) -> i8 {
        assert_eq!(bits.len(), 8);
        let signed = bits.iter().rev().fold(0, |acc, &b| acc * 2 + (if b { 1 } else { 0 }));
        signed as i8
    }

    #[test]
    fn test_to_i8() {
        assert_eq!(to_i8(&vec![false, false, false, false, false, false, false, false]), 0);
        assert_eq!(to_i8(&vec![true, true, true, true, true, true, true, false]), 127);
        assert_eq!(to_i8(&vec![true, true, true, true, true, true, true, true]), -1);
        assert_eq!(to_i8(&vec![false, false, false, false, false, false, false, true]), -128);
        assert_eq!(to_i8(&vec![true, false, true, false, false, false, false, false]), 5);
    }

    // LSB first
    fn to_bool_vec(n: i8) -> Vec<bool> {
        let mut vec = vec![false; 8];
        let u = n as u8;
        for i in 0..8 {
            if u & (1 << i) > 0 {
                vec[i] = true;
            }
        }
        vec
    }

    #[test]
    fn test_to_bool_vec() {
        assert_eq!(to_bool_vec(0), vec![false, false, false, false, false, false, false, false]);
        assert_eq!(to_bool_vec(127), vec![true, true, true, true, true, true, true, false]);
        assert_eq!(to_bool_vec(-1), vec![true, true, true, true, true, true, true, true]);
        assert_eq!(to_bool_vec(-128), vec![false, false, false, false, false, false, false, true]);
        assert_eq!(to_bool_vec(5), vec![true, false, true, false, false, false, false, false]);
    }

    fn adder8_ref(inputs: &Vec<bool>) -> Vec<bool> {
        assert_eq!(inputs.len(), 16);
        let a = to_i8(&inputs[0..8]);
        let b = to_i8(&inputs[8..16]);
        let sum = a.wrapping_add(b);
        to_bool_vec(sum as i8)
    }

    #[test]
    fn run_adder8() {
        let mut f = ChipFactory::new();
        let mut c = adder8(&mut f);
        assert_eq!("ADDER8", c.name());
        test_against_reference(&mut c,
            vec!["a_0", "a_1", "a_2", "a_3", "a_4", "a_5", "a_6", "a_7",
                 "b_0", "b_1", "b_2", "b_3", "b_4", "b_5", "b_6", "b_7",],
            vec!["out_0", "out_1", "out_2", "out_3", "out_4", "out_5", "out_6", "out_7"],
            adder8_ref);
    }
}
