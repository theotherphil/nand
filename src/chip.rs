
use petgraph::prelude::*;
use std::collections::HashMap;
use graph_algorithms::*;
use utils::*;

pub const CHIPS: &'static [&'static str] =
    &["NOT", "OR", "AND", "XOR", "MUX", "DMUX",
      "NOT16", "OR16", "AND16", "MUX16", "OR8WAY",
      "HALFADDER"];

pub fn create_chip(chip: &str) -> Composite {
    let mut factory = ChipFactory::new();
    match chip {
        "NOT" => not(&mut factory),
        "OR" => or(&mut factory),
        "AND" => and(&mut factory),
        "XOR" => xor(&mut factory),
        "MUX" => mux(&mut factory),
        "DMUX" => dmux(&mut factory),
        "NOT16" => not16(&mut factory),
        "OR16" => or16(&mut factory),
        "AND16" => and16(&mut factory),
        "MUX16" => mux16(&mut factory),
        "OR8WAY" => or8way(&mut factory),
        "HALFADDER" => halfadder(&mut factory),
        _ => panic!("Unrecognised chip")
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
        let mut map = ::std::collections::HashMap::new();
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
        let mut map = ::std::collections::HashMap::new();
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
pub struct Nand {
    id: u32,
    a: bool,
    b: bool,
    out: bool
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
                 inputs: HashMap<String, Vec<(NodeIndex, String)>>,
                 outputs: HashMap<String, (NodeIndex, String)>) -> Composite {
        let composite = Composite {
            id: self.chip_count,
            name: name.into(),
            graph: graph,
            inputs: inputs,
            outputs: outputs
        };
        self.chip_count += 1;
        composite
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
    pub inputs: HashMap<String, Vec<(NodeIndex, String)>>,
    pub outputs: HashMap<String, (NodeIndex, String)>,
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
        let nodes = topological_sort(&self.graph);
        for u in nodes {
            self.graph.node_weight_mut(u).unwrap().run();

            // It appears that I can't just iterate over edges here, due to lifetime
            // issues when mutating the graph.
            let neighbours: Vec<NodeIndex>
                = self.graph.neighbors_directed(u, Direction::Outgoing).collect();

            for v in neighbours {
                let e = self.graph.find_edge(u, v).unwrap();
                let wire = self.graph.edge_weight(e).unwrap().clone();
                let state = self.graph.node_weight(u).unwrap().read_output(&wire.from_port);
                self.graph.node_weight_mut(v).unwrap().set_input(&wire.to_port, state);
            }
        }
    }

    fn set_input(&mut self, pin: &str, state: bool) {
        log_input_set(&self.name(), pin, state);
        if !self.inputs.contains_key(&pin.to_string()) {
            invalid_pin_write(&self.name, pin, self.inputs.keys().map(|a| &**a).collect::<Vec<_>>())
        }
        let node_pins = self.inputs[&pin.to_string()].clone();
        for (node, inner_pin) in node_pins.into_iter() {
            let mut chip = self.graph.node_weight_mut(node).unwrap();
            chip.set_input(&inner_pin, state);
        }
    }

    fn read_output(&self, pin: &str) -> bool {
        if !self.outputs.contains_key(&pin.to_string()) {
            invalid_pin_read(&self.name, pin, self.outputs.keys().map(|a| &**a).collect::<Vec<_>>())
        }
        let (node, inner_pin) = self.outputs[&pin.to_string()].clone();
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
        "Attempting to read invalid pin {} on chip {}. The available inputs pins are: {}",
        pin_name, chip_name, join(available.iter(), ", ")));
}

fn invalid_pin_write(chip_name: &str, pin_name: &str, available: Vec<&str>) -> ! {
    panic!(format!(
        "Attempting to write invalid pin {} on chip {}. The available output pins are: {}",
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

pub fn not16(f: &mut ChipFactory) -> Composite {
    let mut inputs = HashMap::new();
    let mut outputs = HashMap::new();
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
    let mut inputs = HashMap::new();
    let mut outputs = HashMap::new();
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
    let mut inputs = HashMap::new();
    let mut outputs = HashMap::new();
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
    let mut inputs = HashMap::new();
    let mut outputs = HashMap::new();
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
        let test_cases = enumerate_bool_vecs(num_inputs);

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
            assert_eq!(actual, expected);

            if PRINT_TRUTH_TABLES {
                let row = input.iter()
                    .chain(actual.iter())
                    .map(|b| format!("{val:>width$}", val=if *b { "T" } else { "F" }, width=3));

                println!("{}", join(row, "|"));
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
}
