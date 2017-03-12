
use std::ffi::OsStr;
use std::process::Command;
use std::path::Path;
use std::io::Write;
use chip::*;
use utils::*;

// TODO:
//     subgraph inputs {
//         rank="min";
// ...
//     subgraph output {
//         rank="max";
// ...
//         subgraph inner_inputs {
//             rank="same";
//             a_inner [shape=point];
//             b_inner [shape=point];
//             sel_inner [shape=point];
//         }
//

pub fn run_dot<P: AsRef<Path> + AsRef<OsStr>>(dot_file: P) {
    let status = Command::new("/usr/local/bin/dot")
                         .arg(dot_file)
                         .arg("-Tsvg")
                         .arg("-O")
                         .status()
                         .expect("Failed to run dot");

    assert!(status.success());
}

/// At some point we might want to convert chips into a dot-specific Graph type
/// but for now we'll just write the dot contents directly from the chips.
pub trait Renderable {
    fn render<'a, W: Write + 'a>(&self, r: &mut GraphRenderer<'a, W>);
}

impl Renderable for Nand {
    // For writing recursive rendering we want to make the inputs and outputs
    // optional here. Making Chip an enum instead of a trait would help a lot
    fn render<'a, W: Write + 'a>(&self, r: &mut GraphRenderer<'a, W>) {
        r.add_input("a".into(), vec![
            (self.name(), self.id(), "a".into()),
            (self.name(), self.id(), "b".into())
        ]);
        r.add_output("out".into(), (self.name(), self.id(), "out".into()));
        r.add_node(self.name(), self.id(), vec!["a".into(), "b".into()], vec!["out".into()]);
        r.complete();
    }
}

impl Renderable for Composite {
    fn render<'a, W: Write + 'a>(&self, r: &mut GraphRenderer<'a, W>) {
        for input in &self.inputs {
            let mut targets = Vec::new();
            for node_and_port in input.1 {
                let chip = self.graph.node_weight(node_and_port.0).unwrap();
                targets.push((chip.name(), chip.id(), node_and_port.1.clone()));
            }
            r.add_input(input.0.clone(), targets);
        }
        for output in &self.outputs {
            let node_and_port = output.1;
            let chip = self.graph.node_weight(node_and_port.0).unwrap();
            let source = (chip.name(), chip.id(), node_and_port.1.clone());
            r.add_output(output.0.clone(), source);
        }
        for node in self.graph.node_indices() {
            let chip = self.graph.node_weight(node).unwrap();
            let inputs = chip.input_pins();
            let outputs = chip.output_pins();
            r.add_node(chip.name(), chip.id(), inputs, outputs);
        }
        for edge in self.graph.raw_edges() {
            let ref wire = edge.weight;
            let from_chip = self.graph.node_weight(edge.source()).unwrap();
            let to_chip = self.graph.node_weight(edge.target()).unwrap();
            r.add_edge(
                from_chip.name(), from_chip.id(), wire.from_port.clone(),
                to_chip.name(), to_chip.id(), wire.to_port.clone());
        }
        r.complete();
    }
}

pub struct GraphRenderer<'a, W: Write + 'a> {
    w: &'a mut W,
    edges: Vec<(String, String, String, String, String, String)>
}

impl<'a, W: Write> GraphRenderer<'a, W> {
    // Do I need the Chip trait, or should I just make it an enum?
    // data Chip = Composite(Composite) | Primitive(Primitive)
    // enum would mean that I could write a single render impl, and would allow
    // recursive expansion of chips when rendering. It would also avoid the need
    // to box everything.

    pub fn add_input(&mut self, name: String, targets: Vec<(String, u32, String)>) {
        writeln!(self.w, "{} [label={},shape=plaintext];", name, name).unwrap();
        for target in targets {
            let target_port = format!("{}_{}:{}", target.0, target.1, target.2);
            writeln!(self.w, "{}->{};", name, target_port).unwrap();
        }
    }

    pub fn add_output(&mut self, name: String, source: (String, u32, String)) {
        writeln!(self.w, "{} [label={},shape=plaintext];", name, name).unwrap();
        let source_port = format!("{}_{}:{}", source.0, source.1, source.2);
        writeln!(self.w, "{}->{};", source_port, name).unwrap();
    }

    pub fn add_node(&mut self, name: String, id: u32, input_pins: Vec<String>, output_pins: Vec<String>) {
        let id = format!("{}_{}", name, id);
        let label = label_with_fields2(input_pins, output_pins, name);
        writeln!(self.w, "{} [shape=record,label={}];", id, label).unwrap();
    }

    pub fn add_edge(&mut self,
                    from_name: String, from_id: u32, from_port: String,
                    to_name: String, to_id: u32, to_port: String) {
        self.edges.push((
            from_name, from_id.to_string(), from_port,
            to_name, to_id.to_string(), to_port));
    }

    pub fn new(name: &str, w: &'a mut W) -> GraphRenderer<'a, W> {
        writeln!(w, "digraph {} {{", name).unwrap();
        writeln!(w, "graph [rankdir=LR];").unwrap();
        writeln!(w, "edge [arrowsize=0.5];").unwrap();
        writeln!(w, "label={}", name).unwrap();
        GraphRenderer {
            w: w,
            edges: vec![]
        }
    }

    pub fn complete(&mut self) {
        for edge in &self.edges {
            let from = format!("{}_{}:{}", edge.0, edge.1, edge.2);
            let to = format!("{}_{}:{}", edge.3, edge.4, edge.5);
            writeln!(self.w, "{}->{};", from, to).unwrap();
        }
        writeln!(self.w, "}}").unwrap();
    }
}

fn label_with_fields2(inputs: Vec<String>, outputs: Vec<String>, text: String) -> String {
    let mut label = String::from("\"{{");
    label.push_str(&join(inputs.iter().map(|i| format!("<{x}>{x}", x = i)), "|"));
    label.push_str("}");
    label.push_str(&format!("|{}|", text));
    label.push_str("{");
    label.push_str(&join(outputs.iter().map(|i| format!("<{x}>{x}", x= i)), "|"));
    label.push_str("}}\"");
    label
}
