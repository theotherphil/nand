
extern crate fnv;
extern crate petgraph;

#[macro_use]
pub mod utils;
#[macro_use]
pub mod chip;
pub mod dot;
pub mod graph_algorithms;

use std::io::Write;
use std::fs::File;
use std::fs;
use std::io;
use std::path::Path;
use dot::*;
use chip::*;

fn generate_dot_files<P: AsRef<Path>>(dir: P) -> io::Result<()> {
    for chip in CHIPS {
        let g = create_chip(*chip);
        let dot_path = dir.as_ref().join(chip.to_string() + ".dot");
        let mut f = File::create(&dot_path)?;
        let mut renderer = GraphRenderer::new(*chip, &mut f);
        g.render(&mut renderer);
    }
    Ok(())
}

fn generate_svg_files<P: AsRef<Path>>(dir: P) -> io::Result<()> {
    for chip in CHIPS {
        let dot_path = dir.as_ref().join(chip.to_string() + ".dot");
        run_dot(&dot_path);
    }
    Ok(())
}

fn write_chips_page<P: AsRef<Path>>(dir: P) -> io::Result<()> {
    let chips_page = dir.as_ref().join("chips.html");
    let mut f = File::create(chips_page)?;

    f.write("<html>".as_bytes()).unwrap();
    f.write("<body>".as_bytes()).unwrap();
    for chip in CHIPS {
        let chip_path = dir.as_ref().join(format!("{}.dot.svg", chip));
        write!(&mut f, "<p><img src={:?}></img></p>", chip_path).unwrap();
    }
    f.write("</body>".as_bytes()).unwrap();
    f.write("</html>".as_bytes()).unwrap();

    Ok(())
}

fn main() {
    run().unwrap();
}

fn run() -> io::Result<()> {
    let chips_dir = std::env::current_dir()?.join("chips");
    if !chips_dir.exists() {
        fs::create_dir(&chips_dir)?;
    }
    generate_dot_files(&chips_dir)?;
    generate_svg_files(&chips_dir)?;
    write_chips_page(&chips_dir)?;
    Ok(())
}
