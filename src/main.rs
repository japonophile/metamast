use std::fs;

use metamast::mm_parser::parse_program;

fn main() {
    let filename = "mm/lib/set.mm";
    let program = fs::read_to_string(filename)
        .expect("Could not read file");

    parse_program(&program);

    println!("Done");
}

