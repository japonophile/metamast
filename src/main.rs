use std::env;
use metamast::mm_parser::{ parse_metamath, verify_proofs };

fn main() {
    let args: Vec<String> = env::args().collect();
    let filename = &args[1];
    let program = parse_metamath(filename.as_str());
    verify_proofs(&program);
    println!("Done");
}

