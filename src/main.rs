use std::env;
use metamast::mm_parser::parse_metamath;

fn main() {
    let args: Vec<String> = env::args().collect();
    let filename = &args[1];

    parse_metamath(filename.as_str());

    println!("Done");
}

