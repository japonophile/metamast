use std::fs;
extern crate pest;
#[macro_use]
extern crate pest_derive;

use pest::Parser;

#[derive(Parser)]
#[grammar = "mm.pest"]
pub struct MetamathParser;

fn main() {
    let filename = "mm/lib/set.mm";
    let program = fs::read_to_string(filename)
        .expect("Could not read file");

    let result = MetamathParser::parse(Rule::database, &program)
        .expect("Parse error")
        .next().unwrap();

    println!("Parse result: {:?}", result);
}

