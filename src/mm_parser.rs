use std::fmt;
use pest::Parser;
use pest::iterators::Pair;
use regex::Regex;
use std::path::Path;
use crate::io::{IO, FileIO};

#[derive(Parser)]
#[grammar = "mm.pest"]
pub struct MetamathParser;

pub fn strip_comments<'a>(program: &'a str) -> Result<String, &'a str> {
    let mut processed = "".to_string();
    let mut rest = program;

    loop {
        match rest.find("$(") {
            Some(start) => {
                match rest.find("$)") {
                    Some(end) => {
                        if end < start {
                            return Err("Malformed comment");
                        }
                        match rest[(start + 2)..].find("$(") {
                            Some(next_comment) => if next_comment < (end - (start + 2)) {
                                return Err("Comments may not be nested");
                            }
                            None => ()
                        }
                        processed.push_str(&rest[..start]);
                        rest = &rest[(end + 2)..];
                    }
                    None => {
                        return Err("Malformed comment");
                    }
                }
            }
            None => {
                processed.push_str(&rest);
                break
            },
        }
    }

    return Ok(processed.to_string());
}

fn read_file<'a>(io: &dyn IO, filename: &str, includes: Vec<String>, root: &str) -> Result<(String, Vec<String>), &'a str> {
    let full_path = format!("{}/{}", root, filename);
    let file_content = io.slurp(&full_path);
    let new_root = Path::new(&full_path).parent().unwrap().to_str().unwrap();

    return load_includes(io, strip_comments(&file_content).unwrap(), includes, new_root);
}

pub fn load_includes<'a>(io: &dyn IO, program: String, includes: Vec<String>, root: &str) -> Result<(String, Vec<String>), &'a str> {
    lazy_static! {
        static ref INCLUDE_FILENAME_REGEX: Regex = Regex::new("\\$\\[\\s+(?P<filename>[^\\$]+)\\s+\\$\\]").unwrap();
        static ref BLOCK_AND_INCLUDE_REGEX: Regex = Regex::new("(\\$[{}])|(\\$\\[\\s+[^\\$]+\\s+\\$\\])").unwrap();
    }

    let mut updated_includes = includes.to_vec();
    let mut processed = "".to_string();
    let mut rest = program.as_str();

    loop {
        if !INCLUDE_FILENAME_REGEX.is_match(rest) {
            processed.push_str(rest);
            break;
        }

        let filename = &INCLUDE_FILENAME_REGEX.captures(rest).unwrap()["filename"];

        let mut depth = 0;
        for c in BLOCK_AND_INCLUDE_REGEX.find_iter(rest) {
            match &rest[c.start()..(c.start()+2)] {
                "${" => depth += 1,
                "$}" => depth -= 1,
                "$[" => {
                    if depth == 0 {
                        processed.push_str(&rest[..c.start()]);
                        if !updated_includes.iter().any(|e| e == &filename) {
                            updated_includes.push(filename.to_owned());
                            let result = read_file(io, &filename, updated_includes, root);
                            match result {
                                Ok((file_content, included_files)) => {
                                    processed.push_str(&file_content);
                                    updated_includes = included_files;
                                },
                                _ => return result
                            }
                        }
                        rest = &rest[c.end()..];
                        break;
                    }
                    else {
                        return Err("Include statement only allowed in outermost scope");
                    }
                },
                // This should never be reached
                _ => return Err("Malformed include statement"),
            }
        }
    }

    return Ok((processed.to_string(), updated_includes));
}

pub struct Program {
    constants: Vec<String>,
    variables: Vec<String>
}

pub fn parse_constant_stmt<'a>(stmt: Pair<Rule>, program: Program) -> Result<Program, String> {
    println!("Parse constant_stmt");
    let mut program = program;
    for constant in stmt.into_inner() {
        let c = constant.as_span().as_str();
        if program.constants.contains(&c.to_string()) {
            return Err(format!("Constant {} was already defined before", c));
        }
        println!("  Constant: {}", c);
        program.constants.push(c.to_string());
    }
    return Ok(program);
}

pub fn parse_variable_stmt<'a>(stmt: Pair<Rule>, program: Program) -> Result<Program, String> {
    println!("Parse variable_stmt");
    let mut program = program;
    for variable in stmt.into_inner() {
        let v = variable.as_span().as_str();
        if program.variables.contains(&v.to_string()) {
            return Err(format!("Variable {} was already defined before", v));
        }
        println!("  Variable: {}", v);
        program.variables.push(v.to_string());
    }
    return Ok(program);
}

pub fn traverse_tree<'a>(tree: Pair<Rule>, program: Program) -> Result<Program, String> {
    match tree.as_rule() {
        Rule::constant_stmt => return parse_constant_stmt(tree, program),
        Rule::variable_stmt => return parse_variable_stmt(tree, program),
        _ => {
            println!("Statement: {:?}", tree.as_rule());
            return tree.into_inner().fold(Ok(program),
                |p, rule| match p {
                    Ok(prog) => traverse_tree(rule, prog),
                    Err(e) => Err(e)
                });
        }
    }
}

impl std::fmt::Display for Program {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Constants: {:?}, Variables: {:?}", self.constants, self.variables)
    }
}

pub fn parse_program(program: &str) -> Result<Program, String> {
    println!("Parse program");
    let tree = MetamathParser::parse(Rule::database, program)
        .expect("Parse error")
        .next().unwrap();
    println!("Result: {:?}", tree);
    return traverse_tree(tree, Program { constants: vec![], variables: vec![] });
}

pub fn parse_metamath(filename: &str) {
    let io = FileIO {};
    let (program_text, _included_files) = read_file(&io, filename, vec![], ".").unwrap();
    let program = parse_program(&program_text);
    println!("Result: {}", program.unwrap());
}

