use std::path::Path;
use pest::Parser;
use regex::Regex;
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

pub fn parse_program(program: &str) {
    println!("Parse program");
    let result = MetamathParser::parse(Rule::database, program)
        .expect("Parse error")
        .next().unwrap();
    println!("Result: {:?}", result);
}

pub fn parse_metamath(filename: &str) {
    let io = FileIO {};
    let (program, _included_files) = read_file(&io, filename, vec![], ".").unwrap();
    parse_program(&program);
}

