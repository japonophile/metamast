use pest::Parser;

#[derive(Parser)]
#[grammar = "mm.pest"]
pub struct MetamathParser;

fn find_start_at<'a>(slice: &'a str, at: usize, pat: &'a str) -> Option<usize> {
    slice[at..].find(pat).map(|i| at + i)
}

pub fn strip_comments(_text: &str) -> Result<String, &str> {
    let mut program = String::from(_text);
    let mut i = 0;
    loop {
        match find_start_at(&program, i, "$(") {
            Some(start) => {
                match find_start_at(&program, i, "$)") {
                    Some(end) => {
                        if end < start {
                            return Err("Malformed comment");
                        }
                        match find_start_at(&program, start + 2, "$(") {
                            Some(next_comment) => if next_comment < end {
                                return Err("Comments may not be nested");
                            }
                            None => ()
                        }
                        let mut p = program[..start].to_string();
                        p.push_str(&program[(end + 2)..]);
                        program = p;
                    }
                    None => {
                        return Err("Malformed comment");
                    }
                }
                i = start;
            }
            None => break,
        }
        if i >= program.len() {
            break;
        }
    }
    return Ok(program);
}

pub fn parse_program(_program: &str) {
    let result = MetamathParser::parse(Rule::database, _program)
        .expect("Parse error")
        .next().unwrap();
    println!("Result: {:?}", result);
}

