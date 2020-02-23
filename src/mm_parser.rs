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
            Some(j) => {
                println!("Found");
                i = j;
                match find_start_at(&program, i, "$)") {
                    Some(k) => {
                        let mut p = program[..i].to_string();
                        p.push_str(&program[(k+2)..]);
                        program = p;
                    }
                    None => {
                        return Err("Malformed comment");
                    }
                }
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

