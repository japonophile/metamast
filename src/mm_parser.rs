use pest::Parser;
use pest::iterators::Pair;
use regex::Regex;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt;
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

    Ok(processed.to_string())
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

    Ok((processed.to_string(), updated_includes))
}

#[derive(Clone, Debug)]
pub struct Floating {
    pub typ: String,
    pub var: String
}

#[derive(Debug)]
pub struct TypedSymbols {
    pub typ: String,
    pub syms: Vec<String>
}

#[derive(Debug)]
pub struct Scope {
    pub variables: Vec<String>,
    pub floatings: HashMap<String, Floating>,
    pub essentials: HashMap<String, TypedSymbols>,
    pub disjoints: Vec<(String, String)>
}

#[derive(Debug)]
pub enum Proof {
    Uncompressed {
        syms: Vec<String>
    },
    Compressed {
        chars: String
    }
}

#[derive(Debug)]
pub struct Axiom {
    pub ax: TypedSymbols,
    pub scope: Scope
}

#[derive(Debug)]
pub struct Provable {
    pub ax: TypedSymbols,
    pub proof: Proof,
    pub scope: Scope
}

pub struct Program {
    pub constants: Vec<String>,
    pub variables: Vec<String>,
    pub vartypes: HashMap<String, String>,
    pub labels: Vec<String>,
    pub axioms: HashMap<String, Axiom>,
    pub provables: HashMap<String, Provable>,
    pub scope: Scope
}

impl Clone for TypedSymbols {
    fn clone(&self) -> TypedSymbols {
        TypedSymbols {
            typ: self.typ.clone(),
            syms: self.syms.clone()
        }
    }
}

impl Clone for Scope {
    fn clone(&self) -> Scope {
        Scope {
            variables: self.variables.to_vec(),
            floatings: self.floatings.clone(),
            essentials: self.essentials.clone(),
            disjoints: self.disjoints.to_vec()
        }
    }
}

impl std::fmt::Display for Scope {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Variables: {:?}\nFloatings: {:?}\nEssentials: {:?}\nDisjoints: {:?}",
               self.variables, self.floatings, self.essentials, self.disjoints)
    }
}

impl std::fmt::Display for Program {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Constants: {:?}, Scope: {}", self.constants, self.scope)
    }
}

pub fn parse_constant_stmt(stmt: Pair<Rule>, program: Program) -> Result<Program, String> {
    println!("Parse constant_stmt");
    let mut program = program;
    for constant in stmt.into_inner() {
        let c = constant.as_span().as_str();
        if program.constants.contains(&c.to_string()) {
            return Err(format!("Constant {} was already defined before", c));
        }
        if program.variables.contains(&c.to_string()) {
            return Err(format!("Constant {} was previously defined as a variable", c));
        }
        if program.labels.contains(&c.to_string()) {
            return Err(format!("Constant {} matches an existing label", c));
        }
        println!("  Constant: {}", c);
        program.constants.push(c.to_string());
    }
    Ok(program)
}

pub fn parse_variable_stmt(stmt: Pair<Rule>, program: Program) -> Result<Program, String> {
    println!("Parse variable_stmt");
    let mut program = program;
    for variable in stmt.into_inner() {
        let v = variable.as_span().as_str();
        if program.scope.variables.contains(&v.to_string()) {
            return Err(format!("Variable {} was already defined before", v));
        }
        if program.constants.contains(&v.to_string()) {
            return Err(format!("Variable {} matches an existing constant", v));
        }
        if program.labels.contains(&v.to_string()) {
            return Err(format!("Variable {} matches an existing label", v));
        }
        println!("  Variable: {}", v);
        program.scope.variables.push(v.to_string());
        if !program.variables.contains(&v.to_string()) {
            program.variables.push(v.to_string());
        }
    }
    Ok(program)
}

pub fn get_variable_type(variable: &str, program: &Program) -> Option<String> {
    for (_, floating) in program.scope.floatings.iter() {
        if floating.var == variable {
            return Some(floating.typ.to_string());
        }
    }
    None
}

pub fn parse_floating_stmt(stmt: Pair<Rule>, program: Program) -> Result<Program, String> {
    println!("Parse floating_stmt");
    let mut program = program;
    let mut children = stmt.into_inner();

    let label = children.next().unwrap().as_span().as_str().to_string();
    let typecode = children.next().unwrap().as_span().as_str();
    let variable = children.next().unwrap().as_span().as_str();

    if !program.constants.contains(&typecode.to_string()) {
        return Err(format!("Type {} not found in constants", typecode));
    }
    if !program.scope.variables.contains(&variable.to_string()) {
        return Err(format!("Variable {} not defined", variable));
    }
    match get_variable_type(&variable, &program) {
        Some(typecode) => return Err(format!("Variable {} was previously assigned type {}",
                                             variable, typecode)),
        _ => {}
    }
    if program.vartypes.contains_key(variable) &&
        program.vartypes[variable] != typecode {
        return Err(format!("Variable {} was previously assigned type {}", variable,
                           program.vartypes[variable]));
    }

    println!("  {} {} {}", label, typecode, variable);
    program.scope.floatings.insert(label, Floating {
        typ: typecode.to_string(), var: variable.to_string() });
    program.vartypes.insert(variable.to_string(), typecode.to_string());

    Ok(program)
}

pub fn parse_typed_symbols(stmt: &Pair<Rule>, program: &Program) -> Result<(String, TypedSymbols), String> {
    let mut children = stmt.clone().into_inner();

    let label = children.next().unwrap().as_span().as_str().to_string();
    let typecode = children.next().unwrap().as_span().as_str().to_string();
    if !program.constants.contains(&typecode) {
        return Err(format!("Type {} not found in constants", typecode));
    }

    let mut syms = vec![];
    for sym in children {
        if sym.as_rule() != Rule::math_symbol {
            continue
        }
        let s = sym.as_span().as_str();
        syms.push(s.to_string());
        if program.scope.variables.contains(&s.to_string()) {
            if get_variable_type(&s, &program).is_none() {
                return Err(format!("Variable {} must be assigned a type", s));
            }
        }
        else if !program.constants.contains(&s.to_string()) {
           return Err(format!("Variable or constant {} not defined", s));
        }
    }

    return Ok((label, TypedSymbols { typ: typecode, syms: syms }));
}

pub fn add_label(label: &str, mut program: Program) -> Result<Program, String> {
    if program.labels.contains(&label.to_string()) {
       return Err(format!("Label {} was already defined before", label));
    }
    if program.constants.contains(&label.to_string()) {
       return Err(format!("Label {} matches a constant", label));
    }
    if program.variables.contains(&label.to_string()) {
       return Err(format!("Label {} matches a variable", label));
    }
    program.labels.push(label.to_string());
    Ok(program)
}

pub fn parse_essential_stmt(stmt: Pair<Rule>, program: Program) -> Result<Program, String> {
    println!("Parse essential_stmt");

    match parse_typed_symbols(&stmt, &program) {
        Ok((label, typed_symbols)) => {
            println!("  {} {} {:?}", label, typed_symbols.typ, typed_symbols.syms);
            match add_label(&label, program) {
                Ok(mut program) => {
                    program.scope.essentials.insert(label, typed_symbols);
                    Ok(program)
                },
                Err(e) => Err(e)
            }
        },
        Err(e) => Err(e)
    }
}

pub fn parse_disjoint_stmt(stmt: Pair<Rule>, program: Program) -> Result<Program, String> {
    println!("Parse disjoint_stmt");
    let mut program = program;
    let children = stmt.into_inner();

    let mut vars = vec![];
    for var in children {
        let v = var.as_span().as_str();
        if vars.contains(&v.to_string()) {
           return Err(format!("Variable {} appears more than once in a disjoint statement", v));
        }
        if !program.scope.variables.contains(&v.to_string()) {
            return Err(format!("Variable {} not active", v));
        }
        vars.push(v.to_string());
    }
    vars.sort();

    let (mut i, mut j, n) = (0, 1, vars.len());
    loop {
        println!("  {} {}", vars[i], vars[j]);
        program.scope.disjoints.push((vars[i].to_string(), vars[j].to_string()));
        j += 1;
        if j >= n {
            i += 1;
            if i >= n - 1 {
                break;
            }
            j = i + 1;
        }
    }

    Ok(program)
}

pub fn parse_axiom_stmt(stmt: Pair<Rule>, program: Program) -> Result<Program, String> {
    println!("Parse axiom_stmt");

    match parse_typed_symbols(&stmt, &program) {
        Ok((label, typed_symbols)) => {
            println!("  {} {} {:?}", label, typed_symbols.typ, typed_symbols.syms);
            match add_label(&label, program) {
                Ok(mut program) => {
                    program.axioms.insert(label, Axiom {
                        ax: typed_symbols,
                        scope: program.scope.clone()
                    });
                    return Ok(program)
                },
                Err(e) => Err(e)
            }
        },
        Err(e) => Err(e)
    }
}

pub fn parse_proof(stmt: &Pair<Rule>) -> Result<Proof, String> {
    let children = stmt.clone().into_inner();
    for c in children {
        if c.as_rule() != Rule::proof {
            continue
        }
        let mut children = c.into_inner();
        let proof = children.next().unwrap();
        match proof.as_rule() {
            Rule::uncompressed_proof => {
                let syms = proof.into_inner().fold(
                    vec![], |mut ss, s| { ss.push(s.as_span().as_str().to_string()); ss });
                println!("  uncompressed_proof {:?}", syms);
                return Ok(Proof::Uncompressed { syms: syms })
            },
            Rule::compressed_proof => {
                println!("  compressed_proof {:?}", proof);
                return Ok(Proof::Compressed { chars: proof.as_span().as_str().to_string() })
            },
            _ => {
                return Err("Proof should be either uncompressed or compressed".to_string())
            }
        }
    }
    Err("Proof not found".to_string())
}

pub fn parse_provable_stmt(stmt: Pair<Rule>, program: Program) -> Result<Program, String> {
    println!("Parse provable_stmt");

    match parse_typed_symbols(&stmt, &program) {
        Ok((label, typed_symbols)) => {
            println!("  {} {} {:?}", label, typed_symbols.typ, typed_symbols.syms);
            match parse_proof(&stmt) {
                Ok(proof) => {
                    match add_label(&label, program) {
                        Ok(mut program) => {
                            program.provables.insert(
                                label, Provable {
                                    ax: typed_symbols,
                                    proof: proof,
                                    scope: program.scope.clone()
                                });
                            Ok(program)
                        },
                        Err(e) => Err(e)
                    }
                },
                Err(e) => Err(e)
            }
        },
        Err(e) => Err(e)
    }
}

pub fn parse_block(stmt: Pair<Rule>, program: Program) -> Result<Program, String> {
    println!("Parse block");
    let original_scope = program.scope.clone();
    let result = stmt.into_inner().fold(Ok(program),
    |p, rule| match p {
        Ok(prog) => traverse_tree(rule, prog),
        Err(e) => Err(e)
    });
    match result {
        Ok(mut prog) => {
            prog.scope = original_scope;
            Ok(prog)
        },
        _ => result
    }
}

pub fn traverse_tree(tree: Pair<Rule>, program: Program) -> Result<Program, String> {
    match tree.as_rule() {
        Rule::constant_stmt  => parse_constant_stmt(tree, program),
        Rule::variable_stmt  => parse_variable_stmt(tree, program),
        Rule::block          => parse_block(tree, program),
        Rule::floating_stmt  => parse_floating_stmt(tree, program),
        Rule::essential_stmt => parse_essential_stmt(tree, program),
        Rule::disjoint_stmt  => parse_disjoint_stmt(tree, program),
        Rule::axiom_stmt     => parse_axiom_stmt(tree, program),
        Rule::provable_stmt  => parse_provable_stmt(tree, program),
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

pub fn mandatory_variables(axiom: &Axiom) -> HashSet<String> {
    let mut mvars = HashSet::new();

    for s in axiom.ax.syms.iter() {
        if axiom.scope.variables.contains(&s.to_string()) {
            mvars.insert(s.to_string());
        }
    }
    for e in axiom.scope.essentials.values() {
        for s in e.syms.iter() {
            if axiom.scope.variables.contains(&s.to_string()) {
                mvars.insert(s.to_string());
            }
        }
    }

    mvars
}

pub fn parse_program(program: &str) -> Result<Program, String> {
    println!("Parse program");
    let mut result = MetamathParser::parse(Rule::database, program);
    match result {
        Ok(ref mut tree) => {
            println!("Result: {:?}", tree);
            return traverse_tree(tree.next().unwrap(), Program {
                constants: vec![],
                variables: vec![],
                vartypes: HashMap::new(),
                labels: vec![],
                axioms: HashMap::new(),
                provables: HashMap::new(),
                scope: Scope {
                    variables: vec![],
                    floatings: HashMap::new(),
                    essentials: HashMap::new(),
                    disjoints: vec![]
                } });
        },
        _ => Err("Parse error".to_string())
    }
}

pub fn parse_metamath(filename: &str) {
    let io = FileIO {};
    let (program_text, _included_files) = read_file(&io, filename, vec![], ".").unwrap();
    let program = parse_program(&program_text);
    println!("Result: {}", program.unwrap());
}

