use itertools::Itertools;
use pest::Parser;
use pest::iterators::Pair;
use regex::Regex;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt;
use std::path::Path;
use std::time::Instant;
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
    pub variables: HashSet<String>,
    pub floatings: HashMap<String, Floating>,
    pub essentials: HashMap<String, TypedSymbols>,
    pub disjoints: HashSet<(String, String)>
}

#[derive(Debug)]
pub enum Proof {
    Uncompressed {
        labels: Vec<String>
    },
    Compressed {
        chars: String
    }
}

#[derive(Debug)]
pub struct Assertion {
    pub ax: TypedSymbols,
    pub proof: Option<Proof>,
    pub scope: Scope
}

pub struct Program {
    pub constants: HashSet<String>,
    pub variables: HashSet<String>,
    pub vartypes: HashMap<String, String>,
    pub labels: HashMap<String, u32>,
    pub axioms: HashMap<String, Assertion>,
    pub provables: HashMap<String, Assertion>,
    pub scope: Scope,
    pub counters: HashMap<String, u32>,
    pub timings: HashMap<String, u32>
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
            variables: self.variables.clone(),
            floatings: self.floatings.clone(),
            essentials: self.essentials.clone(),
            disjoints: self.disjoints.clone()
        }
    }
}

impl std::fmt::Display for Scope {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Variables: {:?}\nFloatings: {:?}\nEssentials: {:?}\nDisjoints: {:?}",
               self.variables.len(), self.floatings.len(), self.essentials.len(), self.disjoints.len())
    }
}

impl std::fmt::Display for Program {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut s = "".to_string();
        for (k, v) in self.counters.iter() {
            s += format!("{} ({} msec * {}), ", k, self.timings[k] as f32 / self.counters[k] as f32, v).as_str();
        }
        write!(f, "Constants: {}, Variables: {}, Vartypes: {}, Labels: {}, Axioms: {}, Provables: {}\nTimings: {}", self.constants.len(), self.variables.len(), self.vartypes.keys().len(), self.labels.len(), self.axioms.keys().len(), self.provables.keys().len(), s)
    }
}

pub fn parse_constant_stmt(stmt: Pair<Rule>, program: Program) -> Result<Program, String> {
    // println!("Parse constant_stmt");
    let now = Instant::now();
    let mut program = program;
    for constant in stmt.into_inner() {
        let c = constant.as_span().as_str().to_string();
        if program.constants.contains(&c) {
            return Err(format!("Constant {} was already defined before", c));
        }
        if program.variables.contains(&c) {
            return Err(format!("Constant {} was previously defined as a variable", c));
        }
        if program.labels.contains_key(&c) {
            return Err(format!("Constant {} matches an existing label", c));
        }
        // println!("  Constant: {}", c);
        program.constants.insert(c);
    }
    *program.counters.entry("constant".to_string()).or_insert(0) += 1;
    *program.timings.entry("constant".to_string()).or_insert(0) += now.elapsed().subsec_millis();
    Ok(program)
}

pub fn parse_variable_stmt(stmt: Pair<Rule>, program: Program) -> Result<Program, String> {
    // println!("Parse variable_stmt");
    let now = Instant::now();
    let mut program = program;
    for variable in stmt.into_inner() {
        let v = variable.as_span().as_str().to_string();
        if program.scope.variables.contains(&v) {
            return Err(format!("Variable {} was already defined before", v));
        }
        if program.constants.contains(&v) {
            return Err(format!("Variable {} matches an existing constant", v));
        }
        if program.labels.contains_key(&v) {
            return Err(format!("Variable {} matches an existing label", v));
        }
        // println!("  Variable: {}", v);
        program.scope.variables.insert(v.to_string());
        if !program.variables.contains(&v) {
            program.variables.insert(v.to_string());
        }
    }
    *program.counters.entry("variable".to_string()).or_insert(0) += 1;
    *program.timings.entry("variable".to_string()).or_insert(0) += now.elapsed().subsec_millis();
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
    // println!("Parse floating_stmt");
    let now = Instant::now();
    let mut children = stmt.into_inner();

    let label = children.next().unwrap().as_span().as_str().to_string();
    let typecode = children.next().unwrap().as_span().as_str().to_string();
    let variable = children.next().unwrap().as_span().as_str().to_string();

    if !program.constants.contains(&typecode) {
        return Err(format!("Type {} not found in constants", typecode));
    }
    if !program.scope.variables.contains(&variable) {
        return Err(format!("Variable {} not defined", variable));
    }
    match get_variable_type(&variable, &program) {
        Some(typecode) => return Err(format!("Variable {} was previously assigned type {}",
                                             variable, typecode)),
        _ => {}
    }
    if program.vartypes.contains_key(&variable) &&
        program.vartypes[&variable] != typecode {
        return Err(format!("Variable {} was previously assigned type {}", variable,
                           program.vartypes[&variable]));
    }

    // println!("  {} {} {}", label, typecode, variable);
    match add_label(&label, program) {
        Ok(mut program) => {
            program.scope.floatings.insert(label, Floating {
                typ: typecode.to_string(), var: variable.to_string() });
            program.vartypes.insert(variable.to_string(), typecode.to_string());
            *program.counters.entry("floating".to_string()).or_insert(0) += 1;
            *program.timings.entry("floating".to_string()).or_insert(0) += now.elapsed().subsec_millis();
            Ok(program)
        },
        Err(e) => Err(e)
    }
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
        let s = sym.as_span().as_str().to_string();
        syms.push(s.to_string());
        if program.scope.variables.contains(&s) {
            if get_variable_type(&s, &program).is_none() {
                return Err(format!("Variable {} must be assigned a type", s));
            }
        }
        else if !program.constants.contains(&s) {
           return Err(format!("Variable or constant {} not defined", s));
        }
    }

    return Ok((label, TypedSymbols { typ: typecode, syms: syms }));
}

pub fn add_label(label: &str, mut program: Program) -> Result<Program, String> {
    let label = label.to_string();
    if program.labels.contains_key(&label) {
       return Err(format!("Label {} was already defined before", label));
    }
    if program.constants.contains(&label) {
       return Err(format!("Label {} matches a constant", label));
    }
    if program.variables.contains(&label) {
       return Err(format!("Label {} matches a variable", label));
    }
    program.labels.insert(label, program.labels.len() as u32);
    Ok(program)
}

pub fn parse_essential_stmt(stmt: Pair<Rule>, program: Program) -> Result<Program, String> {
    // println!("Parse essential_stmt");
    let now = Instant::now();

    match parse_typed_symbols(&stmt, &program) {
        Ok((label, typed_symbols)) => {
            // println!("  {} {} {:?}", label, typed_symbols.typ, typed_symbols.syms);
            match add_label(&label, program) {
                Ok(mut program) => {
                    program.scope.essentials.insert(label, typed_symbols);
                    *program.counters.entry("essential".to_string()).or_insert(0) += 1;
                    *program.timings.entry("essential".to_string()).or_insert(0) += now.elapsed().subsec_millis();
                    Ok(program)
                },
                Err(e) => Err(e)
            }
        },
        Err(e) => Err(e)
    }
}

pub fn parse_disjoint_stmt(stmt: Pair<Rule>, program: Program) -> Result<Program, String> {
    // println!("Parse disjoint_stmt");
    let mut program = program;
    let children = stmt.into_inner();

    let mut vars = vec![];
    for var in children {
        let v = var.as_span().as_str().to_string();
        if vars.contains(&v) {
           return Err(format!("Variable {} appears more than once in a disjoint statement", v));
        }
        if !program.scope.variables.contains(&v) {
            return Err(format!("Variable {} not active", v));
        }
        vars.push(v.to_string());
    }
    vars.sort();

    for (v1, v2) in vars.iter().tuple_combinations() {
        program.scope.disjoints.insert((v1.to_string(), v2.to_string()));
    }

    Ok(program)
}

pub fn parse_axiom_stmt(stmt: Pair<Rule>, program: Program) -> Result<Program, String> {
    // println!("Parse axiom_stmt");

    match parse_typed_symbols(&stmt, &program) {
        Ok((label, typed_symbols)) => {
            // println!("  {} {} {:?}", label, typed_symbols.typ, typed_symbols.syms);
            match add_label(&label, program) {
                Ok(mut program) => {
                    program.axioms.insert(label, Assertion {
                        ax: typed_symbols,
                        proof: None,
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
                // println!("  uncompressed_proof {:?}", syms);
                return Ok(Proof::Uncompressed { labels: syms })
            },
            Rule::compressed_proof => {
                // println!("  compressed_proof {:?}", proof);
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
    // println!("Parse provable_stmt");

    match parse_typed_symbols(&stmt, &program) {
        Ok((label, typed_symbols)) => {
            // println!("  {} {} {:?}", label, typed_symbols.typ, typed_symbols.syms);
            match parse_proof(&stmt) {
                Ok(proof) => {
                    match add_label(&label, program) {
                        Ok(mut program) => {
                            program.provables.insert(
                                label, Assertion {
                                    ax: typed_symbols,
                                    proof: Some(proof),
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
    // println!("Parse block");
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
            // println!("Statement: {:?}", tree.as_rule());
            return tree.into_inner().fold(Ok(program),
                |p, rule| match p {
                    Ok(prog) => traverse_tree(rule, prog),
                    Err(e) => Err(e)
                });
        }
    }
}

pub fn parse_program(program_text: &str) -> Result<Program, String> {
    println!("Parsing program...");
    let now = Instant::now();
    let mut result = MetamathParser::parse(Rule::database, program_text);
    match result {
        Ok(ref mut tree) => {
            println!(" . Program parsed in {} seconds.", now.elapsed().as_secs());
            println!("Checking program...");
            let now = Instant::now();
            let program = traverse_tree(tree.next().unwrap(), Program {
                constants: HashSet::new(),
                variables: HashSet::new(),
                vartypes: HashMap::new(),
                labels: HashMap::new(),
                axioms: HashMap::new(),
                provables: HashMap::new(),
                scope: Scope {
                    variables: HashSet::new(),
                    floatings: HashMap::new(),
                    essentials: HashMap::new(),
                    disjoints: HashSet::new(),
                },
                counters: HashMap::new(),
                timings: HashMap::new()
            });
            println!(" . Program checked in {} seconds.", now.elapsed().as_secs());
            program
        },
        _ => Err("Parse error".to_string())
    }
}

pub fn mandatory_variables(axiom: &Assertion) -> HashSet<String> {
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

pub fn mandatory_hypotheses(axiom: &Assertion, labels: &HashMap<String, u32>) -> Vec<String> {
    let mut mhyps = HashSet::new();

    let mvars = mandatory_variables(axiom);
    for (label, f) in axiom.scope.floatings.iter() {
        if mvars.contains(&f.var) {
            mhyps.insert(label.to_string());
        }
    }
    for label in axiom.scope.essentials.keys() {
        mhyps.insert(label.to_string());
    }

    let mut sorted_mhyps: Vec<String> = mhyps.iter().cloned().collect();
    sorted_mhyps.sort_by_key(|k| labels[k]);

    sorted_mhyps
}

pub fn mandatory_disjoints(axiom: &Assertion) -> HashSet<(String, String)> {
    let mut mdisjs = HashSet::new();

    let mvars = mandatory_variables(axiom);
    for (v1, v2) in axiom.scope.disjoints.iter() {
        if mvars.contains(v1) && mvars.contains(v2) {
            mdisjs.insert((v1.to_string(), v2.to_string()));
        }
    }

    mdisjs
}

pub fn decompress_proof(proof: &Proof) -> Vec<String> {
    match proof {
        Proof::Uncompressed { labels } => labels.clone(),
        Proof::Compressed { chars: _ } => vec![]
    }
}

pub fn apply_substitutions(subst: &HashMap<String, Vec<String>>, syms: &Vec<String>, constants: &HashSet<String>) -> Vec<String> {
    let mut subst_syms = vec![];
    for s in syms {
        if constants.contains(&s.to_string()) {
            subst_syms.push(s.to_string());
            continue;
        }
        subst_syms.extend_from_slice(&subst[&s.to_string()]);
    }
    subst_syms
}

pub fn find_substitutions(stack: &Vec<TypedSymbols>, mhyps: &Vec<String>, scope: &Scope, constants: &HashSet<String>) -> Result<HashMap<String, Vec<String>>, String> {
    let mut subst = HashMap::new();
    let mut i = stack.len() - mhyps.len();
    for label in mhyps {
        let l = label.to_string();
        let target = &stack[i];
        if scope.floatings.contains_key(&l) {
            let f = &scope.floatings[&l];
            if f.typ != target.typ {
                return Err(format!("Incorrect type when trying to substitute variable \
                                   '{}' by '{}' (got {}, expected {})",
                                   f.var, target.syms.join(" "), target.typ, f.typ));
            }
            subst.insert(f.var.to_string(), target.syms.clone());
        }
        else if scope.essentials.contains_key(&l) {
            let e = &scope.essentials[&l];
            if e.typ != target.typ {
                return Err(format!("Incorrect type for essential hypothesis \
                                   '{}' (got {}, expected {})",
                                   l, target.typ, e.typ));
            }
            let subst_syms = apply_substitutions(&subst, &e.syms, &constants);
            if subst_syms != target.syms {
                return Err(format!("Mismatch after substitution in essential hypothesis \
                                   '{}' (got '{}', expected '{}')",
                                   l, target.syms.join(" "), subst_syms.join(" ")));
            }
        }
        i = i + 1;
    }
    Ok(subst)
}

pub fn are_expressions_disjoint(expr1: &Vec<String>, expr2: &Vec<String>, provable_vars: &HashSet<String>, provable_disjs: &HashSet<(String, String)>) -> bool {
    let vars1 = expr1.into_iter().filter(|v| provable_vars.contains(&v.to_string())).collect_vec();
    let vars2 = expr2.into_iter().filter(|v| provable_vars.contains(&v.to_string())).collect_vec();
    let allpairs = vars2.iter().flat_map(|v2| vars1.iter().clone().map(move |v1| (v1.to_string(), v2.to_string())));
    for vpair in allpairs {
        if !provable_disjs.contains(&vpair) {
            return false;
        }
    }
    true
}

pub fn is_disjoint_restriction_verified(vpair: (&str, &str), mdisjs: &HashSet<(String, String)>, provable_scope: &Scope, subst: &HashMap<String, Vec<String>>) -> bool {
    let (v1, v2) = vpair;
    let vpair = (v1.to_string(), v2.to_string());
    let (v1, v2) = (v1.to_string(), v2.to_string());
    if mdisjs.contains(&vpair) && subst.contains_key(&v1) && subst.contains_key(&v2) {
        let (expr1, expr2) = (subst[&v1].to_vec(), subst[&v2].to_vec());
        return are_expressions_disjoint(&expr1, &expr2, &provable_scope.variables, &provable_scope.disjoints);
    }
    true
}

pub fn are_disjoint_restrictions_verified(axiom: &Assertion, provable_scope: &Scope, subst: &HashMap<String, Vec<String>>) -> bool {
    let mvars = mandatory_variables(axiom);
    let mdisjs = mandatory_disjoints(axiom);
    for (v1, v2) in mvars.iter().tuple_combinations() {
        if !is_disjoint_restriction_verified((v1, v2), &mdisjs, provable_scope, subst) {
            return false;
        }
    }
    true
}

pub fn apply_axiom(axiom: &Assertion, provable_scope: &Scope, program: &Program, mut stack: Vec<TypedSymbols>) -> Result<Vec<TypedSymbols>, String> {
    let mhyps = mandatory_hypotheses(axiom, &program.labels);
    if stack.len() < mhyps.len() {
        return Err("Not enough items on the stack".to_string());
    }
    let n = stack.len() - mhyps.len();
    let (remaining_stack, substack) = stack.split_at_mut(n);
    match find_substitutions(&substack.to_vec(), &mhyps, &axiom.scope, &program.constants) {
        Ok(subst) => {
            if are_disjoint_restrictions_verified(axiom, provable_scope, &subst) {
                let subst_syms = apply_substitutions(&subst, &axiom.ax.syms, &program.constants);
                let mut new_stack = remaining_stack.to_vec();
                new_stack.push(TypedSymbols { typ: axiom.ax.typ.to_string(), syms: subst_syms });
                Ok(new_stack)
            }
            else {
                Err("Disjoint restriction violated".to_string())
            }
        },
        Err(e) => Err(e)
    }
}

pub fn verify_proof(provable: &Assertion, program: &Program) -> Result<(), String> {
    let mut stack = vec![];
    let proof_labels = decompress_proof(provable.proof.as_ref().unwrap());
    let scope = &provable.scope;

    for label in proof_labels {
        if scope.floatings.contains_key(&label) {
            let f = &scope.floatings[&label];
            stack.push(TypedSymbols { typ: f.typ.to_string(), syms: vec![f.var.to_string()] });
            continue
        }
        if scope.essentials.contains_key(&label) {
            stack.push(scope.essentials[&label].clone());
            continue
        }
        if program.axioms.contains_key(&label) {
            match apply_axiom(&program.axioms[&label], scope, &program, stack) {
                Ok(updated_stack) => stack = updated_stack,
                Err(e) => return Err(e)
            }
            continue
        }
        if program.provables.contains_key(&label) {
            match apply_axiom(&program.provables[&label], scope, &program, stack) {
                Ok(updated_stack) => stack = updated_stack,
                Err(e) => return Err(e)
            }
            continue
        }
    }

    if stack.len() > 1 {
        return Err("Too many items left in the stack".to_string());
    }
    match stack.pop() {
        Some(proof_result) => {
            if proof_result.typ != provable.ax.typ ||
               proof_result.syms != provable.ax.syms {
                return Err(format!("Proof result {:?} does not match assertion {:?}",
                                   proof_result, provable.ax));
            }
            return Ok(())
        },
        _ => {
            return Err("No item left in the stack".to_string());
        }
    }
}

pub fn verify_proofs(program: &Program) -> bool {
    program.provables.iter().all(|(l, p)| {
        print!("Verifying {:?} ...", l);
        match verify_proof(p, program) {
            Ok(()) => { println!(" OK!"); true },
            Err(e) => { println!(" FAILED ({})", e); false }
        }
    })
}

pub fn parse_metamath(filename: &str) {
    let io = FileIO {};
    let (program_text, _included_files) = read_file(&io, filename, vec![], ".").unwrap();
    let program = parse_program(&program_text).unwrap();
    println!("Result: {}", program);
    // println!("There are {} theorems to prove", program.provables.len());
}

