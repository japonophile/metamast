use metamast::io::MockIO;
use metamast::mm_parser::{strip_comments, load_includes, parse_program,
                          mandatory_variables, mandatory_hypotheses, mandatory_disjoints};
use std::collections::HashSet;

#[test]
fn test_strip_comments() {
    // The token $( begins a comment and $) ends a comment.
    // Comments are ignored (treated like white space) for the purpose of parsing.
    let text = strip_comments("$c wff $.\n$( comment $)\n$v x $.\n");
    assert_eq!(text.unwrap().to_string(), "$c wff $.\n\n$v x $.\n");
    let text = strip_comments("$c wff $.\n$( first comment $)\n$v x $.\n$( second comment $)\nax1 $a x $.\n");
    assert_eq!(text.unwrap().to_string(), "$c wff $.\n\n$v x $.\n\nax1 $a x $.\n");
    let text = strip_comments("$c wff $.\n$( multiline \ncomment $)\n$v x $.\n");
    assert_eq!(text.unwrap().to_string(), "$c wff $.\n\n$v x $.\n");
    let text = strip_comments("$c wff $.\n$( unfinished comment");
    assert_eq!(text.err(), Some("Malformed comment"));
    let text = strip_comments("$c wff $.\n$) $v x $.\n$( finished comment $)\n");
    assert_eq!(text.err(), Some("Malformed comment"));

    // $( $[ $) is a comment
    let text = strip_comments("$c wff $.\n$( $[ $)\n$v x $.\n");
    assert_eq!(text.unwrap().to_string(), "$c wff $.\n\n$v x $.\n");

    // they may not contain the 2-character sequences $( or $) (comments do not nest)
    let text = strip_comments("$c wff $.\n$( comment $( nested comment, illegal $) $)\n$v x $.\n");
    assert_eq!(text.err(), Some("Comments may not be nested"));
}

#[test]
fn test_load_includes() {
    let mut mock = MockIO::new();
    mock.expect_slurp()
        .returning(
            |f|
            {
                match f {
                    "./abc.mm"           => "$c a b c $.\n",
                    "./xyz.mm"           => "$v x y z $.\n",
                    "./xyz-comment.mm"   => "$c wff $.\n$( comment $)\n$v x y z $.\n",
                    "./xyz-include.mm"   => "$c wff $.\n$[ abc.mm $]\n$v x y z $.\n",
                    "./xyz-include2.mm"  => "$c wff $.\n$[ abc.mm $]\n$[ root.mm $]\n$v x y z $.\n",
                    "./wrong-include.mm" => "$c a $.\n${ $[ xyz.mm $] $}\n$v n $.\n",
                    _                    => "$c this file should not be included $.\n",
                }
            }.to_string());

    // A file inclusion command consists of $[ followed by a file name followed by $].
    let result = load_includes(&mock,
                               "$c a $.\n$[ xyz.mm $]\n$v n $.\n".to_string(),
                               ["root.mm".to_string()].to_vec(), ".");
    assert_eq!(result.unwrap().0, "$c a $.\n$v x y z $.\n\n$v n $.\n");
    let result = load_includes(&mock,
                               "$c a $.\n$[ xyz-comment.mm $]\n$v n $.\n".to_string(),
                               ["root.mm".to_string()].to_vec(), ".");
    assert_eq!(result.unwrap().0, "$c a $.\n$c wff $.\n\n$v x y z $.\n\n$v n $.\n");

    // It is only allowed in the outermost scope (i.e., not between ${ and $})"
    let result = load_includes(&mock,
                               "$[ wrong-include.mm $]\n".to_string(),
                               ["root.mm".to_string()].to_vec(), ".");
    assert_eq!(result.err(), Some("Include statement only allowed in outermost scope"));

    // nested inclusion
    let result = load_includes(&mock,
                               "$c a $.\n$[ xyz-include.mm $]\n$v n $.\n".to_string(),
                               ["root.mm".to_string()].to_vec(), ".");
    assert_eq!(result.unwrap().0, "$c a $.\n$c wff $.\n$c a b c $.\n\n$v x y z $.\n\n$v n $.\n");
    let result = load_includes(&mock,
                               "$c a $.\n$[ xyz-include2.mm $]\n$v n $.\n".to_string(),
                               ["root.mm".to_string()].to_vec(), ".");
    assert_eq!(result.unwrap().0, "$c a $.\n$c wff $.\n$c a b c $.\n\n\n$v x y z $.\n\n$v n $.\n");

    // no multiple inclusion
    let result = load_includes(&mock,
                               "$c a $.\n$[ root.mm $]\n$v n $.\n".to_string(),
                               ["root.mm".to_string()].to_vec(), ".");
    assert_eq!(result.unwrap().0, "$c a $.\n\n$v n $.\n");
    let result = load_includes(&mock,
                               "$c a $.\n$[ xyz-include.mm $]\n$v n $.\n$[ abc.mm $]\n".to_string(),
                               ["root.mm".to_string()].to_vec(), ".");
    assert_eq!(result.unwrap().0, "$c a $.\n$c wff $.\n$c a b c $.\n\n$v x y z $.\n\n$v n $.\n\n");
}

#[test]
fn test_parse_constants_variables() {
    // The same math symbol may not occur twice in a given $v or $c statement
    let result = parse_program("$c c c $.\n");
    assert_eq!(result.err(), Some("Constant c was already defined before".to_string()));
    let result = parse_program("$v x y x $.\n");
    assert_eq!(result.err(), Some("Variable x was already defined before".to_string()));

    // A math symbol becomes active when declared and stays active
    // until the end of the block in which it is declared.
    let program = parse_program("$v x y $.\n").unwrap();
    assert!(program.scope.variables.contains(&"x".to_string()));

    // A constant must be declared in the outermost block
    parse_program("$c a b c $.\n${\n  $v x y $.\n$}\n$c d e f $.\n").unwrap();
    let result = parse_program("$c a b c $.\n${\n  $c d e f $.\n$}\n");
    assert_eq!(result.err(), Some("Parse error".to_string()));

    // A constant ... may not be declared a second time.
    let result = parse_program("$c a b c $.\n${\n  $v x y $.\n$}\n$c b $.\n");
    assert_eq!(result.err(), Some("Constant b was already defined before".to_string()));

    // A variable may not be declared a second time while it is active
    let result = parse_program("${\n  $v x y $.\n  $v z x $. $}\n");
    assert_eq!(result.err(), Some("Variable x was already defined before".to_string()));

    // [a variable] may be declared again (as a variable, but not as a constant)
    // after it becomes inactive.
    parse_program("${\n  $v x y $.\n$}\n$v z x $.\n").unwrap();
    let result = parse_program("${\n  $v x y $.\n$}\n$c z x $.\n");
    assert_eq!(result.err(), Some("Constant x was previously defined as a variable".to_string()));

    // A variable must not match an existing constant (follows from other rules)
    let result = parse_program("$c x $.\n$v x $.\n");
    assert_eq!(result.err(), Some("Variable x matches an existing constant".to_string()));
}

#[test]
fn test_parse_hypotheses() {
    // A $f statement consists of a label, followed by $f, followed by its typecode
    // (an active constant), followed by an active variable, followed by the $. token.
    let program = parse_program("$c var c $.\n$v x $.\nvarx $f var x $.\n").unwrap();
    assert!(program.scope.floatings.contains_key("varx"));
    let result = parse_program("$c var c $.\n$v x $.\nvarx $f bar x $.\n");
    assert_eq!(result.err(), Some("Type bar not found in constants".to_string()));
    let result = parse_program("$c var c $.\n$v x $.\nvarx $f var y $.\n");
    assert_eq!(result.err(), Some("Variable y not defined".to_string()));
    let result = parse_program("$c var c $.\n$v x $.\nvarx $f var c $.\n");
    assert_eq!(result.err(), Some("Variable c not defined".to_string()));

    // A $e statement consists of a label, followed by $e, followed by its typecode
    // (an active constant), followed by zero or more active math symbols, followed
    // by the $. token.
    let program = parse_program(
        "$c var a b $.\n$v x $.\nvarx $f var x $.\ness1 $e var x a a $.\n").unwrap();
    assert!(program.scope.essentials.contains_key("ess1"));
    let program = parse_program("$c var $.\ness1 $e var $.\n").unwrap();
    assert!(program.scope.essentials.contains_key("ess1"));
    let result = parse_program(
        "$c var a b $.\n$v x $.\nvarx $f var x $.\ness1 $e bar x a a $.\n");
    assert_eq!(result.err(), Some("Type bar not found in constants".to_string()));
    let result = parse_program("$c var a b $.\n$v x $.\ness1 $e var y a a $.\n");
    assert_eq!(result.err(), Some("Variable or constant y not defined".to_string()));
    let result = parse_program(
        "$c var a b $.\n$v x $.\nvarx $f var x $.\ness1 $e var x a b a x c $.\n");
    assert_eq!(result.err(), Some("Variable or constant c not defined".to_string()));
    let result = parse_program("$c var a b $.\n${ $v x $. $}\ness1 $e var x a a $.\n");
    assert_eq!(result.err(), Some("Variable or constant x not defined".to_string()));

    // The type declared by a $f statement for a given label is global
    // even if the variable is not (e.g., a database may not have wff P in one
    // local scope and class P in another).
    let result = parse_program(
        "$c wff class $.\n${ $v P $.\nwff_P $f wff P $. $}\n${ $v P $.\nclass_P $f class P $. $}\n");
    assert_eq!(result.err(), Some("Variable P was previously assigned type wff".to_string()));

    // There may not be two active $f statements containing the same variable.
    let result = parse_program(
        "$c var int $.\n$v x $.\nvarx $f var x $.\nintx $f int x $.\n");
    assert_eq!(result.err(), Some("Variable x was previously assigned type var".to_string()));
    let result = parse_program(
        "$c var int $.\n$v x $.\nvarx $f var x $.\nvarx2 $f var x $.\n");
    assert_eq!(result.err(), Some("Variable x was previously assigned type var".to_string()));
}

#[test]
fn test_parse_disjoints() {
    // A simple $d statement consists of $d, followed by two different
    // active variables, followed by the $. token.
    let program = parse_program("$v x y $.\n$d x y $.\n").unwrap();
    assert_eq!(1, program.scope.disjoints.len());
    let result = parse_program("$v x y $.\n$d x x $.\n");
    assert_eq!(result.err(), Some("Variable x appears more than once in a disjoint statement".to_string()));
    let result = parse_program("$v y $.\n$d x y $.\n");
    assert_eq!(result.err(), Some("Variable x not active".to_string()));
    let result = parse_program("$v y $.\n${ $v x $. $}\n$d x y $.\n");
    assert_eq!(result.err(), Some("Variable x not active".to_string()));

    // A compound $d statement consists of $d, followed by three or more
    // variables (all different), followed by the $. token.
    let program = parse_program("$v x y z $.\n$d x z y $.\n").unwrap();
    assert_eq!(3, program.scope.disjoints.len());
    let result = parse_program("$v x y z $.\n$d z x z y $.\n");
    assert_eq!(result.err(), Some("Variable z appears more than once in a disjoint statement".to_string()));

    // The order of the variables in a $d statement is unimportant.
    let disjoints1 = parse_program("$v x y z $.\n$d x y z $.\n").unwrap().scope.disjoints;
    let disjoints2 = parse_program("$v x y z $.\n$d x z y $.\n").unwrap().scope.disjoints;
    assert_eq!(disjoints1, disjoints2);
}

#[test]
fn test_parse_assertions() {
    // A $a statement consists of a label, followed by $a, followed by its typecode
    // (an active constant), followed by zero or more active math symbols,
    // followed by the $. token.
    let program = parse_program(
        "$c var wff $.\n$v x $.\nvarx $f var x $.\nax1 $a wff x $.\n").unwrap();
    assert!(program.axioms.contains_key("ax1"));
    let program = parse_program(
        "$c var wff = $.\n$v x $.\nvarx $f var x $.\nax1 $a wff = x x $.\n").unwrap();
    assert!(program.axioms.contains_key("ax1"));
    let result = parse_program("$c var wff $.\n$v x $.\nvarx $f var x $.\nax1 $a woof x $.\n");
    assert_eq!(result.err(), Some("Type woof not found in constants".to_string()));
    let result = parse_program("$c var wff $.\n$v x $.\nvarx $f var x $.\nax1 $a wff y $.\n");
    assert_eq!(result.err(), Some("Variable or constant y not defined".to_string()));

    // A $p statement consists of a label, followed by $p, followed by its typecode
    // (an active constant), followed by zero or more active math symbols,
    // followed by $=, followed by a sequence of labels, followed by the $. token.
    let program = parse_program(
        "$c var wff $.\n$v x $.\nvarx $f var x $.\ndum $a var x $.\n\
        p1 $p wff x $= dum dum $.\n").unwrap();
    assert!(program.provables.contains_key("p1"));
    let program = parse_program(
        "$c var wff = $.\n$v x $.\nvarx $f var x $.\nding $a var x $.\n\
        dong $a wff x $.\np1 $p wff = x x $= ding dong $.\n").unwrap();
    assert!(program.provables.contains_key("p1"));
    let result = parse_program(
        "$c var wff $.\n$v x $.\nvarx $f var x $.\ndum $a var x $.\n\
        p1 $p woof x $= dum dum $.\n");
    assert_eq!(result.err(), Some("Type woof not found in constants".to_string()));

    // Each variable in a $e, $a, or $p statement must exist in an active $f statement.
    let result = parse_program("$c var wff $.\n$v x $.\nmin $e wff x $.\n");
    assert_eq!(result.err(), Some("Variable x must be assigned a type".to_string()));
    let result = parse_program("$c var wff $.\n$v x $.\nax1 $a wff x $.\n");
    assert_eq!(result.err(), Some("Variable x must be assigned a type".to_string()));
    let result = parse_program("$c var wff $.\n$v x $.\nho $a wff $.\np1 $p wff x $= ho ho $.\n");
    assert_eq!(result.err(), Some("Variable x must be assigned a type".to_string()));
    let result = parse_program("$c var wff $.\n$v x y $.\nvarx $f var x $.\nax1 $a wff x y $.\n");
    assert_eq!(result.err(), Some("Variable y must be assigned a type".to_string()));

    // Each label token must be unique
    let result = parse_program(
        "$c var wff $.\n$v x $.\nvarx $f var x $.\nax1 $a wff x $.\nax1 $a wff $.\n");
    assert_eq!(result.err(), Some("Label ax1 was already defined before".to_string()));
    let result = parse_program(
        "$c var wff $.\n$v x $.\n${ varx $f var x $.\nax1 $a wff x $. $}\n\
        varxx $f var x $.\nax1 $a wff $.\n");
    assert_eq!(result.err(), Some("Label ax1 was already defined before".to_string()));
    let result = parse_program(
        "$c var wff $.\n$v x $.\nvarx $f var x $.\np1 $p wff x $= wff $.\np1 $p wff $= wff $.\n");
    assert_eq!(result.err(), Some("Label p1 was already defined before".to_string()));
    let result = parse_program(
        "$c var a b $.\n$v x $.\nvarx $f var x $.\ness1 $e var x a a $.\ness1 $e var x b b $.\n");
    assert_eq!(result.err(), Some("Label ess1 was already defined before".to_string()));

    // no label token may match any math symbol token.
    let result = parse_program(
        "$c var wff ax1 $.\n$v x $.\nvarx $f var x $.\nax1 $a wff x $.\n");
    assert_eq!(result.err(), Some("Label ax1 matches a constant".to_string()));
    let result = parse_program(
        "$c var wff $.\n$v x ax1 $.\nvarx $f var x $.\nax1 $a wff x $.\n");
    assert_eq!(result.err(), Some("Label ax1 matches a variable".to_string()));
    let result = parse_program(
        "$c var wff $.\n$v x $.\nvarx $f var x $.\nc $a wff x $.\n$c c $.\n");
    assert_eq!(result.err(), Some("Constant c matches an existing label".to_string()));
    let result = parse_program(
        "$c var wff $.\n$v x $.\nvarx $f var x $.\ny $a wff x $.\n$v y $.\n");
    assert_eq!(result.err(), Some("Variable y matches an existing label".to_string()));
}

#[test]
fn mandatory_elements() {
    // The set of mandatory variables associated with an assertion is the set
    // of (zero or more) variables in the assertion and in any active $e statements.
    let program = parse_program(
        "$c var wff = $.\n$v x y z $.\nvarx $f var x $.\n\
        varz $f var z $.\nax1 $a wff = x z $.\n").unwrap();
    let mvars: HashSet<String> = ["x", "z"].iter().map(|s| s.to_string()).collect();
    assert_eq!(mvars, mandatory_variables(&program.axioms["ax1"]));

    let program = parse_program(
        "$c var wff = $.\n$v n x y z $.\nvarx $f var x $.\n\
        vary $f var y $.\nvarz $f var z $.\nmin $e wff = x y $.\n\
        ax1 $a wff = x z $.\n").unwrap();
    let mvars: HashSet<String> = ["x", "y", "z"].iter().map(|s| s.to_string()).collect();
    assert_eq!(mvars, mandatory_variables(&program.axioms["ax1"]));

    // The (possibly empty) set of mandatory hypotheses is the set of all active
    // $f statements containing mandatory variables, together with all active $e statements.
    let program = parse_program(
        "$c var wff = $.\n$v x y z $.\nvarx $f var x $.\n\
        varz $f var z $.\nax1 $a wff = x z $.\n").unwrap();
    let mhyps: Vec<String> = ["varx", "varz"].iter().map(|s| s.to_string()).collect();
    assert_eq!(mhyps, mandatory_hypotheses(&program.axioms["ax1"], program.labels));

    let program = parse_program(
        "$c var wff = $.\n$v x y z $.\nvarx $f var x $.\n\
        vary $f var y $.\nvarz $f var z $.\nax1 $a wff = x z $.\n").unwrap();
    let mhyps: Vec<String> = ["varx", "varz"].iter().map(|s| s.to_string()).collect();
    assert_eq!(mhyps, mandatory_hypotheses(&program.axioms["ax1"], program.labels));

    let program = parse_program(
        "$c var wff = $.\n$v n x y z $.\nvarx $f var x $.\n\
        vary $f var y $.\nvarz $f var z $.\nmin $e wff = x y $.\n\
        ax1 $a wff = x z $.\n").unwrap();
    let mhyps: Vec<String> =
        ["varx", "vary", "varz", "min"].iter().map(|s| s.to_string()).collect();
    assert_eq!(mhyps, mandatory_hypotheses(&program.axioms["ax1"], program.labels));

    let program = parse_program(
        "$c var wff = $.\n$v n x y z $.\nvary $f var y $.\n\
        varx $f var x $.\nmin $e wff = x y $.\nvarz $f var z $.\n\
        ax1 $a wff = x z $.\n").unwrap();
    let mhyps: Vec<String> =
        ["vary", "varx", "min", "varz"].iter().map(|s| s.to_string()).collect();
    assert_eq!(mhyps, mandatory_hypotheses(&program.axioms["ax1"], program.labels));

    // The set of mandatory $d statements associated with an assertion
    // are those active $d statements whose variables are both among
    // the assertion’s mandatory variables.
    let program = parse_program(
        "$c var wff = $.\n$v x y z $.\nvarx $f var x $.\nvarz $f var z $.\n\
        $d x y $.\n$d y z $.\n$d x z $.\nax1 $a wff = x z $.\n").unwrap();
    let mdisjs: HashSet<(String, String)> =
        [("x".to_string(), "z".to_string())].iter().cloned().collect();
    assert_eq!(mdisjs, mandatory_disjoints(&program.axioms["ax1"]));

    let program = parse_program(
        "$c var wff = $.\n$v x y z $.\nvarx $f var x $.\nvarz $f var z $.\n\
        $d x y $.\n$d y z $.\nmin $e wff = x z $.\nax1 $a wff = x z $.\n").unwrap();
    let mdisjs = HashSet::new();
    assert_eq!(mdisjs, mandatory_disjoints(&program.axioms["ax1"]));

    let program = parse_program(
        "$c var wff = $.\n$v x y z $.\nvarx $f var x $.\nvary $f var y $.\n\
        varz $f var z $.\n$d x y $.\n$d y z $.\n$d x z $.\nmin $e = y y $.\n\
        ax1 $a wff = x z $.\n").unwrap();
    let mdisjs: HashSet<(String, String)> = [("x", "y"), ("x", "z"), ("y", "z")
        ].iter().map(|(v1, v2)| (v1.to_string(), v2.to_string())).collect();
    assert_eq!(mdisjs, mandatory_disjoints(&program.axioms["ax1"]));
}

