use metamast::io::MockIO;
use metamast::mm_parser::{strip_comments, load_includes, parse_program};

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
    assert!(text.is_err(), "Malformed comment");

    let text = strip_comments("$c wff $.\n$) $v x $.\n$( finished comment $)\n");
    assert!(text.is_err(), "Malformed comment");

    // $( $[ $) is a comment

    let text = strip_comments("$c wff $.\n$( $[ $)\n$v x $.\n");
    assert_eq!(text.unwrap().to_string(), "$c wff $.\n\n$v x $.\n");

    // they may not contain the 2-character sequences $( or $) (comments do not nest)

    let text = strip_comments("$c wff $.\n$( comment $( nested comment, illegal $) $)\n$v x $.\n");
    assert!(text.is_err(), "Comments may not be nested");
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
    assert!(result.is_err(), "Include statement only allowed in outermost scope");

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
    assert!(result.is_err(), "Constant c was already defined before");
    let result = parse_program("$v x y x $.\n");
    assert!(result.is_err(), "Variable x was already defined before");

    // A math symbol becomes active when declared and stays active
    // until the end of the block in which it is declared.
    let program = parse_program("$v x y $.\n").unwrap();
    assert!(program.scope.variables.contains(&"x".to_string()));

    // A constant must be declared in the outermost block
    parse_program("$c a b c $.\n${\n  $v x y $.\n$}\n$c d e f $.\n").unwrap();
    let result = parse_program("$c a b c $.\n${\n  $c d e f $.\n$}\n");
    assert!(result.is_err(), "Parse error");

    // A constant ... may not be declared a second time.
    let result = parse_program("$c a b c $.\n${\n  $v x y $.\n$}\n$c b $.\n");
    assert!(result.is_err(), "Constant b was already defined before");

    // A variable may not be declared a second time while it is active
    let result = parse_program("${\n  $v x y $.\n  $v z x $. $}\n");
    assert!(result.is_err(), "Variable x was already defined before");

    // [a variable] may be declared again (as a variable, but not as a constant)
    // after it becomes inactive.
    parse_program("${\n  $v x y $.\n$}\n$v z x $.\n").unwrap();
    let result = parse_program("${\n  $v x y $.\n$}\n$c z x $.\n");
    assert!(result.is_err(), "Constant x was previously defined as a variable");

    // A variable must not match an existing constant (follows from other rules)
    let result = parse_program("$c x $.\n$v x $.\n");
    assert!(result.is_err(), "Variable x matches an existing constant");
}

#[test]
fn test_parse_hypotheses() {
    // A $f statement consists of a label, followed by $f, followed by its typecode
    // (an active constant), followed by an active variable, followed by the $. token.
    let program = parse_program("$c var c $.\n$v x $.\nvarx $f var x $.\n").unwrap();
    assert!(program.scope.floatings.contains_key(&"varx".to_string()));
    let result = parse_program("$c var c $.\n$v x $.\nvarx $f bar x $.\n");
    assert!(result.is_err(), "Type bar not found in constants");
    let result = parse_program("$c var c $.\n$v x $.\nvarx $f var y $.\n");
    assert!(result.is_err(), "Variable y not defined");
    let result = parse_program("$c var c $.\n$v x $.\nvarx $f var c $.\n");
    assert!(result.is_err(), "Variable c not defined");

    // A $e statement consists of a label, followed by $e, followed by its typecode
    // (an active constant), followed by zero or more active math symbols, followed
    // by the $. token.
    let program = parse_program(
        "$c var a b $.\n$v x $.\nvarx $f var x $.\ness1 $e var x a a $.\n").unwrap();
    assert!(program.scope.essentials.contains_key(&"ess1".to_string()));
    let program = parse_program("$c var $.\ness1 $e var $.\n").unwrap();
    assert!(program.scope.essentials.contains_key(&"ess1".to_string()));
    let result = parse_program(
        "$c var a b $.\n$v x $.\nvarx $f var x $.\ness1 $e bar x a a $.\n");
    assert!(result.is_err(), "Type bar not found in constants");
    let result = parse_program("$c var a b $.\n$v x $.\ness1 $e var y a a $.\n");
    assert!(result.is_err(), "Variable or constant y not defined");
    let result = parse_program(
        "$c var a b $.\n$v x $.\nvarx $f var x $.\ness1 $e var x a b a x c $.\n");
    assert!(result.is_err(), "Variable or constant c not defined");
    let result = parse_program("$c var a b $.\n${ $v x $. $}\ness1 $e var x a a $.\n");
    assert!(result.is_err(), "Variable or constant x not defined");

    // The type declared by a $f statement for a given label is global
    // even if the variable is not (e.g., a database may not have wff P in one
    // local scope and class P in another).
    let result = parse_program(
        "$c wff class $.\n${ $v P $.\nwff_P $f wff P $. $}\n${ $v P $.\nclass_P $f class P $. $}\n");
    assert!(result.is_err(), "Variable P was previously assigned type wff");

    // There may not be two active $f statements containing the same variable.
    let result = parse_program(
        "$c var int $.\n$v x $.\nvarx $f var x $.\nintx $f int x $.\n");
    assert!(result.is_err(), "Variable x was previously assigned type var");
    let result = parse_program(
        "$c var int $.\n$v x $.\nvarx $f var x $.\nvarx2 $f var x $.\n");
    assert!(result.is_err(), "Variable x was previously assigned type var");
}

#[test]
fn test_parse_disjoints() {
    // A simple $d statement consists of $d, followed by two different
    // active variables, followed by the $. token.
    let program = parse_program("$v x y $.\n$d x y $.\n").unwrap();
    assert_eq!(1, program.scope.disjoints.len());
    let result = parse_program("$v x y $.\n$d x x $.\n");
    assert!(result.is_err(), "Variable x appears more than once in a disjoint statement");
    let result = parse_program("$v y $.\n$d x y $.\n");
    assert!(result.is_err(), "Variable x not active");
    let result = parse_program("$v y $.\n${ $v x $. $}\n$d x y $.\n");
    assert!(result.is_err(), "Variable x not active");

    // A compound $d statement consists of $d, followed by three or more
    // variables (all different), followed by the $. token.
    let program = parse_program("$v x y z $.\n$d x z y $.\n").unwrap();
    assert_eq!(3, program.scope.disjoints.len());
    let result = parse_program("$v x y z $.\n$d z x z y $.\n");
    assert!(result.is_err(), "Variable z appears more than once in a disjoint statement");

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
    assert!(program.axioms.contains_key(&"ax1".to_string()));
    let program = parse_program(
        "$c var wff = $.\n$v x $.\nvarx $f var x $.\nax1 $a wff = x x $.\n").unwrap();
    assert!(program.axioms.contains_key(&"ax1".to_string()));
    let result = parse_program("$c var wff $.\n$v x $.\nvarx $f var x $.\nax1 $a woof x $.\n");
    assert!(result.is_err(), "Type woof not found in constants");
    let result = parse_program("$c var wff $.\n$v x $.\nvarx $f var x $.\nax1 $a wff y $.\n");
    assert!(result.is_err(), "Variable or constant y not defined");

    // A $p statement consists of a label, followed by $p, followed by its typecode
    // (an active constant), followed by zero or more active math symbols,
    // followed by $=, followed by a sequence of labels, followed by the $. token.
    let program = parse_program(
        "$c var wff $.\n$v x $.\nvarx $f var x $.\ndum $a var x $.\np1 $p wff x $= dum dum $.\n").unwrap();
    assert!(program.provables.contains_key(&"p1".to_string()));
    let program = parse_program(
        "$c var wff = $.\n$v x $.\nvarx $f var x $.\nding $a var x $.\ndong $a wff x $.\np1 $p wff = x x $= ding dong $.\n").unwrap();
    assert!(program.provables.contains_key(&"p1".to_string()));
    let result = parse_program(
        "$c var wff $.\n$v x $.\nvarx $f var x $.\ndum $a var x $.\np1 $p woof x $= dum dum $.\n");
    assert!(result.is_err(), "Type woof not found in constants");

    // Each variable in a $e, $a, or $p statement must exist in an active $f statement.
    let result = parse_program("$c var wff $.\n$v x $.\nmin $e wff x $.\n");
    assert!(result.is_err(), "Variable x must be assigned a type");
}

