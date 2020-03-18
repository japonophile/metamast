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
fn test_parse_mm_program() {
    // The same math symbol may not occur twice in a given $v or $c statement
    let result = parse_program("$c c c $.\n");
    assert!(result.is_err(), "Constant c was already defined before");
    let result = parse_program("$v x y x $.\n");
    assert!(result.is_err(), "Variable x was already defined before");
}

