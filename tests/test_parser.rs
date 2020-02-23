use metamast::mm_parser::{strip_comments};

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
