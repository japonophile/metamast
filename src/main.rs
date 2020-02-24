use metamast::mm_parser::parse_metamath;

fn main() {
    let filename = "mm/lib/set.mm";

    parse_metamath(filename);

    println!("Done");
}

