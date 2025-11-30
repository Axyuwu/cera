mod parse;

fn main() {
    let test_str = std::fs::read_to_string("./test.cera").unwrap();
    let test = parse::Atom::parse_module(&test_str).unwrap();
    dbg!(test);
}
