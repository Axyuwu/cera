mod builtins;
mod parse;

fn main() {
    let str = r#"helo (hai hello world wow (test test2 hai hello) ("hellow; \"world\""))"#;
    dbg!(parse::Atom::parse_module(str).unwrap());
}
