mod builtins;
mod parse;

fn main() {
    let input = std::fs::read_to_string("./examples/hello_world_interpreted.cera").unwrap();
    let module = parse::Atom::parse_module(&input).unwrap();
    println!("{}", builtins::eval_builtin(module));
}
