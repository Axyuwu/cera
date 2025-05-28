use std::time::Instant;

mod builtins;
mod parse;
pub mod utils;

fn main() {
    let input = std::fs::read_to_string("./examples/hello_world_interpreted.cera").unwrap();
    let module = parse::Atom::parse_module(&input).unwrap();
    let start = Instant::now();
    let res = builtins::eval_builtin(module);
    println!("took {} seconds", start.elapsed().as_secs_f32());
    println!("{}", res);
}
