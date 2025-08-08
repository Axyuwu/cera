use std::time::Instant;

use crate::write::write_value_pretty;

mod builtins;
mod parse;
pub mod utils;
mod write;

fn main() {
    let input = std::fs::read_to_string("./examples/hello_world_interpreted.cera").unwrap();
    let module = parse::Atom::parse_module(&input).unwrap();
    let start = Instant::now();
    let res = builtins::eval_builtin(module);
    let taken = start.elapsed().as_secs_f32();
    print!("{}", write_value_pretty(&res));
}
