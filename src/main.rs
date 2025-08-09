use std::time::Instant;

use crate::{
    builtins::{atom_to_val_raw, builtin_values::BuiltinLookup},
    utils::sync::cache_arc::CacheArc as Arc,
    write::write_module_pretty,
};

mod builtins;
mod parse;
pub mod utils;
mod write;

fn main() {
    let builtins_str = std::fs::read_to_string("./builtins.cera").unwrap();
    let builtins = parse::Atom::parse_module(&builtins_str).unwrap();
    let builtin_lookup = Arc::new(BuiltinLookup::new(atom_to_val_raw(builtins)));
    let input = std::fs::read_to_string("./examples/hello_world_interpreted.cera").unwrap();
    let module = parse::Atom::parse_module(&input).unwrap();
    let start = Instant::now();
    let res = builtins::eval_builtin(module, &builtin_lookup);
    let taken = start.elapsed().as_secs_f32();
    print!("{}", write_module_pretty(&res));
    eprintln!("taken: {}", taken);
}
