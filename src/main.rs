use crate::value::{Val, ValComplex};

mod parse;
mod value;

fn main() {
    let val = Val::new_complex(ValComplex::new_compound([
        Val::new_usize(1),
        Val::new_usize(2),
        Val::new_complex(ValComplex::new_any(Box::new(["Hello"]))),
    ]));
    dbg!(val.clone());
    /*
    let test_str = std::fs::read_to_string("./test.cera").unwrap();
    let test = parse::parse_module(&test_str).unwrap();
    dbg!(test);
    */
}
