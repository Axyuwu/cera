use crate::interp::value::{Val, ValComplex};

mod interp;
mod parse;

fn main() {
    let val = Val::new_complex(ValComplex::new_any(65u32));
    assert_eq!(val.complex().unwrap().get_any::<u32>().unwrap(), &65);
    /*
    let test_str = std::fs::read_to_string("./test.cera").unwrap();
    let test = parse::parse_module(&test_str).unwrap();
    dbg!(test);
    */
}
