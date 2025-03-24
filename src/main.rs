use parse::Module;

mod parse;

fn main() {
    let str = r#"helo (hai hello.world . wow (test; test2 hai.hello) ("hellow; \"world\"";))"#;
    println!("{:?}", Module::parse(str).unwrap());
}
