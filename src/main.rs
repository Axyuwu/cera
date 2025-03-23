use ast::AST;
use tokens::tokenize;

mod ast;
mod tokens;

fn main() {
    let input = r#"test (hello : world) (() heya, bhellow.vorld; "hey hey!" "hey \"world\"")"#;
    let tokens = tokenize(input).unwrap();
    dbg!(&tokens);
    let ast = AST::parse(tokens).unwrap();
    dbg!(&ast);
}
