use crate::tokens::Token;

#[derive(Debug)]
pub struct AST(Vec<ASTNode>);

#[derive(Debug)]
pub enum ASTNode {
    Identifier(Box<str>),
    String(Box<str>),
    Period,
    Comma,
    Colon,
    Semicolon,
    Group { len: usize },
}

#[derive(Debug)]
pub enum ASTParseError {
    UnclosedParen { paren_stack: Vec<usize> },
    NonClosingParen,
}

impl AST {
    pub fn parse(tokens: impl IntoIterator<Item = Token>) -> Result<Self, ASTParseError> {
        tokens
            .into_iter()
            .try_fold(
                (Vec::new(), Vec::new()),
                |(mut nodes, mut paren_stack), item| {
                    match item {
                        Token::Identifier(e) => nodes.push(ASTNode::Identifier(e)),
                        Token::String(e) => nodes.push(ASTNode::String(e)),
                        Token::SingleChar('.') => nodes.push(ASTNode::Period),
                        Token::SingleChar(',') => nodes.push(ASTNode::Comma),
                        Token::SingleChar(':') => nodes.push(ASTNode::Colon),
                        Token::SingleChar(';') => nodes.push(ASTNode::Semicolon),
                        Token::SingleChar('(') => {
                            paren_stack.push(nodes.len());
                            nodes.push(ASTNode::Group { len: 0 });
                        }
                        Token::SingleChar(')') => {
                            let Some(idx) = paren_stack.pop() else {
                                return Err(ASTParseError::NonClosingParen);
                            };
                            let len = nodes.len() - (idx + 1);
                            nodes[idx] = ASTNode::Group { len };
                        }
                        Token::SingleChar(c) => panic!(
                            "AST::parse received a token with an invalid \
                            Token::SingleChar token with char {c:?}"
                        ),
                    }
                    Ok((nodes, paren_stack))
                },
            )
            .and_then(|(nodes, paren_stack)| {
                paren_stack
                    .is_empty()
                    .then_some(Self(nodes))
                    .ok_or(ASTParseError::UnclosedParen { paren_stack })
            })
    }
}
