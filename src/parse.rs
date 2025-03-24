use std::num::{NonZero, NonZeroUsize};

#[derive(Debug)]
pub struct Module {
    tokens: Vec<Token>,
}

#[derive(Debug)]
pub enum Token {
    Identifier(Box<str>),
    String(Box<str>),
    Field(Box<str>),
    Group { len: usize },
    Line { len: usize },
}

#[derive(Debug)]
pub enum ParseError {
    InvalidChar(char),
    InvalidEscape(char),
    InvalidCharAfterDot(char),
    UnclosedQuote,
    UnclosedParen,
    UnopenedParen,
    TrailingDot,
}

pub type ParseResult<T> = Result<T, ParseError>;

impl Module {
    pub fn parse(mut str: &str) -> ParseResult<Self> {
        #[derive(Debug)]
        struct StackFrame {
            group_idx: usize,
            line_idx: Option<NonZeroUsize>,
        }
        fn end_line(stack: &mut Vec<StackFrame>, tokens: &mut Vec<Token>) {
            let Some(idx) = stack.last().unwrap().line_idx.map(NonZero::get) else {
                return;
            };
            let len = tokens.len() - (idx + 1);
            if len == 0 {
                tokens.pop();
                return;
            }
            tokens[idx] = Token::Line { len };
        }
        fn pop_frame<const FINAL: bool>(
            stack: &mut Vec<StackFrame>,
            tokens: &mut Vec<Token>,
        ) -> ParseResult<()> {
            if (stack.len() == 1) ^ FINAL {
                return Err(if FINAL {
                    ParseError::UnopenedParen
                } else {
                    ParseError::UnclosedParen
                });
            }

            end_line(stack, tokens);

            let idx = stack.pop().unwrap().group_idx;

            let len = tokens.len() - (idx + 1);

            tokens[idx] = Token::Group { len };

            Ok(())
        }

        let mut stack = vec![StackFrame {
            group_idx: 0,
            line_idx: None,
        }];
        let mut tokens = vec![Token::Group { len: 0 }];

        loop {
            str = skip_white_space(str);
            let (Some(char), rem) = split_first_char(str) else {
                pop_frame::<true>(&mut stack, &mut tokens)?;
                return Ok(Self { tokens });
            };
            match char {
                '.' => {
                    str = skip_white_space(rem);
                    let Some(c) = split_first_char(str).0 else {
                        return Err(ParseError::TrailingDot);
                    };
                    let Some((ident, rem)) = parse_ident(str) else {
                        return Err(ParseError::InvalidCharAfterDot(c));
                    };
                    tokens.push(Token::Field(ident));
                    str = rem;
                }
                ';' => {
                    end_line(&mut stack, &mut tokens);
                    stack.last_mut().unwrap().line_idx = NonZero::new(tokens.len());
                    tokens.push(Token::Line { len: 0 });
                    str = rem;
                }
                '\"' => {
                    let (string, rem) = parse_string(rem)?;
                    tokens.push(Token::String(string.into()));
                    str = rem;
                }
                '(' => {
                    stack.push(StackFrame {
                        group_idx: tokens.len(),
                        line_idx: NonZero::new(tokens.len() + 1),
                    });
                    tokens.push(Token::Group { len: 0 });
                    tokens.push(Token::Line { len: 0 });
                    str = rem;
                }
                ')' => {
                    pop_frame::<false>(&mut stack, &mut tokens)?;
                    str = rem;
                }
                c => {
                    let Some((ident, rem)) = parse_ident(str) else {
                        return Err(ParseError::InvalidChar(c));
                    };
                    tokens.push(Token::Identifier(ident));
                    str = rem;
                }
            }
        }
    }
}

fn parse_ident(str: &str) -> Option<(Box<str>, &str)> {
    Some(take_while(str, is_ident_char, std::convert::identity))
        .filter(|s: &(Box<str>, _)| !s.0.is_empty())
}

fn split_first_char(str: &str) -> (Option<char>, &str) {
    let mut chars = str.chars();
    (chars.next(), chars.as_str())
}

fn skip_white_space(mut str: &str) -> &str {
    loop {
        let (char, rem) = split_first_char(str);
        match char {
            Some(' ' | '\t' | '\r' | '\n') => str = rem,
            _ => break str,
        }
    }
}

macro_rules! is_pats {
    ($ident:ident, $($pats:pat)+) => {
        match $ident {
            $($pats)|+ => true,
            _ => false,
        }
    };
}

fn is_ident_char(char: char) -> bool {
    is_pats!(char, '0'..='9' 'a'..='z' 'A'..='Z' '_')
}

fn take_while<'t, I: From<&'t str>, T>(
    str: &'t str,
    cond: impl Fn(char) -> bool,
    map: impl FnOnce(I) -> T,
) -> (T, &'t str) {
    let idx = str
        .char_indices()
        .find_map(|(i, e)| (!cond(e)).then_some(i))
        .unwrap_or(str.len());
    (map(str[0..idx].into()), &str[idx..])
}

/// Tokenises assuming it started with a " that has been consumed
fn parse_string(mut str: &str) -> ParseResult<(String, &str)> {
    let mut acc = String::new();
    loop {
        let (Some(char), rem) = split_first_char(str) else {
            return Err(ParseError::UnclosedQuote);
        };
        let (char, rem) = match char {
            '\\' => parse_escape(rem)?,
            '\"' => break Ok((acc, rem)),
            c => (Some(c), rem),
        };
        char.map(|c| acc.push(c));
        str = rem;
    }
}

fn parse_escape(str: &str) -> ParseResult<(Option<char>, &str)> {
    let (Some(char), rem) = split_first_char(str) else {
        return Err(ParseError::UnclosedQuote);
    };
    match char {
        '\"' => Ok((Some('\"'), rem)),
        '\\' => Ok((Some('\\'), rem)),
        '\r' | '\n' => Ok((None, skip_white_space(rem))),
        c => Err(ParseError::InvalidEscape(c)),
    }
}
