#[derive(Debug)]
pub enum Atom {
    Unit,
    Apply(Box<Apply>),
    Identifier(Box<str>),
    String(Box<str>),
}

/// Left-associative
#[derive(Debug)]
struct Apply {
    lhs: Atom,
    rhs: Atom,
}

#[derive(Debug)]
pub enum ParseError {
    InvalidChar(char),
    InvalidEscape(char),
    UnclosedQuote,
    UnclosedParen,
    UnopenedParen,
}

pub type ParseResult<T> = Result<T, ParseError>;

impl Atom {
    pub fn parse_module(module: &str) -> ParseResult<Self> {
        fn push_atom(frame_atom: &mut Option<Atom>, rhs: Atom) {
            *frame_atom = match frame_atom {
                None => Some(rhs),
                _ => frame_atom
                    .take()
                    .map(|lhs| Atom::Apply(Apply { lhs, rhs }.into())),
            }
        }

        let mut stack = Vec::<Option<Atom>>::new();
        let mut curr_frame = None;
        let mut str = module;
        loop {
            str = skip_white_space(str);
            let (Some(char), rem) = split_first_char(str) else {
                if !stack.is_empty() {
                    break Err(ParseError::UnclosedParen);
                }
                break Ok(curr_frame.unwrap_or(Atom::Unit));
            };
            match char {
                '(' => {
                    stack.push(curr_frame);
                    curr_frame = Default::default();

                    str = rem;
                }
                ')' => {
                    let Some(prev_frame) = stack.pop() else {
                        break Err(ParseError::UnopenedParen);
                    };
                    let atom = std::mem::replace(&mut curr_frame, prev_frame).unwrap_or(Atom::Unit);
                    push_atom(&mut curr_frame, atom);

                    str = rem;
                }
                '\"' => {
                    let (string, rem) = parse_string(rem)?;

                    push_atom(&mut curr_frame, Atom::String(string.into()));

                    str = rem;
                }
                c => {
                    let Some((ident, rem)) = parse_ident(str) else {
                        break Err(ParseError::InvalidChar(c));
                    };

                    push_atom(&mut curr_frame, Atom::Identifier(ident));

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
