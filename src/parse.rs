#[derive(Debug)]
pub enum Atom {
    Aggr(Box<[Atom]>),
    Identifier(Box<str>),
    Bytes(Box<[u8]>),
}

#[derive(Debug)]
pub enum ParseError {
    InvalidChar(char),
    InvalidEscape(char),
    UnclosedQuote,
    UnclosedParen,
    UnopenedParen,
    UnfinishedEscape,
}

pub type ParseResult<T> = Result<T, ParseError>;

impl Atom {
    pub fn parse_module(module: &str) -> ParseResult<Self> {
        let mut stack = Vec::<Vec<Atom>>::new();
        let mut curr_frame = Vec::new();
        let mut str = module;
        loop {
            str = skip_white_space(str);
            let (Some(char), mut rem) = split_first_char(str) else {
                if !stack.is_empty() {
                    break Err(ParseError::UnclosedParen);
                }
                break Ok(Atom::Aggr(curr_frame.into()));
            };
            match char {
                '(' => {
                    stack.push(curr_frame);
                    curr_frame = Default::default();
                }
                ')' => {
                    let Some(mut prev_frame) = stack.pop() else {
                        break Err(ParseError::UnopenedParen);
                    };

                    prev_frame.push(Atom::Aggr(curr_frame.into()));

                    curr_frame = prev_frame;
                }
                '\"' => {
                    let (bytes, rem2) = parse_string(rem)?;

                    curr_frame.push(Atom::Bytes(bytes.into()));

                    rem = rem2;
                }
                c => {
                    let Some((ident, rem2)) = parse_ident(str) else {
                        break Err(ParseError::InvalidChar(c));
                    };

                    curr_frame.push(Atom::Identifier(ident.into()));

                    rem = rem2;
                }
            };
            str = rem
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
fn parse_string(mut str: &str) -> ParseResult<(Vec<u8>, &str)> {
    let mut acc = Vec::new();
    loop {
        let (Some(char), rem) = split_first_char(str) else {
            return Err(ParseError::UnclosedQuote);
        };
        let rem = match char {
            '\\' => parse_escape(rem, &mut acc)?,
            '\"' => break Ok((acc, rem)),
            c => {
                acc.extend_from_slice(c.encode_utf8(&mut [0; 4]).as_bytes());
                rem
            }
        };
        str = rem;
    }
}

fn parse_escape<'t>(str: &'t str, buf: &mut Vec<u8>) -> ParseResult<&'t str> {
    let (Some(char), mut rem) = split_first_char(str) else {
        return Err(ParseError::UnclosedQuote);
    };
    buf.push(match char {
        '\"' => b'\"',
        '\\' => b'\\',
        '\r' | '\n' => {
            return Ok(skip_white_space(rem));
        }
        'n' => b'\n',
        'r' => b'\r',
        't' => b'\t',
        '0' => b'\0',
        'x' => {
            fn char_to_nibble(char: char) -> Option<u8> {
                Some(match char {
                    '0' => 0x0,
                    '1' => 0x1,
                    '2' => 0x2,
                    '3' => 0x3,
                    '4' => 0x4,
                    '5' => 0x5,
                    '6' => 0x6,
                    '7' => 0x7,
                    '8' => 0x8,
                    'a' | 'A' => 0xA,
                    'b' | 'B' => 0xB,
                    'c' | 'C' => 0xC,
                    'd' | 'D' => 0xD,
                    'e' | 'E' => 0xE,
                    'f' | 'F' => 0xF,
                    _ => return None,
                })
            }
            let (Some(large), rem1) = split_first_char(rem) else {
                return Err(ParseError::UnfinishedEscape);
            };
            let Some(large) = char_to_nibble(large) else {
                return Err(ParseError::InvalidEscape(large));
            };
            let (Some(small), rem2) = split_first_char(rem1) else {
                return Err(ParseError::UnfinishedEscape);
            };
            let Some(small) = char_to_nibble(small) else {
                return Err(ParseError::InvalidEscape(small));
            };
            rem = rem2;
            large << 4 | small
        }
        c => return Err(ParseError::InvalidEscape(c)),
    });
    Ok(rem)
}
