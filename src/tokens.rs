#[derive(Debug)]
pub enum Token {
    Identifier(Box<str>),
    String(Box<str>),
    SingleChar(char),
}

#[derive(Debug)]
pub enum TokenizeError {
    InvalidChar(char),
    EarlyEOF,
    InvalidEscape(char),
}

type TokenizeResult<T> = Result<T, TokenizeError>;

pub fn tokenize(mut str: &str) -> TokenizeResult<Vec<Token>> {
    let mut acc = Vec::new();
    loop {
        str = skip_white_space(str);
        if str.is_empty() {
            break Ok(acc);
        };
        let (token, rem) = tokenize_once(str)?;
        acc.push(token);
        str = rem;
    }
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

// errors if called with empty string
fn tokenize_once(str: &str) -> TokenizeResult<(Token, &str)> {
    let (char, rem) = split_first_char(str);
    let char = char.expect("tokenize_once must be called with a nonempty string");
    match char {
        c if is_pats!(char, '.' ',' ';' ':' '(' ')') => Ok((Token::SingleChar(c), rem)),
        _ if is_ident_char(char) => Ok(take_while(str, is_ident_char, Token::Identifier)),
        '\"' => tokenize_string(rem),
        c => Err(TokenizeError::InvalidChar(c)),
    }
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
fn tokenize_string(mut str: &str) -> TokenizeResult<(Token, &str)> {
    let mut acc = String::new();
    loop {
        let (Some(char), rem) = split_first_char(str) else {
            return Err(TokenizeError::EarlyEOF);
        };
        let (char, rem) = match char {
            '\\' => parse_escape(rem)?,
            '\"' => break Ok((Token::String(acc.into()), rem)),
            c => (Some(c), rem),
        };
        char.map(|c| acc.push(c));
        str = rem;
    }
}

fn parse_escape(str: &str) -> TokenizeResult<(Option<char>, &str)> {
    let (Some(char), rem) = split_first_char(str) else {
        return Err(TokenizeError::EarlyEOF);
    };
    match char {
        '\"' => Ok((Some('\"'), rem)),
        '\\' => Ok((Some('\\'), rem)),
        '\r' | '\n' => Ok((None, skip_white_space(rem))),
        c => Err(TokenizeError::InvalidEscape(c)),
    }
}
