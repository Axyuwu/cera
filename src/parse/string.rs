use derive_more::From;
use nom::{
    branch::alt,
    bytes::complete::{is_not, take_while_m_n},
    character::complete::{char, multispace1},
    combinator::{cut, map_res, recognize, value},
    multi::{fold, many1},
    sequence::{delimited, preceded},
    IResult, Parser,
};

pub(super) fn parse_string(s: &str) -> IResult<&str, Vec<u8>> {
    let build_string = fold(0.., parse_fragment, Vec::new, |mut acc, frag| {
        let mut store = [0; 4];
        acc.extend_from_slice(match &frag {
            StringFragment::Str(s) => s.as_bytes(),
            StringFragment::Byte(b) => std::slice::from_ref(b),
            StringFragment::Char(c) => c.encode_utf8(&mut store).as_bytes(),
        });
        acc
    });
    delimited(char('"'), build_string, char('"')).parse(s)
}

#[derive(From)]
enum StringFragment<'t> {
    Str(&'t str),
    Byte(u8),
    Char(char),
}

fn parse_fragment(s: &str) -> IResult<&str, StringFragment> {
    alt((parse_nonescape, parse_escape)).parse(s)
}

fn parse_nonescape(s: &str) -> IResult<&str, StringFragment> {
    let not_quote_slash = is_not("\"\\");
    recognize(many1(not_quote_slash)).map(Into::into).parse(s)
}

fn parse_escape(s: &str) -> IResult<&str, StringFragment> {
    preceded(
        char('\\'),
        cut(alt((
            parse_whitespace_escape,
            parse_char_escape,
            parse_byte_escape,
            parse_unicode_escape,
        ))),
    )
    .parse(s)
}

fn parse_whitespace_escape(s: &str) -> IResult<&str, StringFragment> {
    multispace1.map(|_| "".into()).parse(s)
}

fn parse_char_escape(s: &str) -> IResult<&str, StringFragment> {
    alt((
        value(b'\n', char('n')),
        value(b'\r', char('r')),
        value(b'\t', char('t')),
        value(b'\\', char('\\')),
        value(b'\\', char('\\')),
        value(b'\0', char('0')),
        value(b'"', char('"')),
    ))
    .map(Into::into)
    .parse(s)
}

fn parse_byte_escape(s: &str) -> IResult<&str, StringFragment> {
    let parse_hex = take_while_m_n(2, 2, |c: char| c.is_ascii_hexdigit());
    let parse_prefixed_hex = preceded(char('x'), parse_hex);
    parse_prefixed_hex
        .map_res(move |hex| u8::from_str_radix(hex, 16))
        .map(Into::into)
        .parse(s)
}

fn parse_unicode_escape(s: &str) -> IResult<&str, StringFragment> {
    let parse_hex = take_while_m_n(1, 6, |c: char| c.is_ascii_hexdigit());
    let parse_delimited_hex = preceded(char('u'), delimited(char('{'), parse_hex, char('}')));
    let parse_u32 = map_res(parse_delimited_hex, move |hex| u32::from_str_radix(hex, 16));
    parse_u32
        .map_opt(std::char::from_u32)
        .map(Into::into)
        .parse(s)
}
