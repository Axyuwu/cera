use std::array;

use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{alphanumeric1, char, multispace0, none_of, satisfy},
    combinator::{opt, recognize, value},
    multi::{fold_many0, many0, many1},
    sequence::{delimited, preceded, terminated},
    AsBytes, AsChar, IResult, Parser,
};

#[derive(Debug)]
pub enum Atom {
    Group(Box<[Atom]>),
    String(Box<[u8]>),
}

pub fn parse_module(s: &str) -> IResult<&str, Atom> {
    parse_atom_many_sep(s)
}

fn parse_atom_many(s: &str) -> IResult<&str, Atom> {
    preceded(
        multispace0,
        many0(parse_atom).map(|s| Atom::Group(s.into())),
    )
    .parse(s)
}

fn parse_atom_many_sep(s: &str) -> IResult<&str, Atom> {
    alt((parse_atom_list, parse_atom_many)).parse(s)
}

fn parse_atom(s: &str) -> IResult<&str, Atom> {
    terminated(
        alt((parse_atom_group, parse_atom_ident, parse_atom_string)),
        multispace0,
    )
    .parse(s)
}

fn parse_atom_group(s: &str) -> IResult<&str, Atom> {
    delimited(char('('), parse_atom_many_sep, char(')')).parse(s)
}

fn parse_atom_ident(s: &str) -> IResult<&str, Atom> {
    recognize(many1(alt((alphanumeric1, tag("_")))))
        .map(|s: &str| Atom::String(s.as_bytes().into()))
        .parse(s)
}

fn parse_atom_list(s: &str) -> IResult<&str, Atom> {
    (
        many1(terminated(parse_atom_many, char(';'))),
        opt(parse_atom_many),
    )
        .map(|(mut vec, elem)| {
            elem.map(|e| vec.push(e));
            Atom::Group(vec.into())
        })
        .parse(s)
}

struct CharStep {
    buf: [u8; 4],
    len: usize,
}
impl<const LEN: usize> From<[u8; LEN]> for CharStep {
    fn from(value: [u8; LEN]) -> Self {
        value.as_bytes().into()
    }
}
impl<const LEN: usize> From<&[u8; LEN]> for CharStep {
    fn from(value: &[u8; LEN]) -> Self {
        value.as_bytes().into()
    }
}
impl From<&[u8]> for CharStep {
    fn from(value: &[u8]) -> Self {
        assert!(value.len() <= 4);
        Self {
            buf: array::from_fn(|i| value.get(i).copied().unwrap_or(0)),
            len: value.len(),
        }
    }
}

fn parse_atom_string(s: &str) -> IResult<&str, Atom> {
    let hex_digit = || satisfy(<char as AsChar>::is_hex_digit);
    let hex_escape = preceded(
        char('x'),
        recognize((hex_digit(), hex_digit()))
            .map_res(|s| u8::from_str_radix(s, 16).map(|e| [e].into())),
    );
    let ascii_escape = alt((
        value(b"\"", char('\"')),
        value(b"\\", char('\\')),
        value(b"\0", char('0')),
        value(b"\n", char('n')),
        value(b"\r", char('r')),
        value(b"\t", char('t')),
    ))
    .map(Into::into);
    let parse_escape = preceded(char('\\'), alt((ascii_escape, hex_escape)));
    let parse_char = none_of("\"\\").map(|c| {
        let mut buf = CharStep {
            buf: [0; _],
            len: 0,
        };
        c.encode_utf8(&mut buf.buf);
        buf.len = c.len_utf8();
        buf
    });
    let parse_one = alt((parse_char, parse_escape));
    let parse_inner = fold_many0(parse_one, Vec::new, |mut v, e| {
        v.extend(&e.buf[..e.len]);
        v
    });
    delimited(char('\"'), parse_inner, char('\"'))
        .map(|s| Atom::String(s.into()))
        .parse(s)
}
