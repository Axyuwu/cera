use nom::{
    IResult, Parser, branch::alt, bytes::complete::tag, character::complete::{alphanumeric1, char, multispace0, one_of}, combinator::{cut, opt, recognize}, multi::{many0, many1}, sequence::{delimited, terminated}
};

use crate::parse::string::parse_string;

#[derive(Debug)]
pub enum Atom {
    Group(Box<[Atom]>),
    String(Box<[u8]>),
    Ident(Box<str>),
    Operator(Box<str>),
}

pub(super) fn parse_atom_many_sep(s: &str) -> IResult<&str, Atom> {
    alt((parse_atom_list, parse_atom_many)).parse(s)
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

fn parse_atom_many(s: &str) -> IResult<&str, Atom> {
    many0(parse_atom).map(|s| Atom::Group(s.into())).parse(s)
}

fn parse_atom(s: &str) -> IResult<&str, Atom> {
    delimited(
        multispace0,
        alt((parse_atom_group, parse_atom_ident, parse_atom_string)),
        multispace0,
    )
    .parse(s)
}

fn parse_atom_group(s: &str) -> IResult<&str, Atom> {
    alt((
        delimited(char('('), parse_atom_many_sep, cut(char(')'))),
        delimited(char('{'), parse_atom_many_sep, cut(char('}'))),
        delimited(char('['), parse_atom_many_sep, cut(char(']'))),
    ))
    .parse(s)
}

fn parse_atom_ident(s: &str) -> IResult<&str, Atom> {
    recognize(many1(alt((alphanumeric1, tag("_")))))
        .map(|s: &str| Atom::Ident(s.into()))
        .parse(s)
}

fn parse_atom_string(s: &str) -> IResult<&str, Atom> {
    parse_string.map(Into::into).map(Atom::String).parse(s)
}
