use nom::{
    branch::alt,
    bytes::complete::{escaped, tag},
    character::complete::{alphanumeric1, char, multispace0, none_of, satisfy},
    combinator::{not, opt, recognize},
    multi::{fold_many0, many, many0, many1},
    sequence::{delimited, preceded, terminated},
    IResult, Parser,
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
    terminated(alt((parse_atom_group, parse_atom_ident)), multispace0).parse(s)
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

/*
fn parse_atom_string(s: &str) -> IResult<&str, Atom> {
    //let hex_escape = preceeded(char('x'), recognize().map(u8::fro))
    //let parse_escape = preceded(char('\\'), ());
    let parse_char = alt((,)); //parse_escape));
    let parse_inner = many0(parse_char);
    delimited(char('\"'), parse_inner, char('\"'))
        .map(|s| Atom::String(s.into()))
        .parse(s)
}
*/
