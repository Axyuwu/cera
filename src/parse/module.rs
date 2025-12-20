use nom::Finish as _;

use crate::parse::{parse_atom_many_sep, Atom};

pub fn parse_module(s: &str) -> Result<(&str, Atom), nom::error::Error<&str>> {
    parse_atom_many_sep(s).finish()
}
