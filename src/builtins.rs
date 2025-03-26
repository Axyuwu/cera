use std::any::Any;

use crate::parse::{Apply, Atom};

#[derive(Debug)]
pub enum EvalError {
    UnknownIdent(Box<str>),
    CannotApplyStr,
    CannotApplyUnit,
    InvalidArg { arg: EvalValue, apply: EvalValue },
}

type EvalResult = Result<EvalValue, EvalError>;

type EvalValue = Box<dyn Value>;

pub fn eval(atom: &Atom) -> EvalResult {
    eval_ctx(
        atom,
        Context {
            curr_lookup: &|ident| match ident {
                "builtin" => Some(Box::new(Builtin)),
                _ => None,
            },
            prev: None,
        },
    )
}

pub fn eval_ctx(atom: &Atom, ctx: Context) -> EvalResult {
    Ok(match atom {
        Atom::Unit => Box::new(Unit),
        Atom::Apply(apply) => {
            let Apply { ref lhs, ref rhs } = **apply;
            eval_ctx(lhs, ctx)?.apply(rhs, ctx)?
        }
        Atom::Identifier(s) => ctx.resolve_ident(s)?,
        Atom::String(s) => Box::new(s.clone()),
    })
}

#[derive(Clone, Copy)]
pub struct Context<'t> {
    curr_lookup: &'t dyn Fn(&str) -> Option<EvalValue>,
    prev: Option<&'t Context<'t>>,
}

impl<'t> Context<'t> {
    fn resolve_ident(self, ident: &str) -> EvalResult {
        if let Some(v) = (self.curr_lookup)(ident) {
            return Ok(v);
        }
        if let Some(prev) = self.prev {
            return prev.resolve_ident(ident);
        }
        Err(EvalError::UnknownIdent(ident.into()))
    }
}

pub trait Value: Any + std::fmt::Debug {
    fn apply(&self, atom: &Atom, ctx: Context) -> EvalResult;
}

impl dyn Value {
    fn downcast<T: Value>(&self) -> Option<&T> {
        if self.type_id() == std::any::TypeId::of::<T>() {
            // Safety: same as the normal Any implementation
            Some(unsafe { &*(self as *const dyn Value as *const T) })
        } else {
            None
        }
    }
}

impl Value for Box<str> {
    fn apply(&self, _atom: &Atom, _ctx: Context) -> EvalResult {
        Err(EvalError::CannotApplyStr)
    }
}

#[derive(Debug)]
struct Unit;
impl Value for Unit {
    fn apply(&self, _atom: &Atom, _ctx: Context) -> EvalResult {
        Err(EvalError::CannotApplyUnit)
    }
}

#[derive(Debug)]
struct Builtin;
impl Value for Builtin {
    fn apply(&self, atom: &Atom, ctx: Context) -> EvalResult {
        eval_ctx(
            atom,
            Context {
                curr_lookup: &|ident| match ident {
                    "interp" => Some(Box::new(Interpreter)),
                    _ => None,
                },
                prev: Some(&ctx),
            },
        )
    }
}

#[derive(Debug)]
struct Interpreter;
impl Value for Interpreter {
    fn apply(&self, atom: &Atom, ctx: Context) -> EvalResult {
        eval_ctx(
            atom,
            Context {
                curr_lookup: &|ident| match ident {
                    "print" => Some(Box::new(Print)),
                    _ => None,
                },
                prev: Some(&ctx),
            },
        )
    }
}

#[derive(Debug)]
struct Print;
impl Value for Print {
    fn apply(&self, atom: &Atom, ctx: Context) -> EvalResult {
        let arg = eval_ctx(atom, ctx)?;
        let Some(str) = arg.downcast::<Box<str>>() else {
            return Err(EvalError::InvalidArg {
                arg,
                apply: Box::new(Print),
            });
        };
        print!("{}", str);
        Ok(Box::new(Unit))
    }
}
