use std::sync::Arc;

use crate::parse::{Apply, Atom};

#[derive(Debug, Clone)]
pub enum EvalSlice<'t, T> {
    Arc(Arc<[T]>),
    Borrowed(&'t [T]),
}

impl<'t, T> std::ops::Deref for EvalSlice<'t, T> {
    type Target = [T];
    fn deref(&self) -> &[T] {
        match self {
            EvalSlice::Arc(items) => items.as_ref(),
            EvalSlice::Borrowed(items) => items.as_ref(),
        }
    }
}

impl<'t, T> EvalSlice<'t, T> {
    fn get_mut(&mut self) -> Option<&mut [T]> {
        match self {
            EvalSlice::Arc(items) => Arc::get_mut(items),
            _ => None,
        }
    }
    fn make_mut(&mut self) -> &mut [T]
    where
        T: Clone,
    {
        match self {
            EvalSlice::Arc(items) => Arc::make_mut(items),
            EvalSlice::Borrowed(items) => {
                *self = Self::Arc((*items).into());
                self.make_mut()
            }
        }
    }
}

#[derive(Debug, Clone)]
pub enum EvalValue<'t> {
    Bytes(EvalSlice<'t, u8>),
    Aggregate(EvalSlice<'t, EvalValue<'t>>),
}

impl<'t> EvalValue<'t> {
    const fn slice_const(slice: &'t [Self]) -> Self {
        Self::Aggregate(EvalSlice::Borrowed(slice))
    }
    fn slice(slice: &'t (impl AsRef<[Self]> + 't + ?Sized)) -> Self {
        Self::slice_const(slice.as_ref())
    }
    fn slice_cloned(slice: impl AsRef<[Self]>) -> Self {
        Self::Aggregate(EvalSlice::Arc(slice.as_ref().into()))
    }
    fn arc(arc: Arc<[Self]>) -> Self {
        Self::Aggregate(EvalSlice::Arc(arc))
    }
    const fn byte_slice_const(slice: &'t [u8]) -> Self {
        Self::Bytes(EvalSlice::Borrowed(slice))
    }
    fn byte_slice(slice: &'t (impl AsRef<[u8]> + 't + ?Sized)) -> Self {
        Self::byte_slice_const(slice.as_ref())
    }
    fn byte_slice_cloned(slice: impl AsRef<[u8]>) -> Self {
        Self::Bytes(EvalSlice::Arc(slice.as_ref().into()))
    }
    fn byte_arc(arc: Arc<[u8]>) -> Self {
        Self::Bytes(EvalSlice::Arc(arc))
    }
}

// TODO: bytecode builtin
pub const BUILTIN: EvalValue = EvalValue::slice_const(&[]);

pub fn eval_builtin<'t>(atom: &'t Atom) -> EvalValue<'t> {
    apply(BUILTIN, atom)
}

fn atom_to_val<'t>(atom: &'t Atom) -> EvalValue<'t> {
    match atom {
        Atom::Unit => EvalValue::slice(const { &[EvalValue::byte_slice_const(b"unit")] }),
        Atom::Apply(apply) => {
            let Apply { lhs, rhs } = &**apply;
            let (e0, [e1, e2]) = (EvalValue::byte_slice(b"apply"), [lhs, rhs].map(atom_to_val));
            EvalValue::slice_cloned([e0, e1, e2])
        }
        Atom::Identifier(s) => EvalValue::slice_cloned([
            EvalValue::byte_slice("identifier"),
            EvalValue::byte_slice(s.as_bytes()),
        ]),
        Atom::String(s) => EvalValue::slice_cloned([
            EvalValue::byte_slice("string"),
            EvalValue::byte_slice(s.as_bytes()),
        ]),
    }
}

fn apply<'t>(val: EvalValue<'t>, atom: &'t Atom) -> EvalValue<'t> {
    // TODO: actual functions with bytecode etc
    EvalValue::slice_cloned([val, atom_to_val(atom)])
}
