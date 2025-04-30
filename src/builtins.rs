use std::fmt::Write;
use std::sync::Arc;
use std::{fmt::Display, hash::Hash};

use crate::parse::{Apply, Atom};

#[derive(Debug, Clone)]
pub enum EvalSlice<T: 'static> {
    Arc(Arc<[T]>),
    Borrowed(&'static [T]),
}

impl<T> std::ops::Deref for EvalSlice<T> {
    type Target = [T];
    fn deref(&self) -> &[T] {
        match self {
            EvalSlice::Arc(items) => items.as_ref(),
            EvalSlice::Borrowed(items) => items.as_ref(),
        }
    }
}
impl<T: PartialEq> PartialEq for EvalSlice<T> {
    fn eq(&self, other: &Self) -> bool {
        &**self == &**other
    }
}
impl<T: Eq> Eq for EvalSlice<T> {}
impl<T: Hash> Hash for EvalSlice<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        (&**self).hash(state)
    }
}
impl<T: PartialOrd> PartialOrd for EvalSlice<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        (&**self).partial_cmp(&**other)
    }
}
impl<T: Ord> Ord for EvalSlice<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (&**self).cmp(&**other)
    }
}

impl<T> EvalSlice<T> {
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
pub enum Value {
    Bytes(EvalSlice<u8>),
    Aggregate(EvalSlice<Value>),
}

impl Value {
    const fn slice_const(slice: &'static [Self]) -> Self {
        Self::Aggregate(EvalSlice::Borrowed(slice))
    }
    fn slice(slice: &'static (impl AsRef<[Self]> + ?Sized)) -> Self {
        Self::slice_const(slice.as_ref())
    }
    fn slice_cloned(slice: impl AsRef<[Self]>) -> Self {
        Self::Aggregate(EvalSlice::Arc(slice.as_ref().into()))
    }
    fn slice_move(slice: impl Into<Arc<[Self]>>) -> Self {
        Self::Aggregate(EvalSlice::Arc(slice.into()))
    }
    fn arc(arc: Arc<[Self]>) -> Self {
        Self::Aggregate(EvalSlice::Arc(arc))
    }
    const fn byte_slice_const(slice: &'static [u8]) -> Self {
        Self::Bytes(EvalSlice::Borrowed(slice))
    }
    fn byte_slice(slice: &'static (impl AsRef<[u8]> + ?Sized)) -> Self {
        Self::byte_slice_const(slice.as_ref())
    }
    fn byte_slice_cloned(slice: impl AsRef<[u8]>) -> Self {
        Self::Bytes(EvalSlice::Arc(slice.as_ref().into()))
    }
    fn byte_slice_move(slice: impl Into<Arc<[u8]>>) -> Self {
        Self::Bytes(EvalSlice::Arc(slice.into()))
    }
    fn byte_arc(arc: Arc<[u8]>) -> Self {
        Self::Bytes(EvalSlice::Arc(arc))
    }
    fn prefix_fmt(&self, f: &mut std::fmt::Formatter<'_>, prefix: &mut String) -> std::fmt::Result {
        fn write_hexdump_width(
            bytes: &[u8],
            f: &mut std::fmt::Formatter<'_>,
            prefix: &str,
            width: usize,
        ) -> std::fmt::Result {
            fn write_byte(byte: u8, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                fn nibble_to_char(nibble: u8) -> char {
                    match nibble {
                        0x00 => '0',
                        0x01 => '1',
                        0x02 => '2',
                        0x03 => '3',
                        0x04 => '4',
                        0x05 => '5',
                        0x06 => '6',
                        0x07 => '7',
                        0x08 => '8',
                        0x09 => '9',
                        0x0A => 'A',
                        0x0B => 'B',
                        0x0C => 'C',
                        0x0D => 'D',
                        0x0E => 'E',
                        0x0F => 'F',
                        _ => unreachable!(),
                    }
                }
                f.write_char(nibble_to_char(byte / 0x10))?;
                f.write_char(nibble_to_char(byte % 0x10))
            }

            bytes.chunks(width).enumerate().try_for_each(|(idx, line)| {
                f.write_str(prefix)?;

                (0..width)
                    .map(|i| line.get(i).unwrap_or(&0x20))
                    .try_for_each(|c| {
                        if matches!(c, 0x20..0x7F) {
                            f.write_char(*c as char)
                        } else {
                            f.write_char('.')
                        }
                    })?;
                f.write_str("    ")?;

                (idx * width)
                    .to_be_bytes()
                    .last_chunk::<4>()
                    .unwrap()
                    .iter()
                    .try_for_each(|b| write_byte(*b, f))?;

                line.iter().try_for_each(|b| {
                    f.write_char(' ')?;
                    write_byte(*b, f)
                })?;
                f.write_char('\n')
            })
        }
        match self {
            Value::Bytes(eval_slice) => {
                write!(f, "{prefix}[\n")?;
                let len = prefix.len();
                prefix.push_str("    ");
                write_hexdump_width(eval_slice, f, prefix, 16)?;
                prefix.truncate(len);
                write!(f, "{prefix}]\n")?;
            }
            Value::Aggregate(eval_slice) => {
                write!(f, "{prefix}(\n")?;
                let len = prefix.len();
                prefix.push_str("    ");
                eval_slice
                    .iter()
                    .try_for_each(|value| value.prefix_fmt(f, prefix))?;
                prefix.truncate(len);
                write!(f, "{prefix})\n")?;
            }
        }
        Ok(())
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.prefix_fmt(f, &mut String::new())
    }
}

// TODO: bytecode builtin
pub const BUILTIN: Value = Value::slice_const(&[]);

pub fn eval_builtin(atom: Atom) -> Value {
    eval(BUILTIN, atom_to_val(atom))
}

fn atom_to_val(atom: Atom) -> Value {
    match atom {
        Atom::Unit => Value::slice(const { &[Value::byte_slice_const(b"unit")] }),
        Atom::Apply(apply) => {
            let Apply { lhs, rhs } = *apply;
            let (e0, [e1, e2]) = (Value::byte_slice("apply"), [lhs, rhs].map(atom_to_val));
            Value::slice_move([e0, e1, e2])
        }
        Atom::Identifier(s) => Value::slice_move([
            Value::byte_slice("identifier"),
            Value::byte_slice_move(s.into_boxed_bytes()),
        ]),
        Atom::String(s) => Value::slice_move([
            Value::byte_slice("string"),
            Value::byte_slice_move(s.into_boxed_bytes()),
        ]),
    }
}

// expression: ((builtin_func_ident | expression) expression) | builtin_value_ident | value
// *ident: ("ident" <name>)
// value: ("value" <value>)
fn eval(expression: Value, input: Value) -> Value {
    Value::slice_move([expression, input])
}
