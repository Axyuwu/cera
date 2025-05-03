use std::fmt::Write;
use std::ops::ControlFlow;
use std::sync::Arc;
use std::{fmt::Display, hash::Hash};

use anyhow::{anyhow, bail, Context, Result};

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
    fn as_aggregate(self) -> Result<EvalSlice<Value>> {
        let Self::Aggregate(s) = self else {
            bail!("expected aggregate, found bytes:\n{}", self)
        };
        Ok(s)
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
    fn as_bytes(self) -> Result<EvalSlice<u8>> {
        let Self::Bytes(s) = self else {
            bail!("expected bytes, found aggregate:\n{}", self)
        };
        Ok(s)
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

                (idx * width)
                    .to_be_bytes()
                    .last_chunk::<4>()
                    .unwrap()
                    .iter()
                    .try_for_each(|b| write_byte(*b, f))?;
                f.write_char(':')?;

                (0..width)
                    .map(|i| (i, line.get(i)))
                    .try_for_each(|(i, b)| {
                        if i % 2 == 0 {
                            f.write_char(' ')?;
                        }
                        let Some(b) = b else {
                            return f.write_str("  ");
                        };
                        if matches!(b, 0x20..0x7F) {
                            f.write_str("\x01\x1B[0;32m\x02")?;
                        } else {
                            f.write_str("\x01\x1B[0;30m\x02")?;
                        }
                        write_byte(*b, f)
                    })?;

                f.write_str("  ")?;

                (0..width)
                    .map(|i| line.get(i).unwrap_or(&0x20))
                    .try_for_each(|b| {
                        if matches!(b, 0x20..0x7F) {
                            f.write_str("\x01\x1B[0;32m\x02")?;
                            f.write_char(*b as char)
                        } else {
                            f.write_str("\x01\x1B[0;30m\x02")?;
                            f.write_char('.')
                        }
                    })?;

                f.write_char('\n')?;
                f.write_str("\x01\x1B[0m\x02")
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

// TODO: make builtin transform allow for a minimal representation that can emit values which can
// be evaluated using eval, such that the user may create the remaining of the compiler
pub const BUILTIN_EVAL_FUNC: Value = Value::slice_const(const { &[] });

pub fn eval_builtin(atom: Atom) -> Result<Value> {
    todo!();
    eval(Value::slice_move([BUILTIN_EVAL_FUNC, atom_to_val(atom)]))
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

// expression: (func_ident value)
fn eval(expression: Value) -> Result<Value> {
    let mut thunk = BuiltinThunk::new(expression);
    loop {
        match thunk.call()? {
            ControlFlow::Continue(t) => thunk = t,
            ControlFlow::Break(b) => break Ok(b),
        }
    }
}

struct BuiltinThunk {
    state: BuiltinThunkState,
    value: Value,
}

impl BuiltinThunk {
    fn new(expression: Value) -> Self {
        Self {
            state: BuiltinThunkState {
                callback: None,
                func: BuiltinFunc::BuiltinEval,
            },
            value: expression,
        }
    }
    fn call(self) -> Result<ControlFlow<Value, Self>> {
        let Self { state, value } = self;
        use ControlFlow::*;
        use FuncThunk::*;
        let BuiltinThunkState { callback, func } = state;
        Ok(match (func.poll(value)?, callback) {
            (
                Pending {
                    pending_func,
                    new_func,
                    value,
                },
                callback,
            ) => Continue(Self {
                state: BuiltinThunkState {
                    callback: Some(Box::new(BuiltinThunkState {
                        callback,
                        func: pending_func,
                    })),
                    func: new_func,
                },
                value,
            }),
            (Step { func, value }, callback) => Continue(Self {
                state: BuiltinThunkState { callback, func },
                value,
            }),
            (Done { value }, Some(callback)) => Continue(Self {
                state: *callback,
                value,
            }),
            (Done { value }, None) => Break(value),
        })
    }
}

struct BuiltinThunkState {
    callback: Option<Box<BuiltinThunkState>>,
    func: BuiltinFunc,
}

enum FuncThunk {
    Pending {
        pending_func: BuiltinFunc,
        new_func: BuiltinFunc,
        value: Value,
    },
    Step {
        func: BuiltinFunc,
        value: Value,
    },
    Done {
        value: Value,
    },
}

enum BuiltinFunc {
    BuiltinEval,
    SetMove,
    SetLen,
    SetMkLen,
    SetMap(SetMap),
    SetNest,
    Add,
}

impl BuiltinFunc {
    fn poll(self, value: Value) -> Result<FuncThunk> {
        use FuncThunk::*;
        Ok(match self {
            Self::BuiltinEval => {
                let [ident, value] = get_args(value)?;
                Step {
                    func: BuiltinFunc::from_value(&ident)?,
                    value,
                }
            }
            BuiltinFunc::SetMove => {
                let [set, args] = get_args(value)?;
                let [src, dst] = {
                    let [src, dst] = get_args(args)?.map(|e| get_usize(&e));
                    [src?, dst?]
                };
                let mut set = set.as_aggregate()?;
                let slice = set.make_mut();

                let Some(src) = slice.get(src).map(Clone::clone) else {
                    bail!(
                        "src index {src} out of bound of value:\n{}",
                        Value::slice_cloned(slice)
                    )
                };
                let Some(dst) = slice.get_mut(dst) else {
                    bail!(
                        "dst index {dst} out of bound of value\n{}",
                        Value::slice_cloned(slice)
                    )
                };
                *dst = src;

                Done {
                    value: Value::Aggregate(set),
                }
            }
            BuiltinFunc::SetLen => Done {
                value: Value::byte_slice_move(value.as_aggregate()?.len().to_le_bytes()),
            },
            BuiltinFunc::SetMkLen => Done {
                value: {
                    let [set, len] = get_args(value)?;
                    let set = set.as_aggregate()?;
                    let len = get_usize(&len)?;
                    if set.len() == len {
                        Value::Aggregate(set)
                    } else {
                        Value::slice_move(
                            (0..len)
                                .map(|i| {
                                    set.get(i)
                                        .unwrap_or(&const { Value::slice_const(&[]) })
                                        .clone()
                                })
                                .collect::<Box<_>>(),
                        )
                    }
                },
            },
            BuiltinFunc::SetMap(SetMap::Init) => {
                let [set, idx, func] = get_args(value)?;

                let idx = get_usize(&idx)?;
                let mut set = set.as_aggregate()?;
                let slice = set.make_mut();

                let Some(elem) = slice.get_mut(idx) else {
                    bail!(
                        "index {idx} out of bound of value\n{}",
                        Value::slice_cloned(slice)
                    )
                };

                Pending {
                    value: std::mem::replace(elem, Value::slice_const(&[])),
                    pending_func: Self::SetMap(SetMap::Pending { set, idx }),
                    new_func: Self::from_value(&func)?,
                }
            }
            BuiltinFunc::SetMap(SetMap::Pending { mut set, idx }) => {
                let slice = set.make_mut();
                let Some(elem) = slice.get_mut(idx) else {
                    bail!(
                        "index {idx} out of bound of value\n{}",
                        Value::slice_cloned(slice)
                    )
                };
                *elem = value;
                Done {
                    value: Value::Aggregate(set),
                }
            }
            BuiltinFunc::SetNest => Done {
                value: Value::slice_move([value]),
            },
            Self::Add => Done {
                value: {
                    let args = get_args(value)?;
                    let args = {
                        let [a1, a2] = args.each_ref().map(|e| get_bytes(&e));
                        [a1?, a2?]
                    };
                    let mut acc = Vec::new();
                    let mut idx = 0;
                    let mut carry = false;
                    while !args.into_iter().all(<[_]>::is_empty) {
                        let [lhs, rhs] = args.map(|s| s.get(idx).cloned().unwrap_or_default());
                        let (lhs, c1) = lhs.overflowing_add(rhs);
                        let (lhs, c2) = lhs.overflowing_add(carry as u8);
                        carry = c1 || c2 as bool;
                        acc.push(lhs);
                        idx += 1;
                    }
                    carry.then(|| acc.push(1));
                    Value::byte_slice_move(acc)
                },
            },
        })
    }
    fn from_value(value: &Value) -> Result<Self> {
        Ok(match get_bytes(value)? {
            b"builtin_eval" => Self::BuiltinEval,
            b"set_move" => Self::SetMove,
            b"set_len" => Self::SetLen,
            b"set_mklen" => Self::SetMkLen,
            b"set_map" => Self::SetMap(SetMap::Init),
            b"set_nest" => Self::SetNest,
            b"add" => Self::Add,
            _ => bail!(
                "tried making builtin func from value without that value being valid bytes:\n{}",
                value
            ),
        })
    }
}

enum SetMap {
    Init,
    Pending { set: EvalSlice<Value>, idx: usize },
}

fn get_args<const SIZE: usize>(value: Value) -> Result<[Value; SIZE]> {
    let Value::Aggregate(slice) = &value else {
        bail!(
            "expected aggregate value with {SIZE} elements, found bytes:\n{}",
            value
        );
    };
    TryInto::<&[Value; SIZE]>::try_into(&**slice)
        .map(Clone::clone)
        .with_context(|| {
            format!(
                "expected aggregate value with {SIZE} elements, found {}:\n{}",
                slice.len(),
                value
            )
        })
}

fn get_bytes(value: &Value) -> Result<&[u8]> {
    let Value::Bytes(b) = value else {
        bail!(
            "expected value to be byte string, found aggregate:\n{}",
            value
        );
    };
    Ok(&**b)
}

fn get_usize(value: &Value) -> Result<usize> {
    get_bytes(value)?
        .iter()
        .rev()
        .try_fold(0usize, |acc, byte| {
            acc.checked_mul(u8::MAX as usize)?
                .checked_add(*byte as usize)
        })
        .ok_or_else(|| {
            anyhow!(
                "overflowed trying to get a usize from byte string:\n{}",
                value
            )
        })
}
