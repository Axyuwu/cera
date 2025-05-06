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
    const fn unit() -> Self {
        Self::slice_const(&[])
    }
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
    fn into_aggregate(self) -> Result<EvalSlice<Value>> {
        let Self::Aggregate(s) = self else {
            bail!("expected aggregate, found bytes:\n{}", self)
        };
        Ok(s)
    }
    fn as_aggregate(&self) -> Result<&EvalSlice<Value>> {
        let Self::Aggregate(s) = self else {
            bail!("expected aggregate, found bytes:\n{}", self)
        };
        Ok(s)
    }
    fn as_aggregate_mut(&mut self) -> Result<&mut EvalSlice<Value>> {
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
    fn into_bytes(self) -> Result<EvalSlice<u8>> {
        let Self::Bytes(s) = self else {
            bail!("expected bytes, found aggregate:\n{}", self)
        };
        Ok(s)
    }
    fn as_bytes(&self) -> Result<&EvalSlice<u8>> {
        let Self::Bytes(s) = self else {
            bail!("expected bytes, found aggregate:\n{}", self)
        };
        Ok(s)
    }
    fn as_bytes_mut(&mut self) -> Result<&mut EvalSlice<u8>> {
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
pub const BUILTIN_EVAL_FUNC: Value = Value::slice_const(
    const {
        &[
            Value::slice_const(
                const {
                    &[
                        Value::byte_slice_const(&[128, 4, 8]),
                        Value::byte_slice_const(&[200, 2, 7]),
                    ]
                },
            ),
            Value::slice_const(
                const {
                    &[
                        Value::slice_const(
                            const {
                                &[
                                    Value::byte_slice_const(b"add"),
                                    Value::slice_const(
                                        const {
                                            &[
                                                Value::byte_slice_const(&[1]),
                                                Value::byte_slice_const(&[2]),
                                            ]
                                        },
                                    ),
                                ]
                            },
                        ),
                        Value::slice_const(
                            const {
                                &[
                                    Value::byte_slice_const(b"identity"),
                                    Value::slice_const(
                                        const {
                                            &[
                                                Value::byte_slice_const(&[0]),
                                                Value::byte_slice_const(&[1]),
                                                Value::byte_slice_const(&[2]),
                                                Value::byte_slice_const(&[3]),
                                                Value::byte_slice_const(&[4]),
                                            ]
                                        },
                                    ),
                                ]
                            },
                        ),
                    ]
                },
            ),
        ]
    },
);

pub fn eval_builtin(atom: Atom) -> Result<Value> {
    eval(Value::slice_move([
        Value::byte_slice("call"),
        Value::slice_move([BUILTIN_EVAL_FUNC, atom_to_val(atom)]),
    ]))
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

fn eval(expression: Value) -> Result<Value> {
    let mut thunk = BuiltinThunk::new(expression, 100);
    loop {
        match thunk.call()? {
            ControlFlow::Continue(t) => thunk = t,
            ControlFlow::Break(b) => break Ok(b),
        }
    }
}

struct BuiltinThunk {
    state: BuiltinThunkState,
    max_depth: usize,
    value: Value,
}

impl BuiltinThunk {
    fn new(expression: Value, max_depth: usize) -> Self {
        Self {
            state: BuiltinThunkState {
                callback: None,
                depth: 0,
                func: BuiltinFunc::BuiltinEval,
            },
            max_depth,
            value: expression,
        }
    }
    fn call(self) -> Result<ControlFlow<Value, Self>> {
        let Self {
            state,
            max_depth,
            value,
        } = self;
        use ControlFlow::*;
        use FuncThunk::*;
        let BuiltinThunkState {
            callback,
            depth,
            func,
        } = state;
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
                        depth,
                        func: pending_func,
                    })),
                    depth: {
                        let depth = depth + 1;
                        if depth > max_depth {
                            bail!("max depth {max_depth} exceeded: {depth}");
                        }
                        depth
                    },
                    func: new_func,
                },
                max_depth,
                value,
            }),
            (Step { func, value }, callback) => Continue(Self {
                state: BuiltinThunkState {
                    callback,
                    depth,
                    func,
                },
                max_depth,
                value,
            }),
            (Done { value }, Some(callback)) => Continue(Self {
                state: *callback,
                max_depth,
                value,
            }),
            (Done { value }, None) => Break(value),
        })
    }
}

struct BuiltinThunkState {
    callback: Option<Box<BuiltinThunkState>>,
    depth: usize,
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
    Let(Let),
    LetArgEval(LetArgEval),
    Call,
    Identity,
    AggrGet,
    AggrSet,
    AggrLen,
    AggrMake,
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
            Self::Let(Let::Init { arg }) => {
                let [constants, expressions] = {
                    let [a1, a2] = get_args(value.clone())?.map(|a| a.into_aggregate());
                    [a1?, a2?]
                };
                if expressions.is_empty() {
                    bail!(
                        "no expression in let binding:\n{}",
                        Value::slice_move([
                            Value::Aggregate(constants),
                            Value::Aggregate(expressions)
                        ])
                    )
                }
                // (self, constant1, constant2, constant3, arg?, expression1, expression2, expression3)
                // where each step, the leftmost expression gets evaluated and turned into a
                // constant
                let mut state = std::iter::once(value)
                    .chain(constants.iter().map(Clone::clone))
                    .chain(arg)
                    .chain(expressions.iter().map(Clone::clone))
                    .collect::<Arc<_>>();
                let idx = state.len() - expressions.len();

                {
                    fn flatten(val: &Value) -> impl Iterator<Item = &[u8]> {
                        struct Iter<'t>(Vec<&'t Value>);
                        impl<'t> Iterator for Iter<'t> {
                            type Item = &'t [u8];
                            fn next(&mut self) -> Option<Self::Item> {
                                loop {
                                    match self.0.pop()? {
                                        Value::Bytes(b) => break Some(b.as_ref()),
                                        Value::Aggregate(elems) => {
                                            elems.iter().for_each(|e| self.0.push(e))
                                        }
                                    }
                                }
                            }
                        }
                        Iter(vec![val])
                    }

                    let state = Arc::make_mut(&mut state);
                    let mut liveness = std::iter::repeat(false)
                        .take(state.len() - constants.len() - 2)
                        .collect::<Box<_>>();

                    state[idx..].iter_mut().enumerate().rev().try_for_each(
                        |(i, elem)| -> Result<_> {
                            let [func, args] = get_args(std::mem::replace(elem, Value::unit()))?;

                            let mut drops = Vec::new();

                            flatten(&args)
                                .map(get_usize)
                                .map(|i| i.map(|i| (i, i.checked_sub(constants.len() + 1))))
                                .chain(std::iter::once(Ok((i + idx - 1, Some(i)))))
                                .try_for_each(|idx_res| -> Result<_> {
                                    let (real_idx, Some(liveness_idx)) = idx_res? else {
                                        return Ok(());
                                    };

                                    if liveness_idx > i {
                                        bail!(
                                            "index {real_idx} out of bound of bindings in function"
                                        );
                                    }

                                    let liveness = &mut liveness[liveness_idx];
                                    if *liveness {
                                        return Ok(());
                                    }
                                    *liveness = true;
                                    drops.push(real_idx);

                                    Ok(())
                                })?;

                            drops.sort();
                            drops.dedup();

                            *elem = Value::slice_move([
                                func,
                                args,
                                Value::slice_move(
                                    drops.into_iter().map(usize_to_val).collect::<Arc<_>>(),
                                ),
                            ]);
                            Ok(())
                        },
                    )?;
                }
                Pending {
                    value: Value::unit(),
                    pending_func: Self::Let(Let::PendingArgEval { idx }),
                    new_func: Self::LetArgEval(LetArgEval::Init {
                        state: {
                            let tmp = Value::slice_move(state);
                            tmp
                        },
                        idx,
                    }),
                }
            }
            Self::Let(Let::PendingArgEval { idx }) => {
                let [state, value] = get_args(value)?;

                if idx + 1 == state.as_aggregate()?.len() {
                    // Breaks the loop, and we get tail call optimization for free!
                    Step {
                        func: Self::BuiltinEval,
                        value,
                    }
                } else {
                    Step {
                        func: Self::Let(Let::Drops { idx, arg: value }),
                        value: state,
                    }
                }
            }
            Self::Let(Let::Drops { idx, arg }) => {
                let mut state = value;
                let [_func, _args, drops] = get_args(
                    state
                        .as_aggregate()?
                        .get(idx)
                        .ok_or_else(|| anyhow!("index {idx} out of bound of state:\n{state}"))?
                        .clone(),
                )?;

                {
                    let state = state.as_aggregate_mut()?.make_mut();
                    drops
                        .as_aggregate()?
                        .iter()
                        .try_for_each(|drop| -> Result<_> {
                            let Some(out) = state.get_mut(get_usize(get_bytes(drop)?)?) else {
                                bail!(
                                    "drop index {drop} out of bound of state:\n{}",
                                    Value::slice_cloned(&state)
                                )
                            };
                            *out = Value::unit();
                            Ok(())
                        })?;
                }

                Pending {
                    pending_func: Self::Let(Let::PendingEval { state, idx }),
                    new_func: Self::BuiltinEval,
                    value: arg,
                }
            }
            Self::Let(Let::PendingEval { mut state, idx }) => {
                let state_mut = state.as_aggregate_mut()?.make_mut();
                let Some(out) = state_mut.get_mut(idx) else {
                    bail!("index {idx} out of bound of state:\n{state}")
                };
                *out = value;
                let idx = idx + 1;
                Pending {
                    value: Value::unit(),
                    pending_func: Self::Let(Let::PendingArgEval { idx }),
                    new_func: Self::LetArgEval(LetArgEval::Init { state, idx }),
                }
            }
            Self::LetArgEval(LetArgEval::Init { mut state, idx }) => {
                let state_mut = state.as_aggregate_mut()?.make_mut();
                let Some(step) = state_mut.get_mut(idx) else {
                    bail!("index {idx} out of bound of state:\n{state}")
                };

                let [func, args, _drops] =
                    TryInto::<&mut [Value; 3]>::try_into(step.as_aggregate_mut()?.make_mut())?;

                Pending {
                    value: std::mem::replace(args, Value::unit()),
                    pending_func: Self::LetArgEval(LetArgEval::Final {
                        func: func.clone(),
                        state: state.clone(),
                    }),
                    new_func: Self::LetArgEval(LetArgEval::InitInner { state }),
                }
            }
            Self::LetArgEval(LetArgEval::InitInner { state }) => match value {
                Value::Bytes(idx) => {
                    let idx = get_usize(&idx)?;
                    let Some(res) = state.as_aggregate()?.get(idx) else {
                        bail!("index {idx} out of bound of state:\n{state}")
                    };
                    Done { value: res.clone() }
                }
                Value::Aggregate(aggr) if aggr.is_empty() => Done {
                    value: Value::slice(&[]),
                },
                Value::Aggregate(aggr) => Pending {
                    value: aggr.first().unwrap().clone(),
                    pending_func: Self::LetArgEval(LetArgEval::Pending {
                        state: state.clone(),
                        current: aggr,
                        curr_idx: 0,
                    }),
                    new_func: Self::LetArgEval(LetArgEval::InitInner { state }),
                },
            },
            Self::LetArgEval(LetArgEval::Final { state, func }) => Done {
                value: Value::slice_move([state, Value::slice_move([func, value])]),
            },

            Self::LetArgEval(LetArgEval::Pending {
                state,
                mut current,
                curr_idx,
            }) => {
                let current_mut = current.make_mut();
                current_mut[curr_idx] = value;
                let curr_idx = curr_idx + 1;
                if let Some(next) = current_mut.get_mut(curr_idx) {
                    Pending {
                        value: std::mem::replace(next, Value::unit()),
                        pending_func: Self::LetArgEval(LetArgEval::Pending {
                            state: state.clone(),
                            current,
                            curr_idx,
                        }),
                        new_func: Self::LetArgEval(LetArgEval::InitInner { state }),
                    }
                } else {
                    Done {
                        value: Value::Aggregate(current),
                    }
                }
            }
            Self::Call => {
                let [func, arg] = get_args(value)?;
                Step {
                    func: Self::Let(Let::Init { arg: Some(arg) }),
                    value: func,
                }
            }
            Self::Identity => Done { value },
            Self::AggrGet => Done {
                value: {
                    let [value, idx] = get_args(value)?;
                    let idx = get_usize(get_bytes(&idx)?)?;
                    let aggr = value.as_aggregate()?;
                    aggr.get(idx)
                        .ok_or_else(|| anyhow!("index {idx} out of bounds of aggregate:\n{value}"))?
                        .clone()
                },
            },
            Self::AggrSet => Done {
                value: {
                    let [mut value, idx, src] = get_args(value)?;
                    let idx = get_usize(get_bytes(&idx)?)?;
                    let aggr = value.as_aggregate_mut()?;
                    let Some(dst) = aggr.make_mut().get_mut(idx) else {
                        bail!("index {idx} out of bounds of aggregate:\n{value}")
                    };
                    *dst = src;
                    value
                },
            },
            Self::AggrLen => Done {
                value: usize_to_val(value.into_aggregate()?.len()),
            },
            Self::AggrMake => Done {
                value: Value::slice_move(
                    std::iter::repeat(Value::slice_const(&[]))
                        .take(get_usize(get_bytes(&value)?)?)
                        .collect::<Box<_>>(),
                ),
            },
            Self::Add => Done {
                value: {
                    let args = get_args(value)?;
                    let [lhs, rhs] = {
                        let [a1, a2] = args.each_ref().map(|e| get_bytes(&e));
                        [a1?, a2?]
                    };
                    let mut acc = Vec::new();
                    let mut idx = 0;
                    let mut carry = false;
                    (0..)
                        .map(|i| [lhs.get(i), rhs.get(i)])
                        .take_while(|e| e.iter().any(Option::is_some))
                        .map(|a| a.map(Option::<&_>::cloned).map(Option::unwrap_or_default))
                        .for_each(|[lhs, rhs]| {
                            let (lhs, c1) = lhs.overflowing_add(rhs);
                            let (lhs, c2) = lhs.overflowing_add(carry as u8);
                            carry = c1 || c2 as bool;
                            acc.push(lhs);
                            idx += 1;
                        });
                    carry.then(|| acc.push(1));
                    while let Some(&0) = acc.last() {
                        acc.pop();
                    }
                    Value::byte_slice_move(acc)
                },
            },
        })
    }
    fn from_value(value: &Value) -> Result<Self> {
        Ok(match get_bytes(value)? {
            b"builtin_eval" => Self::BuiltinEval,
            b"let" => Self::Let(Let::Init { arg: None }),
            b"call" => Self::Call,
            b"identity" => Self::Identity,
            b"aggr_get" => Self::AggrGet,
            b"aggr_set" => Self::AggrSet,
            b"aggr_len" => Self::AggrLen,
            b"aggr_make" => Self::AggrMake,
            b"add" => Self::Add,
            _ => bail!("invalid builtin function name:\n{value}"),
        })
    }
}

enum Let {
    Init { arg: Option<Value> },
    PendingArgEval { idx: usize },
    Drops { idx: usize, arg: Value },
    PendingEval { state: Value, idx: usize },
}

enum LetArgEval {
    Init {
        state: Value,
        idx: usize,
    },
    InitInner {
        state: Value,
    },
    Final {
        state: Value,
        func: Value,
    },
    Pending {
        state: Value,
        current: EvalSlice<Value>,
        curr_idx: usize,
    },
}

fn get_args<const SIZE: usize>(value: Value) -> Result<[Value; SIZE]> {
    let Value::Aggregate(slice) = &value else {
        bail!("expected aggregate, found bytes:\n{value}");
    };
    TryInto::<&[Value; SIZE]>::try_into(&**slice)
        .map(Clone::clone)
        .with_context(|| {
            format!(
                "expected aggregate with {SIZE} elements, found {}:\n{value}",
                slice.len(),
            )
        })
}

fn get_bytes(value: &Value) -> Result<&[u8]> {
    let Value::Bytes(b) = value else {
        bail!("expected value to be byte string, found aggregate:\n{value}");
    };
    Ok(&**b)
}

// Little endian
fn get_usize(bytes: &[u8]) -> Result<usize> {
    bytes
        .iter()
        .rev()
        .try_fold(0usize, |acc, byte| {
            acc.checked_mul(u8::MAX as usize)?
                .checked_add(*byte as usize)
        })
        .ok_or_else(|| anyhow!("overflowed trying to get a usize from bytes:\n{bytes:?}"))
}

fn usize_to_val(usize: usize) -> Value {
    let bytes = usize.to_le_bytes();
    let idx = bytes
        .iter()
        .enumerate()
        .rev()
        .find(|(_, v)| **v != 0)
        .map(|(i, _)| i + 1)
        .unwrap_or(0);
    Value::byte_slice_cloned(&bytes[0..idx])
}
