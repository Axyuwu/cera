mod arithemtic;
pub mod builtin_values;
mod world;

use std::convert::Infallible;
use std::fmt::Debug;
use std::fmt::Display;
use std::fmt::Write;
use std::ops::ControlFlow;
use std::ops::Deref;
use std::sync::Arc;

use anyhow::{anyhow, bail, ensure, Context, Result};
use arithemtic::trim_zeros;
use arithemtic::Arithmetic;
use builtin_values::BuiltinImport;
use builtin_values::FALSE;
use builtin_values::TRUE;
use world::World;
use world::WorldIo;

use crate::parse::Atom;

pub trait SliceStorage<T>: Sized {
    fn get(&self) -> &[T];
    fn get_mut(&mut self) -> &mut [T];
    fn try_new(slice: &[T]) -> Option<Self>;
    fn eq(&self, rhs: &[T]) -> bool;
}

#[derive(Debug, Clone)]
pub struct U8SliceStorage {
    len: u8,
    storage: [u8; 22],
}

impl SliceStorage<u8> for U8SliceStorage {
    fn get(&self) -> &[u8] {
        &self.storage[..(self.len as usize)]
    }

    fn get_mut(&mut self) -> &mut [u8] {
        &mut self.storage[..(self.len as usize)]
    }

    fn try_new(slice: &[u8]) -> Option<Self> {
        if slice.len() > 22 {
            None
        } else {
            let mut storage = [0; 22];
            storage[0..(slice.len())].copy_from_slice(slice);
            Some(Self {
                len: slice.len() as u8,
                storage,
            })
        }
    }

    fn eq(&self, rhs: &[u8]) -> bool {
        self.get() == rhs
    }
}
impl<T> SliceStorage<T> for Infallible {
    fn get(&self) -> &[T] {
        unreachable!()
    }

    fn get_mut(&mut self) -> &mut [T] {
        unreachable!()
    }

    fn try_new(_slice: &[T]) -> Option<Self> {
        unreachable!()
    }

    fn eq(&self, _rhs: &[T]) -> bool {
        unreachable!()
    }
}

pub trait HasSliceStorage: Sized {
    type Storage: SliceStorage<Self>;
}

impl HasSliceStorage for Value {
    type Storage = Infallible;
}
impl HasSliceStorage for u8 {
    type Storage = U8SliceStorage;
}

#[repr(u8)]
#[derive(Debug, Clone)]
pub enum EvalSlice<T: 'static + HasSliceStorage> {
    Arc(Arc<[T]>),
    Borrowed(&'static [T]),
    Inline(T::Storage),
}

impl<T: HasSliceStorage> Deref for EvalSlice<T> {
    type Target = [T];
    fn deref(&self) -> &[T] {
        match self {
            EvalSlice::Arc(items) => items.as_ref(),
            EvalSlice::Borrowed(items) => items.as_ref(),
            EvalSlice::Inline(items) => items.get(),
        }
    }
}

impl<T: HasSliceStorage> EvalSlice<T> {
    fn get_mut(&mut self) -> Option<&mut [T]> {
        match self {
            EvalSlice::Arc(items) => Arc::get_mut(items),
            EvalSlice::Borrowed(_) => None,
            EvalSlice::Inline(items) => Some(items.get_mut()),
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
            EvalSlice::Inline(items) => items.get_mut(),
        }
    }
    fn addr_eq(&self, rhs: &Self) -> bool {
        match (self, rhs) {
            (Self::Inline(lhs), rhs) => lhs.eq(&*rhs),
            (Self::Borrowed(lhs), Self::Borrowed(rhs)) => std::ptr::eq(lhs, rhs),
            (Self::Arc(lhs), Self::Arc(rhs)) => std::ptr::eq(&*lhs, &*rhs),
            _ => false,
        }
    }
}

#[derive(Clone)]
pub enum Value {
    Bytes(EvalSlice<u8>),
    Aggregate(EvalSlice<Value>),
}

impl Debug for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        <Self as Display>::fmt(&self, f)
    }
}

impl Value {
    pub const fn unit() -> Self {
        Self::aggregate_const(&[])
    }
    pub fn is_unit(&self) -> bool {
        match self {
            Self::Aggregate(slice) if slice.len() == 0 => true,
            _ => false,
        }
    }
    pub const fn aggregate_const(slice: &'static [Self]) -> Self {
        Self::Aggregate(EvalSlice::Borrowed(slice))
    }
    pub fn aggregate(slice: &'static (impl AsRef<[Self]> + ?Sized)) -> Self {
        Self::aggregate_const(slice.as_ref())
    }
    pub fn aggregate_cloned(slice: impl AsRef<[Self]>) -> Self {
        Self::Aggregate(EvalSlice::Arc(slice.as_ref().into()))
    }
    pub fn aggregate_move(slice: impl Into<Arc<[Self]>>) -> Self {
        Self::Aggregate(EvalSlice::Arc(slice.into()))
    }
    pub fn into_aggregate(self) -> Result<EvalSlice<Value>> {
        let Self::Aggregate(s) = self else {
            bail!("expected aggregate, found bytes:\n{}", self)
        };
        Ok(s)
    }
    pub fn as_aggregate(&self) -> Result<&EvalSlice<Value>> {
        let Self::Aggregate(s) = self else {
            bail!("expected aggregate, found bytes:\n{}", self)
        };
        Ok(s)
    }
    pub fn as_aggregate_mut(&mut self) -> Result<&mut EvalSlice<Value>> {
        let Self::Aggregate(s) = self else {
            bail!("expected aggregate, found bytes:\n{}", self)
        };
        Ok(s)
    }
    pub const fn bytes_const(slice: &'static [u8]) -> Self {
        Self::Bytes(EvalSlice::Borrowed(slice))
    }
    pub fn bytes(slice: &'static (impl AsRef<[u8]> + ?Sized)) -> Self {
        let bytes = slice.as_ref();
        if let Some(slice) = U8SliceStorage::try_new(bytes) {
            Self::Bytes(EvalSlice::Inline(slice))
        } else {
            Self::Bytes(EvalSlice::Borrowed(bytes))
        }
    }
    pub fn bytes_cloned(slice: impl AsRef<[u8]>) -> Self {
        let bytes = slice.as_ref();
        if let Some(slice) = U8SliceStorage::try_new(bytes) {
            Self::Bytes(EvalSlice::Inline(slice))
        } else {
            Self::Bytes(EvalSlice::Arc(bytes.into()))
        }
    }
    pub fn bytes_move(slice: impl Into<Arc<[u8]>> + AsRef<[u8]>) -> Self {
        if let Some(slice) = U8SliceStorage::try_new(slice.as_ref()) {
            Self::Bytes(EvalSlice::Inline(slice))
        } else {
            Self::Bytes(EvalSlice::Arc(slice.into()))
        }
    }
    pub fn into_bytes(self) -> Result<EvalSlice<u8>> {
        let Self::Bytes(s) = self else {
            bail!("expected bytes, found aggregate:\n{}", self)
        };
        Ok(s)
    }
    pub fn as_bytes(&self) -> Result<&EvalSlice<u8>> {
        let Self::Bytes(s) = self else {
            bail!("expected bytes, found aggregate:\n{}", self)
        };
        Ok(s)
    }
    pub fn as_bytes_mut(&mut self) -> Result<&mut EvalSlice<u8>> {
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
    pub fn from_res<I1, I2, F1, F2>(res: std::result::Result<I1, I2>, f1: F1, f2: F2) -> Value
    where
        F1: FnOnce(I1) -> Value,
        F2: FnOnce(I2) -> Value,
    {
        match res {
            Ok(i1) => Value::aggregate_move([Value::bytes_const(b"ok"), f1(i1)]),
            Err(i2) => Value::aggregate_move([Value::bytes_const(b"err"), f2(i2)]),
        }
    }
    pub fn addr_eq(&self, rhs: &Self) -> bool {
        match (self, rhs) {
            (Self::Bytes(lhs), Self::Bytes(rhs)) => lhs.addr_eq(rhs),
            (Self::Aggregate(lhs), Self::Aggregate(rhs)) => lhs.addr_eq(rhs),
            _ => false,
        }
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.prefix_fmt(f, &mut String::new())
    }
}

pub fn eval_builtin(atom: Atom) -> Result<Value> {
    let (world, world_handle) = World::new();
    eval(
        Value::aggregate_move([
            Value::bytes("call"),
            Value::aggregate_move([builtin_values::BUILTIN_EVAL_FUNC, atom_to_val(atom)]),
        ]),
        world,
    )
}

fn atom_to_val(atom: Atom) -> Value {
    match atom {
        Atom::Aggr(aggr) => Value::aggregate_move([
            Value::bytes("aggregate"),
            Value::aggregate_move(
                <Box<[_]> as IntoIterator>::into_iter(aggr)
                    .map(atom_to_val)
                    .collect::<Arc<_>>(),
            ),
        ]),
        Atom::Identifier(s) => Value::aggregate_move([
            Value::bytes("identifier"),
            Value::bytes_move(s.into_boxed_bytes()),
        ]),
        Atom::Bytes(s) => Value::aggregate_move([Value::bytes("string"), Value::bytes_move(s)]),
    }
}

pub fn eval(expression: Value, mut world: World) -> Result<Value> {
    let mut thunk = BuiltinThunk::new(expression, 100);
    loop {
        match thunk
            .call(&mut world)
            .with_context(|| format!("world state: {world:?}"))?
        {
            ControlFlow::Continue(t) => thunk = t,
            ControlFlow::Break(b) => break Ok(b),
        }
    }
}

#[derive(Debug)]
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
    fn call(self, world: &mut World) -> Result<ControlFlow<Value, Self>> {
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
        Ok(match (func.poll(value, world)?, callback) {
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
                        ensure!(
                            depth <= max_depth,
                            "max depth {max_depth} exceeded: {depth}",
                        );

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

#[derive(Debug)]
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

#[derive(Debug)]
enum BuiltinFunc {
    BuiltinEval,
    Let(Let),
    LetArgEval(LetArgEval),
    Call,
    If,
    BytesEq,
    Identity,
    AggrGet,
    AggrSet,
    AggrLen,
    AggrMake,
    Arithmetic(Arithmetic),
    WorldIo(WorldIo),
    BuiltinImport(BuiltinImport),
}

impl BuiltinFunc {
    fn poll(self, value: Value, world: &mut World) -> Result<FuncThunk> {
        use FuncThunk::*;
        Ok(match self {
            Self::BuiltinEval => {
                let [ident, value] = get_args(value).context("in builtin_eval")?;
                Step {
                    func: BuiltinFunc::from_value(&ident).context("in builtin_eval")?,
                    value,
                }
            }
            Self::Let(Let::Init { arg }) => {
                let [constants, expressions] = {
                    let [a1, a2] = get_args(value.clone())
                        .context("in let init binding")?
                        .map(|a| a.into_aggregate());
                    [a1?, a2?]
                };
                ensure!(
                    !expressions.is_empty(),
                    "no expression in let binding:\n{}",
                    Value::aggregate_move([
                        Value::Aggregate(constants),
                        Value::Aggregate(expressions)
                    ])
                );

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

                    state[idx..]
                        .iter_mut()
                        .enumerate()
                        .rev()
                        .try_for_each(|(i, elem)| -> Result<_> {
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

                                    ensure!(
                                        liveness_idx <= i,
                                        "index {real_idx} out of bound of bindings in function"
                                    );

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

                            *elem = Value::aggregate_move([
                                func,
                                args,
                                Value::aggregate_move(
                                    drops.into_iter().map(usize_to_val).collect::<Arc<_>>(),
                                ),
                            ]);
                            Ok(())
                        })
                        .context("while parsing step for let init")?;
                }
                Pending {
                    value: Value::unit(),
                    pending_func: Self::Let(Let::PendingArgEval { idx }),
                    new_func: Self::LetArgEval(LetArgEval::Init {
                        state: {
                            let tmp = Value::aggregate_move(state);
                            tmp
                        },
                        idx,
                    }),
                }
            }
            Self::Let(Let::PendingArgEval { idx }) => {
                let [state, value] =
                    get_args(value).context("while parsing arg eval in let binding")?;

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
                        .as_aggregate()
                        .context("while processing drops for let binding")?
                        .get(idx)
                        .ok_or_else(|| anyhow!("index {idx} out of bound of state:\n{state}"))?
                        .clone(),
                )
                .context("while processing drops for let builtin")?;

                {
                    let state = state.as_aggregate_mut()?.make_mut();
                    drops
                        .as_aggregate()?
                        .iter()
                        .try_for_each(|drop| -> Result<_> {
                            let Some(out) = state.get_mut(get_usize(drop.as_bytes()?)?) else {
                                bail!(
                                    "drop index {drop} out of bound of state:\n{}",
                                    Value::aggregate_cloned(&state)
                                )
                            };
                            *out = Value::unit();
                            Ok(())
                        })
                        .context("while processing drops for let builtin")?;
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
                    value: Value::aggregate(&[]),
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
                value: Value::aggregate_move([state, Value::aggregate_move([func, value])]),
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
                let [func, arg] = get_args(value).context("while getting args for call builtin")?;
                Step {
                    func: Self::Let(Let::Init { arg: Some(arg) }),
                    value: func,
                }
            }
            Self::If => {
                let [cond, ifthen, ifelse] =
                    get_args(value).context("while getting args to if builtin")?;
                Step {
                    func: Self::BuiltinEval,
                    value: match trim_zeros(
                        &**cond
                            .as_bytes()
                            .context("while processing condition for if builtin")?,
                    ) {
                        &[1] => ifthen,
                        &[] => ifelse,
                        _ => bail!("non zero or one value given to if:\n{cond}"),
                    },
                }
            }
            Self::BytesEq => Done {
                value: {
                    let [lhs, rhs] = get_args(value)?.map(Value::into_bytes);

                    match *lhs? == *rhs? {
                        true => TRUE,
                        false => FALSE,
                    }
                },
            },
            Self::Identity => Done { value },
            Self::AggrGet => Done {
                value: {
                    let [value, idx] =
                        get_args(value).context("while getting args for aggrget builtin")?;
                    let idx = get_usize(idx.as_bytes()?)?;
                    let aggr = value.as_aggregate()?;
                    aggr.get(idx)
                        .ok_or_else(|| anyhow!("index {idx} out of bounds of aggregate:\n{value}"))?
                        .clone()
                },
            },
            Self::AggrSet => Done {
                value: {
                    let [mut value, idx, src] =
                        get_args(value).context("while getting args for aggrget builtin")?;
                    let idx = get_usize(idx.as_bytes()?)?;
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
                value: Value::aggregate_move(
                    std::iter::repeat(Value::unit())
                        .take(get_usize(value.as_bytes()?)?)
                        .collect::<Box<_>>(),
                ),
            },
            Self::Arithmetic(arithmetic) => Done {
                value: arithmetic
                    .poll(value)
                    .context("while evaluating arithmetic builtin")?,
            },
            Self::WorldIo(world_io) => Done {
                value: world_io
                    .poll(value, world)
                    .context("while evaluating worldio builtin")?,
            },
            Self::BuiltinImport(builtin_import) => Done {
                value: builtin_import
                    .poll(value)
                    .context("while evaluating builtin_import builtin")?,
            },
        })
    }
    fn from_value(value: &Value) -> Result<Self> {
        Ok(match &**value.as_bytes()? {
            b"builtin_eval" => Self::BuiltinEval,
            b"let" => Self::Let(Let::Init { arg: None }),
            b"call" => Self::Call,
            b"if" => Self::If,
            b"bytes_eq" => Self::BytesEq,
            b"identity" => Self::Identity,
            b"aggr_get" => Self::AggrGet,
            b"aggr_set" => Self::AggrSet,
            b"aggr_len" => Self::AggrLen,
            b"aggr_make" => Self::AggrMake,
            s => {
                if let Some(a) = Arithmetic::from_ident(s) {
                    Self::Arithmetic(a)
                } else if let Some(w) = WorldIo::from_ident(s) {
                    Self::WorldIo(w)
                } else if let Some(b) = BuiltinImport::from_ident(s) {
                    Self::BuiltinImport(b)
                } else {
                    bail!("invalid builtin function name:\n{value}")
                }
            }
        })
    }
}

#[derive(Debug)]
enum Let {
    Init { arg: Option<Value> },
    PendingArgEval { idx: usize },
    Drops { idx: usize, arg: Value },
    PendingEval { state: Value, idx: usize },
}

#[derive(Debug)]
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

pub fn get_args<const SIZE: usize>(value: Value) -> Result<[Value; SIZE]> {
    let slice = value.as_aggregate().context("while getting args")?;
    TryInto::<&[Value; SIZE]>::try_into(&**slice)
        .map(Clone::clone)
        .with_context(|| {
            format!(
                "expected aggregate with {SIZE} elements, found {}:\n{value}",
                slice.len(),
            )
        })
}

// Little endian

pub fn get_usize(bytes: &[u8]) -> Result<usize> {
    bytes
        .iter()
        .rev()
        .try_fold(0usize, |acc, byte| {
            acc.checked_mul(u8::MAX as usize)?
                .checked_add(*byte as usize)
        })
        .ok_or_else(|| {
            anyhow!(
                "overflowed trying to get a usize from bytes:\n{}",
                Value::bytes_cloned(bytes)
            )
        })
}

pub fn usize_to_val(usize: usize) -> Value {
    let bytes = usize.to_le_bytes();
    let idx = bytes
        .iter()
        .enumerate()
        .rev()
        .find(|(_, v)| **v != 0)
        .map(|(i, _)| i + 1)
        .unwrap_or(0);
    Value::bytes_cloned(&bytes[0..idx])
}

pub fn get_u128(bytes: &[u8]) -> Result<u128> {
    bytes
        .iter()
        .rev()
        .try_fold(0u128, |acc, byte| {
            acc.checked_mul(u8::MAX as u128)?.checked_add(*byte as u128)
        })
        .ok_or_else(|| {
            anyhow!(
                "overflowed trying to get a usize from bytes:\n{}",
                Value::bytes_cloned(bytes)
            )
        })
}
