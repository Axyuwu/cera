mod arithemtic;
pub mod builtin_values;
mod world;

use crate::utils::sync::cache_arc::CacheArc as Arc;
use crate::utils::sync::cache_lock::CacheLock;
use std::convert::Infallible;
use std::fmt::Debug;
use std::fmt::Display;
use std::fmt::Write;
use std::ops::ControlFlow;
use std::ops::Deref;

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

const U8_SLICE_STORAGE_SIZE: usize = 16;
#[derive(Debug, Clone)]
pub struct U8SliceStorage {
    len: usize,
    storage: [u8; U8_SLICE_STORAGE_SIZE],
}

impl SliceStorage<u8> for U8SliceStorage {
    fn get(&self) -> &[u8] {
        &self.storage[..(self.len as usize)]
    }

    fn get_mut(&mut self) -> &mut [u8] {
        &mut self.storage[..(self.len as usize)]
    }

    fn try_new(slice: &[u8]) -> Option<Self> {
        if slice.len() > U8_SLICE_STORAGE_SIZE {
            None
        } else {
            let mut storage = [0; U8_SLICE_STORAGE_SIZE];
            storage[0..(slice.len())].copy_from_slice(slice);
            Some(Self {
                len: slice.len(),
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
        None
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
    //type Storage = Infallible;
    type Storage = U8SliceStorage;
}

type Cache = CacheLock<CacheInner>;

#[derive(Debug, Clone)]
pub struct CacheInner {
    func: Arc<LetProcessed>,
}

#[derive(Debug, Clone)]
pub enum EvalSlice<T: 'static + HasSliceStorage> {
    Arc(Arc<[T], Cache>),
    Borrowed(&'static Cache, &'static [T]),
    Inline(T::Storage),
}

impl<T: HasSliceStorage> Deref for EvalSlice<T> {
    type Target = [T];
    fn deref(&self) -> &[T] {
        match self {
            EvalSlice::Arc(items) => items.as_ref(),
            EvalSlice::Borrowed(_, items) => items.as_ref(),
            EvalSlice::Inline(items) => items.get(),
        }
    }
}

impl<T: HasSliceStorage> EvalSlice<T> {
    fn get_mut(&mut self) -> Option<&mut [T]> {
        match self {
            EvalSlice::Arc(items) => Arc::get_mut(items),
            EvalSlice::Borrowed(_, _) => None,
            EvalSlice::Inline(items) => Some(items.get_mut()),
        }
    }
    fn make_mut(&mut self) -> &mut [T]
    where
        T: Clone,
    {
        match self {
            EvalSlice::Arc(items) => Arc::<[_], _>::make_mut(items),
            EvalSlice::Borrowed(_, items) => {
                *self = Self::Arc((*items).into());
                self.make_mut()
            }
            EvalSlice::Inline(items) => items.get_mut(),
        }
    }
    fn addr_eq(&self, rhs: &Self) -> bool {
        match (self, rhs) {
            (Self::Inline(lhs), rhs) => lhs.eq(&*rhs),
            (Self::Borrowed(_, lhs), Self::Borrowed(_, rhs)) => std::ptr::eq(lhs, rhs),
            (Self::Arc(lhs), Self::Arc(rhs)) => std::ptr::eq(&*lhs, &*rhs),
            _ => false,
        }
    }
    fn into_array<const SIZE: usize>(self) -> [T; SIZE]
    where
        T: Clone,
    {
        let s = &*self;
        assert!(s.len() == SIZE);
        match self {
            Self::Arc(inner) => Arc::unwrap_or_clone(inner.try_into().unwrap()),
            _ => TryInto::<&[T; SIZE]>::try_into(s).unwrap().clone(),
        }
    }
    fn as_array<const SIZE: usize>(&self) -> &[T; SIZE] {
        (&**self).try_into().unwrap()
    }
    #[inline]
    fn gen_cache(&mut self)
    where
        T: Clone,
    {
        match self {
            EvalSlice::Inline(storage) => {
                *self = EvalSlice::Arc(storage.get().into());
            }
            _ => (),
        }
    }
    #[inline]
    fn cache(&self) -> &Cache {
        match self {
            EvalSlice::Arc(arc) => Arc::cache(arc),
            EvalSlice::Borrowed(cache, _) => cache,
            _ => panic!(),
        }
    }
    pub const fn static_copy(&self) -> Self {
        match self {
            EvalSlice::Borrowed(cache_lock, items) => Self::Borrowed(cache_lock, items),
            _ => panic!(),
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
    pub const fn static_copy(&self) -> Self {
        match self {
            Value::Bytes(eval_slice) => Self::Bytes(eval_slice.static_copy()),
            Value::Aggregate(eval_slice) => Self::Aggregate(eval_slice.static_copy()),
        }
    }
    #[inline]
    pub fn gen_cache(&mut self) {
        match self {
            Value::Bytes(eval_slice) => eval_slice.gen_cache(),
            Value::Aggregate(eval_slice) => eval_slice.gen_cache(),
        }
    }
    #[inline]
    pub fn cache(&self) -> &Cache {
        match self {
            Value::Bytes(eval_slice) => eval_slice.cache(),
            Value::Aggregate(eval_slice) => eval_slice.cache(),
        }
    }
    pub const fn unit() -> Self {
        static CACHE: Cache = Cache::new();
        Self::aggregate_const(&CACHE, &[])
    }
    pub fn is_unit(&self) -> bool {
        match self {
            Self::Aggregate(slice) if slice.len() == 0 => true,
            _ => false,
        }
    }
    pub const fn aggregate_const(cache: &'static Cache, slice: &'static [Self]) -> Self {
        Self::Aggregate(EvalSlice::Borrowed(cache, slice))
    }
    pub fn aggregate(slice: &'static (impl AsRef<(Cache, [Self])> + ?Sized)) -> Self {
        let (cache, slice) = slice.as_ref();
        Self::aggregate_const(cache, slice)
    }
    pub fn aggregate_cloned(slice: impl AsRef<[Self]>) -> Self {
        Self::Aggregate(EvalSlice::Arc(slice.as_ref().into()))
    }
    pub fn aggregate_move(slice: impl Into<Arc<[Self], Cache>>) -> Self {
        Self::Aggregate(EvalSlice::Arc(slice.into()))
    }
    pub fn into_aggregate(self) -> EvalSlice<Value> {
        let Self::Aggregate(s) = self else {
            panic!("expected aggregate, found bytes:\n{}", self)
        };
        s
    }
    pub fn as_aggregate(&self) -> &EvalSlice<Value> {
        let Self::Aggregate(s) = self else {
            panic!("expected aggregate, found bytes:\n{}", self)
        };
        s
    }
    pub fn as_aggregate_mut(&mut self) -> &mut EvalSlice<Value> {
        let Self::Aggregate(s) = self else {
            panic!("expected aggregate, found bytes:\n{}", self)
        };
        s
    }
    pub const fn bytes_const(cache: &'static Cache, slice: &'static [u8]) -> Self {
        Self::Bytes(EvalSlice::Borrowed(cache, slice))
    }
    pub fn bytes(slice: &'static (impl AsRef<(Cache, [u8])> + ?Sized)) -> Self {
        let (cache, bytes) = slice.as_ref();

        Self::Bytes(EvalSlice::Borrowed(cache, bytes))
    }
    pub fn bytes_cloned(slice: impl AsRef<[u8]>) -> Self {
        let bytes = slice.as_ref();
        if let Some(slice) = <u8 as HasSliceStorage>::Storage::try_new(bytes) {
            Self::Bytes(EvalSlice::Inline(slice))
        } else {
            Self::Bytes(EvalSlice::Arc(bytes.into()))
        }
    }
    pub fn bytes_move(slice: impl Into<Arc<[u8], Cache>> + AsRef<[u8]>) -> Self {
        if let Some(slice) = <u8 as HasSliceStorage>::Storage::try_new(slice.as_ref()) {
            Self::Bytes(EvalSlice::Inline(slice))
        } else {
            Self::Bytes(EvalSlice::Arc(slice.into()))
        }
    }
    pub fn into_bytes(self) -> EvalSlice<u8> {
        let Self::Bytes(s) = self else {
            panic!("expected bytes, found aggregate:\n{}", self)
        };
        s
    }
    pub fn as_bytes(&self) -> &EvalSlice<u8> {
        let Self::Bytes(s) = self else {
            panic!("expected bytes, found aggregate:\n{}", self)
        };
        s
    }
    pub fn as_bytes_mut(&mut self) -> &mut EvalSlice<u8> {
        let Self::Bytes(s) = self else {
            panic!("expected bytes, found aggregate:\n{}", self)
        };
        s
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
        static OK_CACHE: Cache = Cache::new();
        static ERR_CACHE: Cache = Cache::new();
        match res {
            Ok(i1) => Value::aggregate_move([Value::bytes_const(&OK_CACHE, b"ok"), f1(i1)]),
            Err(i2) => Value::aggregate_move([Value::bytes_const(&ERR_CACHE, b"err"), f2(i2)]),
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

pub fn eval_builtin(atom: Atom) -> Value {
    let (world, world_handle) = World::new();
    let atom = atom_to_val(atom);
    static CACHE: Cache = Cache::new();
    eval(
        Value::aggregate_move([
            Value::bytes_const(&CACHE, b"call"),
            Value::aggregate_move([builtin_values::BUILTIN_EVAL_FUNC.static_copy(), atom]),
        ]),
        world,
    )
}

fn atom_to_val(atom: Atom) -> Value {
    static AGGR_CACHE: Cache = Cache::new();
    static IDENTIFIER_CACHE: Cache = Cache::new();
    static STRING_CACHE: Cache = Cache::new();
    match atom {
        Atom::Aggr(aggr) => Value::aggregate_move([
            Value::bytes_const(&AGGR_CACHE, b"aggregate"),
            Value::aggregate_move(
                <Box<[_]> as IntoIterator>::into_iter(aggr)
                    .map(atom_to_val)
                    .collect::<Arc<_, _>>(),
            ),
        ]),
        Atom::Identifier(s) => Value::aggregate_move([
            Value::bytes_const(&IDENTIFIER_CACHE, b"identifier"),
            Value::bytes_move(s.as_bytes()),
        ]),
        Atom::Bytes(s) => Value::aggregate_move([
            Value::bytes_const(&STRING_CACHE, b"string"),
            Value::bytes_move(&*s),
        ]),
    }
}

pub fn eval(expression: Value, mut world: World) -> Value {
    let mut thunk = BuiltinThunk::new(expression, 100);
    loop {
        match thunk.call(&mut world) {
            ControlFlow::Continue(t) => thunk = t,
            ControlFlow::Break(b) => break b,
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
                callbacks: Vec::with_capacity(max_depth),
                func: BuiltinFunc::BuiltinEval,
            },
            max_depth,
            value: expression,
        }
    }
    fn call(self, world: &mut World) -> ControlFlow<Value, Self> {
        let Self {
            state,
            max_depth,
            value,
        } = self;
        use ControlFlow::*;
        use FuncThunk::*;
        let BuiltinThunkState {
            mut callbacks,
            func,
        } = state;
        match func.poll(value, world) {
            Pending {
                pending_func,
                new_func,
                value,
            } => {
                assert!(
                    callbacks.len() <= max_depth,
                    "max depth {max_depth} exceeded",
                );
                callbacks.push(pending_func);
                Continue(Self {
                    state: BuiltinThunkState {
                        callbacks,
                        func: new_func,
                    },
                    max_depth,
                    value,
                })
            }
            Step { func, value } => Continue(Self {
                state: BuiltinThunkState { callbacks, func },
                max_depth,
                value,
            }),
            Done { value } => match callbacks.pop() {
                Some(func) => Continue(Self {
                    state: BuiltinThunkState { callbacks, func },
                    max_depth,
                    value,
                }),
                None => Break(value),
            },
        }
    }
}

#[derive(Debug)]
struct BuiltinThunkState {
    callbacks: Vec<BuiltinFunc>,
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
    #[inline]
    fn poll(self, value: Value, world: &mut World) -> FuncThunk {
        use FuncThunk::*;
        match self {
            Self::BuiltinEval => Self::poll_builtin_eval(value),
            Self::Let(let_eval) => let_eval.poll(value),
            Self::Call => Self::poll_call(value),
            Self::If => Self::poll_if(value),
            Self::BytesEq => Self::poll_bytes_eq(value),
            Self::Identity => Done { value },
            Self::AggrGet => Self::poll_aggr_get(value),
            Self::AggrSet => Self::poll_aggr_set(value),
            Self::AggrLen => Self::poll_aggr_len(value),
            Self::AggrMake => Self::poll_aggr_make(value),
            Self::Arithmetic(arithmetic) => arithmetic.poll(value),
            Self::WorldIo(world_io) => world_io.poll(value, world),
            Self::BuiltinImport(builtin_import) => builtin_import.poll(value),
        }
    }
    fn poll_builtin_eval(value: Value) -> FuncThunk {
        let [ident, value] = get_args(value);
        FuncThunk::Step {
            func: CopyFunc::from_value(&ident).into(),
            value,
        }
    }
    fn poll_call(value: Value) -> FuncThunk {
        let [func, arg] = get_args(value);
        FuncThunk::Step {
            func: Self::Let(Let::init(func)),
            value: arg,
        }
    }
    fn poll_if(value: Value) -> FuncThunk {
        let [cond, ifthen, ifelse] = get_args(value);
        FuncThunk::Step {
            func: Self::BuiltinEval,
            value: match trim_zeros(&**cond.as_bytes()) {
                &[1] => ifthen,
                &[] => ifelse,
                _ => panic!("non zero or one value given to if:\n{cond}"),
            },
        }
    }
    fn poll_bytes_eq(value: Value) -> FuncThunk {
        let [lhs, rhs] = get_args(value).map(Value::into_bytes);

        FuncThunk::Done {
            value: match *lhs == *rhs {
                true => TRUE.static_copy(),
                false => FALSE.static_copy(),
            },
        }
    }
    fn poll_aggr_get(value: Value) -> FuncThunk {
        let [value, idx] = get_args(value);
        let idx = get_usize(idx.as_bytes());
        let aggr = value.as_aggregate();
        FuncThunk::Done {
            value: aggr.get(idx).unwrap().clone(),
        }
    }
    fn poll_aggr_set(value: Value) -> FuncThunk {
        let [mut value, idx, src] = get_args(value);
        let idx = get_usize(idx.as_bytes());
        let aggr = value.as_aggregate_mut();
        let Some(dst) = aggr.make_mut().get_mut(idx) else {
            panic!("index {idx} out of bounds of aggregate:\n{value}")
        };
        *dst = src;
        FuncThunk::Done { value }
    }
    fn poll_aggr_len(value: Value) -> FuncThunk {
        FuncThunk::Done {
            value: usize_to_val(value.into_aggregate().len()),
        }
    }
    fn poll_aggr_make(value: Value) -> FuncThunk {
        FuncThunk::Done {
            value: Value::aggregate_move(
                std::iter::repeat(Value::unit())
                    .take(get_usize(value.as_bytes()))
                    .collect::<Arc<_, _>>(),
            ),
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum CopyFunc {
    BuiltinEval,
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

impl From<CopyFunc> for BuiltinFunc {
    fn from(value: CopyFunc) -> Self {
        match value {
            CopyFunc::BuiltinEval => Self::BuiltinEval,
            CopyFunc::Call => Self::Call,
            CopyFunc::If => Self::If,
            CopyFunc::BytesEq => Self::BytesEq,
            CopyFunc::Identity => Self::Identity,
            CopyFunc::AggrGet => Self::AggrGet,
            CopyFunc::AggrSet => Self::AggrSet,
            CopyFunc::AggrLen => Self::AggrLen,
            CopyFunc::AggrMake => Self::AggrMake,
            CopyFunc::Arithmetic(arithmetic) => Self::Arithmetic(arithmetic),
            CopyFunc::WorldIo(world_io) => Self::WorldIo(world_io),
            CopyFunc::BuiltinImport(builtin_import) => Self::BuiltinImport(builtin_import),
        }
    }
}

impl CopyFunc {
    fn from_value(value: &Value) -> Self {
        match &**value.as_bytes() {
            b"builtin_eval" => Self::BuiltinEval,
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
                    panic!("invalid builtin function name:\n{value}")
                }
            }
        }
    }
}

#[derive(Debug)]
struct Let {
    idx: usize,
    // Contains the constants, a slot for the arg, and a slot for every expression except the last
    state: Box<[Option<Value>]>,
    processed: Arc<LetProcessed>,
}

#[derive(Debug)]
struct LetStep {
    func: CopyFunc,
    args: LetStepArgs,
}

#[derive(Debug)]
enum LetStepArgs {
    Compound(Box<[LetStepArgs]>),
    Index(usize),
    // This means this will be the last occurence of the given index
    IndexMove(usize),
}

impl LetStepArgs {
    fn fetch(&self, state: &mut [Option<Value>]) -> Value {
        match self {
            Self::Compound(compound) => Value::Aggregate(EvalSlice::Arc(
                compound.iter().map(|arg| arg.fetch(state)).collect(),
            )),
            Self::Index(index) => state[*index].clone().unwrap(),
            Self::IndexMove(index) => std::mem::take(&mut state[*index]).unwrap(),
        }
    }
    fn new_no_move(value: &Value) -> Self {
        match value {
            Value::Bytes(eval_slice) => Self::Index(get_usize(eval_slice)),
            Value::Aggregate(eval_slice) => {
                Self::Compound(eval_slice.iter().map(Self::new_no_move).collect())
            }
        }
    }
}

#[derive(Debug)]
struct LetProcessed {
    offset: usize, // = constants.len() + 1
    instructions: Box<[LetStep]>,
    constants: Box<[Value]>,
}

impl LetProcessed {
    fn process_func(func: &Value) -> Self {
        let [constants, expressions] = get_args(func.clone()).map(Value::into_aggregate);
        assert!(!expressions.is_empty(),);

        let constants: Box<[_]> = std::iter::once(func.clone())
            .chain(constants.iter().cloned())
            .collect();

        let mut instructions: Box<[_]> = expressions
            .iter()
            .map(|expression| {
                let expression = expression.as_aggregate();
                let [func, args] = expression.as_array();

                let func = CopyFunc::from_value(func);

                LetStep {
                    func,
                    args: LetStepArgs::new_no_move(args),
                }
            })
            .collect();

        // every value except the last (including arg)
        let mut live_status: Box<[_]> =
            std::iter::repeat_n(false, constants.len() + expressions.len()).collect();
        // compute drops
        fn args_compute_moves(args: &mut LetStepArgs, live_status: &mut [bool]) {
            match args {
                LetStepArgs::Compound(items) => items
                    .iter_mut()
                    .rev()
                    .for_each(|args| args_compute_moves(args, live_status)),
                LetStepArgs::Index(idx)
                    if std::mem::replace(&mut live_status[*idx], true) == false =>
                {
                    *args = LetStepArgs::IndexMove(*idx);
                }
                LetStepArgs::Index(_) => (),
                LetStepArgs::IndexMove(_) => unreachable!(),
            }
        }
        instructions
            .iter_mut()
            .rev()
            .for_each(|step| args_compute_moves(&mut step.args, &mut live_status));

        Self {
            offset: constants.len() + 1,
            instructions,
            constants,
        }
    }
}

impl Let {
    fn poll(mut self, value: Value) -> FuncThunk {
        let Let {
            idx,
            state,
            processed,
        } = &mut self;
        state[*idx] = Some(value);
        *idx += 1;

        let LetStep { func, args } = &processed.instructions[*idx - processed.offset];

        let value = args.fetch(state);

        let func = (*func).into();

        if *idx == state.len() {
            FuncThunk::Step { func, value }
        } else {
            FuncThunk::Pending {
                new_func: func,
                pending_func: BuiltinFunc::Let(self),
                value,
            }
        }
    }
    fn init(func: Value) -> Self {
        let res = func.cache().generate(|| CacheInner {
            func: Arc::new(LetProcessed::process_func(&func)),
        });
        Self::new(res.func.clone())
    }
    fn new(processed: Arc<LetProcessed>) -> Self {
        Self {
            idx: processed.constants.len(),
            state: processed
                .constants
                .iter()
                .map(Clone::clone)
                .map(Some)
                .chain(std::iter::repeat_n(None, processed.instructions.len()))
                .collect(),
            processed,
        }
    }
}

#[inline]
pub fn get_args<const SIZE: usize>(value: Value) -> [Value; SIZE] {
    let slice = value.into_aggregate();
    slice.into_array()
}

#[inline]
pub fn get_args_ref<const SIZE: usize>(value: &Value) -> &[Value; SIZE] {
    let slice = value.as_aggregate();
    slice.as_array()
}

// Little endian
pub fn get_usize(bytes: &[u8]) -> usize {
    bytes
        .iter()
        .rev()
        .try_fold(0usize, |acc, byte| {
            acc.checked_mul(u8::MAX as usize + 1)?
                .checked_add(*byte as usize)
        })
        .unwrap()
}

pub fn usize_to_val(usize: usize) -> Value {
    let bytes = usize.to_le_bytes();
    Value::bytes_cloned(trim_zeros(&bytes))
}

pub fn get_u128(bytes: &[u8]) -> u128 {
    bytes
        .iter()
        .rev()
        .try_fold(0u128, |acc, byte| {
            acc.checked_mul(u8::MAX as u128 + 1)?
                .checked_add(*byte as u128)
        })
        .unwrap()
}
