mod arithemtic;
pub mod builtin_values;
pub mod value;
mod world;

use crate::utils::sync::cache_arc::CacheArc as Arc;
use crate::utils::sync::cache_lock::CacheLock;
use std::fmt::Debug;
use std::iter::repeat_n;

use arithemtic::trim_zeros;
use arithemtic::Arithmetic;
use builtin_values::BuiltinImport;
use builtin_values::FALSE;
use builtin_values::TRUE;
use builtin_values::TYPE_AGGR;
use builtin_values::TYPE_BYTES;
use world::AsWorld;
use world::PureWorld;
use world::World;
use world::WorldIo;

use crate::parse::Atom;

pub use value::EvalSlice;
pub use value::Value;

type Cache = CacheLock<CacheInner>;

#[derive(Debug, Clone)]
pub struct CacheInner {
    func: Arc<LetProcessed>,
}

pub fn eval_builtin(atom: Atom) -> Value {
    let (mut world, world_handle) = World::new();
    let atom = atom_to_val(atom);
    FuncThunk::Step {
        func: BuiltinFunc::Call,
        value: Value::aggregate_move([builtin_values::BUILTIN_EVAL_FUNC.static_copy(), atom]),
    }
    .eval::<false>(&mut world)
}

pub fn eval_pure(value: Value) -> Value {
    FuncThunk::Step {
        func: BuiltinFunc::BuiltinEval,
        value,
    }
    .eval::<false>(&mut PureWorld)
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

enum FuncThunk {
    Step { func: BuiltinFunc, value: Value },
    Done { value: Value },
}

impl FuncThunk {
    fn eval<const IS_CONST_FOLD: bool>(mut self, world: &mut impl AsWorld) -> Value {
        loop {
            match self {
                FuncThunk::Step { func, value } => self = func.poll::<IS_CONST_FOLD>(value, world),
                FuncThunk::Done { value } => break value,
            }
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum BuiltinFunc {
    BuiltinEval,
    Call,
    If,
    BytesEq,
    Identity,
    AggrGet,
    AggrSet,
    AggrLen,
    AggrMake,
    TypeOf,
    Arithmetic(Arithmetic),
    WorldIo(WorldIo),
    BuiltinImport(BuiltinImport),
}

impl BuiltinFunc {
    #[inline]
    fn poll<const IS_CONST_FOLD: bool>(self, value: Value, world: &mut impl AsWorld) -> FuncThunk {
        use FuncThunk::*;
        match self {
            Self::BuiltinEval => Self::poll_builtin_eval(value),
            Self::Call => Self::poll_call::<IS_CONST_FOLD>(value, world),
            Self::If => Self::poll_if(value),
            Self::BytesEq => Self::poll_bytes_eq(value),
            Self::Identity => Done { value },
            Self::AggrGet => Self::poll_aggr_get(value),
            Self::AggrSet => Self::poll_aggr_set(value),
            Self::AggrLen => Self::poll_aggr_len(value),
            Self::AggrMake => Self::poll_aggr_make(value),
            Self::TypeOf => Self::poll_typeof(value),
            Self::Arithmetic(arithmetic) => arithmetic.poll(value),
            Self::WorldIo(world_io) => world_io.poll(value, world),
            Self::BuiltinImport(builtin_import) => builtin_import.poll(value),
        }
    }
    fn poll_builtin_eval(value: Value) -> FuncThunk {
        let [ident, value] = get_args(value);
        FuncThunk::Step {
            func: BuiltinFunc::from_value(&ident).into(),
            value,
        }
    }
    fn poll_call<const IS_CONST_FOLD: bool>(value: Value, world: &mut impl AsWorld) -> FuncThunk {
        let [func, arg] = get_args(value);
        let func = func.into_aggregate();
        match func.len() {
            2 => {
                // Function
                Let::call::<IS_CONST_FOLD>(Value::Aggregate(func), arg, world)
            }
            3 => {
                // Closure
                let [magic, func, captured] = func.into_array();
                debug_assert!(&**magic.as_bytes() == b"closure");
                Let::call::<IS_CONST_FOLD>(func, Value::aggregate_move([captured, arg]), world)
            }
            _ => panic!(),
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
    fn poll_typeof(value: Value) -> FuncThunk {
        FuncThunk::Done {
            value: match value {
                Value::Bytes(_) => TYPE_BYTES.static_copy(),
                Value::Aggregate(_) => TYPE_AGGR.static_copy(),
            },
        }
    }
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
            b"type_of" => Self::TypeOf,
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
    func: BuiltinFunc,
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
    fn try_fetch_no_move(&self, state: &mut [Option<Value>]) -> Option<Value> {
        match self {
            Self::Compound(compound) => Some(Value::Aggregate(EvalSlice::Arc(
                compound
                    .iter()
                    .map(|arg| arg.try_fetch_no_move(state))
                    .collect::<Option<_>>()?,
            ))),
            Self::Index(index) => state[*index].clone(),
            Self::IndexMove(index) => state[*index].clone(),
        }
    }
    fn new(value: &Value) -> Self {
        match value {
            Value::Bytes(eval_slice) => Self::Index(get_usize(eval_slice)),
            Value::Aggregate(eval_slice) => {
                Self::Compound(eval_slice.iter().map(Self::new).collect())
            }
        }
    }
    fn idx_map(&mut self, func: &mut impl FnMut(&mut usize)) {
        match self {
            LetStepArgs::Compound(items) => items.iter_mut().for_each(|e| e.idx_map(func)),
            LetStepArgs::Index(i) => func(i),
            LetStepArgs::IndexMove(i) => func(i),
        }
    }
    fn idx_for_each(&self, func: &mut impl FnMut(usize)) {
        match self {
            LetStepArgs::Compound(items) => items.iter().for_each(|e| e.idx_for_each(func)),
            LetStepArgs::Index(i) => func(*i),
            LetStepArgs::IndexMove(i) => func(*i),
        }
    }
}

#[derive(Debug)]
struct LetProcessed {
    instructions: Box<[LetStep]>,
    constants: Box<[Value]>,
}

impl LetProcessed {
    fn process_func<const IS_CONST_FOLD: bool>(func: &Value) -> Self {
        let [constants, expressions] = get_args(func.clone()).map(Value::into_aggregate);
        assert!(!expressions.is_empty());

        let mut constants: Vec<_> = std::iter::once(func.clone())
            .chain(constants.iter().cloned())
            .collect();

        let mut instructions: Vec<_> = expressions
            .iter()
            .map(|expression| {
                let expression = expression.as_aggregate();
                let [func, args] = expression.as_array();

                let func = BuiltinFunc::from_value(func);

                LetStep {
                    func,
                    args: LetStepArgs::new(args),
                }
            })
            .collect();

        // every value except the last (including arg)
        let mut live_status: Vec<_> =
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

        if !IS_CONST_FOLD {
            Self::constant_fold(&mut constants, &mut instructions);
            Self::trim_dead_code(&mut constants, &mut instructions);
        }

        let (instructions, constants) = (instructions.into(), constants.into());

        Self {
            instructions,
            constants,
        }
    }
    fn constant_fold(constants: &mut Vec<Value>, instructions: &mut Vec<LetStep>) {
        assert!(!instructions.is_empty());

        let mut values: Vec<_> = constants
            .iter()
            .cloned()
            .map(Some)
            .chain(repeat_n(None, instructions.len() + 1))
            .collect();

        let instr_start = constants.len() + 1;

        instructions.iter().enumerate().for_each(|(i, step)| {
            let LetStep { func, args } = step;
            let Some(args) = args.try_fetch_no_move(&mut values) else {
                return;
            };
            let val = FuncThunk::Step {
                func: *func,
                value: args,
            }
            .eval::<true>(&mut PureWorld);
            let idx = i + instr_start;
            values[idx] = Some(val);
        });

        values.drain(0..instr_start);

        if let Some(tail) = values.pop().unwrap() {
            constants.clear();
            instructions.clear();
            constants.push(tail);
            instructions.push(LetStep {
                func: BuiltinFunc::Identity,
                args: LetStepArgs::IndexMove(0),
            });
            return;
        }

        let mut extra_constants = 0usize;
        let value_map = values
            .iter()
            .map(|val| {
                val.is_some().then(|| {
                    let res = extra_constants;
                    extra_constants += 1;
                    res
                })
            })
            .collect::<Box<_>>();
        let value_map_offset = constants.len();

        let value_map_get = |i: usize| {
            i.checked_sub(instr_start)
                .and_then(|i| value_map.get(i).and_then(Option::as_ref))
                .map(|i| *i + value_map_offset)
        };

        instructions.iter_mut().for_each(|instr| {
            instr.args.idx_map(&mut |idx| {
                if let Some(constant) = value_map_get(*idx) {
                    *idx = constant
                } else if *idx >= constants.len() {
                    *idx += extra_constants
                }
            });
        });

        constants.extend(values.into_iter().filter_map(std::convert::identity));
    }
    fn trim_dead_code(constants: &mut Vec<Value>, instructions: &mut Vec<LetStep>) {
        let mut use_status = constants
            .iter()
            .map(|_| false)
            .chain(std::iter::once(true)) // arg
            .chain(std::iter::repeat_n(false, instructions.len() - 1)) // intermediate expressions
            .chain(std::iter::once(true)) // trailing expression
            .collect::<Box<_>>();
        instructions
            .iter()
            .rev()
            .enumerate()
            .for_each(|(idx_back, instr)| {
                if use_status[use_status.len() - 1 - idx_back] {
                    instr.args.idx_for_each(&mut |i| use_status[i] = true)
                }
            });
        let constants_status = &use_status[..constants.len()];
        let instructions_status = &use_status[(constants.len() + 1)..];
        let mut idx = 0;
        let new_indices = use_status
            .iter()
            .map(|i| {
                i.then(|| {
                    let res = idx;
                    idx += 1;
                    res
                })
            })
            .collect::<Box<_>>();
        let mut idx = 0;
        constants.retain(|_| {
            let res = constants_status[idx];
            idx += 1;
            res
        });
        let mut idx = 0;
        instructions.retain(|_| {
            let res = instructions_status[idx];
            idx += 1;
            res
        });
        instructions
            .iter_mut()
            .for_each(|step| step.args.idx_map(&mut |i| *i = new_indices[*i].unwrap()));
    }
}

impl Let {
    fn call<const IS_CONST_FOLD: bool>(
        func: Value,
        arg: Value,
        world: &mut impl AsWorld,
    ) -> FuncThunk {
        Let::init::<IS_CONST_FOLD>(func).poll::<IS_CONST_FOLD>(arg, world)
    }
    fn poll<const IS_CONST_FOLD: bool>(
        mut self,
        mut value: Value,
        world: &mut impl AsWorld,
    ) -> FuncThunk {
        loop {
            let Let {
                idx,
                state,
                processed,
            } = &mut self;
            state[*idx] = Some(value);
            *idx += 1;

            let LetStep { func, args } =
                &processed.instructions[*idx - processed.constants.len() - 1];

            let res = args.fetch(state);

            let func = *func;

            if *idx == state.len() {
                break FuncThunk::Step { func, value: res };
            } else {
                value = FuncThunk::Step { func, value: res }.eval::<IS_CONST_FOLD>(world);
            }
        }
    }
    fn init<const IS_CONST_FOLD: bool>(func: Value) -> Self {
        let func = if !IS_CONST_FOLD {
            let res = func.cache().generate(|| CacheInner {
                func: Arc::new(LetProcessed::process_func::<IS_CONST_FOLD>(&func)),
            });
            res.func.clone()
        } else {
            match func.cache().get() {
                Some(cache) => cache.func.clone(),
                None => Arc::new(LetProcessed::process_func::<IS_CONST_FOLD>(&func)),
            }
        };

        Self::new(func)
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
