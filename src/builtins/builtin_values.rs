use ahash::AHashMap;

use super::FuncThunk;
use super::Value;
use crate::builtins::Cache;

const fn trim_trailing_zeros(slice: &[u8]) -> &[u8] {
    if let Some((0, slice)) = slice.split_last() {
        trim_trailing_zeros(slice)
    } else {
        slice
    }
}

macro_rules! cera_expr {
    ({$expr:expr}) => {
        $expr.static_copy()
    };
    ([$expr:expr]) => {
        {
            static CACHE: Cache = Cache::new();
            Value::bytes_const(&CACHE, trim_trailing_zeros(const {&usize::to_le_bytes($expr)}))
        }
    };
    ($ident:ident) => {
        {
            static CACHE: Cache = Cache::new();
            Value::bytes_const(&CACHE, unsafe { std::mem::transmute(stringify!($ident)) })
        }
    };
    ($literal:literal) => {
        {
            static CACHE: Cache = Cache::new();
            Value::bytes_const(&CACHE, $literal)
        }
    };
    (($($tt:tt)*)) => {
        {
            static CACHE: Cache = Cache::new();
            static DATA: [Value; count!($($tt)*)] = [$(cera_expr!($tt)),*];
            Value::aggregate_const(&CACHE, {
                &DATA
            })
        }
    }
}

pub struct BuiltinLookup(AHashMap<Box<[u8]>, Value>);

impl BuiltinLookup {
    pub fn get(&self, str: &[u8]) -> Value {
        self.0
            .get(str)
            .unwrap_or_else(|| panic!("invalid builtin import: {}", Value::bytes_move(str)))
            .clone()
    }
    pub fn new(value: Value) -> Self {
        Self(
            value
                .into_aggregate()
                .iter()
                .map(|val| {
                    let [key, val] = val.clone().into_aggregate().into_array();
                    ((&**key.as_bytes()).into(), val)
                })
                .collect(),
        )
    }
}

#[derive(Debug, Clone, Copy)]
pub struct BuiltinImport;

impl BuiltinImport {
    pub(super) fn poll(self, value: Value, lookup: &BuiltinLookup) -> FuncThunk {
        FuncThunk::Done {
            value: lookup.get(&**value.as_bytes()),
        }
    }
    pub fn from_ident(ident: &[u8]) -> Option<Self> {
        match ident {
            b"builtin_import" => Some(Self),
            _ => return None,
        }
    }
}

pub static TRUE: Value = cera_expr!([1]);
pub static FALSE: Value = cera_expr!([0]);
pub static CMP_LESS: Value = cera_expr!([0]);
pub static CMP_EQUAL: Value = cera_expr!([1]);
pub static CMP_GREATER: Value = cera_expr!([2]);
pub static TYPE_AGGR: Value = cera_expr!(aggr);
pub static TYPE_BYTES: Value = cera_expr!(bytes);

/*
// (func world) -> func_res
//
// 0: self
// 1: 0
// 2: 1
// 3: ATOM_VALUE_TO_EVALUATABLE
// 4: FUNC_DESUGAR_EXECUTE
// 5: arg
// 6: func (aggr_get (arg 0))
// 7: world (aggr_get (arg 1))
// 8: func2 (call (ATOM_VALUE_TO_EVALUATABLE func))
// call (FUNC_DESUGAR_EXECUTE (func2 world))
#[rustfmt::skip]
pub static BUILTIN_EVAL_FUNC: Value = cera!(
    ([0] [1] {ATOM_VALUE_TO_EVALUATABLE} {FUNC_DESUGAR_EXECUTE})
    (
        (aggr_get ([5] [1]))
        (aggr_get ([5] [2]))
        (call ([3] [6]))
        (call ([4] ([8] [7])))
    )
);

// 0: self
// 1: 0
// 2: 1
// 3: "aggr_map"
// 4: "aggregate"
// 5: "call"
// 6: "identity"
// 7: arg
// 8: type
// 9: value
// 10: type == "aggregate"
// 11: builtin_import 3
// if 10 (call (11 (value self)))) else (identity value)
#[rustfmt::skip]
static ATOM_VALUE_TO_EVALUATABLE: Value = cera!(
    ([0] [1] aggr_map aggregate call identity)
    (
        (aggr_get ([7] [1]))
        (aggr_get ([7] [2]))
        (bytes_eq ([8] [4]))
        (builtin_import [3])
        (if ([10]
            ([5] ([11] ([9] [0])))
            ([6] [9])
        ))
    )
);

// (aggr func) -> aggr
//
// 0: self
// 1: 0
// 2: 1
// 3: aggr_slice_new
// 4: aggr_slice_map
// 5: aggr_slice_buf
// 6: arg
// 7: aggr (aggr_get (arg 0))
// 8: func (aggr_get (arg 1))
// 9: builtin_import 3
// 10: builtin_import 4
// 11: builtin_import 5
// 12: slice (call (9 aggr))
// 13: slice2 (call (10 (slice func)))
// call (11 slice2)
#[rustfmt::skip]
static AGGR_MAP: Value = cera!(
    (
        [0]
        [1]
        aggr_slice_new
        aggr_slice_map
        aggr_slice_buf
    )
    (
        (aggr_get ([6] [1]))
        (aggr_get ([6] [2]))
        (builtin_import [3])
        (builtin_import [4])
        (builtin_import [5])
        (call ([9] [7]))
        (call ([10] ([12] [8])))
        (call ([11] [13]))
    )
);

// aggr -> slice
//
// 0: self
// 1: 0
// 2: arg
// 3: len (aggr_len arg)
// identity (0 len arg)
#[rustfmt::skip]
static AGGR_SLICE_NEW: Value = cera!(
    ([0])
    (
        (aggr_len [2])
        (identity ([1] [3] [2]))
    )
);

// slice -> buf
//
// 0: self
// 1: 2
// 2: arg
// aggr_get (arg 2)
#[rustfmt::skip]
static AGGR_SLICE_BUF: Value = cera!(
    ([2])
    (
        (aggr_get ([2] [1]))
    )
);

// (slice idx) -> value
//
// 0: self
// 1: 0
// 2: 1
// 3: 2
// 4: arg
// 5: slice (aggr_get (arg 0))
// 6: idx (aggr_get (arg 1))
// 7: start (aggr_get (slice 0))
// 8: buf (aggr_get (slice 2))
// 9: idx_real (add (idx start))
// aggr_get (buf idx_real)
#[rustfmt::skip]
static AGGR_SLICE_GET: Value = cera!(
    (
        [0]
        [1]
        [2]
    )
    (
        (aggr_get ([4] [1]))
        (aggr_get ([4] [2]))
        (aggr_get ([5] [1]))
        (aggr_get ([5] [3]))
        (add ([6] [7]))
        (aggr_get ([8] [9]))
    )
);

// (slice idx) -> ("some" value) | ("none" ())
//
// 0: self
// 1: 0
// 2: 1
// 3: 2
// 4: bool_then
// 5: aggr_get
// 6: arg
// 7: slice (aggr_get (arg 0))
// 8: idx (aggr_get (arg 1))
// 9: start (aggr_get (slice 0))
// 10: end (aggr_get (slice 1))
// 11: buf (aggr_get (slice 2))
// 12: idx_real (add (idx start))
// 13: len (aggr_len buf)
// 14: bounds_check (cmp (idx_real len))
// 15: is_in_bounds (eq (0 bounds_check))
// 16: builtin_import "bool_then"
// call (16 (is_in_bounds (aggr_get (buf idx_real))))
#[rustfmt::skip]
static AGGR_SLICE_TRY_GET: Value = cera!(
    ([0] [1] [2] bool_then aggr_get)
    (
        (aggr_get ([6] [1]))
        (aggr_get ([6] [2]))
        (aggr_get ([7] [1]))
        (aggr_get ([7] [2]))
        (aggr_get ([7] [3]))
        (add ([8] [9]))
        (aggr_len [11])
        (cmp ([12] [13]))
        (eq ([1] [14]))
        (builtin_import [4])
        (call ([16] ([15] ([5] ([11] [12])))))
    )
);

// (slice idx value) -> slice
//
// 0: self
// 1: 0
// 2: 1
// 3: 2
// 4: arg
// 5: slice (aggr_get (arg 0))
// 6: idx (aggr_get (arg 1))
// 7: value (aggr_get (arg 2))
// 8: start (aggr_get (slice 0))
// 9: end (agg_get (slice 1))
// 10: buf (aggr_get (slice 2))
// 11: idx_real (add (idx start))
// 12: buf2 (aggr_set (buf idx_real value))
// identity (start end buf2)
#[rustfmt::skip]
static AGGR_SLICE_SET: Value = cera!(
    (
        [0]
        [1]
        [2]
    )
    (
        (aggr_get ([4] [1]))
        (aggr_get ([4] [2]))
        (aggr_get ([4] [3]))
        (aggr_get ([5] [1]))
        (aggr_get ([5] [2]))
        (aggr_get ([5] [3]))
        (add ([6] [8]))
        (aggr_set ([10] [11] [7]))
        (identity ([8] [9] [12]))
    )
);

// (slice idx value) -> (slice ("some" value) | ("none" ()))
//
// 0: self
// 1: 0
// 2: 1
// 3: 2
// 4: bool_then_some
// 5: bool_not
// 6: aggr_set
// 7: identity
// 8: arg
// 9: slice (aggr_get (arg 0))
// 10: idx (aggr_get (arg 1))
// 11: value (aggr_get (arg 2))
// 12: start (aggr_get (slice 0))
// 13: end (aggr_get (slice 1))
// 14: buf (aggr_get (slice 2))
// 15: idx_real (add (idx start))
// 16: len (aggr_len buf)
// 17: bounds_check (cmp (idx_real len))
// 18: is_in_bounds (eq (0 bounds_check))
// 19: buf2 (if (is_in_bounds (aggr_set (buf idx_real value)) (identity buf)))
// 20: bool_then_some (builtin_import bool_then_some)
// 21: bool_not (builtin_import bool_not)
// 20: is_not_in_bounds (call (bool_not is_in_bounds))
// 21: value_rem (call (bool_then_some (is_not_in_bounds value)))
// identity ((start end buf2) value_rem)
#[rustfmt::skip]
static AGGR_SLICE_TRY_SET: Value = cera!(
    (
        [0]
        [1]
        [2]
        bool_then_some
        bool_not
        aggr_set
        identity
    )
    (
        (aggr_get ([8] [1]))
        (aggr_get ([8] [2]))
        (aggr_get ([8] [3]))
        (aggr_get ([9] [1]))
        (aggr_get ([9] [2]))
        (aggr_get ([9] [3]))
        (add ([10] [12]))
        (aggr_len [14])
        (cmp ([15] [16]))
        (eq ([1] [17]))
        (if ([18]
            ([6] ([14] [15] [11]))
            ([7] [14])
        ))
        (builtin_import [4])
        (builtin_import [5])
        (call ([21] [18]))
        (call ([20] ([22] [11])))
        (identity (([12] [13] [19]) [23]))
    )
);

// slice -> bytes
//
// 0: self
// 1: 0
// 2: 1
// 3: arg
// 4: start (aggr_get (arg 0))
// 5: end (aggr_get (arg 1))
// sub (end start)
#[rustfmt::skip]
static AGGR_SLICE_LEN: Value = cera!(
    ([0] [1])
    (
        (aggr_get ([3] [1]))
        (aggr_get ([3] [2]))
        (sub ([5] [4]))
    )
);

// slice -> bool
//
// 0: self
// 1: 0
// 2: 1
// 3: arg
// 4: start (aggr_get (arg 0))
// 5: end (aggr_get (arg 1))
// eq (start end)
#[rustfmt::skip]
static AGGR_SLICE_IS_EMPTY: Value = cera!(
    ([0] [1])
    (
        (aggr_get ([3] [1]))
        (aggr_get ([3] [2]))
        (eq ([4] [5]))
    )
);

// (slice{T} acc{A} func{(A T) -> (A O)}) -> (slice{O} A)
//
// 0: self
// 1: 0
// 2: AGGR_SLICE_MAP_FOLD_INNER
// 3: arg
// 4: slice (aggr_get (arg 0))
// 5: init_start (aggr_get (slice 0))
// 6: value (call (AGGR_SLICE_MAP_FOLD_INNER arg))
// 7: slice_mapped (aggr_get (value 0))
// 8: value2 (aggr_set (value 0 ()))
// 9: slice_mapped2 (aggr_set (slice_mapped 0 init_start))
// aggr_set (value2 0 slice_mapped_2)
#[rustfmt::skip]
static AGGR_SLICE_MAP_FOLD: Value = cera!(
    (
        [0]
        {AGGR_SLICE_MAP_FOLD_INNER}
    )
    (
        (aggr_get ([3] [1]))
        (aggr_get ([4] [1]))
        (call ([2] [3]))
        (aggr_get ([6] [1]))
        (aggr_set ([6] [1] ()))
        (aggr_set ([7] [1] [5]))
        (aggr_set ([8] [1] [9]))
    )
);

// (slice{T} acc{A} func{(A T) -> (A O)}) -> (slice{O#len=0} A)
//
// 0: self
// 1: 0
// 2: 1
// 3: aggr_slice_is_empty
// 4: identity
// 5: call
// 6: pipe
// 7: AGGR_SLICE_MAP_FOLD_STEP
// 8: arg
// 9: slice (aggr_get (arg 0))
// 10: acc (aggr_get (arg 1))
// 11: aggr_slice_is_empty
// 12: is_empty (call (AGGR_SLICE_IS_EMPTY slice))
// 13: pipe (builtin_import pipe)
// if (is_empty
//      (identity (slice acc))
//      (call (pipe ((call (AGGR_SLICE_MAP_FOLD_STEP arg)) self)))
// )
#[rustfmt::skip]
static AGGR_SLICE_MAP_FOLD_INNER: Value = cera!(
    (
        [0]
        [1]
        aggr_slice_is_empty
        identity
        call
        pipe
        {AGGR_SLICE_MAP_FOLD_STEP}
    )
    (
        (aggr_get ([8] [1]))
        (aggr_get ([8] [2]))
        (builtin_import [3])
        (call ([11] [9]))
        (builtin_import [6])
        (if ([12]
            ([4] ([9] [10]))
            ([5] ([13] (([5] ([7] [8])) [0])))
        ))
    )
);

// (slice{T} acc{A} func{(A T) -> (A O)}) -> (slice{T#len-=1} acc{A} func{(A T) -> (A O)})
//
// 0: self
// 1: 0
// 2: 1
// 3: 2
// 4: aggr_slice_get
// 5: aggr_slice_set
// 6: arg
// 7: slice (aggr_get (arg 0))
// 8: acc (aggr_get (arg 1))
// 9: func (aggr_get (arg 2))
// 10: aggr_slice_get (builtin_import aggr_slice_get)
// 11: aggr_slice_set (builtin_import aggr_slice_set)
// 12: elem (call (aggr_slice_get (slice 0)))
// 13: slice2 (call (aggr_slice_set (slice 0 ())))
// 14: func_ret (call (func (acc elem)))
// 15: acc2 (aggr_get (func_ret 0))
// 16: elem2 (aggr_get (func_ret 1))
// 17: slice3 (call (aggr_slice_set (slice2 0 elem2)))
// 18: start (aggr_get (slice3 0))
// 19: start2 (add (start 1))
// 20: slice4 (aggr_set (slice3 0 start2))
// identity (slice4 acc2 func)
#[rustfmt::skip]
static AGGR_SLICE_MAP_FOLD_STEP: Value = cera!(
    (
        [0]
        [1]
        [2]
        aggr_slice_get
        aggr_slice_set
    )
    (
        (aggr_get ([6] [1]))
        (aggr_get ([6] [2]))
        (aggr_get ([6] [3]))
        (builtin_import [4])
        (builtin_import [5])
        (call ([10] ([7] [1])))
        (call ([11] ([7] [1] ())))
        (call ([9] ([8] [12])))
        (aggr_get ([14] [1]))
        (aggr_get ([14] [2]))
        (call ([11] ([13] [1] [16])))
        (aggr_get ([17] [1]))
        (add ([18] [2]))
        (aggr_set ([17] [1] [19]))
        (identity ([20] [15] [9]))
    )
);

// (slice{T} func{T -> O}) -> slice{O}
//
// 0: self
// 1: 0
// 2: 1
// 3: aggr_slice_map_fold
// 4: compose
// 5: ((1)((aggr_get (2 1))))
// 6: (()((identity (() 1))))
// 7: arg
// 8: slice (aggr_get (arg 0))
// 9: func (aggr_get (arg 1))
// 10: aggr_slice_map_fold (builtin_import aggr_slice_map_fold)
// 11: compose (builtin_import compose)
// 12: func2 (call (compose ([5] func)))
// 13: func3 (call (compose (func2 [6])))
// 14: res (call (aggr_slice_map_fold (slice () func3)))
// aggr_get (res 0)
#[rustfmt::skip]
static AGGR_SLICE_MAP: Value = cera!(
    (
        [0]
        [1]
        aggr_slice_map_fold
        compose
        (([1])((aggr_get ([2] [1]))))
        (()((identity (() [1]))))
    )
    (
        (aggr_get ([7] [1]))
        (aggr_get ([7] [2]))
        (builtin_import [3])
        (builtin_import [4])
        (call ([11] ([5] [9])))
        (call ([11] ([12] [6])))
        (call ([10] ([8] () [13])))
        (aggr_get ([14] [1]))
    )
);

// (slice{T} acc{A} func{(A T) -> A}) -> A
//
// 0: self
// 1: 0
// 2: 1
// 3: aggr_slice_is_empty
// 4: identity
// 5: call
// 6: pipe
// 7: AGGR_SLICE_FOLD_STEP
// 8: arg
// 9: slice (aggr_get (arg 0))
// 10: acc (aggr_get (arg 1))
// 11: aggr_slice_is_empty (builtin_import aggr_slice_is_empty)
// 12: pipe (builtin_import pipe)
// 13: is_empty (call (aggr_slice_is_empty slice))
// if (is_empty
//      (identity acc)
//      (call (pipe ((call (AGGR_SLICE_FOLD_STEP arg)) self)))
// )
#[rustfmt::skip]
static AGGR_SLICE_FOLD: Value = cera!(
    (
        [0]
        [1]
        aggr_slice_is_empty
        identity
        call
        pipe
        {AGGR_SLICE_FOLD_STEP}
    )
    (
        (aggr_get ([8] [1]))
        (aggr_get ([8] [2]))
        (builtin_import [3])
        (builtin_import [6])
        (call ([11] [9]))
        (if ([13]
            ([4] [10])
            ([5] ([12] (([5] ([7] [8])) [0])))
        ))
    )
);

// (slice{T} acc{A} func{(A T) -> A}) -> (slice{T#len-=1} acc{A} func{(A T) -> A})
//
// 0: self
// 1: 0
// 2: 1
// 3: 2
// 4: aggr_slice_get
// 5: arg
// 6: slice (aggr_get (arg 0))
// 7: acc (aggr_get (arg 1))
// 8: func (aggr_get (arg 2))
// 9: arg2 (aggr_set (arg 0 ()))
// 10: arg3 (aggr_set (arg2 1 ()))
// 11: aggr_slice_get (builtin_import aggr_slice_get)
// 11: elem (call (aggr_slice_get (slice 0)))
// 12: acc2 (call (func (acc elem)))
// 13: arg4 (aggr_set (arg3 1 acc2))
// 14: start (aggr_get (slice 0))
// 15: start2 (add (start 1))
// 16: slice2 (aggr_set (slice 0 start2))
// aggr_set (arg4 0 slice2)
#[rustfmt::skip]
static AGGR_SLICE_FOLD_STEP: Value = cera!(
    ([0] [1] [2] aggr_slice_get)
    (
        (aggr_get ([5] [1]))
        (aggr_get ([5] [2]))
        (aggr_get ([5] [3]))
        (aggr_set ([5] [1] ()))
        (aggr_set ([9] [2] ()))
        (builtin_import [4])
        (call ([11] ([6] [1])))
        (call ([8] ([7] [12])))
        (aggr_set ([10] [2] [13]))
        (aggr_get ([6] [1]))
        (add ([15] [2]))
        (aggr_set ([6] [1] [16]))
        (aggr_set ([14] [1] [17]))
    )
);

// (src dst) -> dst
//
// 0: self
// 1: 0
// 2: 1
// 3: AGGR_SLICE_COPY_INNER
// 4: arg
// 5: src (aggr_get (arg 0))
// 6: dst (aggr_get (arg 1))
// 7: start (aggr_get (dst 0))
// 8: dst2 (call (AGGR_SLICE_COPY_INNER (src dst)))
// aggr_set (dst2 0 start)
#[rustfmt::skip]
static AGGR_SLICE_COPY: Value = cera!(
    ([0] [1] {AGGR_SLICE_COPY_INNER})
    (
        (aggr_get ([4] [1]))
        (aggr_get ([4] [2]))
        (aggr_get ([6] [1]))
        (call ([3] ([5] [6])))
        (aggr_set ([8] [1] [7]))
    )
);

// (src dst) -> dst
//
// 0: self
// 1: 1
// 2: AGGR_SLICE_IS_EMPTY
// 3: COMPOSE
// 4: AGGR_SLICE_COPY_STEP
// 5: identity
// 6: call
// 7: arg
// 8: dst (aggr_get (arg 1))
// 9: aggr_slice_is_empty (buitlin_import aggr_slice_is_empty)
// 10: compose (builtin_import compose)
// 11: is_empty (call (aggr_slice_is_empty dst))
// 12: tail (call (compose (AGGR_SLICE_COPY_STEP self)))
// if (is_empty (identity dst) (call (tail arg)))
#[rustfmt::skip]
static AGGR_SLICE_COPY_INNER: Value = cera!(
    (
        [1]
        aggr_slice_is_empty
        compose
        {AGGR_SLICE_COPY_STEP}
        identity
        call
    )
    (
        (aggr_get ([7] [1]))
        (builtin_import [2])
        (builtin_import [3])
        (call ([9] [8]))
        (call ([10] ([4] [0])))
        (if ([11]
            ([5] [8])
            ([6] ([12] [7]))
        ))
    )
);

// (src dst) -> (src dst)
//
// 0: self
// 1: 0
// 2: 1
// 3: AGGR_SLICE_GET
// 4: AGGR_SLICE_SET
// 5: arg
// 6: src (aggr_get (arg 0))
// 7: dst (aggr_get (arg 1))
// 8: aggr_slice_get (builtin_import aggr_slice_get)
// 9: aggr_slice_set (builtin_import aggr_slice_set)
// 10: elem (call (aggr_slice_get (src 0)))
// 11: dst2 (call (aggr_slice_set (dst 0 elem)))
// 12: dst_start (aggr_get (dst2 0))
// 13: dst_start2 (add (dst_start 1))
// 14: dst3 (aggr_set (dst2 0 dst_start2))
// 15: src_start (aggr_get (src 0))
// 16: src_start2 (add (src_start 1))
// 17: src2 (aggr_set (src 0 src_start2))
// identity (src2 dst3)
#[rustfmt::skip]
static AGGR_SLICE_COPY_STEP: Value = cera!(
    (
        [0]
        [1]
        aggr_slice_get
        aggr_slice_set
    )
    (
        (aggr_get ([5] [1]))
        (aggr_get ([5] [2]))
        (builtin_import [3])
        (builtin_import [4])
        (call ([8] ([6] [1])))
        (call ([9] ([7] [1] [10])))
        (aggr_get ([11] [1]))
        (add ([12] [2]))
        (aggr_set ([11] [1] [13]))
        (aggr_get ([6] [1]))
        (add ([15] [2]))
        (aggr_set ([6] [1] [16]))
        (identity ([17] [14]))
    )
);

// slice -> aggr
//
// 0: self
// 1: 0
// 2: aggr_slice_len
// 3: aggr_slice_copy
// 4: aggr_slice_buf
// 5: arg
// 6: aggr_slice_len (builtin_import aggr_slice_len)
// 7: aggr_slice_copy (builtin_import aggr_slice_copy)
// 8: aggr_slice_buf (builtin_import aggr_slice_buf)
// 9: len (call (aggr_slice_len arg))
// 10: buf (aggr_make len)
// 11: slice (identity (0 len buf))
// 12: slice2 (call (aggr_slice_copy (arg slice)))
// call (aggr_slice_buf slice2)
#[rustfmt::skip]
static AGGR_SLICE_TO_AGGR: Value = cera!(
    ([0] aggr_slice_len aggr_slice_copy aggr_slice_buf)
    (
        (builtin_import [2])
        (builtin_import [3])
        (builtin_import [4])
        (call ([6] [5]))
        (aggr_make [9])
        (identity ([1] [9] [10]))
        (call ([7] ([5] [11])))
        (call ([8] [12]))
    )
);

// bool -> !bool
//
// 0: self
// 1: true
// 2: false
// 3: identity
// 4: arg
// 5: true (builtin_import true)
// 6: false (builtin_import false)
// if (arg (identity false) (identity false))
#[rustfmt::skip]
static BOOL_NOT: Value = cera!(
    (true false identity)
    (
        (builtin_import [1])
        (builtin_import [2])
        (if ([4] ([3] [6]) ([3] [5])))
    )
);

// (bool expr) -> if bool ("some" {expr}) else ("none" ())
//
// 0: self
// 1: 0
// 2: 1
// 3: call
// 4: pipe
// 5: some_new
// 6: none
// 7: identity
// 8: arg
// 9: bool (aggr_get (arg 0))
// 10: expr (aggr_get (arg 1))
// 11: pipe (builtin_import pipe)
// 12: some_new (builtin_import some_new)
// 13: none (builtin_import none)
// if (bool (call (pipe (expr some_new))) (identity none))
#[rustfmt::skip]
static BOOL_THEN: Value = cera!(
    (
        [0]
        [1]
        call
        pipe
        some_new
        none
        identity
    )
    (
        (aggr_get ([8] [1]))
        (aggr_get ([8] [2]))
        (builtin_import [4])
        (builtin_import [5])
        (builtin_import [6])
        (if ([9]
            ([3] ([11] ([10] [12])))
            ([7] [13])
        ))
    )
);

// (bool value) -> if bool ("some" value) else ("none" ())
//
// 0: self
// 1: 1
// 2: bool_then
// 3: identity
// 4: arg
// 5: value (aggr_get (arg 1))
// 6: arg2 (aggr_set (arg 1 ("identity" value)))
// 7: bool_then (builtin_import bool_then)
// call (bool_then arg2)
#[rustfmt::skip]
static BOOL_THEN_SOME: Value = cera!(
    (
        [1]
        bool_then
        identity
    )
    (
        (aggr_get ([4] [1]))
        (aggr_set ([4] [1] ([3] [5])))
        (builtin_import [2])
        (call ([7] [6]))
    )
);

// value -> ("some" value)
//
// 0: self
// 1: some
// 2: arg
// identity (some arg)
#[rustfmt::skip]
static SOME_NEW: Value = cera!(
    (
        some
    )
    (
        (identity ([1] [2]))
    )
);

#[rustfmt::skip]
static NONE: Value = cera!(
    none ()
);

// (expr{->A} func{A->B}) -> B
//
// 0: self
// 1: 0
// 2: 1
// 3: arg
// 4: expr
// 5: func
// 6: res
// call (func res)
#[rustfmt::skip]
static PIPE: Value = cera!(
    ([0] [1])
    (
        (aggr_get ([3] [1]))
        (aggr_get ([3] [2]))
        (builtin_eval [4])
        (call ([5] [6]))
    )
);

// (func1{A->B} func2{B->C}) -> A -> C
//
// 0: self
// 1: closure
// 2: COMPOSE_FN
// 3: arg
// identity (closure COMPOSE_FN arg)
#[rustfmt::skip]
static COMPOSE: Value = cera!(
    (closure {COMPOSE_FN})
    (
        (identity ([1] [2] [3]))
    )
);

// ((func1{A->B} func2{B->C}) A) -> C
//
// 0: self
// 1: 0
// 2: 1
// 3: arg
// 4: captured (aggr_get (arg 0))
// 5: A (aggr_get (arg 1))
// 6: func1 (aggr_get (captured 0))
// 7: func2 (aggr_get (captured 1))
// 8: B (call (func1 A))
// call (func2 B)
#[rustfmt::skip]
static COMPOSE_FN: Value = cera!(
    ([0] [1])
    (
        (aggr_get ([3] [1]))
        (aggr_get ([3] [2]))
        (aggr_get ([4] [1]))
        (aggr_get ([4] [2]))
        (call ([6] [5]))
        (call ([7] [8]))
    )
);

#[rustfmt::skip]
static AGGR_VEC_INIT: Value = cera!(
    [0] ()
);

// ((len buf) value) -> (len buf)
//
// 0: self
// 1: 0
// 2: 1
// 3: aggr_vec_reserve
// 4: arg
// 5: vec (aggr_get (arg 0))
// 6: value (aggr_get (arg 1))
// 7: len (aggr_get (vec 0))
// 8: new_len (add (len 1))
// 9: aggr_vec_reserve (builtin_import aggr_vec_reserve)
// 10: vec2 (call (aggr_vec_reserve (vec new_len)))
// 11: buf (aggr_get (vec2 1))
// 12: buf2 (aggr_set (buf len value))
// identity (new_len buf2)
#[rustfmt::skip]
static AGGR_VEC_PUSH: Value = cera!(
    ([0] [1] aggr_vec_reserve)
    (
        (aggr_get ([4] [1]))
        (aggr_get ([4] [2]))
        (aggr_get ([5] [1]))
        (add ([7] [2]))
        (builtin_import [3])
        (call ([9] ([5] [8])))
        (aggr_get ([10] [2]))
        (aggr_set ([11] [7] [6]))
        (identity ([8] [12]))
    )
);

// ((len buf) desired_capacity) -> (len buf)
//
// 0: self
// 1: 0
// 2: 1
// 3: call
// 4: AGGR_VEC_RESIZE
// 5: identity
// 6: arg
// 7: vec (aggr_get (arg 0))
// 8: desired_capacity (aggr_get (arg 1))
// 9: buf (aggr_get (vec 1))
// 10: capacity (aggr_len buf)
// 11: len_cmp (cmp (capacity desired_capacity))
// 12: should_resize (eq (len_cmp 0))
// if (should_resize (call (AGGR_VEC_RESIZE arg)) (identity vec))
#[rustfmt::skip]
static AGGR_VEC_RESERVE: Value = cera!(
    ([0] [1] call {AGGR_VEC_RESIZE} identity)
    (
        (aggr_get ([6] [1]))
        (aggr_get ([6] [2]))
        (aggr_get ([7] [2]))
        (aggr_len [9])
        (cmp ([10] [8]))
        (eq ([11] [1]))
        (if ([12]
            ([3] ([4] [6]))
            ([5] [7])
        ))
    )
);

// ((len buf) desired_capacity) -> (len buf)
//
// 0: self
// 1: 0
// 2: 1
// 3: 2
// 4: max
// 5: aggr_slice_copy
// 6: aggr_slice_buf
// 7: arg
// 8: vec (aggr_get (arg 0))
// 9: desired_capacity (aggr_get (arg 1))
// 10: len (aggr_get (vec 0))
// 11: buf (aggr_get (vec 1))
// 12: current_capacity (aggr_len buf)
// 13: min_new_capacity (shl (current_capacity 1))
// 14: max (builtin_import max)
// 15: aggr_slice_copy (builtin_import aggr_slice_copy)
// 16: aggr_slice_buf (builtin_import aggr_slice_buf)
// 17: new_capacity (call (max (desired_capacity min_new_capacity)))
// 18: new_buf (aggr_make new_capacity)
// 19: new_buf_slice (call (aggr_slice_copy ((0 len buf) (0 len new_buf))))
// 20 new_buf2 (call (aggr_slice_buf new_buf_slice))
// identity (len new_buf2)
static AGGR_VEC_RESIZE: Value = cera!(
    ([0] [1] [2] max aggr_slice_copy aggr_slice_buf)
    (
        (aggr_get ([7] [1]))
        (aggr_get ([7] [2]))
        (aggr_get ([8] [1]))
        (aggr_get ([8] [2]))
        (aggr_len [11])
        (shl ([12] [2]))
        (builtin_import [4])
        (builtin_import [5])
        (builtin_import [6])
        (call ([14] ([9] [13])))
        (aggr_make [17])
        (call ([15] (([1] [10] [11]) ([1] [10] [18]))))
        (call ([16] [19]))
        (identity ([10] [20]))
    )
);

// (len buf) -> ((len buf) value)
//
// 0: self
// 1: 0
// 2: 1
// 3: arg
// 4: len (aggr_get (arg 0))
// 5: buf (aggr_get (arg 1))
// 6: len2 (sub (len 1))
// 7: value (aggr_get (buf len2))
// 8: buf2 (aggr_set (buf len2 ()))
// identity ((len2 buf2) value)
#[rustfmt::skip]
static AGGR_VEC_POP: Value = cera!(
    ([0] [1])
    (
        (aggr_get ([3] [1]))
        (aggr_get ([3] [2]))
        (sub ([4] [2]))
        (aggr_get ([5] [6]))
        (aggr_set ([5] [6] ()))
        (identity (([6] [8]) [7]))
    )
);

// (len buf) -> (0 len buf)
//
// 0: self
// 1: 0
// 2: 1
// 3: arg
// 4: len (aggr_get (arg 0))
// 5: buf (aggr_get (arg 1))
// identity (0 len buf)
#[rustfmt::skip]
static AGGR_VEC_BORROW_SLICE: Value = cera!(
    ([0] [1])
    (
        (aggr_get ([3] [1]))
        (aggr_get ([3] [2]))
        (identity ([1] [4] [5]))
    )
);

// (0 len buf) -> (len buf)
//
// 0: self
// 1: 1
// 2: 2
// 3: arg
// 4: len (aggr_get (arg 1))
// 5: buf (aggr_get (arg 2))
// identity (len buf)
#[rustfmt::skip]
static AGGR_VEC_UNBORROW_SLICE: Value = cera!(
    ([1] [2])
    (
        (aggr_get ([3] [1]))
        (aggr_get ([3] [2]))
        (identity ([4] [5]))
    )
);

// (bytes bytes) -> bytes
// 0: self
// 1: 0
// 2: 1
// 3: identity
// 4: arg
// 5: lhs (aggr_get (arg 0))
// 6: rhs (aggr_get (arg 1))
// 7: ord (cmp (lhs rhs))
// 8: lhs_smaller (eq (ord 0))
// if (lhs_smaller (identity lhs) (identity rhs))
#[rustfmt::skip]
static MIN: Value = cera!(
    ([0] [1] identity)
    (
        (aggr_get ([4] [1]))
        (aggr_get ([4] [2]))
        (cmp ([5] [6]))
        (eq ([7] [1]))
        (if ([8]
            ([3] [5])
            ([3] [6])
        ))
    )
);
// (bytes bytes) -> bytes
// 0: self
// 1: 0
// 2: 1
// 3: identity
// 4: arg
// 5: lhs (aggr_get (arg 0))
// 6: rhs (aggr_get (arg 1))
// 7: ord (cmp (lhs rhs))
// 8: lhs_smaller (eq (ord 0))
// if (lhs_smaller (identity rhs) (identity lhs))
#[rustfmt::skip]
static MAX: Value = cera!(
    ([0] [1] identity)
    (
        (aggr_get ([4] [1]))
        (aggr_get ([4] [2]))
        (cmp ([5] [6]))
        (eq ([7] [1]))
        (if ([8]
            ([3] [6])
            ([3] [5])
        ))
    )
);

// (constants expressions) -> (constants_raw expressions_raw)
//
// 0: self
// 1: 0
// 2: 1
// 3: FUNC_LOOKUP_STACK_MAKE
// 4: aggr_slice_to_aggr
// 5: aggr_map
// 6: GET_SECOND
// 7: aggr_slice_fold
// 8: aggr_vec_init
// 9: FUNC_PUSH_EXPRESSION
// 10: aggr_vec_borrow_slice
// 11: arg
// 12: constants (aggr_get (arg 0))
// 13: intermediates (aggr_get (arg 1))
// 14: aggr_slice_to_aggr (builtin_import aggr_slice_to_aggr)
// 15: aggr_map (builtin_import aggr_map)
// 16: aggr_slice_fold (builtin_import aggr_slice_fold)
// 17: aggr_vec_init (builtin_import aggr_vec_init)
// 18: aggr_vec_borrow_slice (builtin_import aggr_vec_borrow_slice)
// 19: lookup_stack (call (FUNC_LOOKUP_STACK_MAKE constants))
// 10: constants_aggr (call (AGGR_SLICE_TO_AGGR constants))
// 21: constants_raw (call (AGGR_MAP (constants_aggr GET_SECOND)))
// 22: res (call (AGGR_SLICE_FOLD (intermediates (AGGR_VEC_INIT lookup_stack) FUNC_PUSH_EXPRESSION)))
// 23: expressions_vec (aggr_get (res 0))
// 24: expressions_raw_slice (call (AGGR_VEC_BORROW_SLICE expressions_vec))
// 25: expressions_raw (call (AGGR_SLICE_TO_AGGR expressions_raw_slice))
// identity (constants_raw expressions_raw)
#[rustfmt::skip]
static FUNC_DESUGAR_BASIC: Value = cera!(
    (
        [0]
        [1]
        {FUNC_LOOKUP_STACK_MAKE}
        aggr_slice_to_aggr
        aggr_map
        {GET_SECOND}
        aggr_slice_fold
        aggr_vec_init
        {FUNC_PUSH_EXPRESSION}
        aggr_vec_borrow_slice
    )
    (
        (aggr_get ([11] [1]))
        (aggr_get ([11] [2]))
        (builtin_import [4])
        (builtin_import [5])
        (builtin_import [7])
        (builtin_import [8])
        (builtin_import [10])
        (call ([3] [12]))
        (call ([14] [12]))
        (call ([15] ([20] [6])))
        (call ([16] ([13] ([17] [19]) [9])))
        (aggr_get ([22] [1]))
        (call ([18] [23]))
        (call ([14] [24]))
        (identity ([21] [25]))
    )
);

// ((expressions_vec lookup_stack) (name expr)) -> (expression_vec lookup_stack)
//
// 0: self
// 1: 0
// 2: 1
// 3: FUNC_EXPRESSION_MAP
// 4: AGGR_VEC_PUSH
// 5: arg
// 6: acc (aggr_get (arg 0))
// 7: intermediate (aggr_get (arg 1))
// 8: expressions_vec (aggr_get (acc 0))
// 9: lookup_stack (aggr_get (acc 1))
// 10: name (aggr_get (intermediate 0))
// 11: expr (aggr_get (intermediate 1))
// 12: expr_raw (call (FUNC_EXPRESSION_MAP (lookup_stack expr)))
// 13: aggr_vec_push (builtin_import aggr_vec_push)
// 14: expressions_vec2 (call (AGGR_VEC_PUSH (expressions_vec expr_raw)))
// 15: lookup_stack2 (call (AGGR_VEC_PUSH (lookup_stack name)))
// identity (expressions_vec2 lookup_stack2)
#[rustfmt::skip]
static FUNC_PUSH_EXPRESSION: Value = cera!(
    ([0] [1] {FUNC_EXPRESSION_MAP} aggr_vec_push)
    (
        (aggr_get ([5] [1]))
        (aggr_get ([5] [2]))
        (aggr_get ([6] [1]))
        (aggr_get ([6] [2]))
        (aggr_get ([7] [1]))
        (aggr_get ([7] [2]))
        (call ([3] ([9] [11])))
        (builtin_import [4])
        (call ([13] ([8] [12])))
        (call ([13] ([9] [10])))
        (identity ([14] [15]))
    )
);

#[rustfmt::skip]
static GET_SECOND: Value = cera!(([1]) ((aggr_get ([2] [1]))));

// constants -> lookup_stack
//
// 0: self
// 1: AGGR_VEC_PUSH
// 2: AGGR_VEC_INIT
// 3: AGGR_SLICE_FOLD
// 4: "self"
// 5: FUNC_LOOKUP_STACK_PUSH
// 6: "arg"
// 7: arg
// 8: aggr_vec_push (builtin_import aggr_vec_push)
// 9: aggr_vec_init (builtin_import aggr_vec_init)
// 10: aggr_slice_fold (builtin_import aggr_slice_fold)
// 11: lookup_stack (call (aggr_vec_push (aggr_vec_init "self")))
// 12: lookup_stack2 (call (aggr_slice_fold (arg lookup_stack FUNC_LOOKUP_STACK_PUSH)))
// call (aggr_vec_push (lookup_stack2 "arg"))
#[rustfmt::skip]
static FUNC_LOOKUP_STACK_MAKE: Value = cera!(
    (
        aggr_vec_push
        aggr_vec_init
        aggr_slice_fold
        self
        {FUNC_LOOKUP_STACK_PUSH}
        arg
    )
    (
        (builtin_import [1])
        (builtin_import [2])
        (builtin_import [3])
        (call ([8] ([9] [4])))
        (call ([10] ([7] [11] [5])))
        (call ([8] ([12] [6])))
    )
);

// (lookup_stack (ident, _)) -> lookup_stack
//
// 0: self
// 1: 0
// 2: 1
// 3: aggr_vec_push
// 4: arg
// 5: lookup_stack (aggr_get (arg 0))
// 6: elem (aggr_get (arg 1))
// 7: ident (aggr_get (elem 0))
// 8: aggr_vec_push (builtin_import aggr_vec_push)
// call (aggr_vec_push (lookup_stack ident))
#[rustfmt::skip]
static FUNC_LOOKUP_STACK_PUSH: Value = cera!(
    ([0] [1] aggr_vec_push)
    (
        (aggr_get ([4] [1]))
        (aggr_get ([4] [2]))
        (aggr_get ([6] [1]))
        (builtin_import [3])
        (call ([8] ([5] [7])))
    )
);

// (lookup_stack (func args)) -> (raw_expr)
//
// 0: self
// 1: 0
// 2: 1
// 3: FUNC_ARGS_MAP
// 4: arg
// 5: lookup_stack (aggr_get (args 0))
// 6: expr (aggr_get (args 1))
// 7: func (aggr_get (expr 0))
// 8: args (aggr_get (expr 1))
// 9: args_raw (call (FUNC_ARGS_MAP (lookup_stack args)))
// identity (func args_raw)
#[rustfmt::skip]
static FUNC_EXPRESSION_MAP: Value = cera!(
    ([0] [1] {FUNC_ARGS_MAP})
    (
        (aggr_get ([4] [1]))
        (aggr_get ([4] [2]))
        (aggr_get ([6] [1]))
        (aggr_get ([6] [2]))
        (call ([3] ([5] [8])))
        (identity ([7] [9]))
    )
);
// (lookup_stack args) -> (raw_args)
//
// 0: self
// 1: 0
// 2: 1
// 3: type_aggr
// 4: closure
// 5: call
// 6: aggr_map
// 7: FUNC_LOOKUP_STACK_FIND
// 8: arg
// 9: lookup_stack (aggr_get (arg 0))
// 10: args (aggr_get (arg 1))
// 11: args_type (type_of args)
// 12: type_aggr (builtin_import type_aggr)
// 13: aggr_map (builtin_import aggr_map)
// 14: is_aggr (bytes_eq (args_type type_aggr))
// 15: aggr_closure (identity (closure self lookup_stack))
// if (is_aggr
//  (call (aggr_map (args aggr_closure)))
//  (call (FUNC_LOOKUP_STACK_FIND (lookup_stack args))))
#[rustfmt::skip]
static FUNC_ARGS_MAP: Value = cera!(
    (
        [0]
        [1]
        type_aggr
        closure
        call
        aggr_map
        {FUNC_LOOKUP_STACK_FIND}
    )
    (
        (aggr_get ([8] [1]))
        (aggr_get ([8] [2]))
        (type_of [10])
        (builtin_import [3])
        (builtin_import [6])
        (bytes_eq ([11] [12]))
        (identity ([4] [0] [9]))
        (if ([14]
            ([5] ([13] ([10] [15])))
            ([5] ([7] ([9] [10])))
        ))
    )
);

// (lookup_stack ident) -> num
//
// 0: self
// 1: 0
// 2: 1
// 3: aggr_vec_borrow_slice
// 4: aggr_slice_fold
// 5: closure
// 6: FUNC_LOOKUP_STACK_FIND_STEP
// 7: arg
// 8: lookup_stack (aggr_get (arg 0))
// 9: ident (aggr_get (arg 1))
// 10: aggr_vec_borrow_slice (builtin_import aggr_vec_borrow_slice)
// 11: aggr_slice_fold (builtin_import aggr_slice_fold)
// 12: slice (call (aggr_vec_borrow_slice lookup_stack))
// 13: res (call (aggr_slice_fold (slice (0 ()) (closure FUNC_LOOKUP_STACK_FIND_STEP ident))))
// aggr_get (res 1)
#[rustfmt::skip]
static FUNC_LOOKUP_STACK_FIND: Value = cera!(
    (
        [0]
        [1]
        aggr_vec_borrow_slice
        aggr_slice_fold
        closure
        {FUNC_LOOKUP_STACK_FIND_STEP}
    )
    (
        (aggr_get ([7] [1]))
        (aggr_get ([7] [2]))
        (builtin_import [3])
        (builtin_import [4])
        (call ([10] [8]))
        (call ([11] ([12] ([1] ()) ([5] [6] [9]))))
        (aggr_get ([13] [2]))
    )
);

// (ident ((curr_idx found_idx) this_ident)) -> (curr_idx found_idx)
//
// 0: self
// 1: 0
// 2: 1
// 3: identity
// 4: arg
// 5: ident (aggr_get (arg 0))
// 6: rhs (aggr_get (arg 1))
// 7: acc (aggr_get (rhs 0))
// 8: this_ident (aggr_get (rhs 1))
// 9: curr_idx (aggr_get (acc 0))
// 10: found_idx (aggr_get (acc 1))
// 11: bytes_eq (bytes_eq (ident this_ident))
// 12: found_idx2 (if (bytes_eq (identity curr_idx) (identity found_idx)))
// 13: curr_idx2 (add (curr_idx 1))
// identity (curr_idx2 found_idx2)
#[rustfmt::skip]
static FUNC_LOOKUP_STACK_FIND_STEP: Value = cera!(
    ([0] [1] identity)
    (
        (aggr_get ([4] [1]))
        (aggr_get ([4] [2]))
        (aggr_get ([6] [1]))
        (aggr_get ([6] [2]))
        (aggr_get ([7] [1]))
        (aggr_get ([7] [2]))
        (bytes_eq ([5] [8]))
        (if ([11]
            ([3] [9])
            ([3] [10])
        ))
        (add ([9] [2]))
        (identity ([13] [12]))
    )
);

#[rustfmt::skip]
static FUNC_DESUGAR_BASIC_AGGR: Value = cera!(
    call ((
        (
            func_desugar_basic
            (
                (
                    [0]
                    [5]
                    (
                        (zero [0])
                        (one [1])
                        (func_desugar_basic b"func_desugar_basic")
                        (aggr_slice_new b"aggr_slice_new")
                        (aggr_map b"aggr_map")
                    )
                )
                (
                    [0]
                    [5]
                    (
                        (func_desugar_basic (builtin_import func_desugar_basic))
                        (aggr_slice_new (builtin_import aggr_slice_new))
                        (aggr_map (builtin_import aggr_map))
                        (arg (call (aggr_map (arg aggr_slice_new))))
                        (return (call (func_desugar_basic arg)))
                    )
                )
            )
        )
        (
            (builtin_import [1])
            (call ([4] [2]))
        )
    ) ())
);

// (func func_arg) -> res
//
// 0: self
// 1: 0
// 2: 1
// 3: func_desugar_basic_aggr
// 4: arg
// 5: func_desugar_basic_aggr (builtin_import func_desugar_basic_aggr)
// 6: func_desugar_basic_aggr (builtin_eval func_desugar_basic_aggr)
// 7: func (aggr_get (arg 0))
// 8: func_arg (aggr_get (arg 1))
// 9: func_processed (call (func_desugar_basic_aggr func))
// call (func_processed func_arg)
#[rustfmt::skip]
static FUNC_DESUGAR_EXECUTE: Value = cera!(
    ([0] [1] func_desugar_basic_aggr)
    (
        (builtin_import [3])
        (builtin_eval [5])
        (aggr_get ([4] [1]))
        (aggr_get ([4] [2]))
        (call ([6] [7]))
        (call ([9] [8]))
    )
);

macro_rules! cera_desugared {
    ($($tt:tt)*) => {
        cera!(call((
            (($($tt)*) b"func_desugar_basic_aggr")
            (
                (builtin_import [2])
                (builtin_eval [4])
                (call ([5] [1]))
            )
        ) ()))
    };
}

// (state tree) -> state
//
// state: (macro_stack ..)
// macro_lookup: Vec<(name macro)>
// macro: (state rem_tree) -> state
#[rustfmt::skip]
static EXTENSIBLE_EVAL: Value = cera_desugared!(
    (
        (aggr_slice_fold b"aggr_slice_fold")
        (zero [0])
        (one [1])
        (step {EXTENSIBLE_EVAL_STEP})
    )
    (
        (state (aggr_get (arg zero)))
        (tree (aggr_get (arg one)))
        (macros_lookup (aggr_get (state zero)))
        (aggr_slice_fold (builtin_import aggr_slice_fold))
        (step (builtin_eval step))
        (return (call (aggr_slice_fold (tree state step))))
    )
);

// (state subtree) -> state
//
// state: (macro_stack ..)
// macro: (state rem_tree) -> state
#[rustfmt::skip]
static EXTENSIBLE_EVAL_STEP: Value = cera_desugared!(
    (
        (aggr_vec_borrow_slice b"aggr_vec_borrow_slice")
        (macro_lookup {MACRO_LOOKUP})
        (aggr_slice_get b"aggr_slice_get")
        (zero [0])
        (one [1])
    )
    (
        (state (aggr_get (arg zero)))
        (subtree (aggr_get (arg one)))
        (macro_stack (aggr_get (state zero)))
        (macro_lookup (builtin_eval macro_lookup))
        (aggr_slice_get (builtin_import aggr_slice_get))
        (macro_ident (call (aggr_slice_get (subtree zero))))
        (tree_start (aggr_get (subtree zero)))
        (tree_start (add (tree_start one)))
        (subtree (aggr_set (subtree zero tree_start)))
        (curr_macro (call (macro_lookup (macro_stack macro_ident))))
        (return (call (curr_macro (state subtree))))
    )
);

// (macro_stack ident) -> macro
// macro_stack: Vec<(ident macro)>
#[rustfmt::skip]
static MACRO_LOOKUP: Value = cera_desugared!(
    (
        (aggr_vec_borrow_slice b"aggr_vec_borrow_slice")
        (aggr_slice_fold b"aggr_slice_fold")
        (zero [0])
        (one [1])
        (macro_lookup_step {MACRO_LOOKUP_STEP})
    )
    (
        (aggr_vec_borrow_slice (builtin_import aggr_vec_borrow_slice))
        (aggr_slice_fold (builtin_import aggr_slice_fold))
        (macro_lookup_step (builtin_eval macro_lookup_step))
        (macro_stack (aggr_get (arg zero)))
        (ident (aggr_get (arg one)))
        (macro_slice (call (aggr_vec_borrow_slice macro_stack)))
        (res (call (aggr_slice_fold (macro_slice (ident ()) macro_lookup_step))))
        (return (aggr_get (res one)))
    )
);

// ((ident found) (curr_ident curr_macro)) -> (ident found)
#[rustfmt::skip]
static MACRO_LOOKUP_STEP: Value = cera_desugared!(
    (
        (zero [0])
        (one [1])
        (identity b"identity")
    )
    (
        (acc (aggr_get (arg zero)))
        (elem (aggr_get (arg one)))
        (ident (aggr_get (acc zero)))
        (found (aggr_get (acc one)))
        (curr_ident (aggr_get (elem zero)))
        (curr_macro (aggr_get (elem one)))
        (is_eq (bytes_eq (curr_ident ident)))
        (found (if (is_eq (identity curr_macro) (identity found))))
        (return (identity (ident found)))
    )
);
*/
