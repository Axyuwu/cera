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

macro_rules! cera {
    ($($tt:tt)*) => {
        cera_expr!(($($tt)*))
    };
}
macro_rules! count {
    () => (0usize);
    ($x:tt $($xs:tt)*) => (1usize + count!($($xs)*))
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

#[derive(Debug, Clone, Copy)]
pub struct BuiltinImport;

impl BuiltinImport {
    pub(super) fn poll(self, value: Value) -> FuncThunk {
        FuncThunk::Done {
            value: match &**value.as_bytes() {
                b"builtin_eval_func" => BUILTIN_EVAL_FUNC.static_copy(),
                b"aggr_map" => AGGR_MAP.static_copy(),
                b"aggr_slice_get" => AGGR_SLICE_GET.static_copy(),
                b"aggr_slice_try_get" => AGGR_SLICE_TRY_GET.static_copy(),
                b"bool_then" => BOOL_THEN.static_copy(),
                b"bool_then_some" => BOOL_THEN_SOME.static_copy(),
                b"some_new" => SOME_NEW.static_copy(),
                b"none" => NONE.static_copy(),
                b"pipe" => PIPE.static_copy(),
                b"compose" => COMPOSE.static_copy(),
                b"bool_not" => BOOL_NOT.static_copy(),
                b"aggr_slice_new" => AGGR_SLICE_NEW.static_copy(),
                b"aggr_slice_buf" => AGGR_SLICE_BUF.static_copy(),
                b"aggr_slice_try_set" => AGGR_SLICE_TRY_SET.static_copy(),
                b"aggr_slice_set" => AGGR_SLICE_SET.static_copy(),
                b"aggr_slice_len" => AGGR_SLICE_LEN.static_copy(),
                b"aggr_slice_is_empty" => AGGR_SLICE_IS_EMPTY.static_copy(),
                b"aggr_slice_map_fold" => AGGR_SLICE_MAP_FOLD.static_copy(),
                b"aggr_slice_map" => AGGR_SLICE_MAP.static_copy(),
                b"aggr_slice_fold" => AGGR_SLICE_FOLD.static_copy(),
                b"aggr_slice_copy" => AGGR_SLICE_COPY.static_copy(),
                b"aggr_slice_to_aggr" => AGGR_SLICE_TO_AGGR.static_copy(),
                b"aggr_vec_borrow_slice" => AGGR_VEC_BORROW_SLICE.static_copy(),
                b"aggr_vec_unborrow_slice" => AGGR_VEC_UNBORROW_SLICE.static_copy(),
                b"aggr_vec_init" => AGGR_VEC_INIT.static_copy(),
                b"aggr_vec_push" => AGGR_VEC_PUSH.static_copy(),
                b"aggr_vec_reserve" => AGGR_VEC_RESERVE.static_copy(),
                b"aggr_vec_pop" => AGGR_VEC_POP.static_copy(),
                b"min" => MIN.static_copy(),
                b"max" => MAX.static_copy(),
                b"true" => TRUE.static_copy(),
                b"false" => FALSE.static_copy(),
                b"cmp_less" => CMP_LESS.static_copy(),
                b"cmp_equal" => CMP_EQUAL.static_copy(),
                b"cmp_greater" => CMP_GREATER.static_copy(),
                b"type_aggr" => TYPE_AGGR.static_copy(),
                b"type_bytes" => TYPE_BYTES.static_copy(),
                b"func_desugar_basic" => FUNC_DESUGAR_BASIC.static_copy(),
                b"func_desugar_basic_aggr" => FUNC_DESUGAR_BASIC_AGGR.static_copy(),
                b"extensible_eval" => EXTENSIBLE_EVAL.static_copy(),
                _ => panic!("invalid builtin_import argument: {value}"),
            },
        }
    }
    pub fn from_ident(ident: &[u8]) -> Option<Self> {
        match ident {
            b"builtin_import" => Some(Self),
            _ => return None,
        }
    }
}

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
// 3: AGGR_MAP
// 4: "aggregate"
// 5: "call"
// 6: "identity"
// 7: arg
// 8: type
// 9: value
// 10: type == "aggregate"
// if 10 (call (AGGR_MAP (value self)))) else (identity value)
#[rustfmt::skip]
static ATOM_VALUE_TO_EVALUATABLE: Value = cera!(
    ([0] [1] {AGGR_MAP} aggregate call identity)
    (
        (aggr_get ([7] [1]))
        (aggr_get ([7] [2]))
        (bytes_eq ([8] [4]))
        (if ([10]
            ([5] ([3] ([9] [0])))
            ([6] [9])
        ))
    )
);

// (aggr func) -> aggr
//
// 0: self
// 1: 0
// 2: 1
// 3: AGGR_SLICE_NEW
// 4: AGGR_SLICE_MAP
// 5: AGGR_SLICE_BUF
// 6: arg
// 7: aggr (aggr_get (arg 0))
// 8: func (aggr_get (arg 1))
// 9: slice (call (AGGR_SLICE_NEW aggr))
// 10: slice2 (call (AGGR_SLICE_MAP (slice func)))
// call (AGGR_SLICE_BUF slice2)
#[rustfmt::skip]
static AGGR_MAP: Value = cera!(
    (
        [0]
        [1]
        {AGGR_SLICE_NEW}
        {AGGR_SLICE_MAP}
        {AGGR_SLICE_BUF}
    )
    (
        (aggr_get ([6] [1]))
        (aggr_get ([6] [2]))
        (call ([3] [7]))
        (call ([4] ([9] [8])))
        (call ([5] [10]))
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
// 4: BOOL_THEN
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
// call (BOOL_THEN (is_in_bounds (aggr_get (buf idx_real))))
#[rustfmt::skip]
static AGGR_SLICE_TRY_GET: Value = cera!(
    ([0] [1] [2] {BOOL_THEN} aggr_get)
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
        (call ([4] ([15] ([5] ([11] [12])))))
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
// 4: BOOL_THEN_SOME
// 5: BOOL_NOT
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
// 20: is_not_in_bounds (BOOL_NOT is_in_bounds)
// 21: value_rem (call (BOOL_THEN_SOME (is_not_in_bounds value)))
// identity ((start end buf2) value_rem)
#[rustfmt::skip]
static AGGR_SLICE_TRY_SET: Value = cera!(
    (
        [0]
        [1]
        [2]
        {BOOL_THEN_SOME}
        {BOOL_NOT}
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
        (call ([5] [18]))
        (call ([4] ([20] [11])))
        (identity (([12] [13] [19]) [21]))
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
// 3: AGGR_SLICE_IS_EMPTY
// 4: identity
// 5: call
// 6: PIPE
// 7: AGGR_SLICE_MAP_FOLD_STEP
// 8: arg
// 9: slice (aggr_get (arg 0))
// 10: acc (aggr_get (arg 1))
// 11: is_empty (call (AGGR_SLICE_IS_EMPTY slice))
// if (is_empty
//      (identity (slice acc))
//      (call (PIPE ((call (AGGR_SLICE_MAP_FOLD_STEP arg)) self)))
// )
#[rustfmt::skip]
static AGGR_SLICE_MAP_FOLD_INNER: Value = cera!(
    (
        [0]
        [1]
        {AGGR_SLICE_IS_EMPTY}
        identity
        call
        {PIPE}
        {AGGR_SLICE_MAP_FOLD_STEP}
    )
    (
        (aggr_get ([8] [1]))
        (aggr_get ([8] [2]))
        (call ([3] [9]))
        (if ([11]
            ([4] ([9] [10]))
            ([5] ([6] (([5] ([7] [8])) [0])))
        ))
    )
);

// (slice{T} acc{A} func{(A T) -> (A O)}) -> (slice{T#len-=1} acc{A} func{(A T) -> (A O)})
//
// 0: self
// 1: 0
// 2: 1
// 3: 2
// 4: AGGR_SLICE_GET
// 5: AGGR_SLICE_SET
// 6: arg
// 7: slice (aggr_get (arg 0))
// 8: acc (aggr_get (arg 1))
// 9: func (aggr_get (arg 2))
// 10: elem (call (AGGR_SLICE_GET (slice 0)))
// 11: slice2 (call (AGGR_SLICE_SET (slice 0 ())))
// 12: func_ret (call (func (acc elem)))
// 13: acc2 (aggr_get (func_ret 0))
// 14: elem2 (aggr_get (func_ret 1))
// 15: slice3 (call (AGGR_SLICE_SET (slice2 0 elem2)))
// 16: start (aggr_get (slice3 0))
// 17: start2 (add (start 1))
// 18: slice4 (aggr_set (slice3 0 start2))
// identity (slice4 acc2 func)
#[rustfmt::skip]
static AGGR_SLICE_MAP_FOLD_STEP: Value = cera!(
    (
        [0]
        [1]
        [2]
        {AGGR_SLICE_GET}
        {AGGR_SLICE_SET}
    )
    (
        (aggr_get ([6] [1]))
        (aggr_get ([6] [2]))
        (aggr_get ([6] [3]))
        (call ([4] ([7] [1])))
        (call ([5] ([7] [1] ())))
        (call ([9] ([8] [10])))
        (aggr_get ([12] [1]))
        (aggr_get ([12] [2]))
        (call ([5] ([11] [1] [14])))
        (aggr_get ([15] [1]))
        (add ([16] [2]))
        (aggr_set ([15] [1] [17]))
        (identity ([18] [13] [9]))
    )
);

// (slice{T} func{T -> O}) -> slice{O}
//
// 0: self
// 1: 0
// 2: 1
// 3: AGGR_SLICE_MAP_FOLD
// 4: COMPOSE
// 5: ((1)((aggr_get (2 1))))
// 6: (()((identity (() 1))))
// 7: arg
// 8: slice (aggr_get (arg 0))
// 9: func (aggr_get (arg 1))
// 10: func2 (call (COMPOSE ([5] func)))
// 11: func3 (call (COMPOSE (func2 [6])))
// 12: res (call (AGGR_SLICE_MAP_FOLD (slice () func3)))
// aggr_get (res 0)
#[rustfmt::skip]
static AGGR_SLICE_MAP: Value = cera!(
    (
        [0]
        [1]
        {AGGR_SLICE_MAP_FOLD}
        {COMPOSE}
        (([1])((aggr_get ([2] [1]))))
        (()((identity (() [1]))))
    )
    (
        (aggr_get ([7] [1]))
        (aggr_get ([7] [2]))
        (call ([4] ([5] [9])))
        (call ([4] ([10] [6])))
        (call ([3] ([8] () [11])))
        (aggr_get ([12] [1]))
    )
);

// (slice{T} acc{A} func{(A T) -> A}) -> A
//
// 0: self
// 1: 0
// 2: 1
// 3: AGGR_SLICE_IS_EMPTY
// 4: identity
// 5: call
// 6: PIPE
// 7: AGGR_SLICE_FOLD_STEP
// 8: arg
// 9: slice (aggr_get (arg 0))
// 10: acc (aggr_get (arg 1))
// 11: is_empty (call (AGGR_SLICE_IS_EMPTY slice))
// if (is_empty
//      (identity acc)
//      (call (PIPE ((call (AGGR_SLICE_FOLD_STEP arg)) self)))
// )
#[rustfmt::skip]
static AGGR_SLICE_FOLD: Value = cera!(
    (
        [0]
        [1]
        {AGGR_SLICE_IS_EMPTY}
        identity
        call
        {PIPE}
        {AGGR_SLICE_FOLD_STEP}
    )
    (
        (aggr_get ([8] [1]))
        (aggr_get ([8] [2]))
        (call ([3] [9]))
        (if ([11]
            ([4] [10])
            ([5] ([6] (([5] ([7] [8])) [0])))
        ))
    )
);

// (slice{T} acc{A} func{(A T) -> A}) -> (slice{T#len-=1} acc{A} func{(A T) -> A})
//
// 0: self
// 1: 0
// 2: 1
// 3: 2
// 4: AGGR_SLICE_GET
// 5: arg
// 6: slice (aggr_get (arg 0))
// 7: acc (aggr_get (arg 1))
// 8: func (aggr_get (arg 2))
// 9: arg2 (aggr_set (arg 0 ()))
// 10: arg3 (aggr_set (arg2 1 ()))
// 11: elem (call (AGGR_SLICE_GET (slice 0)))
// 12: acc2 (call (func (acc elem)))
// 13: arg4 (aggr_set (arg3 1 acc2))
// 14: start (aggr_get (slice 0))
// 15: start2 (add (start 1))
// 16: slice2 (aggr_set (slice 0 start2))
// aggr_set (arg4 0 slice2)
#[rustfmt::skip]
static AGGR_SLICE_FOLD_STEP: Value = cera!(
    ([0] [1] [2] {AGGR_SLICE_GET})
    (
        (aggr_get ([5] [1]))
        (aggr_get ([5] [2]))
        (aggr_get ([5] [3]))
        (aggr_set ([5] [1] ()))
        (aggr_set ([9] [2] ()))
        (call ([4] ([6] [1])))
        (call ([8] ([7] [11])))
        (aggr_set ([10] [2] [12]))
        (aggr_get ([6] [1]))
        (add ([14] [2]))
        (aggr_set ([6] [1] [15]))
        (aggr_set ([13] [1] [16]))
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
// 9: is_empty (call (AGGR_SLICE_IS_EMPTY dst))
// 10: tail (call (COMPOSE (AGGR_SLICE_COPY_STEP self)))
// if (is_empty (identity dst) (call (tail arg)))
#[rustfmt::skip]
static AGGR_SLICE_COPY_INNER: Value = cera!(
    (
        [1]
        {AGGR_SLICE_IS_EMPTY}
        {COMPOSE}
        {AGGR_SLICE_COPY_STEP}
        identity
        call
    )
    (
        (aggr_get ([7] [1]))
        (call ([2] [8]))
        (call ([3] ([4] [0])))
        (if ([9]
            ([5] [8])
            ([6] ([10] [7]))
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
// 8: elem (call (AGGR_SLICE_GET (src 0)))
// 9: dst2 (call (AGGR_SLICE_SET (dst 0 elem)))
// 10: dst_start (aggr_get (dst2 0))
// 11: dst_start2 (add (dst_start 1))
// 12: dst3 (aggr_set (dst2 0 dst_start2))
// 13: src_start (aggr_get (src 0))
// 14: src_start2 (add (src_start 1))
// 15: src2 (aggr_set (src 0 src_start2))
// identity (src2 dst3)
#[rustfmt::skip]
static AGGR_SLICE_COPY_STEP: Value = cera!(
    (
        [0]
        [1]
        {AGGR_SLICE_GET}
        {AGGR_SLICE_SET}
    )
    (
        (aggr_get ([5] [1]))
        (aggr_get ([5] [2]))
        (call ([3] ([6] [1])))
        (call ([4] ([7] [1] [8])))
        (aggr_get ([9] [1]))
        (add ([10] [2]))
        (aggr_set ([9] [1] [11]))
        (aggr_get ([6] [1]))
        (add ([13] [2]))
        (aggr_set ([6] [1] [14]))
        (identity ([15] [12]))
    )
);

// slice -> aggr
//
// 0: self
// 1: 0
// 2: AGGR_SLICE_LEN
// 3: AGGR_SLICE_COPY
// 4: AGGR_SLICE_BUF
// 5: arg
// 6: len (call (AGGR_SLICE_LEN arg))
// 7: buf (aggr_make len)
// 8: slice (identity (0 len buf))
// 9: slice2 (call (AGGR_SLICE_COPY (arg slice)))
// call (AGGR_SLICE_BUF slice2)
#[rustfmt::skip]
static AGGR_SLICE_TO_AGGR: Value = cera!(
    ([0] {AGGR_SLICE_LEN} {AGGR_SLICE_COPY} {AGGR_SLICE_BUF})
    (
        (call ([2] [5]))
        (aggr_make [6])
        (identity ([1] [6] [7]))
        (call ([3] ([5] [8])))
        (call ([4] [9]))
    )
);

pub static TRUE: Value = cera_expr!([1]);
pub static FALSE: Value = cera_expr!([0]);
pub static CMP_LESS: Value = cera_expr!([0]);
pub static CMP_EQUAL: Value = cera_expr!([1]);
pub static CMP_GREATER: Value = cera_expr!([2]);
pub static TYPE_AGGR: Value = cera_expr!(aggr);
pub static TYPE_BYTES: Value = cera_expr!(bytes);

// bool -> !bool
//
// 0: self
// 1: TRUE
// 2: FALSE
// 3: identity
// 4: arg
// if (arg (identity FALSE) (identity TRUE))
#[rustfmt::skip]
static BOOL_NOT: Value = cera!(
    ({TRUE} {FALSE} identity)
    (
        (if ([4] ([3] [2]) ([3] [1])))
    )
);

// (bool expr) -> if bool ("some" {expr}) else ("none" ())
//
// 0: self
// 1: 0
// 2: 1
// 3: call
// 4: PIPE
// 5: SOME_NEW
// 6: NONE
// 7: identity
// 8: arg
// 9: bool (aggr_get (arg 0))
// 10: expr (aggr_get (arg 1))
// if (bool (call (PIPE (expr SOME_NEW))) (identity NONE))
#[rustfmt::skip]
static BOOL_THEN: Value = cera!(
    (
        [0]
        [1]
        call
        {PIPE}
        {SOME_NEW}
        {NONE}
        identity
    )
    (
        (aggr_get ([8] [1]))
        (aggr_get ([8] [2]))
        (if ([9]
            ([3] ([4] ([10] [5])))
            ([7] [6])
        ))
    )
);

// (bool value) -> if bool ("some" value) else ("none" ())
//
// 0: self
// 1: 1
// 2: BOOL_THEN
// 3: identity
// 4: arg
// 5: value (aggr_get (arg 1))
// 6: arg2 (aggr_set (arg 1 ("identity" value)))
// call (BOOL_THEN arg2)
#[rustfmt::skip]
static BOOL_THEN_SOME: Value = cera!(
    (
        [1]
        {BOOL_THEN}
        identity
    )
    (
        (aggr_get ([4] [1]))
        (aggr_set ([4] [1] ([3] [5])))
        (call ([2] [6]))
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
// 3: AGGR_VEC_RESERVE
// 4: arg
// 5: vec (aggr_get (arg 0))
// 6: value (aggr_get (arg 1))
// 7: len (aggr_get (vec 0))
// 8: new_len (add (len 1))
// 9: vec2 (call (AGGR_VEC_RESERVE (vec new_len)))
// 10: buf (aggr_get (vec2 1))
// 11: buf2 (aggr_set (buf len value))
// identity (new_len buf2)
#[rustfmt::skip]
static AGGR_VEC_PUSH: Value = cera!(
    ([0] [1] {AGGR_VEC_RESERVE})
    (
        (aggr_get ([4] [1]))
        (aggr_get ([4] [2]))
        (aggr_get ([5] [1]))
        (add ([7] [2]))
        (call ([3] ([5] [8])))
        (aggr_get ([9] [2]))
        (aggr_set ([10] [7] [6]))
        (identity ([8] [11]))
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
// 4: MAX
// 5: AGGR_SLICE_COPY
// 6: AGGR_SLICE_BUF
// 7: arg
// 8: vec (aggr_get (arg 0))
// 9: desired_capacity (aggr_get (arg 1))
// 10: len (aggr_get (vec 0))
// 11: buf (aggr_get (vec 1))
// 12: current_capacity (aggr_len buf)
// 13: min_new_capacity (shl (current_capacity 1))
// 14: new_capacity (call (MAX (desired_capacity min_new_capacity)))
// 15: new_buf (aggr_make new_capacity)
// 16: new_buf_slice (call (AGGR_SLICE_COPY ((0 len buf) (0 len new_buf))))
// 17 new_buf2 (call (AGGR_SLICE_BUF new_buf_slice))
// identity (len new_buf2)
static AGGR_VEC_RESIZE: Value = cera!(
    ([0] [1] [2] {MAX} {AGGR_SLICE_COPY} {AGGR_SLICE_BUF})
    (
        (aggr_get ([7] [1]))
        (aggr_get ([7] [2]))
        (aggr_get ([8] [1]))
        (aggr_get ([8] [2]))
        (aggr_len [11])
        (shl ([12] [2]))
        (call ([4] ([9] [13])))
        (aggr_make [14])
        (call ([5] (([1] [10] [11]) ([1] [10] [15]))))
        (call ([6] [16]))
        (identity ([10] [17]))
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
// 4: AGGR_SLICE_TO_AGGR
// 5: AGGR_MAP
// 6: GET_SECOND
// 7: AGGR_SLICE_FOLD
// 8: AGGR_VEC_INIT
// 9: FUNC_PUSH_EXPRESSION
// 10: AGGR_VEC_BORROW_SLICE
// 11: arg
// 12: constants (aggr_get (arg 0))
// 13: intermediates (aggr_get (arg 1))
// 14: lookup_stack (call (FUNC_LOOKUP_STACK_MAKE constants))
// 15: constants_aggr (call (AGGR_SLICE_TO_AGGR constants))
// 16: constants_raw (call (AGGR_MAP (constants_aggr GET_SECOND)))
// 17: res (call (AGGR_SLICE_FOLD (intermediates (AGGR_VEC_INIT lookup_stack) FUNC_PUSH_EXPRESSION)))
// 18: expressions_vec (aggr_get (res 0))
// 19: expressions_raw_slice (call (AGGR_VEC_BORROW_SLICE expressions_vec))
// 20: expressions_raw (call (AGGR_SLICE_TO_AGGR expressions_raw_slice))
// identity (constants_raw expressions_raw)
#[rustfmt::skip]
static FUNC_DESUGAR_BASIC: Value = cera!(
    (
        [0]
        [1]
        {FUNC_LOOKUP_STACK_MAKE}
        {AGGR_SLICE_TO_AGGR}
        {AGGR_MAP}
        {GET_SECOND}
        {AGGR_SLICE_FOLD}
        {AGGR_VEC_INIT}
        {FUNC_PUSH_EXPRESSION}
        {AGGR_VEC_BORROW_SLICE}
    )
    (
        (aggr_get ([11] [1]))
        (aggr_get ([11] [2]))
        (call ([3] [12]))
        (call ([4] [12]))
        (call ([5] ([15] [6])))
        (call ([7] ([13] ([8] [14]) [9])))
        (aggr_get ([17] [1]))
        (call ([10] [18]))
        (call ([4] [19]))
        (identity ([16] [20]))
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
// 13: expressions_vec2 (call (AGGR_VEC_PUSH (expressions_vec expr_raw)))
// 14: lookup_stack2 (call (AGGR_VEC_PUSH (lookup_stack name)))
// identity (expressions_vec2 lookup_stack2)
#[rustfmt::skip]
static FUNC_PUSH_EXPRESSION: Value = cera!(
    ([0] [1] {FUNC_EXPRESSION_MAP} {AGGR_VEC_PUSH})
    (
        (aggr_get ([5] [1]))
        (aggr_get ([5] [2]))
        (aggr_get ([6] [1]))
        (aggr_get ([6] [2]))
        (aggr_get ([7] [1]))
        (aggr_get ([7] [2]))
        (call ([3] ([9] [11])))
        (call ([4] ([8] [12])))
        (call ([4] ([9] [10])))
        (identity [8])
        (identity [9])
        (identity ([13] [14]))
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
// 8: lookup_stack (call (AGGR_VEC_PUSH (AGGR_VEC_INIT "self")))
// 9: lookup_stack2 (call (AGGR_SLICE_FOLD (arg lookup_stack FUNC_LOOKUP_STACK_PUSH)))
// call (AGGR_VEC_PUSH (lookup_stack2 "arg"))
#[rustfmt::skip]
static FUNC_LOOKUP_STACK_MAKE: Value = cera!(
    (
        {AGGR_VEC_PUSH}
        {AGGR_VEC_INIT}
        {AGGR_SLICE_FOLD}
        self
        {FUNC_LOOKUP_STACK_PUSH}
        arg
    )
    (
        (call ([1] ([2] [4])))
        (call ([3] ([7] [8] [5])))
        (call ([1] ([9] [6])))
    )
);

// (lookup_stack (ident, _)) -> lookup_stack
//
// 0: self
// 1: 0
// 2: 1
// 3: AGGR_VEC_PUSH
// 4: arg
// 5: lookup_stack (aggr_get (arg 0))
// 6: elem (aggr_get (arg 1))
// 7: ident (aggr_get (elem 0))
// call (AGGR_VEC_PUSH (lookup_stack ident))
#[rustfmt::skip]
static FUNC_LOOKUP_STACK_PUSH: Value = cera!(
    ([0] [1] {AGGR_VEC_PUSH})
    (
        (aggr_get ([4] [1]))
        (aggr_get ([4] [2]))
        (aggr_get ([6] [1]))
        (call ([3] ([5] [7])))
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
// 3: TYPE_AGGR
// 4: closure
// 5: call
// 6: AGGR_MAP
// 7: FUNC_LOOKUP_STACK_FIND
// 8: arg
// 9: lookup_stack (aggr_get (arg 0))
// 10: args (aggr_get (arg 1))
// 11: args_type (type_of args)
// 12: is_aggr (bytes_eq (args_type TYPE_AGGR))
// 13: aggr_closure (identity (closure self lookup_stack))
// if (is_aggr
//  (call (AGGR_MAP (args aggr_closure)))
//  (call (FUNC_LOOKUP_STACK_FIND (lookup_stack args))))
#[rustfmt::skip]
static FUNC_ARGS_MAP: Value = cera!(
    (
        [0]
        [1]
        {TYPE_AGGR}
        closure
        call
        {AGGR_MAP}
        {FUNC_LOOKUP_STACK_FIND} 
    )
    (
        (aggr_get ([8] [1]))
        (aggr_get ([8] [2]))
        (type_of [10])
        (bytes_eq ([11] [3]))
        (identity ([4] [0] [9]))
        (if ([12]
            ([5] ([6] ([10] [13])))
            ([5] ([7] ([9] [10])))
        ))
    )
);

// (lookup_stack ident) -> num
//
// 0: self
// 1: 0
// 2: 1
// 3: AGGR_VEC_BORROW_SLICE
// 4: AGGR_SLICE_FOLD (slice acc func)
// 5: closure
// 6: FUNC_LOOKUP_STACK_FIND_STEP
// 7: arg
// 8: lookup_stack (aggr_get (arg 0))
// 9: ident (aggr_get (arg 1))
// 10: slice (call (AGGR_VEC_BORROW_SLICE lookup_stack))
// 11: res (call (AGGR_VEC_SLICE_FOLD (slice (0 ()) (closure FUNC_LOOKUP_STACK_FIND_STEP ident))))
// aggr_get (res 1)
#[rustfmt::skip]
static FUNC_LOOKUP_STACK_FIND: Value = cera!(
    (
        [0]
        [1]
        {AGGR_VEC_BORROW_SLICE}
        {AGGR_SLICE_FOLD}
        closure
        {FUNC_LOOKUP_STACK_FIND_STEP}
    )
    (
        (aggr_get ([7] [1]))
        (aggr_get ([7] [2]))
        (call ([3] [8]))
        (call ([4] ([10] ([1] ()) ([5] [6] [9]))))
        (aggr_get ([11] [2]))
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
            {FUNC_DESUGAR_BASIC}
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
        ((call ([1] [2])))
    ) ())
);

// (func func_arg) -> res
//
// 0: self
// 1: 0
// 2: 1
// 3: FUNC_DESUGAR_BASIC_AGGR
// 4: arg
// 5: FUNC_DESUGAR_BASIC_AGGR2 (builtin_eval FUNC_DESUGAR_BASIC_AGGR)
// 6: func (aggr_get (arg 0))
// 7: func_arg (aggr_get (arg 1))
// 8: func_processed (call (FUNC_DESUGAR_BASIC_AGGR2 func))
// call (func_processed func_arg)
#[rustfmt::skip]
static FUNC_DESUGAR_EXECUTE: Value = cera!(
    ([0] [1] {FUNC_DESUGAR_BASIC_AGGR})
    (
        (builtin_eval [3])
        (aggr_get ([4] [1]))
        (aggr_get ([4] [2]))
        (call ([5] [6]))
        (call ([8] [7]))
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
