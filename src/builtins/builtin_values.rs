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
                b"aggr_vec_slice" => AGGR_VEC_SLICE.static_copy(),
                b"min" => MIN.static_copy(),
                b"max" => MAX.static_copy(),
                b"true" => TRUE.static_copy(),
                b"false" => FALSE.static_copy(),
                b"cmp_less" => CMP_LESS.static_copy(),
                b"cmp_equal" => CMP_EQUAL.static_copy(),
                b"cmp_greater" => CMP_GREATER.static_copy(),
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

// 0: self
// 1: ATOM_VALUE_TO_EVALUATABLE
// 2: arg
// 3: evaluatable (call (ATOM_VALUE_TO_EVALUATABLE arg))
// 4: builtin_eval evaluatable
#[rustfmt::skip]
pub static BUILTIN_EVAL_FUNC: Value = cera!(
    ({ ATOM_VALUE_TO_EVALUATABLE })
    (
        (call ([1] [2]))
        (builtin_eval [3])
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

// slice -> self
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

pub static TRUE: Value = cera_expr!([1]);
pub static FALSE: Value = cera_expr!([0]);
pub static CMP_LESS: Value = cera_expr!([0]);
pub static CMP_EQUAL: Value = cera_expr!([1]);
pub static CMP_GREATER: Value = cera_expr!([2]);

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
// 1: 0
// 2: 1
// 3: 2
// 4: 3
// 5: 4
// 6: call
// 7: arg
// 8: func1
// 9: func2
// identity ((func1 func2)(
//  (call (1 3))
//  (call (2 4))
// ))
#[rustfmt::skip]
static COMPOSE: Value = cera!(
    ([0] [1] [2] [3] [4] call)
    (
        (aggr_get ([7] [1]))
        (aggr_get ([7] [2]))
        (identity (([8] [9])(
            ([6] ([2] [4]))
            ([6] ([3] [5]))
        )))
    )
);

#[rustfmt::skip]
static AGGR_VEC_INIT: Value = cera!(
    [0] ()
);

#[rustfmt::skip]
static AGGR_VEC_PUSH: Value = cera!();

// ((len buf) desired_len) -> (len buf)
//
// 0: self
//  0
//  1
//  vec
//  arg
//  len
//  buf
//  desired_len
//  len_cmp (cmp (len desired_len))
//  should_resize (eq (len_cmp 0))
//  if (should_resize () (identity (len buf)))
#[rustfmt::skip]
static AGGR_VEC_RESERVE: Value = cera!(

);

// ((len buf) desired_len) -> (len buf)
//
// 0: self
//  0
//  1
//  MAX
//  arg
//  vec (aggr_get (arg 0))
//  len (aggr_get (vec 0))
//  buf (aggr_get (vec 1))
//  desired_len (aggr_get (arg 1))
//  min_new_len (shl (len 1))
//  new_len (MAX (desired_len min_new_len))
//  new_buf (aggr_make new_len)
static AGGR_VEC_RESIZE: Value = cera!();

// (len buf) -> ((len buf) value)
#[rustfmt::skip]
static AGGR_VEC_POP: Value = cera!(
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
static AGGR_VEC_SLICE: Value = cera!(
    ([0] [1])
    (
        (aggr_get ([3] [1]))
        (aggr_get ([3] [2]))
        (identity ([1] [4] [5]))
    )
);

#[rustfmt::skip]
static AGGR_VEC_BORROW_SLICE: Value = cera!();

#[rustfmt::skip]
static AGGR_VEC_UNBORROW_SLICE: Value = cera!();

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
        (cmp [5] [6])
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
        (cmp [5] [6])
        (eq ([7] [1]))
        (if ([8]
            ([3] [6])
            ([3] [5])
        ))
    )
);

#[rustfmt::skip]
static FUNC_SYNTAX_DESUGAR_BASIC: Value = cera!();
