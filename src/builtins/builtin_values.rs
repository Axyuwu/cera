use super::Value;

macro_rules! cera {
    ($($tt:tt)*) => {
        cera_inner!(($($tt)*))
    };
}
macro_rules! cera_inner {
    ({$ident:ident}) => {
        $ident
    };
    ([$expr:expr]) => {
        const { Value::bytes_const( const { &usize::to_le_bytes($expr) })}
    };
    ($ident:ident) => {
        const { Value::bytes_const(unsafe { std::mem::transmute(stringify!($ident)) }) }
    };
    ($literal:literal) => {
        const { Value::bytes_const($literal) }
    };
    (($($tt:tt)*)) => {
        const {
            Value::aggregate_const(const {&[$(cera_inner!($tt)),*]})
        }
    }
}

// 0: self
// 1: ATOM_VALUE_TO_EVALUATABLE
// 2: arg
// 3: evaluatable (call (ATOM_VALUE_TO_EVALUATABLE arg))
// 4: builtin_eval evaluatable
#[rustfmt::skip]
pub const BUILTIN_EVAL_FUNC: Value = cera!(
    ({ ATOM_VALUE_TO_EVALUATABLE })
    (
        (call ([1] [2]))
        (builtin_eval [3] )
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
// if 10 (call (self, value))) else (identity value)
#[rustfmt::skip]
const ATOM_VALUE_TO_EVALUATABLE: Value = cera!(
    ([0] [1] {AGGR_MAP} aggregate call identity)
    (
        (aggr_get ([7] [1]))
        (aggr_get ([7] [2]))
        (eq ([8] [4]))
        (if ([10]
            ([5] ([3] ([9] [0])))
            ([6] [9])
        ))
    )
);

// 0: self
// 1: 0
// 2: 1
// 3: AGGR_MAP_INNER
// 4: arg
// 5: aggr
// 6: func
// call (AGGR_MAP_INNER, (aggr, func, 0))
#[rustfmt::skip]
const AGGR_MAP: Value = cera!(
    ([0] [1] {AGGR_MAP_INNER})
    (
        (aggr_get ([4] [1]))
        (aggr_get ([4] [2]))
        (call ([3] ([5] [6] [1])))
    )
);

// 0: self
// 1: 0
// 2: 1
// 3: 2
// 4: "identity"
// 5: "call"
// 6: tailfunc
// 7: arg  (aggr, func, idx)
// 8: aggr
// 9: func
// 10: idx
// 11: aggr_len aggr
// 12: cmp (idx, len) (0: idx < len, 1: idx == len)
// if 12 (aggr) else (tailfunc (aggr, func, idx, self))
#[rustfmt::skip]
const AGGR_MAP_INNER: Value = cera!(
    ([0] [1] [2] identity call {AGGR_TAILFUNC})
    (
        (aggr_get ([7] [1]))
        (aggr_get ([7] [2]))
        (aggr_get ([7] [3]))
        (aggr_len [8])
        (cmp ([10] [11]))
        (if ([12]
            ([4] [8])
            ([5] ([6] ([8] [9] [10] [0])))
        ))
    )
);

// 0: self
// 1: 0
// 2: 1
// 3: 2
// 4: 3
// 5: arg
// 6: aggr
// 7: func
// 8: idx
// 9: tail
// 10: func_arg ("aggr_get" (aggr, idx))
// 11: new_aggr ("aggr_set" (aggr, idx, ()))
// 12: new_func_val ("call" (func, func_arg))
// 13: new_aggr2 ("aggr_set" (new_aggr, idx, new_func_val))
// 14: new_idx ("add" (idx, 1))
// tail (new_aggr2, func, new_idx)
#[rustfmt::skip]
const AGGR_TAILFUNC: Value = cera!(
    ([0] [1] [2] [3])
    (
        (aggr_get ([5] [1]))
        (aggr_get ([5] [2]))
        (aggr_get ([5] [3]))
        (aggr_get ([5] [4]))
        (aggr_get ([6] [8]))
        (aggr_set ([6] [8] ()))
        (call ([7] [10]))
        (aggr_set ([6] [8] [12]))
        (add ([8] [2]))
        (call ([9] ([13] [7] [14])))
    )
);
