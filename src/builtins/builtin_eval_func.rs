use super::Value;

// 0: self
// 1: ATOM_VALUE_TO_EVALUATABLE
// 2: arg
// 3: evaluatable (call (ATOM_VALUE_TO_EVALUATABLE arg))
// 4: builtin_eval evaluatable
pub const BUILTIN_EVAL_FUNC: Value = Value::aggregate_const(
    const {
        &[
            Value::aggregate_const(const { &[ATOM_VALUE_TO_EVALUATABLE] }),
            Value::aggregate_const(
                const {
                    &[
                        Value::aggregate_const(
                            const {
                                &[
                                    Value::bytes_const(b"call"),
                                    Value::aggregate_const(
                                        const {
                                            &[
                                                Value::bytes_const(&[1]), // ATOM_VALUE_TO_EVALUATABLE
                                                Value::bytes_const(&[2]), // arg
                                            ]
                                        },
                                    ),
                                ]
                            },
                        ),
                        Value::aggregate_const(
                            const {
                                &[
                                    Value::bytes_const(b"builtin_eval"),
                                    Value::bytes_const(&[3]), // evaluatable
                                ]
                            },
                        ),
                    ]
                },
            ),
        ]
    },
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
const ATOM_VALUE_TO_EVALUATABLE: Value = Value::aggregate_const(
    const {
        &[
            Value::aggregate_const(
                const {
                    &[
                        Value::bytes_const(&[0]),
                        Value::bytes_const(&[1]),
                        AGGR_MAP,
                        Value::bytes_const(b"aggregate"),
                        Value::bytes_const(b"call"),
                        Value::bytes_const(b"identity"),
                    ]
                },
            ),
            Value::aggregate_const(
                const {
                    &[
                        Value::aggregate_const(
                            const {
                                &[
                                    Value::bytes_const(b"aggr_get"),
                                    Value::aggregate_const(
                                        const {
                                            &[
                                                Value::bytes_const(&[7]), // arg
                                                Value::bytes_const(&[1]), // 0
                                            ]
                                        },
                                    ),
                                ]
                            },
                        ),
                        Value::aggregate_const(
                            const {
                                &[
                                    Value::bytes_const(b"aggr_get"),
                                    Value::aggregate_const(
                                        const {
                                            &[
                                                Value::bytes_const(&[7]), // arg
                                                Value::bytes_const(&[2]), // 1
                                            ]
                                        },
                                    ),
                                ]
                            },
                        ),
                        Value::aggregate_const(
                            const {
                                &[
                                    Value::bytes_const(b"eq"),
                                    Value::aggregate_const(
                                        const {
                                            &[
                                                Value::bytes_const(&[8]), // type
                                                Value::bytes_const(&[4]), // "aggregate"
                                            ]
                                        },
                                    ),
                                ]
                            },
                        ),
                        Value::aggregate_const(
                            const {
                                &[
                                    Value::bytes_const(b"if"),
                                    Value::aggregate_const(
                                        const {
                                            &[
                                                Value::bytes_const(&[10]), // type == "aggregate"
                                                Value::aggregate_const(
                                                    const {
                                                        &[
                                                            Value::bytes_const(&[5]), // call
                                                            Value::aggregate_const(
                                                                const {
                                                                    &[
                                                                        Value::bytes_const(&[3]), // AGGR_MAP
                                                                        Value::aggregate_const(
                                                                            const {
                                                                                &[
                                                                        Value::bytes_const(&[9]), // value
                                                                        Value::bytes_const(&[0]), // self
                                                                    ]
                                                                            },
                                                                        ),
                                                                    ]
                                                                },
                                                            ),
                                                        ]
                                                    },
                                                ),
                                                Value::aggregate_const(
                                                    const {
                                                        &[
                                                            Value::bytes_const(&[6]), // identity
                                                            Value::bytes_const(&[9]), // value
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
            ),
        ]
    },
);

// 0: self
// 1: 0
// 2: 1
// 3: AGGR_MAP_INNER
// 4: arg
// 5: aggr
// 6: func
// call (AGGR_MAP_INNER, (aggr, func, 0))
const AGGR_MAP: Value = Value::aggregate_const(
    const {
        &[
            Value::aggregate_const(
                const {
                    &[
                        Value::bytes_const(&[0]),
                        Value::bytes_const(&[1]),
                        AGGR_MAP_INNER,
                    ]
                },
            ),
            Value::aggregate_const(
                const {
                    &[
                        Value::aggregate_const(
                            const {
                                &[
                                    Value::bytes_const(b"aggr_get"),
                                    Value::aggregate_const(
                                        const {
                                            &[
                                                Value::bytes_const(&[4]), // arg
                                                Value::bytes_const(&[1]), // 0
                                            ]
                                        },
                                    ),
                                ]
                            },
                        ),
                        Value::aggregate_const(
                            const {
                                &[
                                    Value::bytes_const(b"aggr_get"),
                                    Value::aggregate_const(
                                        const {
                                            &[
                                                Value::bytes_const(&[4]), // arg
                                                Value::bytes_const(&[2]), // 1
                                            ]
                                        },
                                    ),
                                ]
                            },
                        ),
                        Value::aggregate_const(
                            const {
                                &[
                                    Value::bytes_const(b"call"),
                                    Value::aggregate_const(
                                        const {
                                            &[
                                                Value::bytes_const(&[3]), // AGGR_MAP_INNER
                                                Value::aggregate_const(
                                                    const {
                                                        &[
                                                            Value::bytes_const(&[5]), // aggr
                                                            Value::bytes_const(&[6]), // func
                                                            Value::bytes_const(&[1]), // 0
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
            ),
        ]
    },
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
const AGGR_MAP_INNER: Value = Value::aggregate_const(
    const {
        &[
            Value::aggregate_const(
                const {
                    &[
                        Value::bytes_const(&[0]),
                        Value::bytes_const(&[1]),
                        Value::bytes_const(&[2]),
                        Value::bytes_const(b"identity"),
                        Value::bytes_const(b"call"),
                        AGGR_TAILFUNC,
                    ]
                },
            ),
            Value::aggregate_const(
                const {
                    &[
                        Value::aggregate_const(
                            const {
                                &[
                                    Value::bytes_const(b"aggr_get"),
                                    Value::aggregate_const(
                                        const {
                                            &[
                                                Value::bytes_const(&[7]), // arg
                                                Value::bytes_const(&[1]), // 0
                                            ]
                                        },
                                    ),
                                ]
                            },
                        ),
                        Value::aggregate_const(
                            const {
                                &[
                                    Value::bytes_const(b"aggr_get"),
                                    Value::aggregate_const(
                                        const {
                                            &[
                                                Value::bytes_const(&[7]), // arg
                                                Value::bytes_const(&[2]), // 1
                                            ]
                                        },
                                    ),
                                ]
                            },
                        ),
                        Value::aggregate_const(
                            const {
                                &[
                                    Value::bytes_const(b"aggr_get"),
                                    Value::aggregate_const(
                                        const {
                                            &[
                                                Value::bytes_const(&[7]), // arg
                                                Value::bytes_const(&[3]), // 2
                                            ]
                                        },
                                    ),
                                ]
                            },
                        ),
                        Value::aggregate_const(
                            const {
                                &[
                                    Value::bytes_const(b"aggr_len"),
                                    Value::bytes_const(&[8]), // aggr
                                ]
                            },
                        ),
                        Value::aggregate_const(
                            const {
                                &[
                                    Value::bytes_const(b"cmp"),
                                    Value::aggregate_const(
                                        const {
                                            &[
                                                Value::bytes_const(&[10]), // idx
                                                Value::bytes_const(&[11]), // len
                                            ]
                                        },
                                    ),
                                ]
                            },
                        ),
                        Value::aggregate_const(
                            const {
                                &[
                                    Value::bytes_const(b"if"),
                                    Value::aggregate_const(
                                        const {
                                            &[
                                                Value::bytes_const(&[12]), // idx == len
                                                Value::aggregate_const(
                                                    const {
                                                        &[
                                                            Value::bytes_const(&[4]), // identity
                                                            Value::bytes_const(&[8]), // aggr
                                                        ]
                                                    },
                                                ),
                                                Value::aggregate_const(
                                                    const {
                                                        &[
                                                            Value::bytes_const(&[5]), // call
                                                            Value::aggregate_const(
                                                                const {
                                                                    &[
                                                                        Value::bytes_const(&[6]), // tailfunc
                                                                        Value::aggregate_const(
                                                                            const {
                                                                                &[
                                                                        Value::bytes_const(&[8]), // aggr
                                                                        Value::bytes_const(&[9]), // func
                                                                        Value::bytes_const(&[10]), // idx
                                                                        Value::bytes_const(&[0]), // self
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
const AGGR_TAILFUNC: Value = Value::aggregate_const(
    const {
        &[
            Value::aggregate_const(
                const {
                    &[
                        Value::bytes_const(&[0]),
                        Value::bytes_const(&[1]),
                        Value::bytes_const(&[2]),
                        Value::bytes_const(&[3]),
                    ]
                },
            ),
            Value::aggregate_const(
                const {
                    &[
                        Value::aggregate_const(
                            const {
                                &[
                                    Value::bytes_const(b"aggr_get"),
                                    Value::aggregate_const(
                                        const {
                                            &[
                                                Value::bytes_const(&[5]), //arg
                                                Value::bytes_const(&[1]), // 0
                                            ]
                                        },
                                    ),
                                ]
                            },
                        ),
                        Value::aggregate_const(
                            const {
                                &[
                                    Value::bytes_const(b"aggr_get"),
                                    Value::aggregate_const(
                                        const {
                                            &[
                                                Value::bytes_const(&[5]), //arg
                                                Value::bytes_const(&[2]), // 1
                                            ]
                                        },
                                    ),
                                ]
                            },
                        ),
                        Value::aggregate_const(
                            const {
                                &[
                                    Value::bytes_const(b"aggr_get"),
                                    Value::aggregate_const(
                                        const {
                                            &[
                                                Value::bytes_const(&[5]), // arg
                                                Value::bytes_const(&[3]), // 2
                                            ]
                                        },
                                    ),
                                ]
                            },
                        ),
                        Value::aggregate_const(
                            const {
                                &[
                                    Value::bytes_const(b"aggr_get"),
                                    Value::aggregate_const(
                                        const {
                                            &[
                                                Value::bytes_const(&[5]), // arg
                                                Value::bytes_const(&[4]), // 3
                                            ]
                                        },
                                    ),
                                ]
                            },
                        ),
                        Value::aggregate_const(
                            const {
                                &[
                                    Value::bytes_const(b"aggr_get"),
                                    Value::aggregate_const(
                                        const {
                                            &[
                                                Value::bytes_const(&[6]), // aggr
                                                Value::bytes_const(&[8]), // idx
                                            ]
                                        },
                                    ),
                                ]
                            },
                        ),
                        Value::aggregate_const(
                            const {
                                &[
                                    Value::bytes_const(b"aggr_set"),
                                    Value::aggregate_const(
                                        const {
                                            &[
                                                Value::bytes_const(&[6]), // aggr
                                                Value::bytes_const(&[8]), // idx
                                                Value::aggregate_const(&[]),
                                            ]
                                        },
                                    ),
                                ]
                            },
                        ),
                        Value::aggregate_const(
                            const {
                                &[
                                    Value::bytes_const(b"call"),
                                    Value::aggregate_const(
                                        const {
                                            &[
                                                Value::bytes_const(&[7]),  // func
                                                Value::bytes_const(&[10]), // func_arg
                                            ]
                                        },
                                    ),
                                ]
                            },
                        ),
                        Value::aggregate_const(
                            const {
                                &[
                                    Value::bytes_const(b"aggr_set"),
                                    Value::aggregate_const(
                                        const {
                                            &[
                                                Value::bytes_const(&[6]),  // aggr
                                                Value::bytes_const(&[8]),  // idx
                                                Value::bytes_const(&[12]), // new_func_val
                                            ]
                                        },
                                    ),
                                ]
                            },
                        ),
                        Value::aggregate_const(
                            const {
                                &[
                                    Value::bytes_const(b"add"),
                                    Value::aggregate_const(
                                        const {
                                            &[
                                                Value::bytes_const(&[8]), // idx
                                                Value::bytes_const(&[2]), // 1
                                            ]
                                        },
                                    ),
                                ]
                            },
                        ),
                        Value::aggregate_const(
                            const {
                                &[
                                    Value::bytes_const(b"call"),
                                    Value::aggregate_const(
                                        const {
                                            &[
                                                Value::bytes_const(&[9]), // tail
                                                Value::aggregate_const(
                                                    const {
                                                        &[
                                                            Value::bytes_const(&[13]), // new_aggr2
                                                            Value::bytes_const(&[7]),  // func
                                                            Value::bytes_const(&[14]), // new_idx
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
            ),
        ]
    },
);
