use std::{convert::TryFrom, marker::PhantomData};

struct RawVal(u64);

#[repr(u64)]
enum ValDiscrim {
    Primitive = 0,
    Complex = 1,
}

const VAL_FLAG_BITS: usize = 1;

impl RawVal {
    fn extract_discriminant(&self) -> ValDiscrim {
        let discrim = self.0 >> 64 - VAL_FLAG_BITS;
        match discrim {
            0 => ValDiscrim::Primitive,
            1 => ValDiscrim::Complex,
            _ => unreachable!(),
        }
    }
    fn extract_value(&self) -> u64 {
        self.0 & u64::MAX >> VAL_FLAG_BITS
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct ValPrimitive(u64);

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct TryToValError {}

impl TryFrom<u64> for ValPrimitive {
    type Error = TryToValError;

    fn try_from(value: u64) -> Result<Self, Self::Error> {
        (value.leading_zeros() >= 1)
            .then_some(Self(value))
            .ok_or(TryToValError {})
    }
}
impl From<ValPrimitive> for u64 {
    fn from(value: ValPrimitive) -> Self {
        value.0
    }
}

fn sign_extend(value: u64) -> i64 {
    let sign = value >> 64 - (VAL_FLAG_BITS + 1);
    match sign {
        0 => value as i64,
        1 => (value | u64::MAX << 64 - VAL_FLAG_BITS) as i64,
        _ => unreachable!(),
    }
}
fn sign_shrink(value: i64) -> Option<u64> {
    let lead = VAL_FLAG_BITS as u32 + 1;
    (value.leading_zeros() >= lead || value.leading_ones() >= lead)
        .then_some(value as u64 & u64::MAX >> VAL_FLAG_BITS)
}

impl TryFrom<i64> for ValPrimitive {
    type Error = TryToValError;

    fn try_from(value: i64) -> Result<Self, Self::Error> {
        sign_shrink(value).map(ValPrimitive).ok_or(TryToValError {})
    }
}
impl From<ValPrimitive> for i64 {
    fn from(value: ValPrimitive) -> Self {
        sign_extend(value.0)
    }
}

macro_rules! impl_primitive {
    ($basis:tt, $($prim:tt),*) => {
        $(impl TryFrom<$prim> for ValPrimitive {
            type Error = TryToValError;
            fn try_from(value: $prim) -> Result<Self, Self::Error> {
                (value as $basis).try_into()
            }
        }
        impl From<ValPrimitive> for $prim {
            fn from(value: ValPrimitive) -> Self {
                value.into()
            }
        })*
    };
}

impl_primitive!(u64, u8, u16, u32, usize);
impl_primitive!(i64, i8, i16, i32, isize);

pub struct ValCompound<'t> {
    _phantom: PhantomData<&'t [RawVal]>,
}

pub enum Val<'t> {
    Primitive(ValPrimitive),
    Compound(ValCompound<'t>),
    Func,
    NativeFunc,
}
