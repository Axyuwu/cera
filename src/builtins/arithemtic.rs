mod chain2;

use crate::builtins::{
    builtin_values::{CMP_EQUAL, CMP_GREATER, CMP_LESS},
    get_usize,
};
use anyhow::{ensure, Context as _, Result};
use std::{
    cmp::Ordering,
    ops::{Deref, DerefMut},
    sync::Arc,
};

use super::{
    builtin_values::{FALSE, TRUE},
    get_args, FuncThunk, Value,
};

/// A byte storage which inlines small amounts of data, and otherwise can be freely
/// converted to an Arc
#[repr(u8)]
enum ByteStorage {
    Inline {
        len: u8,
        bytes: [u8; 22],
    },
    /// Invariant: This pointer is a unique reference to the data of a uniquely owned Arc
    Arc(*mut [u8]),
}
impl ByteStorage {
    fn new(size: usize) -> Self {
        match size {
            size @ 0..=22 => Self::Inline {
                len: size as u8,
                bytes: [0; 22],
            },
            size @ 23.. => Self::Arc(
                // Why is there no way to do this safely without doing extra allocations?
                {
                    let mut arc = Arc::<[u8]>::new_uninit_slice(size);
                    // Each uninit value is visited and written to, therefor making them
                    // initialized
                    Arc::make_mut(&mut arc).iter_mut().for_each(|byte| {
                        byte.write(0);
                    });
                    // Therefor this pointer points to initialized, data that belongs to an
                    // Arc, which was just created and without clones which means it is
                    // unique
                    Arc::<[_]>::into_raw(arc) as *mut [u8]
                },
            ),
        }
    }
}
impl AsRef<[u8]> for ByteStorage {
    fn as_ref(&self) -> &[u8] {
        match self {
            Self::Inline { len, bytes } => &bytes[0..(*len as usize)],
            Self::Arc(bytes) => unsafe {
                // This is safe because of the invariant that bytes points to the data of
                // an Arc
                &**bytes
            },
        }
    }
}
impl Deref for ByteStorage {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        self.as_ref()
    }
}
impl DerefMut for ByteStorage {
    fn deref_mut(&mut self) -> &mut Self::Target {
        match self {
            ByteStorage::Inline { len, bytes } => &mut bytes[0..(*len as usize)],
            ByteStorage::Arc(bytes) => unsafe {
                // This is safe because of the invariant that bytes points to the data of
                // a uniquely owned Arc
                &mut **bytes
            },
        }
    }
}
impl Into<Arc<[u8]>> for ByteStorage {
    fn into(self) -> Arc<[u8]> {
        match self {
            Self::Inline { len, bytes } => bytes[0..(len as usize)].into(),
            Self::Arc(bytes) => unsafe {
                // This is safe because of the invariant that bytes points to the data of
                // an Arc
                Arc::from_raw(bytes)
            },
        }
    }
}

/// Operations are little-endian
#[derive(Clone, Copy, Debug)]
pub enum Arithmetic {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    DivFull,
    Cmp,
    Shl,
    Shr,
    Not,
    And,
    Or,
    Xor,
    Eq,
}

impl Arithmetic {
    /// Operations may give results with trailing zeros, to limit allocations when possible, by
    /// always allocating a computed upper bound of the size
    pub fn poll(self, value: Value) -> Result<FuncThunk> {
        Ok(FuncThunk::Done {
            value: match self {
                Self::Add => {
                    let [lhs, rhs] =
                        get_args(value)?.map(|e| e.into_bytes().context("in arithmetic add"));
                    let args = [lhs?, rhs?];
                    let [lhs, rhs] = args.each_ref().map(|e| trim_zeros(e));

                    let mut res = ByteStorage::new(std::cmp::max(lhs.len(), rhs.len()) + 1);

                    res.iter_mut()
                        .zip(
                            lhs.iter()
                                .chain(std::iter::repeat(&0))
                                .zip(rhs.iter().chain(std::iter::repeat(&0))),
                        )
                        .fold(false, |carry, (dst, (lhs, rhs))| {
                            let (r1, c1) = lhs.overflowing_add(*rhs);
                            let (r2, c2) = r1.overflowing_add(carry as u8);
                            *dst = r2;
                            c1 || c2
                        });

                    Value::bytes_move(res)
                }
                Self::Sub => {
                    let [lhs, rhs] = get_args(value)?.map(Value::into_bytes);
                    let args = [lhs?, rhs?];
                    let [lhs, rhs] = args.each_ref().map(|e| trim_zeros(e));

                    let mut res = ByteStorage::new(lhs.len());

                    let carry = res
                        .iter_mut()
                        .zip(
                            lhs.iter()
                                .chain(std::iter::repeat(&0))
                                .zip(rhs.iter().chain(std::iter::repeat(&0))),
                        )
                        .fold(false, |carry, (dst, (lhs, rhs))| {
                            let (r1, c1) = lhs.overflowing_sub(*rhs);
                            let (r2, c2) = r1.overflowing_sub(carry as u8);
                            *dst = r2;
                            c1 || c2
                        });

                    ensure!(
                        !carry,
                        "sub underflowed, left argument was less than right one"
                    );

                    Value::bytes_move(res)
                }
                Self::Mul => {
                    let [lhs, rhs] = get_args(value)?.map(Value::into_bytes);
                    let args = [lhs?, rhs?];
                    let [lhs, rhs] = args.each_ref().map(|e| trim_zeros(e));

                    let mut res = ByteStorage::new(lhs.len() + rhs.len());

                    lhs.iter().enumerate().for_each(|(i, lhs)| {
                        rhs.iter().chain(std::iter::once(&0)).enumerate().fold(
                            0u8,
                            |carry, (j, rhs)| {
                                let dst = &mut res[i + j];
                                // Doesn't overflow, as with all max values:
                                // 255 + 255 + (255 * 255) = 65535 (=u16::MAX)
                                let [curr, carry] =
                                    (*dst as u16 + carry as u16 + (*lhs as u16 * *rhs as u16))
                                        .to_le_bytes();
                                *dst = curr;
                                carry
                            },
                        );
                    });

                    Value::bytes_move(res)
                }
                Self::Div => Value::bytes_move(div_full(value)?.0),
                Self::Rem => Value::bytes_move(div_full(value)?.1),
                Self::DivFull => Value::aggregate_move(
                    Into::<[ByteStorage; 2]>::into(div_full(value)?).map(Value::bytes_move),
                ),
                Self::Cmp => {
                    use Ordering::*;
                    fn ord_to_val(ord: Ordering) -> Value {
                        match ord {
                            Less => CMP_LESS,
                            Equal => CMP_EQUAL,
                            Greater => CMP_GREATER,
                        }
                    }

                    let [lhs, rhs] = get_args(value)?.map(Value::into_bytes);
                    let args = [lhs?, rhs?];
                    let [lhs, rhs] = args.each_ref().map(|e| trim_zeros(e));
                    match lhs.len().cmp(&rhs.len()) {
                        Equal => ord_to_val(lhs.iter().rev().cmp(rhs.iter().rev())),
                        o => ord_to_val(o),
                    }
                }
                Self::Shl => {
                    let [lhs, rhs] = get_args(value)?;
                    let offset = get_usize(rhs.as_bytes()?)?;
                    let lhs = trim_zeros(lhs.as_bytes()?);

                    let (bits, bytes) = (offset % 8, offset / 8);

                    let mut res = ByteStorage::new(lhs.len() + bytes + 1);

                    res.iter_mut()
                        .skip(bytes)
                        .zip(shl_mod8_iter(lhs, bits as u32))
                        .for_each(|(dst, src)| *dst = src);

                    Value::bytes_move(res)
                }
                Self::Shr => {
                    let [lhs, rhs] = get_args(value)?;
                    let offset = get_usize(rhs.as_bytes()?)?;
                    let lhs = trim_zeros(lhs.as_bytes()?);

                    let (bits, bytes) = (offset % 8, offset / 8);

                    let mut res = ByteStorage::new(lhs.len().saturating_sub(bytes));

                    res.iter_mut()
                        .zip(shr_mod8_iter(
                            lhs.get(bytes..).unwrap_or_default(),
                            bits as u32,
                        ))
                        .for_each(|(dst, src)| *dst = src);

                    Value::bytes_move(res)
                }
                Self::Not => {
                    let mut bytes = value;
                    bytes
                        .as_bytes_mut()?
                        .make_mut()
                        .iter_mut()
                        .for_each(|b| *b = !*b);
                    bytes
                }
                Self::And => binary_bytewise(value, std::ops::BitAnd::bitand)
                    .context("in arithmetic function and")?,
                Self::Or => binary_bytewise(value, std::ops::BitOr::bitor)
                    .context("in arithmetic function or")?,
                Self::Xor => binary_bytewise(value, std::ops::BitXor::bitxor)
                    .context("in arithmetic function xor")?,
                Self::Eq => {
                    let [lhs, rhs] = get_args(value)?.map(Value::into_bytes);
                    let args = [lhs?, rhs?];
                    let [lhs, rhs] = args.each_ref().map(|e| trim_zeros(e));

                    match lhs == rhs {
                        true => TRUE,
                        false => FALSE,
                    }
                }
            },
        })
    }
    pub fn from_ident(ident: &[u8]) -> Option<Self> {
        Some(match ident {
            b"add" => Self::Add,
            b"sub" => Self::Sub,
            b"mul" => Self::Mul,
            b"div" => Self::Div,
            b"rem" => Self::Rem,
            b"div_full" => Self::DivFull,
            b"cmp" => Self::Cmp,
            b"shl" => Self::Shl,
            b"shr" => Self::Shr,
            b"not" => Self::Not,
            b"and" => Self::And,
            b"or" => Self::Or,
            b"xor" => Self::Xor,
            b"eq" => Self::Eq,
            _ => return None,
        })
    }
}

fn binary_bytewise(value: Value, func: impl Fn(u8, u8) -> u8) -> Result<Value> {
    let [lhs, rhs] = get_args(value)?.map(Value::into_bytes);
    let (mut lhs, rhs) = (lhs?, rhs?);

    let (mut out, const_side) = if let Some(_) = lhs.get_mut() {
        (lhs, rhs)
    } else {
        (rhs, lhs)
    };
    out.make_mut()
        .iter_mut()
        .zip(&*const_side)
        .for_each(|(lhs, rhs)| *lhs = func(*lhs, *rhs));
    Ok(Value::Bytes(out))
}

// (Quotient, Remainder)
fn div_full(value: Value) -> Result<(ByteStorage, ByteStorage)> {
    let [lhs, rhs] = get_args(value)?.map(Value::into_bytes);
    let args = [lhs?, rhs?];
    let [dividend, divisor] = args.each_ref().map(|e| trim_zeros(e));

    ensure!(divisor.len() != 0, "div by zero, right argument was zero");

    if dividend.len() < divisor.len() {
        return Ok((ByteStorage::new(0), ByteStorage::new(0)));
    }

    let mut quo = ByteStorage::new(dividend.len() - divisor.len() + 1);
    let mut rem = ByteStorage::new(divisor.len() + 1);

    let (dividend_tail, rem_init) = dividend.split_at(dividend.len() - divisor.len());

    rem[..rem_init.len()].copy_from_slice(rem_init);

    let mut dividend_iter = dividend_tail.iter().rev();

    quo.iter_mut().rev().for_each(|dst| {
        *dst = div_partial(&mut rem, divisor);
        if let Some(next_byte) = dividend_iter.next() {
            let range = ..(rem.len() - 1);
            rem.copy_within(range, 1);
            rem[0] = *next_byte;
        }
    });

    Ok((quo, rem))
}

fn div_partial(rem: &mut [u8], divisor: &[u8]) -> u8 {
    assert_eq!(rem.len(), divisor.len() + 1);
    assert!(!divisor.is_empty());

    (0..8).rev().fold(0, |res, shift| {
        res | ((try_sub_shift(rem, divisor, shift) as u8) << shift)
    })
}

fn try_sub_shift(lhs: &mut [u8], rhs: &[u8], bits: u32) -> bool {
    assert_eq!(lhs.len(), rhs.len() + 1);
    assert!(bits < 8);

    if lhs
        .iter()
        .zip(shl_mod8_iter(rhs, bits))
        .rev()
        .find_map(|(lhs, rhs)| match lhs.cmp(&rhs) {
            Ordering::Less => Some(true),
            Ordering::Equal => None,
            Ordering::Greater => Some(false),
        })
        .is_some_and(std::convert::identity)
    {
        return false;
    }

    lhs.iter_mut()
        .zip(shl_mod8_iter(rhs, bits))
        .fold(false, |carry, (lhs, rhs)| {
            let (r1, c1) = lhs.overflowing_sub(rhs);
            let (r2, c2) = r1.overflowing_sub(carry as u8);
            *lhs = r2;
            c1 | c2
        });
    true
}

fn shl_mod8_iter<'t>(
    val: &'t [u8],
    bits: u32,
) -> impl Iterator<Item = u8> + DoubleEndedIterator + ExactSizeIterator + 't {
    assert!(bits < 8);

    let mask = move |(small, big): (&u8, &u8)| {
        (small.checked_shr(8 - bits).unwrap_or_default()) | (big << bits)
    };
    chain2::Chain2 {
        inner: std::iter::once(&0).chain(val),
    }
    .zip(chain2::Chain2 {
        inner: val.iter().chain(std::iter::once(&0)),
    })
    .map(mask)
}
fn shr_mod8_iter<'t>(
    val: &'t [u8],
    bits: u32,
) -> impl Iterator<Item = u8> + DoubleEndedIterator + ExactSizeIterator + 't {
    assert!(bits < 8);

    let mask = move |(small, big): (&u8, &u8)| {
        (small >> bits) | (big.checked_shl(8 - bits).unwrap_or_default())
    };
    val.iter()
        .zip(chain2::Chain2 {
            inner: val.iter().skip(1).chain([0u8].iter()),
        })
        .map(mask)
}

pub(crate) fn trim_zeros(mut slice: &[u8]) -> &[u8] {
    while let [head @ .., 0] = slice {
        slice = head
    }
    slice
}
