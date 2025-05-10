use crate::builtins::get_usize;
use anyhow::{ensure, Context as _, Result};
use std::{
    cmp::Ordering,
    ops::{Deref, DerefMut},
    sync::Arc,
};

use super::{get_args, Value};

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
    Cmp,
    Shl,
    Shr,
    Not,
    And,
    Or,
    Xor,
}

impl Arithmetic {
    /// Operations may give results with trailing zeros, to limit allocations when possible, by
    /// always allocating a computed upper bound of the size
    pub fn poll(self, value: Value) -> Result<Value> {
        Ok(match self {
            Self::Add => {
                let [lhs, rhs] = get_args(value)?.map(Value::into_bytes);
                let args = [lhs?, rhs?];
                let [lhs, rhs] = args.each_ref().map(|e| trim_zeros(e));

                let mut res = ByteStorage::new(std::cmp::max(lhs.len(), rhs.len()) + 1);
                res.iter_mut()
                    .enumerate()
                    .fold(false, |carry, (idx, byte)| {
                        let [lhs, rhs] =
                            [lhs, rhs].map(|s| s.get(idx).copied().unwrap_or_default());
                        let (r1, c1) = lhs.overflowing_add(rhs);
                        let (res, c2) = r1.overflowing_add(carry as u8);
                        *byte = res;
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
                    .enumerate()
                    .fold(false, |carry, (idx, byte)| {
                        let [lhs, rhs] =
                            [lhs, rhs].map(|s| s.get(idx).copied().unwrap_or_default());
                        let (r1, c1) = lhs.overflowing_sub(rhs);
                        let (res, c2) = r1.overflowing_sub(carry as u8);
                        *byte = res;
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
            Self::Div => {
                let [lhs, rhs] = get_args(value)?.map(Value::into_bytes);
                let args = [lhs?, rhs?];
                let [lhs, rhs] = args.each_ref().map(|e| trim_zeros(e));

                ensure!(rhs.len() != 0, "div by zero, right argument was zero");

                let mut res = ByteStorage::new(lhs.len() - rhs.len() + 1);

                todo!()
            }
            Self::Rem => {
                let [lhs, rhs] = get_args(value)?.map(Value::into_bytes);
                let args = [lhs?, rhs?];
                let [lhs, rhs] = args.each_ref().map(|e| trim_zeros(e));

                ensure!(rhs.len() != 0, "rem by zero, right argument was zero");

                let mut res = ByteStorage::new(rhs.len());

                todo!()
            }
            Self::Cmp => {
                use Ordering::*;
                fn ord_to_val(ord: Ordering) -> Value {
                    const LESS: Value = Value::bytes_const(&[0]);
                    const EQUAL: Value = Value::bytes_const(&[1]);
                    const GREATER: Value = Value::bytes_const(&[2]);
                    match ord {
                        Less => LESS,
                        Equal => EQUAL,
                        Greater => GREATER,
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

                let mask = |[small, big]: [u8; 2]| (small >> (8 - bits)) | (big << bits);

                res.iter_mut()
                    .skip(bytes)
                    .enumerate()
                    .for_each(|(idx, byte)| {
                        *byte = mask([
                            idx.checked_sub(1).map(|i| lhs[i]).unwrap_or(0u8),
                            lhs.get(idx).copied().unwrap_or_default(),
                        ]);
                    });

                Value::bytes_move(res)
            }
            Self::Shr => {
                let [lhs, rhs] = get_args(value)?;
                let offset = get_usize(rhs.as_bytes()?)?;
                let lhs = trim_zeros(lhs.as_bytes()?);

                let (bits, bytes) = (offset % 8, offset / 8);

                let mut res = ByteStorage::new(lhs.len().saturating_sub(bytes));

                let mask = |[small, big]: [u8; 2]| (small >> bits) | (big << (8 - bits));

                res.iter_mut()
                    .enumerate()
                    .map(|(idx, byte)| (idx + bytes, byte))
                    .for_each(|(idx, byte)| {
                        *byte = mask([lhs[idx], lhs.get(idx + 1).copied().unwrap_or_default()])
                    });

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
        })
    }
    pub fn from_ident(ident: &[u8]) -> Option<Self> {
        Some(match ident {
            b"add" => Self::Add,
            b"sub" => Self::Sub,
            b"mul" => Self::Mul,
            b"div" => Self::Div,
            b"rem" => Self::Rem,
            b"cmp" => Self::Cmp,
            b"shl" => Self::Shl,
            b"shr" => Self::Shr,
            b"not" => Self::Not,
            b"and" => Self::And,
            b"or" => Self::Or,
            b"xor" => Self::Xor,
            _ => return None,
        })
    }
}

fn binary_bytewise(value: Value, func: impl Fn(u8, u8) -> u8) -> Result<Value> {
    let [lhs, rhs] = get_args(value)?.map(Value::into_bytes);
    let (mut lhs, rhs) = (lhs?, rhs?);
    ensure!(
        lhs.len() == rhs.len(),
        "non equal length bytes for binary bytewise op:\nrhs ({}): {}\n lhs ({}): {}",
        lhs.len(),
        Value::Bytes(lhs),
        rhs.len(),
        Value::Bytes(rhs),
    );

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

fn pop_zeros(mut vec: Vec<u8>) -> Vec<u8> {
    while let Some(&0) = vec.last() {
        vec.pop();
    }
    vec
}

fn trim_zeros(mut slice: &[u8]) -> &[u8] {
    while let [head @ .., 0] = slice {
        slice = head
    }
    slice
}
