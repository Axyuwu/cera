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
    pub fn poll(self, value: Value) -> Result<Value> {
        Ok(match self {
            Self::Add => {
                let args = get_args(value)?;
                let [lhs, rhs] = {
                    let [a1, a2] = args.each_ref().map(|e| e.as_bytes());
                    [a1?, a2?]
                };
                let mut acc = Vec::new();
                let mut idx = 0;
                let mut carry = false;
                (0..)
                    .map(|i| [lhs.get(i), rhs.get(i)])
                    .take_while(|e| e.iter().any(Option::is_some))
                    .map(|a| a.map(Option::<&_>::cloned).map(Option::unwrap_or_default))
                    .for_each(|[lhs, rhs]| {
                        let (lhs, c1) = lhs.overflowing_add(rhs);
                        let (lhs, c2) = lhs.overflowing_add(carry as u8);
                        carry = c1 || c2 as bool;
                        acc.push(lhs);
                        idx += 1;
                    });
                carry.then(|| acc.push(1));
                Value::bytes_move(pop_zeroes(acc))
            }
            Self::Sub => todo!(),
            Self::Mul => todo!(),
            Self::Div => todo!(),
            Self::Rem => todo!(),
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
                let [lhs, rhs] = args.each_ref().map(|e| trim_zeroes(e));
                match lhs.len().cmp(&rhs.len()) {
                    Equal => ord_to_val(lhs.iter().rev().cmp(rhs.iter().rev())),
                    o => ord_to_val(o),
                }
            }
            Self::Shl => {
                let [value, rhs] = get_args(value)?;
                let offset = get_usize(rhs.as_bytes()?)?;

                let lhs_no_trim = value.as_bytes()?;
                let lhs = trim_zeroes(&lhs_no_trim);

                if offset == 0 {
                    return Ok(if lhs_no_trim.len() == lhs.len() {
                        value
                    } else {
                        Value::bytes_cloned(lhs)
                    });
                }

                let (bits, bytes) = (offset % 8, offset / 8);

                let Some(leading_byte) = lhs.last() else {
                    return Ok(Value::bytes(&[]));
                };

                let mut res = ByteStorage::new(
                    bytes + lhs.len() + (leading_byte.leading_zeros() < bits as u32) as usize,
                );

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
                let [value, rhs] = get_args(value)?;
                let offset = get_usize(rhs.as_bytes()?)?;

                let lhs_no_trim = value.as_bytes()?;
                let lhs = trim_zeroes(&lhs_no_trim);

                if offset == 0 {
                    return Ok(if lhs_no_trim.len() == lhs.len() {
                        value
                    } else {
                        Value::bytes_cloned(lhs)
                    });
                }

                let (bits, bytes) = (offset % 8, offset / 8);

                let (lhs, leading_byte) = match lhs.get(bytes..) {
                    Some(lhs @ [.., byte]) => (lhs, byte),
                    _ => return Ok(Value::bytes(&[])),
                };

                let mut res = ByteStorage::new(
                    lhs.len() - (8 - leading_byte.leading_zeros() <= bits as u32) as usize,
                );

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

fn pop_zeroes(mut vec: Vec<u8>) -> Vec<u8> {
    while let Some(&0) = vec.last() {
        vec.pop();
    }
    vec
}

fn trim_zeroes(mut slice: &[u8]) -> &[u8] {
    while let [head @ .., 0] = slice {
        slice = head
    }
    slice
}
