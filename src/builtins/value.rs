use crate::utils::sync::cache_arc::CacheArc as Arc;
use std::convert::Infallible;
use std::fmt::Debug;
use std::fmt::Display;
use std::fmt::Write;
use std::ops::Deref;

use super::Cache;

pub trait SliceStorage<T>: Sized {
    fn get(&self) -> &[T];
    fn get_mut(&mut self) -> &mut [T];
    fn try_new(slice: &[T]) -> Option<Self>;
    fn eq(&self, rhs: &[T]) -> bool;
}

const U8_SLICE_STORAGE_SIZE: usize = 16;
#[derive(Debug, Clone)]
pub struct U8SliceStorage {
    len: usize,
    storage: [u8; U8_SLICE_STORAGE_SIZE],
}

impl SliceStorage<u8> for U8SliceStorage {
    fn get(&self) -> &[u8] {
        &self.storage[..(self.len as usize)]
    }

    fn get_mut(&mut self) -> &mut [u8] {
        &mut self.storage[..(self.len as usize)]
    }

    fn try_new(slice: &[u8]) -> Option<Self> {
        if slice.len() > U8_SLICE_STORAGE_SIZE {
            None
        } else {
            let mut storage = [0; U8_SLICE_STORAGE_SIZE];
            storage[0..(slice.len())].copy_from_slice(slice);
            Some(Self {
                len: slice.len(),
                storage,
            })
        }
    }

    fn eq(&self, rhs: &[u8]) -> bool {
        self.get() == rhs
    }
}
impl<T> SliceStorage<T> for Infallible {
    fn get(&self) -> &[T] {
        unreachable!()
    }

    fn get_mut(&mut self) -> &mut [T] {
        unreachable!()
    }

    fn try_new(_slice: &[T]) -> Option<Self> {
        None
    }

    fn eq(&self, _rhs: &[T]) -> bool {
        unreachable!()
    }
}

pub trait HasSliceStorage: Sized {
    type Storage: SliceStorage<Self>;
}

impl HasSliceStorage for Value {
    type Storage = Infallible;
}
impl HasSliceStorage for u8 {
    //type Storage = Infallible;
    type Storage = U8SliceStorage;
}

#[derive(Debug, Clone)]
pub enum EvalSlice<T: 'static + HasSliceStorage> {
    Arc(Arc<[T], Cache>),
    Borrowed(&'static Cache, &'static [T]),
    Inline(T::Storage),
}

impl<T: HasSliceStorage> Deref for EvalSlice<T> {
    type Target = [T];
    fn deref(&self) -> &[T] {
        match self {
            EvalSlice::Arc(items) => items.as_ref(),
            EvalSlice::Borrowed(_, items) => items.as_ref(),
            EvalSlice::Inline(items) => items.get(),
        }
    }
}

impl<T: HasSliceStorage> EvalSlice<T> {
    pub fn get_mut(&mut self) -> Option<&mut [T]> {
        match self {
            EvalSlice::Arc(items) => Arc::get_mut(items),
            EvalSlice::Borrowed(_, _) => None,
            EvalSlice::Inline(items) => Some(items.get_mut()),
        }
    }
    pub fn make_mut(&mut self) -> &mut [T]
    where
        T: Clone,
    {
        match self {
            EvalSlice::Arc(items) => Arc::<[_], _>::make_mut(items),
            EvalSlice::Borrowed(_, items) => {
                *self = Self::Arc((*items).into());
                self.make_mut()
            }
            EvalSlice::Inline(items) => items.get_mut(),
        }
    }
    pub fn addr_eq(&self, rhs: &Self) -> bool {
        match (self, rhs) {
            (Self::Inline(lhs), rhs) => lhs.eq(&*rhs),
            (Self::Borrowed(_, lhs), Self::Borrowed(_, rhs)) => std::ptr::eq(lhs, rhs),
            (Self::Arc(lhs), Self::Arc(rhs)) => std::ptr::eq(&*lhs, &*rhs),
            _ => false,
        }
    }
    pub fn into_array<const SIZE: usize>(self) -> [T; SIZE]
    where
        T: Clone,
    {
        let s = &*self;
        assert!(s.len() == SIZE);
        match self {
            Self::Arc(inner) => Arc::unwrap_or_clone(inner.try_into().unwrap()),
            _ => TryInto::<&[T; SIZE]>::try_into(s).unwrap().clone(),
        }
    }
    pub fn as_array<const SIZE: usize>(&self) -> &[T; SIZE] {
        (&**self).try_into().unwrap()
    }
    #[inline]
    pub fn gen_cache(&mut self)
    where
        T: Clone,
    {
        match self {
            EvalSlice::Inline(storage) => {
                *self = EvalSlice::Arc(storage.get().into());
            }
            _ => (),
        }
    }
    #[inline]
    pub fn cache(&self) -> &Cache {
        match self {
            EvalSlice::Arc(arc) => Arc::cache(arc),
            EvalSlice::Borrowed(cache, _) => cache,
            _ => panic!(),
        }
    }
    pub const fn static_copy(&self) -> Self {
        match self {
            EvalSlice::Borrowed(cache_lock, items) => Self::Borrowed(cache_lock, items),
            _ => panic!(),
        }
    }
}

#[derive(Clone)]
pub enum Value {
    Bytes(EvalSlice<u8>),
    Aggregate(EvalSlice<Value>),
}

impl Debug for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        <Self as Display>::fmt(&self, f)
    }
}

impl Value {
    #[inline]
    pub fn gen_cache(&mut self) {
        match self {
            Value::Bytes(eval_slice) => eval_slice.gen_cache(),
            Value::Aggregate(eval_slice) => eval_slice.gen_cache(),
        }
    }
    #[inline]
    pub fn cache(&self) -> &Cache {
        match self {
            Value::Bytes(eval_slice) => eval_slice.cache(),
            Value::Aggregate(eval_slice) => eval_slice.cache(),
        }
    }
    pub const fn unit() -> Self {
        static CACHE: Cache = Cache::new();
        Self::aggregate_const(&CACHE, &[])
    }
    pub fn is_unit(&self) -> bool {
        match self {
            Self::Aggregate(slice) if slice.len() == 0 => true,
            _ => false,
        }
    }
    pub const fn aggregate_const(cache: &'static Cache, slice: &'static [Self]) -> Self {
        Self::Aggregate(EvalSlice::Borrowed(cache, slice))
    }
    pub fn aggregate(slice: &'static (impl AsRef<(Cache, [Self])> + ?Sized)) -> Self {
        let (cache, slice) = slice.as_ref();
        Self::aggregate_const(cache, slice)
    }
    pub fn aggregate_cloned(slice: impl AsRef<[Self]>) -> Self {
        Self::Aggregate(EvalSlice::Arc(slice.as_ref().into()))
    }
    pub fn aggregate_move(slice: impl Into<Arc<[Self], Cache>>) -> Self {
        Self::Aggregate(EvalSlice::Arc(slice.into()))
    }
    pub fn into_aggregate(self) -> EvalSlice<Value> {
        let Self::Aggregate(s) = self else {
            panic!("expected aggregate, found bytes:\n{}", self)
        };
        s
    }
    pub fn as_aggregate(&self) -> &EvalSlice<Value> {
        let Self::Aggregate(s) = self else {
            panic!("expected aggregate, found bytes:\n{}", self)
        };
        s
    }
    pub fn as_aggregate_mut(&mut self) -> &mut EvalSlice<Value> {
        let Self::Aggregate(s) = self else {
            panic!("expected aggregate, found bytes:\n{}", self)
        };
        s
    }
    pub const fn bytes_const(cache: &'static Cache, slice: &'static [u8]) -> Self {
        Self::Bytes(EvalSlice::Borrowed(cache, slice))
    }
    pub fn bytes(slice: &'static (impl AsRef<(Cache, [u8])> + ?Sized)) -> Self {
        let (cache, bytes) = slice.as_ref();

        Self::Bytes(EvalSlice::Borrowed(cache, bytes))
    }
    pub fn bytes_cloned(slice: impl AsRef<[u8]>) -> Self {
        let bytes = slice.as_ref();
        if let Some(slice) = <u8 as HasSliceStorage>::Storage::try_new(bytes) {
            Self::Bytes(EvalSlice::Inline(slice))
        } else {
            Self::Bytes(EvalSlice::Arc(bytes.into()))
        }
    }
    pub fn bytes_move(slice: impl Into<Arc<[u8], Cache>> + AsRef<[u8]>) -> Self {
        if let Some(slice) = <u8 as HasSliceStorage>::Storage::try_new(slice.as_ref()) {
            Self::Bytes(EvalSlice::Inline(slice))
        } else {
            Self::Bytes(EvalSlice::Arc(slice.into()))
        }
    }
    pub fn into_bytes(self) -> EvalSlice<u8> {
        let Self::Bytes(s) = self else {
            panic!("expected bytes, found aggregate:\n{}", self)
        };
        s
    }
    pub fn as_bytes(&self) -> &EvalSlice<u8> {
        let Self::Bytes(s) = self else {
            panic!("expected bytes, found aggregate:\n{}", self)
        };
        s
    }
    pub fn as_bytes_mut(&mut self) -> &mut EvalSlice<u8> {
        let Self::Bytes(s) = self else {
            panic!("expected bytes, found aggregate:\n{}", self)
        };
        s
    }
    pub fn prefix_fmt(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        prefix: &mut String,
    ) -> std::fmt::Result {
        pub fn write_hexdump_width(
            bytes: &[u8],
            f: &mut std::fmt::Formatter<'_>,
            prefix: &str,
            width: usize,
        ) -> std::fmt::Result {
            pub fn write_byte(byte: u8, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                pub fn nibble_to_char(nibble: u8) -> char {
                    match nibble {
                        0x00 => '0',
                        0x01 => '1',
                        0x02 => '2',
                        0x03 => '3',
                        0x04 => '4',
                        0x05 => '5',
                        0x06 => '6',
                        0x07 => '7',
                        0x08 => '8',
                        0x09 => '9',
                        0x0A => 'A',
                        0x0B => 'B',
                        0x0C => 'C',
                        0x0D => 'D',
                        0x0E => 'E',
                        0x0F => 'F',
                        _ => unreachable!(),
                    }
                }
                f.write_char(nibble_to_char(byte / 0x10))?;
                f.write_char(nibble_to_char(byte % 0x10))
            }

            bytes.chunks(width).enumerate().try_for_each(|(idx, line)| {
                f.write_str(prefix)?;

                (idx * width)
                    .to_be_bytes()
                    .last_chunk::<4>()
                    .unwrap()
                    .iter()
                    .try_for_each(|b| write_byte(*b, f))?;
                f.write_char(':')?;

                (0..width)
                    .map(|i| (i, line.get(i)))
                    .try_for_each(|(i, b)| {
                        if i % 2 == 0 {
                            f.write_char(' ')?;
                        }
                        let Some(b) = b else {
                            return f.write_str("  ");
                        };
                        if matches!(b, 0x20..0x7F) {
                            f.write_str("\x01\x1B[0;32m\x02")?;
                        } else {
                            f.write_str("\x01\x1B[0;30m\x02")?;
                        }
                        write_byte(*b, f)
                    })?;

                f.write_str("  ")?;

                (0..width)
                    .map(|i| line.get(i).unwrap_or(&0x20))
                    .try_for_each(|b| {
                        if matches!(b, 0x20..0x7F) {
                            f.write_str("\x01\x1B[0;32m\x02")?;
                            f.write_char(*b as char)
                        } else {
                            f.write_str("\x01\x1B[0;30m\x02")?;
                            f.write_char('.')
                        }
                    })?;

                f.write_char('\n')?;
                f.write_str("\x01\x1B[0m\x02")
            })
        }
        match self {
            Value::Bytes(eval_slice) => {
                write!(f, "{prefix}[\n")?;
                let len = prefix.len();
                prefix.push_str("    ");
                write_hexdump_width(eval_slice, f, prefix, 16)?;
                prefix.truncate(len);
                write!(f, "{prefix}]\n")?;
            }
            Value::Aggregate(eval_slice) => {
                write!(f, "{prefix}(\n")?;
                let len = prefix.len();
                prefix.push_str("    ");
                eval_slice
                    .iter()
                    .try_for_each(|value| value.prefix_fmt(f, prefix))?;
                prefix.truncate(len);
                write!(f, "{prefix})\n")?;
            }
        }
        Ok(())
    }
    pub fn from_res<I1, I2, F1, F2>(res: std::result::Result<I1, I2>, f1: F1, f2: F2) -> Value
    where
        F1: FnOnce(I1) -> Value,
        F2: FnOnce(I2) -> Value,
    {
        static OK_CACHE: Cache = Cache::new();
        static ERR_CACHE: Cache = Cache::new();
        match res {
            Ok(i1) => Value::aggregate_move([Value::bytes_const(&OK_CACHE, b"ok"), f1(i1)]),
            Err(i2) => Value::aggregate_move([Value::bytes_const(&ERR_CACHE, b"err"), f2(i2)]),
        }
    }
    pub fn addr_eq(&self, rhs: &Self) -> bool {
        match (self, rhs) {
            (Self::Bytes(lhs), Self::Bytes(rhs)) => lhs.addr_eq(rhs),
            (Self::Aggregate(lhs), Self::Aggregate(rhs)) => lhs.addr_eq(rhs),
            _ => false,
        }
    }
    pub const fn static_copy(&self) -> Self {
        match self {
            Value::Bytes(eval_slice) => Self::Bytes(eval_slice.static_copy()),
            Value::Aggregate(eval_slice) => Self::Aggregate(eval_slice.static_copy()),
        }
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.prefix_fmt(f, &mut String::new())
    }
}
