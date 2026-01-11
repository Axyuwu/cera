use std::{fmt::Debug, mem, ptr::NonNull};

pub use val_complex::ValComplex;

use crate::interp::value::static_bool::{StaticBool, True};

pub mod ref_utils;

pub mod static_bool;

#[repr(usize)]
#[derive(PartialEq, Eq, Debug)]
enum ValDiscrim {
    Complex = 0,
    Primitive = 1,
}

/// A general value inside cera
/// Dropping this type runs destructors
#[repr(transparent)]
pub struct Val(*mut ());

impl Debug for Val {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(c) = self.complex() {
            c.fmt(f)
        } else if let Some(n) = self.usize() {
            n.fmt(f)
        } else {
            unreachable!()
        }
    }
}

impl Drop for Val {
    fn drop(&mut self) {
        let other = Self(self.0);
        drop(other.into_complex());
    }
}

impl PartialEq for Val {
    fn eq(&self, other: &Self) -> bool {
        self.0.addr() == other.0.addr()
    }
}
impl Eq for Val {}

impl Clone for Val {
    fn clone(&self) -> Self {
        if let Some(c) = self.complex() {
            Self::new_complex(c.clone())
        } else if let Some(n) = self.usize() {
            Self::new_usize(n)
        } else {
            unreachable!()
        }
    }
}

impl Val {
    fn extract_discriminant(&self) -> ValDiscrim {
        match self.0.addr() % 2 {
            0 => {
                debug_assert!(
                    self.0.addr() != 0,
                    "Discriminant for complex type was a null pointer"
                );
                ValDiscrim::Complex
            }
            1 => ValDiscrim::Primitive,
            _ => unreachable!(),
        }
    }
    pub fn usize(&self) -> Option<usize> {
        match self.extract_discriminant() {
            ValDiscrim::Complex => None,
            ValDiscrim::Primitive => Some(self.0.addr() >> 1),
        }
    }
    pub fn isize(&self) -> Option<isize> {
        self.usize().map(|n| n as isize)
    }
    pub fn complex(&self) -> Option<&ValComplex>
    where
        StaticBool<{ ValDiscrim::Complex as usize == 0 }>: True,
    {
        match self.extract_discriminant() {
            ValDiscrim::Primitive => None,
            ValDiscrim::Complex => {
                // SAFETY: This is safe to do as we know Self is a valid representation of a
                // pointer, and transitively of a ValComplex, and was created from one
                Some(unsafe { std::mem::transmute::<&Self, &ValComplex>(self) })
            }
        }
    }
    pub fn complex_mut(&mut self) -> Option<&mut ValComplex>
    where
        StaticBool<{ ValDiscrim::Complex as usize == 0 }>: True,
    {
        match self.extract_discriminant() {
            ValDiscrim::Primitive => None,
            ValDiscrim::Complex => {
                // SAFETY: This is safe to do as we know Self is a valid representation of a
                // pointer, and transitively of a ValComplex, and was created from one
                Some(unsafe { std::mem::transmute::<&mut Self, &mut ValComplex>(self) })
            }
        }
    }
    pub fn into_complex(self) -> Option<ValComplex> {
        let res = match self.extract_discriminant() {
            ValDiscrim::Primitive => None,
            ValDiscrim::Complex => {
                // SAFETY: This is safe to do as we know Self is a valid representation of a
                // pointer, and transitively of a ValComplex, and was created from one
                // We know NonNull is not zero since it was also created through a NonNull
                Some(unsafe { ValComplex::from_raw(NonNull::new_unchecked(self.0)) })
            }
        };
        mem::forget(self);
        return res;
    }
    pub fn new_complex(complex: ValComplex) -> Self
    where
        StaticBool<{ ValDiscrim::Complex as usize == 0 }>: True,
    {
        let res = Self(complex.into_raw().as_ptr());
        debug_assert!(res.extract_discriminant() == ValDiscrim::Complex);
        res
    }
    pub fn new_usize(value: usize) -> Self {
        let res = Self(std::ptr::without_provenance_mut((value << 1) + 1));
        res
    }
    pub fn new_isize(value: isize) -> Self {
        let res = Self(std::ptr::without_provenance_mut((value << 1) as usize + 1));
        res
    }
}

mod val_complex;

#[cfg(test)]
mod test {
    use crate::interp::value::{Val, ValComplex};

    #[test]
    fn test_val_any() {
        let val = Val::new_complex(ValComplex::new_any(65u32));
        assert_eq!(val.complex().unwrap().get_any::<u32>().unwrap(), &65);
        let s: &'static str = "Hello world";
        let val = Val::new_complex(ValComplex::new_any(s));
        assert_eq!(
            val.complex().unwrap().get_any::<&'static str>().unwrap(),
            &s
        );
    }

    #[test]
    fn test_val_compound() {
        let val = Val::new_complex(ValComplex::new_compound([
            Val::new_usize(1),
            Val::new_usize(2),
        ]));
        let val2 = val.clone();
        assert!(
            val.complex().unwrap().get_compound().unwrap()
                == val2.complex().unwrap().get_compound().unwrap()
        );
    }
}
