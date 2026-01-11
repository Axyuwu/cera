use std::{marker::PhantomData, mem};

pub trait True {}
pub trait False {}

pub struct StaticBool<const VAL: bool> {}
impl True for StaticBool<true> {}
impl False for StaticBool<false> {}

pub struct StaticTypeEq<A: ?Sized, B: ?Sized> {
    _data_a: PhantomData<A>,
    _data_b: PhantomData<B>,
}
impl<T: ?Sized> True for StaticTypeEq<T, T> {}
impl<A, B> StaticTypeEq<A, B> {
    #[inline(always)]
    pub fn cast(val: A) -> B
    where
        Self: True,
    {
        let val_ptr = &raw const val;
        // SAFETY: We know both types to be the same, and we forget the previous value
        // afterwards
        let res = unsafe { val_ptr.cast::<B>().read() };
        mem::forget(val);
        res
    }
}
