use std::{
    borrow::{Borrow, BorrowMut},
    mem::ManuallyDrop,
};

/// # Safety:
/// This trait should be implemented respecting its specification, otherwise UB may occur
pub unsafe trait Owning<T: ?Sized>: Sized + Borrow<T> + BorrowMut<T> {
    fn move_scoped<R, F: FnOnce(*mut T) -> R>(self, cb: F) -> R;
    fn move_get(self) -> T
    where
        T: Sized,
    {
        self.move_scoped(|p| unsafe { std::ptr::read(p) })
    }
}

unsafe impl<const SIZE: usize, T> Owning<[T]> for [T; SIZE] {
    fn move_scoped<R, F: FnOnce(*mut [T]) -> R>(mut self, cb: F) -> R {
        let res = cb(&raw mut self);
        std::mem::forget(self);
        res
    }
}

unsafe impl<T: ?Sized> Owning<T> for Box<T> {
    fn move_scoped<R, F: FnOnce(*mut T) -> R>(self, cb: F) -> R {
        let ptr = Box::into_raw(self);
        let res = cb(ptr);
        // SAFETY: The pointer was obtained from a box, and [`ManuallyDrop`] is a valid
        // reinterpet of any type, given it is not moved afterwards
        unsafe { drop(Box::from_raw(ptr.cast::<*mut ManuallyDrop<T>>())) };
        res
    }
}

unsafe impl<T> Owning<[T]> for Vec<T> {
    fn move_scoped<R, F: FnOnce(*mut [T]) -> R>(mut self, cb: F) -> R {
        let ptr = &raw mut *self;
        let res = cb(ptr);
        // SAFETY: The pointer was obtained from a vec, and [`ManuallyDrop`] is a valid
        // reinterpet of any type, given it is not moved afterwards
        unsafe { drop(std::mem::transmute::<_, Vec<ManuallyDrop<T>>>(self)) };
        res
    }
}
