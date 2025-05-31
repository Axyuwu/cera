use std::{marker::PhantomData, sync::atomic::Ordering};

use parking_lot_core::{park, unpark_all, ParkToken, UnparkToken};

#[repr(align(2))]
struct CacheLockInner<T>(T);
pub struct CacheLock<T> {
    // Null pointer if it doesn't exist, otherwise it must have been created from a box
    // We use null + 1 as a sentinel lock value, as the inner struct has an alignment requirement
    // making that value invalid
    inner: std::sync::atomic::AtomicPtr<CacheLockInner<T>>,
    _phantom: PhantomData<T>,
}

impl<T> Drop for CacheLock<T> {
    fn drop(&mut self) {
        let ptr = *self.inner.get_mut();
        if !ptr.is_null() && ptr.is_aligned() {
            // This is safe as the pointer is explicitly single owner of a memory location which can be
            // converted to a box, and is nonnull
            std::mem::drop(unsafe { Box::from_raw(ptr) });
        }
    }
}

impl<T: std::fmt::Debug> std::fmt::Debug for CacheLock<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.get() {
            Some(s) => {
                let mut d = f.debug_tuple("CacheLock::Initialized");
                d.field(s);
                d.finish()
            }
            None => f.debug_tuple("CacheLock::Uninitialized").finish(),
        }
    }
}

impl<T> CacheLock<T> {
    /// Will deadlock if func tries to call generate as well
    pub fn generate(&self, func: impl FnOnce() -> T) -> &T {
        let ptr_unaligned = std::ptr::null_mut::<CacheLockInner<T>>().wrapping_add(1);
        let ptr_null = std::ptr::null_mut();
        let key = self as *const _ as usize;

        let ptr: *const _ = match self.inner.compare_exchange(
            ptr_null,
            ptr_unaligned,
            Ordering::Acquire,
            Ordering::Acquire,
        ) {
            Ok(_) => {
                let ptr = Box::into_raw(Box::new(CacheLockInner(func())));
                self.inner.store(ptr, Ordering::Release);
                // Safety: we control key
                unsafe { unpark_all(key, UnparkToken(0)) };
                ptr
            }
            // This is safe as we know the pointer was created from a box
            Err(ptr) if ptr.is_aligned() => ptr,
            Err(ptr) => {
                debug_assert_eq!(ptr, ptr_unaligned);
                let mut res_ptr = std::ptr::null_mut();
                match unsafe {
                    park(
                        key,
                        || {
                            let ptr = self.inner.load(Ordering::Acquire);
                            res_ptr = ptr;
                            ptr == ptr_unaligned
                        },
                        || {},
                        |_, _| {},
                        ParkToken(0),
                        None,
                    )
                } {
                    parking_lot_core::ParkResult::Unparked(_) => {
                        res_ptr = self.inner.load(Ordering::Acquire)
                    }
                    parking_lot_core::ParkResult::Invalid => (),
                    parking_lot_core::ParkResult::TimedOut => unreachable!(),
                }

                debug_assert!(!res_ptr.is_null());

                res_ptr
            }
        };

        unsafe { &ptr.as_ref().unwrap_unchecked().0 }
    }
    #[inline]
    pub fn get(&self) -> Option<&T> {
        let ptr = self.inner.load(Ordering::Relaxed);
        if !ptr.is_aligned() {
            None
        } else {
            Some(&unsafe { ptr.as_ref()? }.0)
        }
    }
    #[inline]
    pub const fn new() -> Self {
        Self {
            inner: std::sync::atomic::AtomicPtr::new(std::ptr::null_mut()),
            _phantom: PhantomData,
        }
    }
    #[inline]
    pub fn new_with(value: T) -> Self {
        Self {
            inner: std::sync::atomic::AtomicPtr::new(Box::into_raw(Box::new(CacheLockInner(
                value,
            )))),
            _phantom: PhantomData,
        }
    }
}

pub trait Initializer {
    type Value;
    fn initialize() -> Self::Value;
}

pub struct InitLock<T: Initializer>(CacheLock<T::Value>);

impl<T: Initializer> InitLock<T> {
    pub fn get(&self) -> &T::Value {
        self.0.generate(T::initialize)
    }
    pub const fn new() -> Self {
        Self(CacheLock::new())
    }
}
