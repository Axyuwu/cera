use std::{
    cell::UnsafeCell,
    fmt::Debug,
    sync::atomic::{AtomicBool, Ordering},
};

pub struct SpinMutex<T> {
    lock: AtomicBool,
    cell: UnsafeCell<T>,
}

unsafe impl<T> Sync for SpinMutex<T> {}

impl<T: Debug> Debug for SpinMutex<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut d = f.debug_struct("SpinMutex");
        if self.try_lock() {
            d.field("data", &&*unsafe { self.read() });
        } else {
            d.field("data", &format_args!("<locked>"));
        }
        d.finish_non_exhaustive()
    }
}

impl<T: Default> Default for SpinMutex<T> {
    fn default() -> Self {
        Self::new(Default::default())
    }
}

impl<T> From<T> for SpinMutex<T> {
    fn from(value: T) -> Self {
        Self::new(value)
    }
}

impl<T> SpinMutex<T> {
    pub fn new(val: T) -> Self {
        Self {
            lock: AtomicBool::new(false),
            cell: UnsafeCell::new(val),
        }
    }
    /// To insure low overhead, ensure F has a low, bounded, time complexity
    pub fn apply<F, O>(&self, func: F) -> O
    where
        F: FnOnce(&mut T) -> O,
    {
        self.spinlock_lock();

        // Safety: we have locked the mutex
        let val = unsafe { self.read() };
        let res = func(val);

        self.unlock();

        res
    }
    /// Safety: must be locked
    unsafe fn read(&self) -> &mut T {
        unsafe { &mut *self.cell.get() }
    }
    fn spinlock_lock(&self) {
        #[cold]
        fn spinlock_step(counter: &mut usize) {
            match *counter {
                c @ 0..5 => {
                    (0..(1 << c)).for_each(|_| std::hint::spin_loop());
                    *counter += 1
                }
                _ => std::thread::yield_now(),
            }
        }
        let mut counter = 0;
        while !self.try_lock() {
            spinlock_step(&mut counter);
        }
    }
    // Returns whether the locking was successful
    fn try_lock(&self) -> bool {
        self.lock
            .compare_exchange_weak(false, true, Ordering::Acquire, Ordering::Relaxed)
            .is_ok()
    }
    fn unlock(&self) {
        self.lock.store(false, Ordering::Release)
    }
}
