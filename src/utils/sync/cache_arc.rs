use std::{
    alloc::Layout,
    convert::Infallible,
    error::Error,
    marker::PhantomData,
    mem::MaybeUninit,
    ops::Deref,
    ptr::NonNull,
    sync::atomic::{AtomicUsize, Ordering},
};

use super::cache_lock::CacheLock;

#[macro_export]
macro_rules! static_arc {
    ($data:expr, $data_t:ty) => {
        static_arc!($data, $data_t, (), ())
    };
    ($data:expr, $data_t:ty, $cache:expr, $cache_t:ty) => {{
        static mut STORAGE: $crate::utils::sync::cache_arc::CacheArcInner<$data_t, $cache_t> =
            $crate::utils::sync::cache_arc::CacheArcInner {
                cache: $cache,
                count: ::std::sync::atomic::AtomicUsize::new(1),
                data: $data,
            };
        let val = crate::utils::sync::cache_arc::CacheArc {
            inner: unsafe { ::std::ptr::NonNull::new_unchecked(::std::ptr::addr_of_mut!(STORAGE)) },
            _phantom: ::std::marker::PhantomData,
        };
        val.increment_leak();
        val
    }};
}

pub trait CacheArcCache {
    fn init() -> Self;
}

impl CacheArcCache for () {
    fn init() -> Self {
        ()
    }
}

impl<T> CacheArcCache for CacheLock<T> {
    fn init() -> Self {
        Self::new()
    }
}

#[repr(C)]
pub struct CacheArc<T: ?Sized, C = ()> {
    inner: NonNull<CacheArcInner<T, C>>,
    _phantom: PhantomData<CacheArcInner<T, C>>,
}

unsafe impl<T: ?Sized, C> Send for CacheArc<T, C> {}
unsafe impl<T: ?Sized, C> Sync for CacheArc<T, C> {}

#[repr(C)]
struct CacheArcInner<T: ?Sized, C> {
    cache: C,
    count: AtomicUsize,
    data: T,
}

impl<T: ?Sized + std::fmt::Debug, C: std::fmt::Debug> std::fmt::Debug for CacheArc<T, C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut d = f.debug_struct("CacheArc");
        d.field("data", &*self);
        d.field("cache", &self.inner().cache);
        d.finish()
    }
}

const MAX_REFCOUNT: usize = (isize::MAX) as usize;

impl<T: ?Sized, C> Clone for CacheArc<T, C> {
    fn clone(&self) -> Self {
        self.increment_leak();

        Self {
            inner: self.inner,
            _phantom: self._phantom,
        }
    }
}

impl<T: ?Sized, C> Drop for CacheArc<T, C> {
    fn drop(&mut self) {
        // This only needs to ensure memory accesses that happen before stay before on the happy
        // path
        if self.inner().count.fetch_sub(1, Ordering::Release) != 1 {
            return;
        }

        // Once we drop, we syncronise with the previous release ordering, such that the drop
        // happens after every memory operation before the release on other threads
        std::sync::atomic::fence(Ordering::Acquire);

        // We know this is the last use of self so this is afe
        unsafe { self.drop_slow() };
    }
}

impl<T: ?Sized, C> CacheArc<T, C> {
    pub fn cache(this: &Self) -> &C {
        &Self::inner(this).cache
    }

    /// Returns whether this is the only arc pointing to that data, with Acquire ordering
    /// As we do not have weak references, this means this arc can be safely used mutably so long
    /// as it is not cloned or otherwise made to no longer be unique
    pub fn is_unique(this: &Self) -> bool {
        this.inner().count.load(Ordering::Acquire) == 1
    }

    pub fn get_mut(this: &mut Self) -> Option<&mut T>
    where
        C: CacheArcCache,
    {
        Self::is_unique(this).then(|| unsafe { Self::mut_unchecked(this) })
    }

    /// Saftey: this must be the only copy of this arc
    pub unsafe fn mut_unchecked(this: &mut Self) -> &mut T
    where
        C: CacheArcCache,
    {
        let data = unsafe { this.inner.as_mut() };
        data.cache = C::init();
        &mut data.data
    }

    fn inner(&self) -> &CacheArcInner<T, C> {
        unsafe { &*self.inner.as_ptr() }
    }

    /// Safety: self must not be used at all after this call
    #[inline(never)]
    unsafe fn drop_slow(&mut self) {
        std::mem::drop(unsafe { Box::from_raw(self.inner.as_ptr()) })
    }

    /// Safety: it must be valid to cast a box of the same type
    pub unsafe fn cast<U>(this: Self) -> CacheArc<U, C> {
        let Self { inner, _phantom } = this;
        std::mem::forget(this);
        let ptr = inner.as_ptr() as _;
        CacheArc {
            inner: unsafe { NonNull::new_unchecked(ptr) },
            _phantom: PhantomData,
        }
    }

    /// Safety: it must be valid to cast a box of the same type
    pub unsafe fn cast_cache<U>(this: Self) -> CacheArc<T, U> {
        let Self { inner, _phantom } = this;
        std::mem::forget(this);
        let ptr = inner.as_ptr() as _;
        CacheArc {
            inner: unsafe { NonNull::new_unchecked(ptr) },
            _phantom: PhantomData,
        }
    }

    pub fn increment_leak(&self) {
        let old_size = self.inner().count.fetch_add(1, Ordering::Relaxed);

        if old_size > MAX_REFCOUNT {
            std::process::abort();
        }
    }
}

impl<T, C> CacheArc<T, C> {
    /// Safety: value must be initliazed
    pub unsafe fn assume_init(this: CacheArc<MaybeUninit<T>, C>) -> Self
    where
        T: Sized,
        C: CacheArcCache,
    {
        CacheArc::cast(this)
    }
    pub fn new(data: T) -> Self
    where
        C: CacheArcCache,
    {
        Self {
            inner: unsafe {
                NonNull::new_unchecked(Box::into_raw(Box::new(CacheArcInner {
                    cache: C::init(),
                    count: AtomicUsize::new(1),
                    data,
                })))
            },
            _phantom: PhantomData,
        }
    }

    pub fn new_uninit() -> CacheArc<MaybeUninit<T>, C>
    where
        C: CacheArcCache,
    {
        CacheArc {
            inner: unsafe {
                NonNull::new_unchecked(Box::into_raw(Box::new(CacheArcInner {
                    cache: C::init(),
                    count: AtomicUsize::new(1),
                    data: MaybeUninit::uninit(),
                })))
            },
            _phantom: PhantomData,
        }
    }

    pub fn unwrap_or_clone(this: Self) -> T
    where
        T: Clone,
    {
        if !Self::is_unique(&this) {
            return (&*this).clone();
        }

        let res = unsafe { std::ptr::read(&this.inner().data) };

        // This cast is safe as we essentially just uninitialized the stored value
        std::mem::drop(unsafe { Self::cast::<MaybeUninit<T>>(this) });

        res
    }
    pub fn make_mut(this: &mut Self) -> &mut T
    where
        T: Clone,
        C: CacheArcCache,
    {
        if !Self::is_unique(this) {
            *this = Self::new((**this).clone());
        }
        // Safety: we just insured that it was unique
        unsafe { Self::mut_unchecked(this) }
    }
}

impl<T: Sized, C> CacheArc<[T], C> {
    pub fn new_uninit(len: usize) -> CacheArc<[MaybeUninit<T>], C>
    where
        C: CacheArcCache,
    {
        let slice_layout = Layout::array::<MaybeUninit<T>>(len).unwrap();
        let layout = Layout::new::<CacheArcInner<(), C>>()
            .extend(slice_layout)
            .unwrap()
            .0
            .pad_to_align();

        // Safety: Layout matches Self
        let allocated = unsafe { std::alloc::alloc(layout) };

        let fat = std::ptr::slice_from_raw_parts_mut(allocated as *mut MaybeUninit<T>, len);
        let slice = unsafe { &mut *std::ptr::slice_from_raw_parts_mut(allocated, layout.size()) };
        slice.iter_mut().for_each(|d| *d = 0);

        let mut res = CacheArc {
            inner: NonNull::new(fat as *mut CacheArcInner<[MaybeUninit<T>], C>).unwrap(),
            _phantom: PhantomData,
        };

        // This might be unsound but it seems to work
        let inner = unsafe { res.inner.as_mut() };
        inner.count = AtomicUsize::new(1);
        inner.cache = C::init();
        res
    }
    pub fn new_from_ref(data: &[T]) -> Self
    where
        C: CacheArcCache,
        T: Clone,
    {
        let mut res = Self::new_uninit(data.len());
        unsafe { res.inner.as_mut() }
            .data
            .iter_mut()
            .zip(data)
            .for_each(|(dst, src)| *dst = MaybeUninit::new(src.clone()));
        // Safety: we just initialized it
        unsafe { Self::assume_init(res) }
    }

    /// Safety: it must be valid to cast a box of the same type
    pub unsafe fn cast_slice<U>(this: Self) -> CacheArc<[U], C> {
        let Self { inner, _phantom } = this;
        std::mem::forget(this);
        let ptr = inner.as_ptr() as _;
        CacheArc {
            inner: unsafe { NonNull::new_unchecked(ptr) },
            _phantom: PhantomData,
        }
    }

    /// Safety: slice must be initliazed
    pub unsafe fn assume_init(this: CacheArc<[MaybeUninit<T>], C>) -> Self {
        CacheArc::cast_slice(this)
    }

    /// Safety: the arc will get ownership of the data, so it should be considered moved
    /// The pointer should also be valid
    pub unsafe fn new_move_slice(slice: *const [T]) -> Self
    where
        C: CacheArcCache,
    {
        let mut res = Self::new_uninit(slice.len());
        let data = slice as *const MaybeUninit<T>;
        // Safety: data and res have the same length, and we own res
        unsafe {
            std::ptr::copy_nonoverlapping(
                data,
                CacheArc::mut_unchecked(&mut res) as *mut _ as *mut _,
                slice.len(),
            )
        };
        // Safety: we just initialized it
        unsafe { Self::assume_init(res) }
    }
    pub fn make_mut(this: &mut Self) -> &mut [T]
    where
        T: Clone,
        C: CacheArcCache,
    {
        if !Self::is_unique(this) {
            *this = Self::new_from_ref(&this);
        }
        // Safety: we just insured that it was unique
        unsafe { Self::mut_unchecked(this) }
    }
}

impl<T: ?Sized, C> Deref for CacheArc<T, C> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &Self::inner(self).data
    }
}

impl<T: ?Sized, C> AsRef<T> for CacheArc<T, C> {
    fn as_ref(&self) -> &T {
        &*self
    }
}

#[derive(Debug, Copy, Clone)]
pub struct TryFromSliceError(());

impl std::fmt::Display for TryFromSliceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        "could not convert slice to array".fmt(f)
    }
}

impl Error for TryFromSliceError {}

impl From<Infallible> for TryFromSliceError {
    fn from(x: Infallible) -> TryFromSliceError {
        match x {}
    }
}

impl<const SIZE: usize, T, C> TryFrom<CacheArc<[T], C>> for CacheArc<[T; SIZE], C> {
    type Error = TryFromSliceError;

    fn try_from(value: CacheArc<[T], C>) -> Result<Self, Self::Error> {
        if value.len() == SIZE {
            // Safety: this is safe as the lengths match so this is a same-size conversion
            Ok(unsafe { CacheArc::cast(value) })
        } else {
            Err(TryFromSliceError(()))
        }
    }
}

impl<const SIZE: usize, T, C> From<CacheArc<[T; SIZE], C>> for CacheArc<[T], C> {
    fn from(value: CacheArc<[T; SIZE], C>) -> Self {
        let CacheArc { inner, _phantom } = value;
        std::mem::forget(value);
        Self {
            inner,
            _phantom: PhantomData,
        }
    }
}

impl<T: Clone, C: CacheArcCache> From<&T> for CacheArc<T, C> {
    fn from(value: &T) -> Self {
        value.clone().into()
    }
}

impl<T: Clone, C: CacheArcCache> From<&[T]> for CacheArc<[T], C> {
    fn from(value: &[T]) -> Self {
        Self::new_from_ref(value)
    }
}

impl<T, C: CacheArcCache> From<T> for CacheArc<T, C> {
    fn from(value: T) -> Self {
        Self::new(value)
    }
}

impl<const SIZE: usize, T, C: CacheArcCache> From<[T; SIZE]> for CacheArc<[T], C> {
    fn from(value: [T; SIZE]) -> Self {
        CacheArc::new(value).into()
    }
}

impl<T, C: CacheArcCache> FromIterator<T> for CacheArc<[T], C> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut acc = iter.into_iter().collect::<Vec<_>>();
        // Safety: we forget the data right after
        let res = unsafe { Self::new_move_slice(&*acc) };
        unsafe {
            acc.set_len(0);
        }
        res
    }
}
