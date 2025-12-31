use std::{mem, ptr::NonNull};

pub use val_complex::ValComplex;

mod owning {
    use std::{mem::MaybeUninit, ops::DerefMut};

    /// Safety:
    /// This trait should be implemented respecting its specification, otherwise UB may occur
    pub unsafe trait Owning: DerefMut {
        fn move_out<F: FnOnce(*mut Self::Target)>(self, cb: F);
    }

    unsafe impl<T> Owning for Box<T> {
        fn move_out<F: FnOnce(*mut Self::Target)>(self, cb: F) {
            let ptr = Box::into_raw(self);
            cb(ptr);
            unsafe { drop(Box::from_raw(ptr.cast::<*mut MaybeUninit<T>>())) };
        }
    }
    unsafe impl<T> Owning for Box<[T]> {
        fn move_out<F: FnOnce(*mut Self::Target)>(self, cb: F) {
            let ptr = Box::into_raw(self);
            cb(ptr);
            unsafe { drop(Box::from_raw(ptr.cast::<*mut [MaybeUninit<T>]>())) };
        }
    }

    unsafe impl<T> Owning for Vec<T> {
        fn move_out<F: FnOnce(*mut Self::Target)>(mut self, cb: F) {
            let ptr = &raw mut *self;
            cb(ptr);
            unsafe { drop(std::mem::transmute::<_, Vec<MaybeUninit<T>>>(self)) };
        }
    }
}

pub struct StaticBool<const VAL: bool> {}
pub trait True {}
trait False {}
impl True for StaticBool<true> {}
impl False for StaticBool<false> {}

/// A general value inside cera
/// Dropping this type runs destructors
#[repr(transparent)]
pub struct Val(*mut ());

#[repr(usize)]
#[derive(PartialEq, Eq, Debug)]
enum ValDiscrim {
    Complex = 0,
    Primitive = 1,
}

impl Drop for Val {
    fn drop(&mut self) {
        let other = Self(self.0);
        drop(other.into_complex());
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
        let res = Self(complex.data.as_ptr());
        debug_assert!(res.extract_discriminant() == ValDiscrim::Complex);
        mem::forget(complex);
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

mod val_complex {
    use std::{
        alloc::{alloc, dealloc, Layout},
        any::TypeId,
        ptr::NonNull,
        sync::atomic::{fence, AtomicUsize, Ordering},
    };

    use crate::interp::value::{owning::Owning, StaticBool, True, Val};

    enum ValComplexTag {
        Compound {
            count: AtomicUsize,
            len: usize,
        },
        Any {
            count: AtomicUsize,
            type_id: TypeId,
            size: usize,
            align: usize,
            drop: unsafe fn(*mut ()),
        },
    }

    impl ValComplexTag {
        fn new_any<T: 'static>() -> Self {
            unsafe fn drop_in_place<T>(ptr: *mut ()) {
                unsafe {
                    std::ptr::drop_in_place::<T>(ptr.cast());
                }
            }
            Self::Any {
                count: AtomicUsize::new(1),
                type_id: TypeId::of::<T>(),
                size: size_of::<T>(),
                align: align_of::<T>(),
                drop: drop_in_place::<T>,
            }
        }
        fn new_compound(compound: &[Val]) -> Self {
            Self::Compound {
                count: AtomicUsize::new(1),
                len: compound.len(),
            }
        }
    }

    /// This type points to some backing data
    /// The tag data is located behind the pointer, with the pointer directly after the data
    /// Padding is applied before the tag in the allocation
    ///
    /// Invariant: The [`super::VAL_FLAG_BITS`] most significant bits are always set to zero
    #[repr(C)]
    pub struct ValComplex {
        pub(super) data: NonNull<()>,
    }

    impl Drop for ValComplex {
        fn drop(&mut self) {
            match self.extract_tag() {
                ValComplexTag::Compound { count, len } => {
                    if count.fetch_sub(1, Ordering::Release) != 1 {
                        return;
                    };
                    fence(Ordering::Acquire);
                    // SAFETY: This is the last instance of our arc, which means we can drop its
                    // contents
                    unsafe {
                        std::ptr::drop_in_place(std::slice::from_raw_parts_mut(
                            self.data.cast::<Val>().as_ptr(),
                            *len,
                        ));
                    }
                }
                ValComplexTag::Any {
                    count,
                    drop,
                    size,
                    align,
                    ..
                } => {
                    if count.fetch_sub(1, Ordering::Release) != 1 {
                        return;
                    };
                    fence(Ordering::Acquire);
                    // SAFETY: This is the last instance of our arc, which means we can drop its
                    // contents
                    unsafe { drop(self.data.as_ptr()) }

                    // SAFETY: These values were obtained from the approprimate methods when
                    // instantiating the dynamic type
                    let data_layout = Layout::from_size_align(*size, *align).unwrap();
                    let tag_layout = Layout::new::<ValComplexTag>();
                    let (total_layout, data_offset) = tag_layout.extend(data_layout).unwrap();
                    let total_layout = total_layout.pad_to_align();
                    // SAFETY: This is the same layout as the initial allocation
                    unsafe {
                        dealloc(
                            self.data.byte_sub(data_offset).as_ptr().cast(),
                            total_layout,
                        );
                    }
                }
            }
        }
    }

    impl ValComplex {
        fn extract_tag(&self) -> &ValComplexTag {
            // SAFETY: type invariant, the data pointer points to after the tag
            unsafe { self.data.cast::<ValComplexTag>().sub(1).as_ref() }
        }
        /// Returns a pointer to an allocation in which you may copy over the given data, with the
        /// tag placed in accordance to [`ValComplexOwn`]'s defined layout
        fn new_uninit_val<T: ?Sized>(tag: ValComplexTag, data: &T) -> NonNull<()>
        where
            // By modular arithmetic, if the alignment is at least two and the size is "aligned" to
            // two, the following field would also be aligned to two
            StaticBool<{ align_of::<ValComplexTag>() >= 2 }>: True,
            StaticBool<{ size_of::<ValComplexTag>() % 2 == 0 }>: True,
        {
            let data_layout = Layout::for_value(data);
            let tag_layout = Layout::new::<ValComplexTag>();
            let (total_layout, data_offset) = tag_layout.extend(data_layout).unwrap();
            let total_layout = total_layout.pad_to_align();

            // SAFETY: layout sirawze is never zero
            let alloc_start =
                NonNull::new(unsafe { alloc(total_layout) }).expect("allocation should succeed");

            // SAFETY: This within the allocation, according to our layout
            let res: NonNull<ValComplexTag> = unsafe { alloc_start.add(data_offset).cast() };

            debug_assert!(
                res.addr().get() % 2 == 0,
                "Pointer alignment should aligned to 2"
            );

            // SAFETY: res_tag is properly aligned, as its trailing padding makes the end pointer a
            // multiple of its alignment as well
            // It points to a valid, uninit allocation
            unsafe {
                std::ptr::write(res.sub(1).as_ptr(), tag);
            }

            res.cast()
        }
        pub fn new_compound<T: Owning<Target = [Val]>>(compound: T) -> Self {
            let res: NonNull<Val> =
                Self::new_uninit_val(ValComplexTag::new_compound(&compound), &compound).cast();

            compound.move_out(|ptr| {
                // SAFETY: [`move_out`] guarentees that the destructors of [`ptr`] won't be ran,
                // and the pointer is ready to be written to from new_uninit_val
                unsafe {
                    std::ptr::copy_nonoverlapping(ptr.cast(), res.as_ptr(), ptr.len());
                }
            });
            Self { data: res.cast() }
        }
        pub fn new_any<T: 'static + Send + Sync>(data: T) -> Self {
            let res = Self::new_uninit_val(ValComplexTag::new_any::<T>(), &data).cast();

            // SAFETY: res is ready to be written to from the previous function call
            unsafe {
                std::ptr::write(res.as_ptr(), data);
            }

            Self { data: res.cast() }
        }
        pub fn get_any<T: 'static>(&self) -> Option<&T> {
            match self.extract_tag() {
                ValComplexTag::Any { type_id, .. } if *type_id == TypeId::of::<T>() => {
                    // SAFETY: This is safe as we have dynamically checked that the type is right
                    Some(unsafe { self.data.cast().as_ref() })
                }
                _ => None,
            }
        }
        /// Warning: may leak memory, as this doesn't run destructors
        pub(super) fn into_raw(self) -> NonNull<()> {
            let res = self.data;
            std::mem::forget(self);
            return res;
        }
        /// # Safety:
        /// ptr must have been created by [`Self::into_raw`]
        pub(super) unsafe fn from_raw(ptr: NonNull<()>) -> Self {
            Self { data: ptr }
        }
    }
}

#[cfg(test)]
mod test {
    use crate::interp::value::{Val, ValComplex};

    #[test]
    fn test_any() {
        let val = Val::new_complex(ValComplex::new_any(65u32));
        assert_eq!(val.complex().unwrap().get_any::<u32>().unwrap(), &65);
        std::mem::forget(val);
    }
}
