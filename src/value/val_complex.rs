use std::{
    alloc::{alloc, dealloc, Layout},
    any::TypeId,
    fmt::Debug,
    mem,
    ptr::NonNull,
    slice::{self},
    sync::atomic::{fence, AtomicUsize, Ordering},
};

use crate::value::{ref_utils::Owning, StaticBool, True, Val};

enum ValComplexTag {
    Compound {
        count: AtomicUsize,
        len: usize,
    },
    Any {
        count: AtomicUsize,
        type_id: TypeId,
        layout: Layout,
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
            layout: Layout::new::<T>(),
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

impl Clone for ValComplex {
    fn clone(&self) -> Self {
        const MAX_REFCOUNT: usize = isize::MAX as usize;

        let count = match self.extract_tag() {
            ValComplexTag::Compound { count, .. } => count,
            ValComplexTag::Any { count, .. } => count,
        };
        // Only relaxed ordering is required, as the current thread must own at least one
        // count, and thus free or transfer that count while still owning it
        // Those operations would be fully ordered with this add, and so the observable owning
        // count of this thread will stay at least 1 until the thread drops its final value,
        // ordering after everything in this thread
        let prev = count.fetch_add(1, Ordering::Relaxed);
        // From the atomic ordering this is *technically* unsound as there exists a window
        // where any given thread may own a copy over this maximum, however, on the order of
        // [`MAX_REFCOUNT`] threads would be required to exist to overflow
        if prev > MAX_REFCOUNT {
            // Same reasoning as the [`fetch_add`]
            count.fetch_sub(1, Ordering::Relaxed);
            panic!(
                "Created more than {} copies of the same arc, someone's leaking references",
                usize::MAX / 2
            );
        }
        // We can now safely create a bitwise copy as we have incremented the reference count
        Self { data: self.data }
    }
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
                layout: data_layout,
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
                let tag_layout = Layout::new::<ValComplexTag>();
                let (total_layout, data_offset) = tag_layout.extend(*data_layout).unwrap();
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

impl PartialEq for ValComplex {
    fn eq(&self, other: &Self) -> bool {
        self.data.addr() == other.data.addr()
    }
}
impl Eq for ValComplex {}

impl Debug for ValComplex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.extract_tag() {
            ValComplexTag::Compound { count, .. } => f
                .debug_struct("Compound")
                .field("count", count)
                .field("data", &self.get_compound().unwrap())
                .finish(),
            ValComplexTag::Any { count, type_id, .. } => f
                .debug_struct("Any")
                .field("type_id", type_id)
                .field("count", count)
                .finish_non_exhaustive(),
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
    pub fn new_compound<T: Owning<[Val]>>(compound: T) -> Self {
        let res: NonNull<Val> = Self::new_uninit_val(
            ValComplexTag::new_compound(compound.borrow()),
            compound.borrow(),
        )
        .cast();

        compound.move_scoped(|ptr| {
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
    pub fn get_compound(&self) -> Option<&[Val]> {
        match self.extract_tag() {
            ValComplexTag::Compound { len, .. } => {
                Some(unsafe { slice::from_raw_parts(self.data.cast().as_ptr(), *len) })
            }
            _ => None,
        }
    }
    /// Warning: may leak memory, as this doesn't run destructors
    pub(super) fn into_raw(self) -> NonNull<()> {
        let res = self.data;
        mem::forget(self);
        return res;
    }
    /// # Safety:
    /// ptr must have been created by [`Self::into_raw`]
    pub(super) unsafe fn from_raw(ptr: NonNull<()>) -> Self {
        Self { data: ptr }
    }
}
