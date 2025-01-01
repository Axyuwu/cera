use std::{
    mem::size_of,
    ops::{ControlFlow, Range},
};

pub struct ExecutionEngine<const STACK_SIZE: usize = 0x10000> {
    stack: EngineStack<STACK_SIZE>,
    instruction_pointer: usize,
}

impl ExecutionEngine {
    pub fn run(&mut self) -> EngineResult<()> {
        loop {
            if let ControlFlow::Break(e) = self.step()? {
                break Ok(e);
            }
        }
    }
    pub fn step(&mut self) -> EngineResult<ControlFlow<()>> {
        let module = self.active_module();
        let ip = self.instruction_pointer;
        let (codepoint, len) = decode_varuint::<u8>(&module.as_ref()[ip..])?;
        let ip = ip + len;

        let proxy = EngineProxy;

        StdISA::exec_instruction(codepoint, proxy)?;

        self.instruction_pointer = ip;

        Ok(ControlFlow::Continue(()))
    }
    #[inline]
    fn active_module(&self) -> impl AsRef<[u8]> {
        todo!();
        &[]
    }
}

struct EngineProxy;

type InstructionResult = EngineResult<ControlFlow<()>>;

trait Instruction {
    fn run(proxy: EngineProxy) -> InstructionResult;
}

macro_rules! instructions {
    (
        $isa:ident,
        $((
            $($name:ident)?
            $(($repeat_type:ident: $($names:ident)+) $type:ident)?
            ,
            $proxy:ident $impl:tt
        ))+
    ) => {
        instructions!($isa, 0, $(($($name)? $(($repeat_type: $($names)+) $type)?, $proxy $impl))+);
        instructions_to_fn!($isa, $($($name)? $($($names),+)?),+);
    };
    ($_isa:ident, $_codepoint:expr $(,)?) => {};
    (
        $isa:ident,
        $codepoint:expr,
        (
            $($name:ident)?
            $(($repeat_type:ident: $($names:ident)+) $type:ident)?
            ,
            $proxy:ident $impl:tt
        )
        $((
            $($rem_name:ident)?
            $(($rem_repeat_type:ident: $($rem_names:ident)+) $rem_type:ident)?
            ,
            $rem_proxy:ident $rem_impl:tt
        ))*
    ) => {
        instructions_impl!(
            $isa, $($name)? $(($repeat_type: $($names)+) $type)?, $codepoint, $proxy $impl
        );
        instructions!(
            $isa,
            $codepoint + instructions_size!($($name)? $($repeat_type)?),
            $((
                $($rem_name)?
                $(($rem_repeat_type: $($rem_names)+) $rem_type)?
                ,
                $rem_proxy $rem_impl
            ))*
        );
    };
}
macro_rules! instructions_to_fn {
    (
        $isa:ident,
        $(
            $name:ident
        ),+
    ) => {
        impl ISA for $isa {
            fn exec_instruction(codepoint: u8, proxy: EngineProxy) -> InstructionResult {
                match codepoint {
                    $($name => {
                        <<$isa as ISAType>::Instruction::<$name> as Instruction>::run(proxy)
                    })+
                    _ => Err(EngineError::InvalidInstruction),
                }
            }
        }
    };
}
macro_rules! instructions_size {
    // u8 u16 u32 u64
    (usized) => {
        4
    };
    // i8 i16 i32 i64
    (isized) => {
        4
    };
    // u8 u16 u32 u64 i8 i16 i32 i64
    (sized) => {
        8
    };
    // f32 f64
    (floats) => {
        2
    };
    ($_name:ident) => {
        1
    };
}
macro_rules! instructions_impl {
    ($isa:ident, $name:ident, $codepoint:expr, $proxy:ident $impl:tt) => {
        const $name: u8 = $codepoint;
        impl Instruction for <$isa as ISAType>::Instruction::<$name> {
            fn run(mut $proxy: EngineProxy) -> InstructionResult $impl
        }
    };
    ($isa:ident, (usized:
        $name1:ident $name2:ident $name3:ident $name4:ident) $type:ident,
        $codepoint:expr, $proxy:ident $impl:tt) => {
        instructions_typed_impl!($isa, $name1 $type u8, $codepoint, $proxy $impl);
        instructions_typed_impl!($isa, $name2 $type u16, $codepoint + 1, $proxy $impl);
        instructions_typed_impl!($isa, $name3 $type u32, $codepoint + 2, $proxy $impl);
        instructions_typed_impl!($isa, $name4 $type u64, $codepoint + 3, $proxy $impl);
    };
    ($isa:ident, (isized:
        $name1:ident $name2:ident $name3:ident $name4:ident) $type:ident,
        $codepoint:expr, $proxy:ident $impl:tt) => {
        instructions_typed_impl!($isa, $name1 $type i8, $codepoint, $proxy $impl);
        instructions_typed_impl!($isa, $name2 $type i16, $codepoint + 1, $proxy $impl);
        instructions_typed_impl!($isa, $name3 $type i32, $codepoint + 2, $proxy $impl);
        instructions_typed_impl!($isa, $name4 $type i64, $codepoint + 3, $proxy $impl);
    };
    ($isa:ident, (sized:
        $name1:ident $name2:ident $name3:ident $name4:ident
        $name5:ident $name6:ident $name7:ident $name8:ident) $type:ident,
        $codepoint:expr, $proxy:ident $impl:tt) => {
        instructions_typed_impl!($isa, $name1 $type u8, $codepoint, $proxy $impl);
        instructions_typed_impl!($isa, $name2 $type u16, $codepoint + 1, $proxy $impl);
        instructions_typed_impl!($isa, $name3 $type u32, $codepoint + 2, $proxy $impl);
        instructions_typed_impl!($isa, $name4 $type u64, $codepoint + 3, $proxy $impl);
        instructions_typed_impl!($isa, $name5 $type i8, $codepoint + 4, $proxy $impl);
        instructions_typed_impl!($isa, $name6 $type i16, $codepoint + 5, $proxy $impl);
        instructions_typed_impl!($isa, $name7 $type i32, $codepoint + 6, $proxy $impl);
        instructions_typed_impl!($isa, $name8 $type i64, $codepoint + 7, $proxy $impl);
    };
    ($isa:ident,
        (floats: $name1:ident $name2:ident)
    $type:ident, $codepoint:expr, $proxy:ident $impl:tt) => {
        instructions_typed_impl!($isa, $name1 $type f32, $codepoint, $proxy $impl);
        instructions_typed_impl!($isa, $name2 $type f64, $codepoint + 1, $proxy $impl);
    };
}
macro_rules! instructions_typed_impl {
    ($isa:ident, $name:ident $type:ident $type_val:ty, $codepoint:expr, $proxy:ident $impl:tt) => {
        const $name: u8 = $codepoint;
        impl Instruction for <$isa as ISAType>::Instruction<$name> {
            fn run($proxy: EngineProxy) -> InstructionResult {
                type $type = $type_val;
                #[allow(unused_braces)]
                $impl
            }
        }
    };
}

instructions!(
    StdISA,
    (NOOP, _proxy { Ok(ControlFlow::Continue(())) })
    ((sized: UMUL8 UMUL16 UMUL32 UMUL64 IMUL8 IUML16 IMUL32 IMUL64) _Type, _proxy { todo!() })
    ((sized: UDIV8 UDIV16 UDIV32 UDIV64 IDIV8 IDIV16 IDIV32 IDIV64) _Type, _proxy { todo!() })
    ((sized: USUB8 USUB16 USUB32 USUB64 ISUB8 ISUB16 ISUB32 ISUB64) _Type, _proxy { todo!() })
    ((sized: UADD8 UADD16 UADD32 UADD64 IADD8 IADD16 IADD32 IADD64) _Type, _proxy { todo!() })
    ((sized: UMOD8 UMOD16 UMOD32 UMOD64 IMOD8 IMOD16 IMOD32 IMOD64) _Type, _proxy { todo!() })
    ((usized: SHL8 SHL16 SHL32 SHL64) _Type, _proxy { todo!() })
    ((usized: SHR8 SHR16 SHR32 SHR64) _Type, _proxy { todo!() })
    ((sized: UCMP8 UCMP16 UCMP32 UCMP64 ICMP8 ICMP16 ICMP32 ICMP64) _Type, _proxy { todo!() })
    ((floats: FCMP32 FCMP64) _Type, _proxy { todo!() })
    ((floats: FMUL32 FMUL64) _Type, _proxy { todo!() })
    ((floats: FDIV32 FDIV64) _Type, _proxy { todo!() })
    ((floats: FSUB32 FSUB64) _Type, _proxy { todo!() })
    ((floats: FADD32 FADD64) _Type, _proxy { todo!() })
    ((floats: FMOD32 FMOD64) _Type, _proxy { todo!() })
    ((usized: OR8 OR16 OR32 OR64) _Type, _proxy { todo!() })
    ((usized: XOR8 XOR16 XOR32 XOR64) _Type, _proxy { todo!() })
    ((usized: AND8 AND16 AND32 AND64) _Type, _proxy { todo!() })
    ((usized: NOT8 NOT16 NOT32 NOT64) _Type, _proxy { todo!() })
    (PAD, _proxy { todo!() })
    (PADTO, _proxy { todo!() })
    (PUSH, _proxy { todo!() })
    (LOAD, _proxy { todo!() })
    (STORE, _proxy { todo!() })
    (SLICE, _proxy { todo!() })
    (ALLOC, _proxy { todo!() })
    (FREE, _proxy { todo!() })
    (FREEZE, _proxy { todo!() })
    (UNFREEZE, _proxy { todo!() })
    (SKIP, _proxy { todo!() })
    (SKIPIF, _proxy { todo!() })
    (TBLSKIP, _proxy { todo!() })
    (SYSCALL, _proxy { todo!() })
    (CALL, _proxy { todo!() })
    (TAILREC, _proxy { todo!() })
    (RET, _proxy { todo!() })
);

#[allow(dead_code)]
struct StdISA;
trait ISAType {
    type Instruction<const CODEPOINT: u8>;
}
impl ISAType for StdISA {
    type Instruction<const CODEPOINT: u8> = StdInstruction<CODEPOINT>;
}
trait ISA {
    fn exec_instruction(codepoint: u8, proxy: EngineProxy) -> InstructionResult;
}

#[allow(dead_code)]
struct StdInstruction<const CODEPOINT: u8>;

#[derive(Debug)]
pub enum EngineError {
    EOF,
    InvalidInstruction,
    StackOverflow,
    OutOfFrameAccess,
    VarUIntDecodeError(VarUIntDecodeError),
}
impl From<VarUIntDecodeError> for EngineError {
    fn from(val: VarUIntDecodeError) -> Self {
        Self::VarUIntDecodeError(val)
    }
}
pub type EngineResult<T> = Result<T, EngineError>;

pub trait EngineValue: Sized {
    const SIZE: usize;
    /// [`bytes`] must be [`Self::SIZE`] long, may panic otherwise
    unsafe fn from_bytes_unsafe(bytes: impl AsRef<[u8]>) -> Self;
    /// [`bytes`] must be [`Self::SIZE`] long
    fn from_bytes(bytes: impl AsRef<[u8]>) -> Self
    where
        Self: SafeEngineValue,
    {
        unsafe { Self::from_bytes_unsafe(bytes) }
    }
    /// The byte slice is guarenteed to be [`Self::SIZE`] long
    fn to_bytes(&self) -> impl AsRef<[u8]>;
}

/// Safety: This trait guarentees that any bit pattern is safe to use to create this value
pub unsafe trait SafeEngineValue: EngineValue {}

macro_rules! engine_value_impl {
    (($($types:ty),*), $impl:tt) => {
        $(
            impl EngineValue for $types $impl
            unsafe impl SafeEngineValue for $types {}
        )*
    };
}
engine_value_impl!(
    (u8, u16, u32, u64, usize, i8, i16, i32, i64, isize, f32, f64),
    {
        const SIZE: usize = size_of::<Self>();
        /// [`bytes`] must be [`Self::SIZE`] long
        #[inline]
        unsafe fn from_bytes_unsafe(bytes: impl AsRef<[u8]>) -> Self {
            Self::from_be_bytes(bytes.as_ref().try_into().unwrap())
        }
        #[inline]
        fn to_bytes(&self) -> impl AsRef<[u8]> {
            self.to_be_bytes()
        }
    }
);

#[derive(Debug)]
pub struct EngineStack<const STACK_SIZE: usize> {
    frame_start: usize,
    frame_len: usize,
    stack: [u8; STACK_SIZE],
}

impl<const STACK_SIZE: usize> EngineStack<STACK_SIZE> {
    pub fn new() -> Self {
        Self {
            frame_start: 0,
            frame_len: 0,
            stack: [0; STACK_SIZE],
        }
    }
    pub fn read_value<T: SafeEngineValue>(&self, idx: usize) -> EngineResult<T> {
        Ok(T::from_bytes(self.read(idx, T::SIZE)?))
    }
    /// Safety: the stack must contain a valid representation of [`T`] at [`idx`]
    pub unsafe fn read_value_unsafe<T: EngineValue>(&self, idx: usize) -> EngineResult<T> {
        Ok(T::from_bytes_unsafe(self.read(idx, T::SIZE)?))
    }
    pub fn push_value<T: EngineValue>(&mut self, value: &T) -> EngineResult<()> {
        self.push(value.to_bytes().as_ref())
    }
    pub fn read(&self, start: usize, len: usize) -> EngineResult<&[u8]> {
        if len > self.frame_len {
            return Err(EngineError::OutOfFrameAccess);
        }
        let start = start + self.frame_start;
        Ok(&self.stack[start..(start + len)])
    }
    pub fn read_const<const LEN: usize>(&self, idx: usize) -> EngineResult<&[u8; LEN]> {
        self.read(idx, LEN)
            .map(TryInto::try_into)
            .map(Result::unwrap)
    }
    pub fn push(&mut self, src: &[u8]) -> EngineResult<()> {
        let start = self.frame_start + self.frame_len;
        let Some(dst) = self.stack.get_mut(start..(start + src.len())) else {
            return Err(EngineError::StackOverflow);
        };
        dst.copy_from_slice(src);
        self.frame_len += src.len();
        Ok(())
    }
    pub fn padto(&mut self, len: usize) -> EngineResult<()> {
        if len > STACK_SIZE || len < self.frame_len {
            return Err(EngineError::StackOverflow);
        }
        self.frame_len = len;
        Ok(())
    }
    pub fn pad(&mut self, len: usize) -> EngineResult<()> {
        self.padto(len + self.frame_len)
    }
    pub fn push_stack_frame<T: EngineValue, U>(
        &mut self,
        frame: T,
        thunk: impl FnOnce(&mut StackFrameTransitionProxy<STACK_SIZE>, &T) -> U,
    ) -> Result<U, (EngineError, T)> {
        let src_len = self.frame_len;

        if let Err(err) = self.push_value(&frame) {
            return Err((err, frame));
        }

        if let Err(err) = self.push_value(&self.frame_start.clone()) {
            return Err((err, frame));
        }

        let new_frame_start = self.frame_start + self.frame_len;
        let mut proxy = StackFrameTransitionProxy {
            stack: &mut self.stack,
            src_start: self.frame_start,
            src_len,
            dst_top: new_frame_start,
        };
        let res = thunk(&mut proxy, &frame);
        std::mem::forget(frame);

        self.frame_len = proxy.dst_top - new_frame_start;
        self.frame_start = new_frame_start;

        Ok(res)
    }
    /// Safety: the previously pushed stack frame must be of the same type
    /// Panics: if this has been called more times than [`Self::push_stack_frame`]
    pub unsafe fn pop_stack_frame<T: EngineValue>(
        &mut self,
        returned_values: impl Iterator<Item = Range<usize>>,
    ) -> (T, Result<(), EngineError>) {
        let frame_header_start = self.frame_start - (T::SIZE + usize::SIZE);
        let frame_bytes = &self.stack[frame_header_start..];
        let (frame_data, prev_frame_start) = (
            unsafe { T::from_bytes_unsafe(&frame_bytes[..T::SIZE]) },
            usize::from_bytes(&frame_bytes[T::SIZE..][..usize::SIZE]),
        );

        let prev_frame_len = frame_header_start - prev_frame_start;
        let prev_frame_end = prev_frame_start + prev_frame_len;
        let current_frame_end = self.frame_start + self.frame_len;

        let mut return_len = 0;
        let (lhs, rhs) = self.stack.split_at_mut(current_frame_end);
        let lhs = &lhs[self.frame_start..];
        for range in returned_values {
            let len = range.end - range.start;

            let Some(dst) = rhs.get_mut(return_len..).and_then(|s| s.get_mut(..len)) else {
                // IMPORTANT: UB may occur otherwise as the caller will likely call this function
                // again, thus double freeing one instance of [`T`]
                (self.frame_start, self.frame_len) = (prev_frame_start, prev_frame_len);
                return (frame_data, Err(EngineError::StackOverflow));
            };
            let Some(src) = lhs.get(range) else {
                // IMPORTANT: UB may occur otherwise as the caller will likely call this function
                // again, thus double freeing one instance of [`T`]
                (self.frame_start, self.frame_len) = (prev_frame_start, prev_frame_len);
                return (frame_data, Err(EngineError::OutOfFrameAccess));
            };

            dst.copy_from_slice(src);
            return_len += len;
        }

        self.stack.copy_within(
            current_frame_end..(current_frame_end + return_len),
            prev_frame_end,
        );

        // IMPORTANT: UB may occur otherwise as the caller will likely call this function
        // again, thus double freeing one instance of [`T`]
        (self.frame_start, self.frame_len) = (prev_frame_start, prev_frame_len + return_len);

        (frame_data, Ok(()))
    }
}

pub struct StackFrameTransitionProxy<'t, const STACK_SIZE: usize> {
    stack: &'t mut [u8; STACK_SIZE],
    src_start: usize,
    src_len: usize,
    dst_top: usize,
}

impl<'t, const STACK_SIZE: usize> StackFrameTransitionProxy<'t, STACK_SIZE> {
    #[inline]
    pub fn push_to_next(&mut self, range: Range<usize>) -> EngineResult<()> {
        let (src, dst) = self.stack.split_at_mut(self.dst_top);
        let src = src[self.src_start..][..self.src_len]
            .get(range)
            .ok_or(EngineError::OutOfFrameAccess)?;
        self.dst_top = self
            .dst_top
            .checked_add(src.len())
            .filter(|top| *top <= STACK_SIZE)
            .ok_or(EngineError::StackOverflow)?;
        dst[..src.len()].copy_from_slice(src);
        Ok(())
    }
}

type VPtr = u32;

#[derive(Debug)]
pub enum VarUIntDecodeError {
    Overflow,
    EOF,
}
trait UInt: Copy + Eq {
    const ZERO: Self;
    fn checked_mul(self, rhs: u8) -> Option<Self>;
    fn unsig_bitwise_or(self, rhs: u8) -> Self;
}
macro_rules! uint_impl {
    ($($t:ident),*) => {
        $(impl UInt for $t {
            const ZERO: Self = 0;
            #[inline]
            fn checked_mul(self, rhs: u8) -> Option<Self> {
                self.checked_mul(rhs as Self)
            }
            #[inline]
            fn unsig_bitwise_or(self, rhs: u8) -> Self {
                self | (rhs as Self)
            }
        })*
    };
}
uint_impl!(u8, u16, u32, u64, u128, usize);
/// Little endian
fn decode_varuint<T: UInt>(bytes: &[u8]) -> Result<(T, usize), VarUIntDecodeError> {
    let mut idx = 0;
    let mut pull_byte = move || -> Option<u8> {
        let byte = bytes.get(idx).map(|e| *e);
        if byte.is_some() {
            idx += 1;
        }
        byte
    };
    let mut result = T::ZERO;
    loop {
        let Some(next_byte) = pull_byte() else {
            return Err(VarUIntDecodeError::EOF);
        };

        const VALUE_BITS_SIZE: u32 = u8::BITS - 1;
        const CONTINUATION_BIT: u8 = 0x01 << VALUE_BITS_SIZE;
        const VALUE_BITS: u8 = !CONTINUATION_BIT;

        let byte_value = next_byte & VALUE_BITS;
        let continue_bit = next_byte & CONTINUATION_BIT == CONTINUATION_BIT;

        result = result
            .checked_mul(CONTINUATION_BIT)
            .ok_or(VarUIntDecodeError::Overflow)?
            .unsig_bitwise_or(byte_value);

        if !continue_bit {
            return Ok((result, idx));
        }
    }
}
