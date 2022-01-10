use scroll::{Endian, Pwrite, ctx::TryIntoCtx};
use std::ops::*;

/// A buffer designed for `Pwrite` that dynamically expands to hold all types written into it.
/// Uses a standard `Vec` under the hood.
///
/// # Use Cases
///
/// * You don't know exactly how much you're writing ahead of time.
/// * Your types change size depending on context parameters or specific values.
///
/// # Allocations
///
/// By default, this buffer expands every time one byte is written. The `with_increment`
/// constructor can be used to change how much the buffer expands to reduce overall number of allocations.
///
/// # Pwrite and TryIntoCtx
///
/// Types must implement `TryIntoCtx` with a second generic parameter of `DynamicBuffer` to be used.
///
/// ```rust
/// use scroll::{ctx::TryIntoCtx, Error, LE, Pwrite};
/// use scroll_buffer::DynamicBuffer;
///
/// struct EvenOdd(u32);
///
/// impl TryIntoCtx<(), DynamicBuffer> for EvenOdd {
///     type Error = Error;
///
///     fn try_into_ctx(self, buf: &mut DynamicBuffer, _: ()) -> Result<usize, Self::Error> {
///         let offset = &mut 0;
///
///         if self.0 % 2 == 0 {
///             buf.gwrite_with(self.0, offset, LE)?;
///         } else {
///             buf.gwrite_with(self.0 as u64, offset, LE)?;
///         }
///
///         Ok(*offset)
///     }
/// }
///
/// let mut buf = DynamicBuffer::new();
///
/// let offset = buf.pwrite(EvenOdd(2), 0).unwrap();
/// assert_eq!(buf.get(), [2, 0, 0, 0]);
/// buf.pwrite(EvenOdd(3), offset).unwrap();
/// assert_eq!(buf.get()[offset..], [3, 0, 0, 0, 0, 0, 0, 0]);
/// ```
///
/// ## Why can't I use types that already implement the default TryIntoCtx?
///
/// The default type parameters for `TryIntoCtx` expose a mutable raw slice to write into.
/// This is great for pre-allocated buffers and types that have a static written size; however,
/// we cannot create a custom slice type that performs dynamic expansions under the hood.
///
/// As a result, we need to expose a separate writing type that can track offsets and calculate when to allocate.
///
/// However, if your `TryIntoCtx` impls don't use any special slice APIs and just use `Pwrite` and/or
/// basic indexing, it's extremely easy to migrate! Just add the `DynamicBuffer` generic type.
pub struct DynamicBuffer {
    pub(crate) buffer: Vec<u8>,
    alloc_increment: usize,
    pub(crate) start_offset: usize,
    write_end: usize,
}

impl DynamicBuffer {
    /// Constructs an empty `DynamicBuffer` with the default allocation increment of one byte.
    pub fn new() -> DynamicBuffer {
        Self::with_increment(1)
    }

    /// Constructs an empty `DynamicBuffer` with a custom allocation increment.
    pub fn with_increment(alloc_increment: usize) -> DynamicBuffer {
        DynamicBuffer {
            buffer: vec![],
            alloc_increment,
            start_offset: 0,
            write_end: 0,
        }
    }

    /// Gets a slice of all written bytes. Does not include extra bytes allocated by a large increment.
    /// ```rust
    /// use scroll::{LE, Pwrite};
    /// use scroll_buffer::DynamicBuffer;
    ///
    /// let mut buf = DynamicBuffer::new();
    ///
    /// assert_eq!(buf.get(), []);
    /// buf.pwrite_with(2u32, 0, LE).unwrap();
    /// assert_eq!(buf.get(), [2, 0, 0, 0]);
    /// ```
    pub fn get(&self) -> &[u8] {
        &self.buffer[..self.write_end]
    }

    /// Resets the buffer's contents. Maintains already allocated capacity.
    /// ```rust
    /// use scroll::{LE, Pwrite};
    /// use scroll_buffer::DynamicBuffer;
    ///
    /// let mut buf = DynamicBuffer::new();
    ///
    /// buf.pwrite_with(2u16, 0, LE).unwrap();
    /// assert_eq!(buf.get(), [2, 0]);
    ///
    /// buf.clear();
    /// assert_eq!(buf.get(), []);
    ///
    /// // does not reallocate!
    /// buf.pwrite_with(0xffu8, 0, LE).unwrap();
    /// assert_eq!(buf.get(), [0xff]);
    /// ```
    pub fn clear(&mut self) {
        self.buffer.clear();
        self.start_offset = 0;
        self.write_end = 0;
    }
}

impl Index<usize> for DynamicBuffer {
    type Output = u8;

    fn index(&self, index: usize) -> &Self::Output {
        self.buffer.index(self.start_offset + index)
    }
}
impl IndexMut<usize> for DynamicBuffer {
    fn index_mut(&mut self, mut index: usize) -> &mut Self::Output {
        index += self.start_offset;

        if let Some(diff) = index.checked_sub(self.buffer.len()) {
            self.buffer
                .extend(std::iter::repeat(0).take(std::cmp::max(self.alloc_increment, diff + 1)));
        }

        self.write_end = self.write_end.max(index + 1);

        self.buffer.index_mut(index)
    }
}

impl<Ctx: Copy, E> Pwrite<Ctx, E> for DynamicBuffer {
    fn pwrite_with<N: TryIntoCtx<Ctx, Self, Error = E>>(
        &mut self,
        n: N,
        offset: usize,
        ctx: Ctx,
    ) -> Result<usize, E> {
        self.start_offset += offset;

        let end = n.try_into_ctx(self, ctx)?;

        self.start_offset -= offset;

        Ok(end)
    }
}

impl TryIntoCtx<(), DynamicBuffer> for &'_ [u8] {
    type Error = scroll::Error; // doesn't matter, this is infallible

    fn try_into_ctx(self, into: &mut DynamicBuffer, _: ()) -> Result<usize, Self::Error> {
        let len = self.len();

        // set final byte to 0
        // if the buffer is not large enough, this will automatically allocate through IndexMut
        into[len - 1] = 0;

        // the following range is now guaranteed to be valid
        // TODO: should consumers have this kind of IndexMut<Range> access?
        into.buffer[into.start_offset..into.start_offset + len].copy_from_slice(self);

        Ok(len)
    }
}

macro_rules! num_impl {
    ($t:ty) => {
        impl TryIntoCtx<scroll::Endian, DynamicBuffer> for $t {
            type Error = scroll::Error; // also infallible

            fn try_into_ctx(
                self,
                buf: &mut DynamicBuffer,
                ctx: Endian,
            ) -> Result<usize, Self::Error> {
                (&if ctx.is_little() {
                    self.to_le_bytes()
                } else {
                    self.to_be_bytes()
                }).try_into_ctx(buf, ())
            }
        }

        impl TryIntoCtx<scroll::Endian, DynamicBuffer> for &$t {
            type Error = scroll::Error;

            fn try_into_ctx(
                self,
                buf: &mut DynamicBuffer,
                ctx: Endian,
            ) -> Result<usize, Self::Error> {
                (*self).try_into_ctx(buf, ctx)
            }
        }
    };
}

num_impl!(i8);
num_impl!(i16);
num_impl!(i32);
num_impl!(i64);
num_impl!(i128);

num_impl!(u8);
num_impl!(u16);
num_impl!(u32);
num_impl!(u64);
num_impl!(u128);

num_impl!(f32);
num_impl!(f64);

#[cfg(test)]
mod tests {
    use super::DynamicBuffer;
    use scroll::{Endian, Pwrite, ctx::TryIntoCtx};

    struct Test {
        a: u16,
        b: u32,
        c: u64,
    }

    #[test]
    fn int_write() {
        let mut buf = DynamicBuffer::new();

        buf.pwrite_with(0x1234u16, 0, Endian::Little).unwrap();
        buf.pwrite_with(0x5678i16, 2, Endian::Big).unwrap();

        assert_eq!(buf.get(), [0x34, 0x12, 0x56, 0x78]);
    }

    #[test]
    fn offset_write() {
        let mut buf = DynamicBuffer::new();

        buf.pwrite_with(0x1234u16, 2, Endian::Big).unwrap();

        assert_eq!(buf.get(), [0, 0, 0x12, 0x34]);
    }

    #[test]
    fn slice_write() {
        let mut buf = DynamicBuffer::new();

        buf.pwrite([1u8; 4].as_slice(), 0).unwrap();
        assert_eq!(buf.get(), [1, 1, 1, 1]);

        buf.pwrite([2u8; 2].as_slice(), 2).unwrap();
        assert_eq!(buf.get(), [1, 1, 2, 2]);
    }

    #[test]
    fn basic_write() {
        impl TryIntoCtx<Endian, DynamicBuffer> for Test {
            type Error = scroll::Error;

            fn try_into_ctx(
                self,
                buf: &mut DynamicBuffer,
                ctx: Endian,
            ) -> Result<usize, Self::Error> {
                let offset = &mut 0;

                buf.gwrite_with(self.a, offset, ctx)?;
                buf.gwrite_with(self.b, offset, ctx)?;
                buf.gwrite_with(self.c, offset, ctx)?;

                Ok(*offset)
            }
        }

        let mut buf = DynamicBuffer::new();

        buf.pwrite_with(Test { a: 1, b: 2, c: 3 }, 0, Endian::Little)
            .unwrap();

        assert_eq!(buf.get(), [1, 0, 2, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0]);
    }

    #[test]
    fn dyn_size_write() {
        impl TryIntoCtx<(bool, Endian), DynamicBuffer> for Test {
            type Error = scroll::Error;

            fn try_into_ctx(
                self,
                buf: &mut DynamicBuffer,
                (is16, ctx): (bool, Endian),
            ) -> Result<usize, Self::Error> {
                let offset = &mut 0;

                if is16 {
                    buf.gwrite_with(self.a, offset, ctx)?;
                } else {
                    buf.gwrite_with(self.a as u32, offset, ctx)?;
                }

                buf.gwrite_with(self.b, offset, ctx)?;
                buf.gwrite_with(self.c, offset, ctx)?;

                Ok(*offset)
            }
        }

        let mut buf1 = DynamicBuffer::new();
        buf1.pwrite_with(Test { a: 1, b: 2, c: 3 }, 0, (true, Endian::Little))
            .unwrap();
        assert_eq!(buf1.get(), [1, 0, 2, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0]);

        let mut buf1 = DynamicBuffer::new();
        buf1.pwrite_with(Test { a: 1, b: 2, c: 3 }, 0, (false, Endian::Little))
            .unwrap();
        assert_eq!(buf1.get(), [1, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0]);
    }

    #[test]
    fn alloc_size() {
        let mut buf = DynamicBuffer::with_increment(8);

        buf.pwrite_with(0xbabecafe_u32, 0, Endian::Big).unwrap();

        assert_eq!(buf.buffer.len(), 8);
        assert_eq!(buf.get(), [0xba, 0xbe, 0xca, 0xfe]);
    }
}

#[cfg(doctest)]
doc_comment::doctest!("../README.md");
