use std::fmt;
use std::mem::MaybeUninit;
use std::pin::Pin;
use std::task::{Context, Poll};

// New IO traits? What?! Why, are you bonkers?
//
// I mean, yes, probably. But, here's the goals:
//
// 1. Supports poll-based IO operations.
// 2. Opt-in vectored IO.
// 3. Can use an optional buffer pool.
// 4. Able to add completion-based (uring) IO eventually.
//
// Frankly, the last point is the entire reason we're doing this. We want to
// have forwards-compatibility with an eventually stable io-uring runtime. We
// don't need that to work right away. But it must be possible to add in here
// without breaking hyper 1.0.
//
// While in here, if there's small tweaks to poll_read or poll_write that would
// allow even the "slow" path to be faster, such as if someone didn't remember
// to forward along an `is_completion` call.

/// dox
pub trait Read {
    /// dox
    fn poll_read(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>,
        buf: ReadBufCursor<'_>,
    ) -> Poll<Result<(), std::io::Error>>;
}

/// dox
pub trait Write {
    /// dox
    fn poll_write(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>,
        buf: &[u8],
    ) -> Poll<Result<usize, std::io::Error>>;

    /// dox
    fn poll_flush(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Result<(), std::io::Error>>;

    /// dox
    fn poll_shutdown(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>,
    ) -> Poll<Result<(), std::io::Error>>;

    /// dox
    fn is_write_vectored(&self) -> bool {
        false
    }

    /// dox
    fn poll_write_vectored(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>,
        bufs: &[std::io::IoSlice<'_>],
    ) -> Poll<Result<usize, std::io::Error>> {
        let buf = bufs
            .iter()
            .find(|b| !b.is_empty())
            .map_or(&[][..], |b| &**b);
        self.poll_write(cx, buf)
    }
}

/// dox
pub struct ReadBuf<'a> {
    raw: &'a mut [MaybeUninit<u8>],
    filled: usize,
    init: usize,
}

/// dox
#[derive(Debug)]
pub struct ReadBufCursor<'a> {
    buf: &'a mut ReadBuf<'a>,
}

impl<'data> ReadBuf<'data> {
    /// dox
    #[inline]
    #[cfg(test)]
    pub(crate) fn new(raw: &'data mut [u8]) -> Self {
        let len = raw.len();
        Self {
            // SAFETY: We never de-init the bytes ourselves.
            raw: unsafe { &mut *(raw as *mut [u8] as *mut [MaybeUninit<u8>]) },
            filled: 0,
            init: len,
        }
    }

    /// dox
    #[inline]
    pub fn uninit(raw: &'data mut [MaybeUninit<u8>]) -> Self {
        Self {
            raw,
            filled: 0,
            init: 0,
        }
    }

    /// dox
    #[inline]
    pub fn filled(&self) -> &[u8] {
        // SAFETY: We only slice the filled part of the buffer, which is always valid
        unsafe { &*(&self.raw[0..self.filled] as *const [MaybeUninit<u8>] as *const [u8]) }
    }

    /// dox
    #[inline]
    pub fn unfilled<'cursor>(&'cursor mut self) -> ReadBufCursor<'cursor> {
        ReadBufCursor {
            // SAFETY: self.buf is never re-assigned, so its safe to narrow
            // the lifetime.
            buf: unsafe {
                std::mem::transmute::<&'cursor mut ReadBuf<'data>, &'cursor mut ReadBuf<'cursor>>(
                    self,
                )
            },
        }
    }

    #[inline]
    pub(crate) unsafe fn set_init(&mut self, n: usize) {
        self.init = self.init.max(n);
    }

    #[inline]
    pub(crate) unsafe fn set_filled(&mut self, n: usize) {
        self.filled = self.filled.max(n);
    }

    #[inline]
    pub(crate) fn len(&self) -> usize {
        self.filled
    }

    #[inline]
    pub(crate) fn init_len(&self) -> usize {
        self.init
    }

    #[inline]
    fn remaining(&self) -> usize {
        self.capacity() - self.filled
    }

    #[inline]
    fn capacity(&self) -> usize {
        self.raw.len()
    }
}

impl<'data> fmt::Debug for ReadBuf<'data> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ReadBuf")
            .field("filled", &self.filled)
            .field("init", &self.init)
            .field("capacity", &self.capacity())
            .finish()
    }
}

impl<'data> ReadBufCursor<'data> {
    /// Access the unfilled part of the buffer.
    ///
    /// # Safety
    ///
    /// The caller must not uninitialize any bytes that may have been
    /// initialized before.
    #[inline]
    pub unsafe fn as_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        &mut self.buf.raw[self.buf.filled..]
    }

    /// Advance the `filled` cursor by `n` bytes.
    ///
    /// # Safety
    ///
    /// The caller must take care that `n` more bytes have been initialized.
    #[inline]
    pub unsafe fn advance(&mut self, n: usize) {
        self.buf.filled = self.buf.filled.checked_add(n).expect("overflow");
        self.buf.init = self.buf.filled.max(self.buf.init);
    }

    #[inline]
    pub(crate) fn remaining(&self) -> usize {
        self.buf.remaining()
    }

    #[inline]
    pub(crate) fn put_slice(&mut self, buf: &[u8]) {
        assert!(
            self.buf.remaining() >= buf.len(),
            "buf.len() must fit in remaining()"
        );

        let amt = buf.len();
        // Cannot overflow, asserted above
        let end = self.buf.filled + amt;

        // Safety: the length is asserted above
        unsafe {
            self.buf.raw[self.buf.filled..end]
                .as_mut_ptr()
                .cast::<u8>()
                .copy_from_nonoverlapping(buf.as_ptr(), amt);
        }

        if self.buf.init < end {
            self.buf.init = end;
        }
        self.buf.filled = end;
    }
}

macro_rules! deref_async_read {
    () => {
        fn poll_read(
            mut self: Pin<&mut Self>,
            cx: &mut Context<'_>,
            buf: ReadBufCursor<'_>,
        ) -> Poll<std::io::Result<()>> {
            Pin::new(&mut **self).poll_read(cx, buf)
        }
    };
}

impl<T: ?Sized + Read + Unpin> Read for Box<T> {
    deref_async_read!();
}

impl<T: ?Sized + Read + Unpin> Read for &mut T {
    deref_async_read!();
}

macro_rules! deref_async_write {
    () => {
        fn poll_write(
            mut self: Pin<&mut Self>,
            cx: &mut Context<'_>,
            buf: &[u8],
        ) -> Poll<std::io::Result<usize>> {
            Pin::new(&mut **self).poll_write(cx, buf)
        }

        fn poll_write_vectored(
            mut self: Pin<&mut Self>,
            cx: &mut Context<'_>,
            bufs: &[std::io::IoSlice<'_>],
        ) -> Poll<std::io::Result<usize>> {
            Pin::new(&mut **self).poll_write_vectored(cx, bufs)
        }

        fn is_write_vectored(&self) -> bool {
            (**self).is_write_vectored()
        }

        fn poll_flush(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<std::io::Result<()>> {
            Pin::new(&mut **self).poll_flush(cx)
        }

        fn poll_shutdown(
            mut self: Pin<&mut Self>,
            cx: &mut Context<'_>,
        ) -> Poll<std::io::Result<()>> {
            Pin::new(&mut **self).poll_shutdown(cx)
        }
    };
}

impl<T: ?Sized + Write + Unpin> Write for Box<T> {
    deref_async_write!();
}

impl<T: ?Sized + Write + Unpin> Write for &mut T {
    deref_async_write!();
}
