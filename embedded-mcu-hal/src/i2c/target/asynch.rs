//! Async I²C target trait.
//!
//! Async sibling of [`super::blocking`]. Method-for-method identical except
//! every method is `async fn`, so it integrates naturally with embedded
//! executors (Embassy, RTIC v2, etc.) and supports cancellable waits.
//!
//! All shared types ([`Request`], [`ReadStatus`], [`WriteStatus`],
//! [`Error`], [`ErrorKind`], [`ErrorType`]) are the same as for the
//! blocking sibling and live in [`super`]. A driver wrapping a target
//! peripheral can therefore be generic over which flavour it consumes
//! without converting between parallel enum sets.
//!
//! # Cancellation safety
//!
//! All four trait methods are `async`, which means the futures they return
//! can be dropped at *any* `.await` point — including mid-transfer.
//! Implementations must cope with that gracefully, but the API draws a
//! deliberate line: dropping a future does **not** by itself restore the
//! peripheral to a clean baseline.
//!
//! - [`I2c::listen`] is the easy case: dropping its future before any bus
//!   event has fired is a no-op. Implementations should be willing to
//!   re-enter `listen` immediately after a drop.
//!
//! - [`I2c::respond_to_read`] and [`I2c::respond_to_write`] are harder. If
//!   the future is dropped while bytes are in flight, the peripheral may
//!   still be holding the bus, draining a FIFO, or stretching the clock.
//!   The contract for callers is:
//!
//!   > After dropping a `respond_to_*` future, call [`I2c::recover`] before
//!   > the next [`I2c::listen`].
//!
//!   This restores the same baseline the blocking trait's
//!   [`recover`](super::blocking::I2c::recover) provides: in-flight bytes
//!   dropped, latched status cleared, lines released, but configured
//!   addressing/clocking preserved.
//!
//! - [`I2c::recover`] is itself async, so it can in principle also be
//!   cancelled. Implementations should make `recover` re-entrant — calling
//!   it twice in a row, or after a cancelled previous `recover`, must
//!   converge to the same clean baseline.
//!
//! See the [parent module](super) for the full listen → respond → re-listen
//! loop, addressing-mode handling, restart semantics, and worked examples.

use embedded_hal::i2c::{AddressMode, SevenBitAddress};

#[allow(unused_imports)] // referenced by intra-doc links below
use super::{Error, ErrorKind};
use super::{ErrorType, ReadStatus, Request, WriteStatus};

/// Async I²C target.
///
/// Generic over the [`AddressMode`] used by the underlying peripheral.
/// Defaults to [`SevenBitAddress`] to match the overwhelming majority of
/// real-world targets.
///
/// See the [parent module](super) for usage patterns, implementation
/// guidance, and worked examples — the loop is identical to the blocking
/// version except every call becomes `.await`.
#[allow(async_fn_in_trait)]
pub trait I2c<A: AddressMode = SevenBitAddress>: ErrorType {
    /// Bring the target back to a known-clean state after a wedged or
    /// cancelled transfer.
    ///
    /// This is the async sibling of
    /// [`super::blocking::I2c::recover`] and provides the same guarantees:
    ///
    /// - Any in-flight FIFO bytes are dropped.
    /// - Latched bus-event status is cleared.
    /// - The target is no longer driving SCL or SDA.
    /// - Configured addresses, general-call / SMBus-alert settings, and
    ///   clocking are *preserved* — the next [`listen`](Self::listen) will
    ///   accept a fresh transaction without re-initialising the driver.
    ///
    /// Callers **must** call this method after dropping a
    /// [`respond_to_read`](Self::respond_to_read) or
    /// [`respond_to_write`](Self::respond_to_write) future, before the next
    /// [`listen`](Self::listen). Implementations should make `recover`
    /// itself re-entrant: calling it twice in a row, or after a cancelled
    /// previous `recover`, must converge to the same clean baseline.
    ///
    /// This method does **not** recover a bus that the *controller* has
    /// wedged (e.g. SCL stuck low). That requires a board-level GPIO-toggle
    /// dance that no target peripheral can perform.
    async fn recover(&mut self) -> Result<(), Self::Error>;

    /// Wait for the next event from the controller.
    ///
    /// Returns a future that resolves once the bus produces an addressable
    /// event for this target. The future is cancellation-safe: dropping it
    /// before any event has fired leaves the peripheral in the same state
    /// it would be in had `listen` never been called.
    ///
    /// # I²C Events (contract)
    ///
    /// ```text
    /// Bus:    ST SAD+W ACK ...
    ///                      ^-- listen().await returns Request::Write(addr) here
    ///
    /// Bus:    ... Sr SAD+R ACK ...
    ///             ^-- listen().await returns Request::RepeatedStart(prev_addr) here
    ///                          ^-- next listen().await returns Request::Read(addr) here
    ///
    /// Bus:    ... SP
    ///             ^-- listen().await returns Request::Stop(addr) here
    /// ```
    async fn listen(&mut self) -> Result<Request<A>, Self::Error>;

    /// Supply outgoing bytes for an in-flight read transfer.
    ///
    /// Call this *only* after [`listen`](Self::listen) has returned
    /// [`Request::Read`]. The provided slice is clocked out byte by byte
    /// in order; the future resolves when the controller terminates the
    /// transfer (stop, repeated start) or when the buffer is exhausted.
    ///
    /// # Termination
    ///
    /// - [`ReadStatus::Complete`] — buffer exhausted at exactly the same
    ///   moment the controller NACKed and stopped.
    /// - [`ReadStatus::NeedMore`] — buffer exhausted with the controller
    ///   still asking for more. Call again with more bytes.
    /// - [`ReadStatus::EarlyStop`] — controller stopped (or restarted)
    ///   before the buffer ran out.
    ///
    /// # Cancellation
    ///
    /// If this future is dropped mid-transfer, the peripheral may still be
    /// holding the bus or draining its TX FIFO. The caller must call
    /// [`recover`](Self::recover) before the next [`listen`](Self::listen).
    ///
    /// # I²C Events (contract)
    ///
    /// ```text
    /// Bus:  SAD+R ACK B0 ACK B1 ACK ... BN NACK SP
    ///                 ^-- bytes from the supplied slice
    ///                                             ^-- ReadStatus returned here
    /// ```
    async fn respond_to_read(&mut self, buf: &[u8]) -> Result<ReadStatus, Self::Error>;

    /// Drain incoming bytes for an in-flight write transfer.
    ///
    /// Call this *only* after [`listen`](Self::listen) has returned
    /// [`Request::Write`] or [`Request::GeneralCall`]. The provided slice
    /// is filled byte by byte in order; the future resolves when the
    /// controller terminates the transfer (stop, repeated start) or when
    /// the buffer is full.
    ///
    /// # Termination
    ///
    /// - [`WriteStatus::Stopped`] — controller issued a `STOP`.
    /// - [`WriteStatus::Restarted`] — controller issued a repeated start.
    ///   The next [`listen`](Self::listen) will report the new
    ///   direction/address.
    /// - [`WriteStatus::BufferFull`] — buffer filled before the controller
    ///   terminated. Call again with more buffer space.
    ///
    /// # Cancellation
    ///
    /// If this future is dropped mid-transfer, the peripheral may still be
    /// holding the bus or have bytes queued in its RX FIFO. The caller must
    /// call [`recover`](Self::recover) before the next
    /// [`listen`](Self::listen).
    ///
    /// # I²C Events (contract)
    ///
    /// ```text
    /// Bus:  SAD+W ACK B0 ACK B1 ACK ... BN ACK SP-or-Sr
    ///                 ^-- bytes drained into the supplied buffer
    ///                                             ^-- WriteStatus returned here
    /// ```
    async fn respond_to_write(&mut self, buf: &mut [u8]) -> Result<WriteStatus, Self::Error>;
}

impl<A: AddressMode, T: I2c<A> + ?Sized> I2c<A> for &mut T {
    #[inline]
    async fn recover(&mut self) -> Result<(), Self::Error> {
        T::recover(self).await
    }

    #[inline]
    async fn listen(&mut self) -> Result<Request<A>, Self::Error> {
        T::listen(self).await
    }

    #[inline]
    async fn respond_to_read(&mut self, buf: &[u8]) -> Result<ReadStatus, Self::Error> {
        T::respond_to_read(self, buf).await
    }

    #[inline]
    async fn respond_to_write(&mut self, buf: &mut [u8]) -> Result<WriteStatus, Self::Error> {
        T::respond_to_write(self, buf).await
    }
}
