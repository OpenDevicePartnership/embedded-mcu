//! Blocking I²C target trait.
//!
//! See the [parent module](super) for usage patterns, addressing-mode
//! handling, the listen → respond → re-listen loop, restart semantics, and
//! worked examples. This module hosts only the blocking trait itself; all
//! shared types ([`Request`], [`ReadStatus`], [`WriteStatus`], [`Error`],
//! [`ErrorKind`], [`ErrorType`]) live in [`super`].
//!
//! For an `async fn`-based sibling that supports cancellable waits and
//! integrates with embedded executors, see the `async` sibling module under
//! [`super`].

use embedded_hal::i2c::{AddressMode, SevenBitAddress};

#[allow(unused_imports)] // referenced by intra-doc links below
use super::{Error, ErrorKind};
use super::{ErrorType, ReadStatus, Request, WriteStatus};

/// Blocking I²C target.
///
/// Generic over the [`AddressMode`] used by the underlying peripheral.
/// Defaults to [`SevenBitAddress`] to match the overwhelming majority of
/// real-world targets.
///
/// See the [parent module](super) for usage patterns, implementation
/// guidance, and worked examples.
pub trait I2c<A: AddressMode = SevenBitAddress>: ErrorType {
    /// Bring the target back to a known-clean state after a wedged transfer.
    ///
    /// Use cases include:
    ///
    /// - An async `respond_to_read` / `respond_to_write` future was
    ///   cancelled while bytes were in flight.
    /// - The controller NACKed a byte unexpectedly and the FSM is parked
    ///   waiting for a stop that never came.
    /// - An [`ErrorKind::Bus`] was reported and the application wants to
    ///   re-baseline before the next [`listen`](Self::listen).
    ///
    /// On return:
    ///
    /// - Any in-flight FIFO bytes are dropped.
    /// - Latched bus-event status is cleared.
    /// - The target is no longer driving SCL or SDA.
    /// - Configured addresses, general-call / SMBus-alert settings, and
    ///   clocking are *preserved* — the next [`listen`](Self::listen) will
    ///   accept a fresh transaction without re-initialising the driver.
    ///
    /// This method does **not** recover a bus that the *controller* has
    /// wedged (e.g. SCL stuck low). That requires a board-level GPIO-toggle
    /// dance that no target peripheral can perform.
    fn recover(&mut self) -> Result<(), Self::Error>;

    /// Wait for the next event from the controller.
    ///
    /// Blocks until the bus produces an addressable event for this target.
    /// Returns the [`Request`] that describes what the controller wants;
    /// the caller must service it (typically with one of the `respond_*`
    /// methods, then call `listen` again).
    ///
    /// # I²C Events (contract)
    ///
    /// ```text
    /// Bus:    ST SAD+W ACK ...
    ///                      ^-- listen() returns Request::Write(addr) here
    ///
    /// Bus:    ... Sr SAD+R ACK ...
    ///             ^-- listen() returns Request::RepeatedStart(prev_addr) here
    ///                          ^-- next listen() returns Request::Read(addr) here
    ///
    /// Bus:    ... SP
    ///             ^-- listen() returns Request::Stop(addr) here
    /// ```
    ///
    /// `listen` is allowed to block indefinitely; cancellable waits are
    /// the responsibility of the async sibling trait.
    fn listen(&mut self) -> Result<Request<A>, Self::Error>;

    /// Supply outgoing bytes for an in-flight read transfer.
    ///
    /// Call this *only* after [`listen`](Self::listen) has returned
    /// [`Request::Read`]. The provided slice is clocked out byte by byte
    /// in order; the call returns when the controller terminates the
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
    /// # I²C Events (contract)
    ///
    /// ```text
    /// Bus:  SAD+R ACK B0 ACK B1 ACK ... BN NACK SP
    ///                 ^-- bytes from the supplied slice
    ///                                             ^-- ReadStatus returned here
    /// ```
    fn respond_to_read(&mut self, buf: &[u8]) -> Result<ReadStatus, Self::Error>;

    /// Drain incoming bytes for an in-flight write transfer.
    ///
    /// Call this *only* after [`listen`](Self::listen) has returned
    /// [`Request::Write`] or [`Request::GeneralCall`]. The provided slice
    /// is filled byte by byte in order; the call returns when the
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
    /// # I²C Events (contract)
    ///
    /// ```text
    /// Bus:  SAD+W ACK B0 ACK B1 ACK ... BN ACK SP-or-Sr
    ///                 ^-- bytes drained into the supplied buffer
    ///                                             ^-- WriteStatus returned here
    /// ```
    fn respond_to_write(&mut self, buf: &mut [u8]) -> Result<WriteStatus, Self::Error>;
}

impl<A: AddressMode, T: I2c<A> + ?Sized> I2c<A> for &mut T {
    #[inline]
    fn recover(&mut self) -> Result<(), Self::Error> {
        T::recover(self)
    }

    #[inline]
    fn listen(&mut self) -> Result<Request<A>, Self::Error> {
        T::listen(self)
    }

    #[inline]
    fn respond_to_read(&mut self, buf: &[u8]) -> Result<ReadStatus, Self::Error> {
        T::respond_to_read(self, buf)
    }

    #[inline]
    fn respond_to_write(&mut self, buf: &mut [u8]) -> Result<WriteStatus, Self::Error> {
        T::respond_to_write(self, buf)
    }
}
