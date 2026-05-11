//! I²C target (slave) API.
//!
//! This module is the target-side counterpart to [`embedded_hal::i2c`], which
//! covers the controller (master) role. Where the controller-side trait
//! initiates transactions on the bus, the target-side trait *waits for*
//! transactions and responds to them.
//!
//! Two flavours of the same API are provided:
//!
//! - [`blocking::I2c`] — synchronous, blocks the calling thread.
//! - `asynch::I2c` — `async fn`-based, suitable for embedded executors
//!   (intra-doc links can't reference the raw-keyword module path; see
//!   the `async` submodule listing under [`super`] in the rendered docs).
//!
//! Both flavours share the same [`Request`], [`ReadStatus`], [`WriteStatus`],
//! [`ErrorKind`], [`Error`], [`ErrorType`], and [`NoAcknowledgeSource`]
//! types defined here, so a driver wrapping a target peripheral can be
//! generic over the flavour without converting between parallel enum sets.
//!
//! Like the controller side, this API supports both 7-bit and 10-bit
//! addressing through the sealed [`AddressMode`] marker trait, with
//! [`SevenBitAddress`] (= `u8`) and [`TenBitAddress`](super::TenBitAddress) (= `u16`) as the two
//! implementors. Drivers that only support one mode pick it as the type
//! parameter; drivers that support both can be generic over [`AddressMode`].
//! Since 7-bit addressing is overwhelmingly the common case,
//! [`SevenBitAddress`] is the default and can be omitted.
//!
//! # Multi-address peripherals
//!
//! A single I²C target peripheral often supports multiple addresses
//! (NXP LPI2C dual-address, address-range matching, general call, SMBus
//! alert). The `A` payload carried by [`Request::Read`], [`Request::Write`],
//! [`Request::RepeatedStart`], and [`Request::Stop`] tells the application
//! *which* configured address the controller is currently talking to, so the
//! application can route reads and writes to the right register file.
//! Implementations that only ever match a single address still set this
//! field, returning the matched address on every event.
//!
//! # The listen → respond → re-listen loop
//!
//! Target drivers operate as a state machine driven by the controller. The
//! application's job is to call `listen` to discover what the controller
//! wants, drain or fill bytes via `respond_to_write` / `respond_to_read`,
//! and then call `listen` again to wait for the next event. A typical
//! blocking loop looks like this:
//!
//! ```rust,no_run
//! # use embedded_mcu_hal::i2c::target::{ReadStatus, Request, WriteStatus};
//! # use embedded_mcu_hal::i2c::target::blocking::I2c;
//! # fn run<T: I2c>(target: &mut T) -> Result<(), T::Error> {
//! let mut scratch = [0u8; 32];
//! loop {
//!     match target.listen()? {
//!         Request::Write(_addr) => {
//!             // Controller is writing bytes to us. Drain into a buffer.
//!             let _status = target.respond_to_write(&mut scratch)?;
//!             // Inspect status: did the controller stop, restart, or fill the buffer?
//!         }
//!         Request::Read(_addr) => {
//!             // Controller is reading from us. Provide bytes to send.
//!             let payload = b"hello";
//!             let _status = target.respond_to_read(payload)?;
//!         }
//!         Request::RepeatedStart(_prev_addr) => {
//!             // Previous sub-transaction ended with a restart;
//!             // the next listen() will report the new direction/address.
//!         }
//!         Request::Stop(_addr) => {
//!             // Transaction complete. Reset auto-increment, etc.
//!         }
//!         Request::GeneralCall => { /* drain via respond_to_write */ }
//!         Request::SmbusAlert => { /* host responded to our alert */ }
//!         _ => { /* future variants */ }
//!     }
//! }
//! # }
//! ```
//!
//! The async loop in the [`async` sibling module](self#modules) looks
//! identical except every method call becomes `.await`.
//!
//! Each call to `respond_to_read` / `respond_to_write` services the transfer
//! until it terminates *for any reason* (stop, repeated start, buffer
//! exhausted). The returned [`ReadStatus`] / [`WriteStatus`] reports how
//! many bytes moved and *why* the transfer ended, so the caller can decide
//! whether to call again with more buffer or fall back to `listen` for the
//! next event.
//!
//! # Restart semantics
//!
//! [`Request::RepeatedStart`] fires *on the edge* — i.e. when the previous
//! sub-transaction has ended and a fresh `START` has been seen on the bus
//! before the next address byte. The address carried by the variant is the
//! address of the *just-ended* sub-transaction, mirroring the symmetry with
//! [`Request::Stop`]. This lets multi-address targets correctly preserve or
//! flush per-address state (auto-increment register pointers, SMBus block
//! contexts, secure-element session state, …).
//!
//! # Recovery
//!
//! `recover` brings the target back to a known-clean state when an in-flight
//! transfer has been wedged — typically by an async future being cancelled
//! mid-respond, an unexpected controller NACK, or a reported
//! [`ErrorKind::Bus`]. It is *not* a substitute for re-initialising the
//! driver, and it cannot un-wedge a controller that is itself holding the
//! bus. See the method-level docs for the full contract.
//!
//! # For driver authors
//!
//! Drivers should take an `I2c` instance by value, not `&mut I2c`. The
//! blanket impl for `&mut T` lets the user pass either, but owning the
//! instance keeps the driver's API symmetric with the controller-side
//! [`embedded_hal::i2c`] traits.
//!
//! ## Device driver compatible only with 7-bit addresses
//!
//! ```rust
//! use embedded_mcu_hal::i2c::target::blocking::I2c;
//! use embedded_mcu_hal::i2c::target::{ReadStatus, Request, WriteStatus};
//!
//! /// Tiny register-file target: one writable byte at offset 0.
//! pub struct ScratchTarget<T> {
//!     i2c: T,
//!     value: u8,
//! }
//!
//! impl<T: I2c> ScratchTarget<T> {
//!     pub fn new(i2c: T) -> Self {
//!         Self { i2c, value: 0 }
//!     }
//!
//!     /// Service one event from the bus. Call this in a loop.
//!     pub fn poll(&mut self) -> Result<(), T::Error> {
//!         match self.i2c.listen()? {
//!             Request::Write(_addr) => {
//!                 let mut buf = [0u8; 1];
//!                 if let WriteStatus::Stopped(1) = self.i2c.respond_to_write(&mut buf)? {
//!                     self.value = buf[0];
//!                 }
//!             }
//!             Request::Read(_addr) => {
//!                 let _ = self.i2c.respond_to_read(&[self.value])?;
//!             }
//!             _ => {}
//!         }
//!         Ok(())
//!     }
//! }
//! ```
//!
//! ## Device driver compatible only with 10-bit addresses
//!
//! ```rust
//! use embedded_mcu_hal::i2c::target::blocking::I2c;
//! use embedded_mcu_hal::i2c::target::Request;
//! use embedded_mcu_hal::i2c::TenBitAddress;
//!
//! pub struct TenBitTarget<T> {
//!     i2c: T,
//! }
//!
//! impl<T: I2c<TenBitAddress>> TenBitTarget<T> {
//!     pub fn new(i2c: T) -> Self {
//!         Self { i2c }
//!     }
//!
//!     pub fn poll(&mut self) -> Result<(), T::Error> {
//!         if let Request::Read(_addr) = self.i2c.listen()? {
//!             let _ = self.i2c.respond_to_read(&[0xAA])?;
//!         }
//!         Ok(())
//!     }
//! }
//! ```
//!
//! # For HAL authors
//!
//! - Configuring which address(es) the peripheral matches, the SMBus role,
//!   the general-call enable, and clock stretching is a peripheral concern
//!   handled at construction time. The traits deliberately expose none of
//!   that — they only describe the runtime event/respond interface.
//!
//! - `respond_to_read` / `respond_to_write` must service the transfer to a
//!   clean termination point (stop, repeated start, or buffer exhaustion)
//!   before returning, mirroring the no-pipelining rule of the controller
//!   side.
//!
//! - The blocking `listen` is allowed to block indefinitely — the async
//!   sibling module is the right place for cancellable waits.
//!
//! - The `usize` payloads on [`ReadStatus`] / [`WriteStatus`] count *bytes
//!   moved*, never bytes-remaining or buffer-positions, so callers can
//!   trivially advance their own cursors.
//!
//! [`embedded_hal::i2c`]: https://docs.rs/embedded-hal/1.0.0/embedded_hal/i2c/index.html

use embedded_hal::i2c::{AddressMode, SevenBitAddress};

pub mod asynch;
pub mod blocking;

/// I²C target error.
///
/// HAL implementations are free to define their own concrete error types;
/// they only need to expose a mapping into the generic [`ErrorKind`] set
/// so that generic application code can react.
pub trait Error: core::fmt::Debug {
    /// Convert this error into a generic [`ErrorKind`].
    fn kind(&self) -> ErrorKind;
}

impl Error for core::convert::Infallible {
    #[inline]
    fn kind(&self) -> ErrorKind {
        match *self {}
    }
}

impl Error for ErrorKind {
    #[inline]
    fn kind(&self) -> ErrorKind {
        *self
    }
}

/// I²C target error kind.
///
/// A common set of generic errors that any target HAL implementation can map
/// its concrete error type onto. Mirrors [`embedded_hal::i2c::ErrorKind`]
/// where it makes sense; the differences are documented per variant.
///
/// [`embedded_hal::i2c::ErrorKind`]: https://docs.rs/embedded-hal/1.0.0/embedded_hal/i2c/enum.ErrorKind.html
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
#[non_exhaustive]
pub enum ErrorKind {
    /// Bus error: a `START` or `STOP` condition was detected at an illegal
    /// position (not on a 9-SCL-clock-pulse boundary), framing went wrong,
    /// or the line was held in an invalid state.
    Bus,
    /// The peripheral FIFO was overrun on a write (controller sent bytes
    /// faster than the driver drained them) or underran on a read
    /// (controller clocked bytes faster than the driver supplied them and
    /// clock-stretching was not available or sufficient).
    Overrun,
    /// A bus operation was not acknowledged. See [`NoAcknowledgeSource`]
    /// for which byte was not acknowledged.
    ///
    /// On the target side this is almost always [`NoAcknowledgeSource::Data`]
    /// — the controller NACKing a byte the target sent during a
    /// `respond_to_read`. Address NACKs cannot be observed by the target
    /// itself: an address that does not match is silently ignored rather
    /// than reported as an error.
    NoAcknowledge(NoAcknowledgeSource),
    /// Multi-master arbitration was lost while the target was attempting to
    /// drive the bus (e.g. during clock stretching). Generally rare on
    /// target peripherals but reported by some IPs.
    ArbitrationLoss,
    /// A different error occurred. The original error may carry more
    /// information; consult the HAL implementation's concrete error type.
    Other,
}

/// Source of a [`ErrorKind::NoAcknowledge`].
///
/// Distinguishes whether the unacknowledged byte was an address byte or a
/// data byte. On the target side this is almost always [`Self::Data`], since
/// an unmatched address simply does not trigger an event.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum NoAcknowledgeSource {
    /// The address byte was not acknowledged.
    Address,
    /// A data byte was not acknowledged.
    Data,
    /// Either the address or a data byte was not acknowledged, but the
    /// peripheral cannot distinguish between them.
    Unknown,
}

impl core::fmt::Display for ErrorKind {
    #[inline]
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Bus => write!(f, "Bus error occurred"),
            Self::Overrun => write!(f, "The peripheral FIFO over- or under-ran"),
            Self::NoAcknowledge(s) => s.fmt(f),
            Self::ArbitrationLoss => write!(f, "The arbitration was lost"),
            Self::Other => write!(
                f,
                "A different error occurred. The original error may contain more information"
            ),
        }
    }
}

impl core::fmt::Display for NoAcknowledgeSource {
    #[inline]
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Address => write!(f, "The controller did not acknowledge the address"),
            Self::Data => write!(f, "The controller did not acknowledge a data byte"),
            Self::Unknown => write!(f, "The controller did not acknowledge the address or a data byte"),
        }
    }
}

/// I²C target error type trait.
///
/// Defines the concrete error type used by an I²C target implementation.
/// Kept separate from the trait definitions in [`blocking`] and the `async`
/// sibling module so the same error type can be shared across both flavours
/// of the API.
pub trait ErrorType {
    /// The concrete error type returned by all I²C target methods.
    type Error: Error;
}

impl<T: ErrorType + ?Sized> ErrorType for &mut T {
    type Error = T::Error;
}

/// An event observed on the I²C bus that the target needs to act on.
///
/// Returned by `listen` (in [`blocking::I2c`] or its `async` sibling). Each
/// variant that addresses the target carries the matched address as its `A`
/// payload, so multi-address peripherals can route the response to the right
/// register file. Implementations that only match a single configured
/// address still populate this field for consistency.
///
/// # Variant timing on the bus
///
/// ```text
/// Bus: ST SAD+W ACK B0 ACK B1 ACK ... SR SAD+R ACK D0 ACK D1 NACK SP
///      |-Write--^                     |-RepStart^             |-Stop-^
/// ```
///
/// - [`Self::Write`] is reported once the address+W byte has been ACKed by
///   the target. The caller drains the incoming bytes via
///   `respond_to_write`.
/// - [`Self::Read`] is reported once the address+R byte has been ACKed.
///   The caller supplies outgoing bytes via `respond_to_read`.
/// - [`Self::RepeatedStart`] is reported on the *edge* — once the previous
///   sub-transaction has ended and a fresh `START` has been seen, but
///   before the new address byte is reported as a separate `Read`/`Write`
///   event. The carried address is the address of the *just-ended*
///   sub-transaction.
/// - [`Self::Stop`] is reported when a `STOP` condition is detected. The
///   carried address is the address of the just-ended sub-transaction.
/// - [`Self::GeneralCall`] and [`Self::SmbusAlert`] are special-protocol
///   events that carry no address.
#[derive(Clone, Debug, Copy, Eq, PartialEq)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
#[non_exhaustive]
pub enum Request<A: AddressMode = SevenBitAddress> {
    /// Controller is writing data to this target at the given address.
    /// The caller should drain the bytes via `respond_to_write`.
    Write(A),
    /// Controller is reading data from this target at the given address.
    /// The caller should supply bytes via `respond_to_read`.
    Read(A),
    /// Controller issued a `Sr` (repeated start) terminating the previous
    /// sub-transaction. The carried address is the address of the
    /// **just-ended** sub-transaction (symmetric with [`Self::Stop`]).
    /// The next `listen` call will report the direction and address of the
    /// new sub-transaction.
    RepeatedStart(A),
    /// Controller issued a `STOP` condition terminating the transaction at
    /// the given address.
    Stop(A),
    /// Controller issued a general-call (address `0x00`). Any data that
    /// follows can be drained with `respond_to_write`.
    GeneralCall,
    /// SMBus alert response: the host has acknowledged this target's
    /// previously-asserted alert.
    SmbusAlert,
}

/// Outcome of a `respond_to_read` call.
///
/// Returned when the read response terminates *for any reason*. The `usize`
/// in every variant counts **bytes consumed from the supplied buffer**,
/// i.e. bytes the controller actually clocked out and ACKed.
#[derive(Clone, Debug, Copy, Eq, PartialEq)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
#[non_exhaustive]
pub enum ReadStatus {
    /// The controller terminated the read with a `NACK` + `STOP` exactly
    /// when the supplied buffer was exhausted. `usize` is the buffer
    /// length, i.e. bytes sent.
    Complete(usize),
    /// The supplied buffer was fully consumed but the controller is still
    /// asking for more bytes (it ACKed the last byte). `usize` is the
    /// number of bytes sent so far. The caller should call `respond_to_read`
    /// again with additional bytes, or accept that the controller will see
    /// `0xFF` from the bus pull-ups for any further reads until a stop.
    NeedMore(usize),
    /// The controller issued an early `STOP` (or a repeated `START`) before
    /// the buffer was exhausted. `usize` is the number of bytes the
    /// controller clocked out before terminating.
    EarlyStop(usize),
}

/// Outcome of a `respond_to_write` call.
///
/// Returned when the write response terminates *for any reason*. The `usize`
/// in every variant counts **bytes written into the supplied buffer**,
/// i.e. bytes the target ACKed.
#[derive(Clone, Debug, Copy, Eq, PartialEq)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
#[non_exhaustive]
pub enum WriteStatus {
    /// The controller issued a `STOP` condition. `usize` is the number of
    /// bytes received before the stop.
    Stopped(usize),
    /// The controller issued a `Sr` (repeated start). `usize` is the number
    /// of bytes received before the restart. The next `listen` call will
    /// report the direction/address of the new sub-transaction.
    Restarted(usize),
    /// The supplied buffer was filled before the controller terminated the
    /// transfer. `usize` is the buffer length. The caller should call
    /// `respond_to_write` again with additional buffer space, or accept
    /// that the peripheral may NACK further bytes (HAL-defined).
    BufferFull(usize),
}
