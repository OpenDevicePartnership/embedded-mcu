//! SMBus controller API.
//!
//! This module hosts SMBus controller-side traits built on top of the
//! controller traits from [`embedded_hal_async::i2c`]. Where the underlying
//! I²C controller traits move arbitrary byte streams across the bus, the
//! SMBus traits encode the higher-level SMBus protocol transactions
//! (quick command, send/receive byte, byte/word/block read/write, process
//! calls) together with optional Packet Error Code (PEC) computation and
//! verification.
//!
//! # PEC handling
//!
//! When an SMBus operation is invoked with `use_pec = true`, the
//! implementation obtains a fresh PEC calculator from
//! [`asynch::Smbus::get_pec_calc`] and feeds it the bytes that appear on
//! the wire (address, register, payload, …) in bus order. The truncated
//! low byte of [`core::hash::Hasher::finish`] is treated as the PEC.
//!
//! Implementations that do not support PEC return `None` from
//! `get_pec_calc()`; any operation with `use_pec = true` then fails with
//! [`ErrorKind::Pec`].
//!
//! # For driver authors
//!
//! Drivers should take an `Smbus` instance by value, not by `&mut`. The
//! blanket impl for `&mut T` lets the user pass either, but owning the
//! instance keeps the driver's API symmetric with the controller-side
//! traits in [`embedded_hal_async::i2c`].
//!
//! # For HAL authors
//!
//! - Bus configuration (clocking, addressing, SMBus role) is a peripheral
//!   concern handled at construction time. These traits deliberately
//!   expose none of that — they only describe the protocol-level
//!   transactions.
//!
//! - Block transfers are capped at 255 bytes per the SMBus specification;
//!   exceeding this returns [`ErrorKind::TooLargeBlockTransaction`].
//!
//! - The SMBus slave timeout (35 ms) is reported as [`ErrorKind::Timeout`].
//!
//! [`embedded_hal_async::i2c`]:
//! https://docs.rs/embedded-hal-async/1.0.0/embedded_hal_async/i2c/index.html

pub mod asynch;

/// Maximum payload size, in bytes, of a single SMBus block transfer.
///
/// The SMBus specification caps the `length` field of a block read or
/// block write at one byte, so a single block transaction can carry at
/// most 255 data bytes.
pub(crate) const MAX_BLOCK_SIZE: usize = 255;

/// Read-bit value OR-ed into the shifted address byte to mark a read.
///
/// The 8-bit address byte placed on the wire is `(address << 1) | rw`,
/// where `rw` is `0` for a write and [`READ_BIT`] (`1`) for a read.
pub(crate) const READ_BIT: u8 = 0x01;

/// Compute the 8-bit write-address byte (`address << 1`) used on the wire.
#[inline]
pub(crate) const fn write_address_byte(address: u8) -> u8 {
    address << 1
}

/// Compute the 8-bit read-address byte (`(address << 1) | READ_BIT`) used
/// on the wire.
#[inline]
pub(crate) const fn read_address_byte(address: u8) -> u8 {
    (address << 1) | READ_BIT
}

/// SMBus error.
pub trait Error: core::fmt::Debug {
    /// Convert error to a generic SMBus error kind.
    ///
    /// By using this method, SMBus errors freely defined by HAL implementations
    /// can be converted to a common set of SMBus errors upon which generic
    /// code can act.
    fn kind(&self) -> ErrorKind;
    /// Construct an error from a generic SMBus error kind.
    fn from_kind(kind: ErrorKind) -> Self;
}

impl Error for core::convert::Infallible {
    #[inline]
    fn kind(&self) -> ErrorKind {
        match *self {}
    }
    #[inline]
    fn from_kind(_kind: ErrorKind) -> Self {
        // `Infallible` is uninhabited, so this function can never actually
        // be called
        #[allow(clippy::unreachable)]
        {
            unreachable!()
        }
    }
}

/// SMBus error kind.
///
/// This represents a common set of SMBus operation errors. HAL implementations are
/// free to define more specific or additional error types. However, by providing
/// a mapping to these common SMBus errors, generic code can still react to them.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
#[non_exhaustive]
pub enum ErrorKind {
    /// Error shared with I2C.
    I2c(embedded_hal_async::i2c::ErrorKind),
    /// Bus timeout, SMBus defines slave timeout as 35ms.
    Timeout,
    /// Packet Error Checking (PEC) byte incorrect.
    Pec,
    /// Block read/write too large transfer, at most 255 bytes can be read/written at once.
    TooLargeBlockTransaction,
    /// Block read returned a byte count that did not match the caller's
    /// expected buffer length. Format is (recvd byte count, buffer length).
    BlockSizeMismatch(usize, usize),
    /// A different error occurred. The original error may contain more information.
    Other,
}

impl From<embedded_hal_async::i2c::ErrorKind> for ErrorKind {
    fn from(value: embedded_hal_async::i2c::ErrorKind) -> Self {
        Self::I2c(value)
    }
}

impl Error for ErrorKind {
    #[inline]
    fn kind(&self) -> ErrorKind {
        *self
    }
    #[inline]
    fn from_kind(kind: ErrorKind) -> Self {
        kind
    }
}

impl core::fmt::Display for ErrorKind {
    #[inline]
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::I2c(e) => e.fmt(f),
            Self::Timeout => write!(f, "Bus timeout, SMBus defines slave timeout as 35ms"),
            Self::Pec => write!(f, "Packet Error Checking (PEC) byte incorrect."),
            Self::TooLargeBlockTransaction => write!(
                f,
                "Block read/write transfer size too large, at most 255 bytes can be read/written at once."
            ),
            Self::BlockSizeMismatch(byte_count, buf_len) => write!(
                f,
                "Block read returned a byte count ({byte_count}) that did not match the caller's expected buffer length ({buf_len})."
            ),
            Self::Other => write!(
                f,
                "A different error occurred. The original error may contain more information"
            ),
        }
    }
}

/// SMBus error type trait.
///
/// This just defines the error type, to be used by the other traits.
pub trait ErrorType {
    /// Error type
    type Error: Error + From<embedded_hal_async::i2c::ErrorKind>;
}

impl<T: ErrorType + ?Sized> ErrorType for &mut T {
    type Error = T::Error;
}
