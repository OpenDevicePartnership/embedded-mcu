pub mod asynch;

/// SMBus error.
pub trait Error: core::fmt::Debug {
    /// Convert error to a generic SMBus error kind.
    ///
    /// By using this method, SMBus errors freely defined by HAL implementations
    /// can be converted to a set of generic I2C errors upon which generic
    /// code can act.
    fn kind(&self) -> ErrorKind;
    /// Convert error to a generic SMBus error kind.
    fn to_kind(kind: ErrorKind) -> Self;
}

impl Error for core::convert::Infallible {
    #[inline]
    fn kind(&self) -> ErrorKind {
        match *self {}
    }
    #[inline]
    fn to_kind(_kind: ErrorKind) -> Self {
        unreachable!()
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
    fn to_kind(kind: ErrorKind) -> Self {
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
            Self::Other => write!(
                f,
                "A different error occurred. The original error may contain more information"
            ),
        }
    }
}

/// I2C error type trait.
///
/// This just defines the error type, to be used by the other traits.
pub trait ErrorType {
    /// Error type
    type Error: Error + From<embedded_hal_async::i2c::ErrorKind>;
}

impl<T: ErrorType + ?Sized> ErrorType for &mut T {
    type Error = T::Error;
}
