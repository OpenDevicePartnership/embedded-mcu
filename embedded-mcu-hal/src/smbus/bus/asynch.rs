//! Async SMBus controller trait.
//!
//! See the [parent module](super) for the protocol overview, PEC handling,
//! and driver/HAL guidance.

use core::hash::Hasher;

use crate::smbus::bus::Error as SMBusError;
use embedded_hal_async::i2c::{Error as I2cError, Operation};

/// SMBus helper trait built on top of an async I2C implementation.
///
/// This trait provides higher-level SMBus protocol operations (quick command,
/// send/receive byte, byte/word/block read/write, process calls, and PEC
/// handling) using an underlying asynchronous I2C implementation that
/// implements `embedded_hal_async::i2c::I2c`.
///
/// # Example Implementation
///
/// To implement the `Smbus` trait, you need to:
/// 1. Define an error type that implements both the crate's `ErrorType` trait
///    and converts from `embedded_hal_async::i2c::ErrorKind`.
/// 2. Define a PEC calculator type that implements `core::hash::Hasher`.
/// 3. Implement `crate::smbus::bus::ErrorType` to provide error conversions.
/// 4. Implement `embedded_hal_async::i2c::I2c` for I2C operations.
/// 5. Implement `Smbus` itself with a `get_pec_calc()` method.
///
/// ```ignore
/// // Error type implementing both SMBus and I2C error traits
/// #[derive(Debug, Clone, Copy)]
/// pub enum Error {
///     I2c(embedded_hal::i2c::ErrorKind),
///     Pec,
///     TooLargeBlockTransaction,
/// }
///
/// impl From<embedded_hal::i2c::ErrorKind> for Error {
///     fn from(kind: embedded_hal::i2c::ErrorKind) -> Self {
///         Self::I2c(kind)
///     }
/// }
///
/// impl crate::smbus::bus::Error for Error {
///     fn kind(&self) -> crate::smbus::bus::ErrorKind {
///         match self {
///             Self::I2c(e) => crate::smbus::bus::ErrorKind::I2c(*e),
///             Self::Pec => crate::smbus::bus::ErrorKind::Pec,
///             Self::TooLargeBlockTransaction => crate::smbus::bus::ErrorKind::TooLargeBlockTransaction,
///         }
///     }
///
///     fn to_kind(kind: crate::smbus::bus::ErrorKind) -> Self {
///         match kind {
///             crate::smbus::bus::ErrorKind::I2c(e) => Self::I2c(e),
///             crate::smbus::bus::ErrorKind::Pec => Self::Pec,
///             crate::smbus::bus::ErrorKind::TooLargeBlockTransaction => Self::TooLargeBlockTransaction,
///             _ => Self::I2c(embedded_hal::i2c::ErrorKind::Other),
///         }
///     }
/// }
///
/// // PEC calculator type (example using a simple CRC-8 hasher)
/// pub struct PecCalc(u8);
///
/// impl core::hash::Hasher for PecCalc {
///     fn write(&mut self, bytes: &[u8]) {
///         for &byte in bytes {
///             self.0 = self.0.wrapping_add(byte);
///         }
///     }
///
///     fn finish(&self) -> u64 {
///         self.0 as u64
///     }
/// }
///
/// // I2C master struct implementing both I2c and Smbus
/// pub struct I2cMaster {
///     // I2C hardware handle
/// }
///
/// impl embedded_hal_async::i2c::I2c for I2cMaster {
///     // Implement required I2C methods...
/// }
///
/// impl crate::smbus::bus::ErrorType for I2cMaster {
///     type Error = Error;
/// }
///
/// impl Smbus for I2cMaster {
///     type PecCalc = PecCalc;
///
///     fn get_pec_calc() -> Option<Self::PecCalc> {
///         Some(PecCalc(0))  // Return PEC calculator if available
///     }
/// }
/// ```
#[allow(async_fn_in_trait)]
pub trait Smbus: crate::smbus::bus::ErrorType + embedded_hal_async::i2c::I2c {
    /// PEC (Packet Error Code) calculator type.
    ///
    /// When a SMBus operation requests PEC verification (`use_pec = true`),
    /// implementations should return a `PecCalc` instance from `get_pec_calc()`
    /// that is then fed the transmitted/received bytes in bus order. The calculator
    /// should expose the checksum through `finish()`; this crate treats the
    /// resulting value as a single-byte PEC.
    ///
    /// The type must implement `core::hash::Hasher`. PEC calculators are obtained
    /// via the `get_pec_calc()` method, which returns `Option<Self::PecCalc>`. If
    /// `get_pec_calc()` returns `None`, any operation with `use_pec = true` will
    /// return an error of kind `ErrorKind::Pec`.
    type PecCalc: core::hash::Hasher;

    /// Obtain a PEC calculator instance if PEC support is available.
    ///
    /// This method is called by SMBus operations that request PEC verification
    /// (`use_pec = true`). Implementations should return `Some(calculator)` if PEC
    /// support is available, or `None` if not. When `None` is returned, any
    /// operation with `use_pec = true` will fail with an error of kind
    /// `ErrorKind::Pec`.
    ///
    /// The returned calculator should be a fresh instance ready to hash bytes
    /// in bus order using the `core::hash::Hasher` interface.
    ///
    /// Returns `Some(PecCalc)` if PEC is available, or `None` if PEC support
    /// is not implemented or unavailable.
    fn get_pec_calc() -> Option<Self::PecCalc>;

    /// Check PEC (Packet Error Code) validity.
    ///
    /// Compares a received PEC byte against a computed PEC value to verify data
    /// integrity. This is a helper method used internally by read operations that
    /// perform PEC verification.
    ///
    /// Parameters:
    /// - `received_pec`: The PEC byte received from the bus.
    /// - `computed_pec`: The PEC value computed locally via the `PecCalc` hasher's
    ///   `finish()` method. Only the low byte is used for comparison.
    ///
    /// Returns `Ok(())` if the received PEC matches the computed PEC (after
    /// truncating to a single byte), or an error of kind `ErrorKind::Pec` if
    /// the values do not match, indicating a data integrity error.
    fn check_pec(received_pec: u8, computed_pec: u64) -> Result<(), <Self as crate::smbus::bus::ErrorType>::Error> {
        computed_pec
            .eq(&received_pec.into())
            .then_some(())
            .ok_or_else(|| <Self as crate::smbus::bus::ErrorType>::Error::to_kind(crate::smbus::bus::ErrorKind::Pec))
    }

    /// Obtain a fresh PEC calculator pre-fed with the write-address byte.
    ///
    /// Returns an [`ErrorKind::Pec`](crate::smbus::bus::ErrorKind::Pec) error
    /// if [`get_pec_calc`](Self::get_pec_calc) returns `None`.
    fn pec_calc_with_write_addr(address: u8) -> Result<Self::PecCalc, <Self as crate::smbus::bus::ErrorType>::Error> {
        let mut pec = Self::get_pec_calc().ok_or(<Self as crate::smbus::bus::ErrorType>::Error::to_kind(
            crate::smbus::bus::ErrorKind::Pec,
        ))?;
        pec.write_u8(crate::smbus::bus::write_address_byte(address));
        Ok(pec)
    }

    /// Truncate a finished PEC value to its low byte.
    ///
    /// Returns an [`ErrorKind::Pec`](crate::smbus::bus::ErrorKind::Pec) error
    /// if the value does not fit in a byte.
    fn finalize_pec_byte(pec: u64) -> Result<u8, <Self as crate::smbus::bus::ErrorType>::Error> {
        pec.try_into()
            .map_err(|_| <Self as crate::smbus::bus::ErrorType>::Error::to_kind(crate::smbus::bus::ErrorKind::Pec))
    }

    /// Write a buffer of data with optional PEC computation and verification.
    ///
    /// This is a low-level helper method that performs I2C write operations with
    /// optional PEC (Packet Error Code) computation. When `use_pec` is false, the
    /// data is written as-is. When `use_pec` is true, a PEC byte is computed over
    /// the address and data payload, and the caller-provided buffer must have space
    /// for the PEC byte at the end (i.e., the buffer should be sized to
    /// `payload_len + 1` to accommodate the computed PEC).
    ///
    /// Parameters:
    /// - `address`: 7-bit target device address (used in PEC calculation).
    /// - `use_pec`: When true, compute PEC and append it to the transfer.
    ///   When false, write the buffer without PEC.
    /// - `operations`: Mutable buffer containing the data to write. When `use_pec`
    ///   is true, the last byte of this buffer will be overwritten with the computed
    ///   PEC value. The caller must ensure sufficient space.
    ///
    /// Returns `Ok(())` on success, or an error if:
    /// - The underlying I2C write fails (converted from `I2cError`)
    /// - PEC is requested but unavailable (returns `ErrorKind::Pec`)
    /// - PEC computation fails or overflows (returns `ErrorKind::Pec`)
    async fn write_buf(
        &mut self,
        address: u8,
        use_pec: bool,
        operations: &mut [u8],
    ) -> Result<(), <Self as crate::smbus::bus::ErrorType>::Error> {
        if use_pec {
            let mut pec = Self::pec_calc_with_write_addr(address)?;
            let (pec_elem, rest) =
                operations
                    .split_last_mut()
                    .ok_or(<Self as crate::smbus::bus::ErrorType>::Error::to_kind(
                        crate::smbus::bus::ErrorKind::Pec,
                    ))?;
            pec.write(rest);
            *pec_elem = Self::finalize_pec_byte(pec.finish())?;
        }
        self.write(address, operations)
            .await
            .map_err(|i2c_err| i2c_err.kind())?;
        Ok(())
    }

    /// Read a buffer of data with optional PEC verification.
    ///
    /// This is a low-level helper method that performs I2C read operations with
    /// optional PEC (Packet Error Code) verification. When `use_pec` is false,
    /// the data is read as-is. When `use_pec` is true, the data (excluding the
    /// PEC byte) is hashed using the `PecCalc` calculator, and the final PEC byte
    /// in the buffer is verified against the locally computed PEC. The caller must
    /// ensure the buffer has space for the PEC byte (i.e., for a single data byte
    /// with PEC, provide a 2-byte buffer).
    ///
    /// Parameters:
    /// - `address`: 7-bit target device address (used in PEC calculation).
    /// - `use_pec`: When true, verify the PEC byte at the end of the buffer.
    ///   When false, read the buffer without PEC verification.
    /// - `read`: Mutable buffer to store the received data. The last byte should
    ///   contain the PEC byte if `use_pec` is true. All other bytes contain the
    ///   actual payload data.
    ///
    /// Returns `Ok(())` on success, or an error if:
    /// - The underlying I2C read fails (converted from `I2cError`)
    /// - PEC is requested but unavailable (returns `ErrorKind::Pec`)
    /// - PEC verification fails due to mismatch (returns `ErrorKind::Pec`)
    async fn read_buf(
        &mut self,
        address: u8,
        use_pec: bool,
        read: &mut [u8],
    ) -> Result<(), <Self as crate::smbus::bus::ErrorType>::Error> {
        if use_pec {
            let mut pec = Self::pec_calc_with_write_addr(address)?;
            self.read(address, read).await.map_err(|i2c_err| i2c_err.kind())?;
            let (pec_byte, rest) = read
                .split_last()
                .ok_or(<Self as crate::smbus::bus::ErrorType>::Error::to_kind(
                    crate::smbus::bus::ErrorKind::Pec,
                ))?;
            pec.write(rest);

            Self::check_pec(*pec_byte, pec.finish())?;
        } else {
            self.read(address, read).await.map_err(|i2c_err| i2c_err.kind())?;
        }

        Ok(())
    }

    /// Write a buffer and then read a buffer, with optional PEC verification.
    ///
    /// Performs a single I²C transaction consisting of a `Write(write)`
    /// followed by a `Read(read)`. When `use_pec` is true, the caller must
    /// size `read` to include one extra trailing byte for the PEC; that
    /// byte is then verified against a locally computed PEC that covers
    /// (in bus order) the write-address byte, `write`, the read-address
    /// byte and the data portion of `read` (everything except the trailing
    /// PEC byte).
    ///
    /// Returns an [`ErrorKind::Pec`](crate::smbus::bus::ErrorKind::Pec)
    /// error if PEC support is unavailable or the received PEC does not
    /// match.
    async fn write_read_buf(
        &mut self,
        address: u8,
        use_pec: bool,
        write: &[u8],
        read: &mut [u8],
    ) -> Result<(), <Self as crate::smbus::bus::ErrorType>::Error> {
        // When PEC is requested, fail fast without touching the bus if no
        // PEC calculator is available.
        let mut pec = if use_pec {
            Some(Self::pec_calc_with_write_addr(address)?)
        } else {
            None
        };
        self.transaction(address, &mut [Operation::Write(write), Operation::Read(read)])
            .await
            .map_err(|i2c_err| i2c_err.kind())?;
        if let Some(pec) = pec.as_mut() {
            pec.write(write);
            pec.write_u8(crate::smbus::bus::read_address_byte(address));
            let (pec_byte, rest) = read
                .split_last()
                .ok_or(<Self as crate::smbus::bus::ErrorType>::Error::to_kind(
                    crate::smbus::bus::ErrorKind::Pec,
                ))?;
            pec.write(rest);
            Self::check_pec(*pec_byte, pec.finish())?;
        }
        Ok(())
    }

    /// Quick Command
    ///
    /// Perform an SMBus Quick Command which uses the R/W bit of the 7-bit address
    /// to indicate the command (no data payload is transferred).
    ///
    /// Parameters:
    /// - `address`: 7-bit target device address.
    /// - `read`: when true, the R/W bit denotes a read (controller issues a read);
    ///   otherwise it denotes a write.
    ///
    /// Returns `Ok(())` on success or an error converted from the underlying I2C
    /// implementation on failure.
    #[inline]
    async fn quick_command(
        &mut self,
        address: u8,
        read: bool,
    ) -> Result<(), <Self as crate::smbus::bus::ErrorType>::Error> {
        self.transaction(
            address,
            &mut if read {
                [Operation::Read(&mut [])]
            } else {
                [Operation::Write(&[])]
            },
        )
        .await
        .map_err(|i2c_err| i2c_err.kind())?;
        Ok(())
    }

    /// Send Byte
    ///
    /// Sends a single command byte to the target device.
    ///
    /// Parameters:
    /// - `address`: 7-bit target device address.
    /// - `byte`: command byte to send.
    /// - `use_pec`: when true, compute a PEC byte over the address and command
    ///   and append it to the transfer. If PEC support is unavailable or PEC
    ///   computation fails, an error of kind `ErrorKind::Pec` is returned.
    ///
    /// Returns `Ok(())` on success or an error converted from the underlying I2C
    /// implementation on failure.
    async fn send_byte(
        &mut self,
        address: u8,
        byte: u8,
        use_pec: bool,
    ) -> Result<(), <Self as crate::smbus::bus::ErrorType>::Error> {
        if use_pec {
            self.write_buf(address, true, &mut [byte, 0]).await
        } else {
            self.write_buf(address, false, &mut [byte]).await
        }
    }

    /// Receive Byte
    ///
    /// Read a single byte from the target device.
    ///
    /// Parameters:
    /// - `address`: 7-bit target device address.
    /// - `use_pec`: when true, expect an extra PEC byte after the data and
    ///   verify it against a locally computed PEC. If PEC support is unavailable,
    ///   or on PEC mismatch, an error of kind `ErrorKind::Pec` is returned.
    ///
    /// Returns the received byte on success or an error converted from the
    /// underlying I2C implementation on failure.
    async fn receive_byte(
        &mut self,
        address: u8,
        use_pec: bool,
    ) -> Result<u8, <Self as crate::smbus::bus::ErrorType>::Error> {
        if use_pec {
            let mut buf = [0u8; 2];
            self.read_buf(address, use_pec, &mut buf).await?;
            Ok(buf[0])
        } else {
            let mut buf = [0u8];
            self.read_buf(address, use_pec, &mut buf).await?;
            Ok(buf[0])
        }
    }

    /// Write Byte
    ///
    /// Write a single data byte to a command/register on the target device.
    ///
    /// Parameters:
    /// - `address`: 7-bit target device address.
    /// - `register`: command/register code to write to.
    /// - `byte`: data byte to write.
    /// - `use_pec`: when true, compute and append a PEC byte that covers the
    ///   address, register and data. If PEC support is unavailable or PEC
    ///   computation fails, an error of kind `ErrorKind::Pec` is returned.
    ///
    /// Returns `Ok(())` on success or an error converted from the underlying I2C
    /// implementation on failure.
    async fn write_byte(
        &mut self,
        address: u8,
        register: u8,
        byte: u8,
        use_pec: bool,
    ) -> Result<(), <Self as crate::smbus::bus::ErrorType>::Error> {
        if use_pec {
            self.write_buf(address, use_pec, &mut [register, byte, 0]).await
        } else {
            self.write_buf(address, use_pec, &mut [register, byte]).await
        }
    }

    /// Write Word
    ///
    /// Write a 16-bit word to a command/register on the target device. The word
    /// is transmitted as little-endian (low byte first) on the bus.
    ///
    /// Parameters:
    /// - `address`: 7-bit target device address.
    /// - `register`: command/register code to write to.
    /// - `word`: 16-bit value to send (little-endian on the wire).
    /// - `use_pec`: when true, compute and append a PEC byte that covers the
    ///   address, register and word bytes. If PEC support is unavailable or PEC
    ///   computation fails, an error of kind `ErrorKind::Pec` is returned.
    ///
    /// Returns `Ok(())` on success or an error converted from the underlying I2C
    /// implementation on failure.
    async fn write_word(
        &mut self,
        address: u8,
        register: u8,
        word: u16,
        use_pec: bool,
    ) -> Result<(), <Self as crate::smbus::bus::ErrorType>::Error> {
        let word_bytestream = u16::to_le_bytes(word);
        if use_pec {
            self.write_buf(
                address,
                use_pec,
                &mut [register, word_bytestream[0], word_bytestream[1], 0],
            )
            .await
        } else {
            self.write_buf(
                address,
                use_pec,
                &mut [register, word_bytestream[0], word_bytestream[1]],
            )
            .await
        }
    }

    /// Read Byte
    ///
    /// Write a command/register and then read a single byte from the target
    /// device using a repeated START (no intervening STOP).
    ///
    /// Parameters:
    /// - `address`: 7-bit target device address.
    /// - `register`: command/register code to request.
    /// - `use_pec`: when true, expect an extra PEC byte after the data and
    ///   verify it against a locally computed PEC. If PEC support is unavailable
    ///   or on mismatch, an error of kind `ErrorKind::Pec` is returned.
    ///
    /// Returns the received byte on success or an error converted from the
    /// underlying I2C implementation on failure.
    async fn read_byte(
        &mut self,
        address: u8,
        register: u8,
        use_pec: bool,
    ) -> Result<u8, <Self as crate::smbus::bus::ErrorType>::Error> {
        if use_pec {
            let mut buf = [0u8; 2];
            self.write_read_buf(address, true, &[register], &mut buf).await?;
            Ok(buf[0])
        } else {
            let mut buf = [0u8; 1];
            self.write_read_buf(address, false, &[register], &mut buf).await?;
            Ok(buf[0])
        }
    }

    /// Read Word
    ///
    /// Write a command/register and then read a 16-bit word from the target
    /// device using a repeated START (no intervening STOP). The two bytes are
    /// interpreted as little-endian (low byte first).
    ///
    /// Parameters:
    /// - `address`: 7-bit target device address.
    /// - `register`: command/register code to request.
    /// - `use_pec`: when true, expect an extra PEC byte after the two data
    ///   bytes and verify it against a locally computed PEC. If PEC support
    ///   is unavailable or on mismatch, an error of kind `ErrorKind::Pec`
    ///   is returned.
    ///
    /// Returns the received 16-bit word on success or an error converted from
    /// the underlying I2C implementation on failure.
    async fn read_word(
        &mut self,
        address: u8,
        register: u8,
        use_pec: bool,
    ) -> Result<u16, <Self as crate::smbus::bus::ErrorType>::Error> {
        if use_pec {
            let mut buf = [0u8; 3];
            self.write_read_buf(address, true, &[register], &mut buf).await?;
            Ok(u16::from_le_bytes([buf[0], buf[1]]))
        } else {
            let mut buf = [0u8; 2];
            self.write_read_buf(address, false, &[register], &mut buf).await?;
            Ok(u16::from_le_bytes(buf))
        }
    }

    /// Process Call
    ///
    /// Performs a combined write of a 16-bit word to the given `register`,
    /// followed by a read of a 16-bit response from the device.
    ///
    /// Parameters:
    /// - `address`: 7-bit target address of the slave device.
    /// - `register`: command/register code to send.
    /// - `word`: 16-bit parameter sent to the device (little-endian on the bus).
    /// - `use_pec`: when true, a PEC (Packet Error Code) is calculated and
    ///   verified for the returned data. If PEC support is unavailable or
    ///   verification fails, an error with kind `ErrorKind::Pec` is returned.
    ///
    /// Returns the 16-bit response from the device on success.
    async fn process_call(
        &mut self,
        address: u8,
        register: u8,
        word: u16,
        use_pec: bool,
    ) -> Result<u16, <Self as crate::smbus::bus::ErrorType>::Error> {
        if use_pec {
            let mut buf = [0u8; 3];
            let mut pec = Self::pec_calc_with_write_addr(address)?;
            pec.write_u8(register);
            pec.write_u16(word);
            pec.write_u8(crate::smbus::bus::read_address_byte(address));
            self.transaction(
                address,
                &mut [
                    Operation::Write(&[register]),
                    Operation::Write(&word.to_le_bytes()),
                    Operation::Read(&mut buf),
                ],
            )
            .await
            .map_err(|i2c_err| i2c_err.kind())?;
            let (recvd_pec, data) = buf
                .split_last()
                .ok_or(<Self as crate::smbus::bus::ErrorType>::Error::to_kind(
                    crate::smbus::bus::ErrorKind::Pec,
                ))?;
            pec.write(data);
            Self::check_pec(*recvd_pec, pec.finish())?;
            Ok(u16::from_le_bytes([buf[0], buf[1]]))
        } else {
            let mut buf = [0u8; 2];
            self.transaction(
                address,
                &mut [
                    Operation::Write(&[register]),
                    Operation::Write(&word.to_le_bytes()),
                    Operation::Read(&mut buf),
                ],
            )
            .await
            .map_err(|i2c_err| i2c_err.kind())?;
            Ok(u16::from_le_bytes(buf))
        }
    }

    /// Block Write
    ///
    /// Sends a block write to `register`. The transfer format is:
    /// - write `register`
    /// - write `length` (1 byte)
    /// - write `length` data bytes
    /// - if `use_pec` is true, append PEC (1 byte)
    ///
    /// `data.len()` must be <= 255. When `use_pec` is true a PEC byte is
    /// computed over the same sequence of bytes that appear on the bus and
    /// appended to the transaction. If PEC support is unavailable, an error
    /// of kind `ErrorKind::Pec` is returned.
    async fn block_write(
        &mut self,
        address: u8,
        register: u8,
        data: &[u8],
        use_pec: bool,
    ) -> Result<(), <Self as crate::smbus::bus::ErrorType>::Error> {
        if data.len() > crate::smbus::bus::MAX_BLOCK_SIZE {
            return Err(<Self as crate::smbus::bus::ErrorType>::Error::to_kind(
                crate::smbus::bus::ErrorKind::TooLargeBlockTransaction,
            ));
        }
        if use_pec {
            let mut pec = Self::pec_calc_with_write_addr(address)?;
            pec.write_u8(register);
            pec.write_u8(data.len() as u8);
            pec.write(data);
            let pec: u8 = Self::finalize_pec_byte(pec.finish())?;
            Ok(self
                .transaction(
                    address,
                    &mut [
                        Operation::Write(&[register]),
                        Operation::Write(&[data.len() as u8]),
                        Operation::Write(data),
                        Operation::Write(&[pec]),
                    ],
                )
                .await
                .map_err(|i2c_err| i2c_err.kind())?)
        } else {
            Ok(self
                .transaction(
                    address,
                    &mut [
                        Operation::Write(&[register]),
                        Operation::Write(&[data.len() as u8]),
                        Operation::Write(data),
                    ],
                )
                .await
                .map_err(|i2c_err| i2c_err.kind())?)
        }
    }

    /// Block Read
    ///
    /// Reads a block from `register`. The expected transfer sequence is:
    /// - write `register`
    /// - read `length` (1 byte)
    /// - read `length` data bytes into `data`
    /// - if `use_pec` is true, read one PEC byte and verify it
    ///
    /// The provided `data` buffer should be sized to hold the expected
    /// incoming block payload (max 255). If `use_pec` is true, the PEC
    /// byte is validated against a locally computed PEC. If PEC support
    /// is unavailable or on mismatch, an error with kind `ErrorKind::Pec`
    /// is returned.
    async fn block_read(
        &mut self,
        address: u8,
        register: u8,
        data: &mut [u8],
        use_pec: bool,
    ) -> Result<(), <Self as crate::smbus::bus::ErrorType>::Error> {
        if data.len() > crate::smbus::bus::MAX_BLOCK_SIZE {
            return Err(<Self as crate::smbus::bus::ErrorType>::Error::to_kind(
                crate::smbus::bus::ErrorKind::TooLargeBlockTransaction,
            ));
        }
        let mut msg_size = [0u8];
        if use_pec {
            let mut pec_buf = [0u8];
            let mut pec = Self::pec_calc_with_write_addr(address)?;
            pec.write_u8(register);
            pec.write_u8(crate::smbus::bus::read_address_byte(address));
            self.transaction(
                address,
                &mut [
                    Operation::Write(&[register]),
                    Operation::Read(&mut msg_size),
                    Operation::Read(data),
                    Operation::Read(&mut pec_buf),
                ],
            )
            .await
            .map_err(|i2c_err| i2c_err.kind())?;
            pec.write(&msg_size);
            pec.write(data);
            Self::check_pec(pec_buf[0], pec.finish())?;
            Ok(())
        } else {
            self.transaction(
                address,
                &mut [
                    Operation::Write(&[register]),
                    Operation::Read(&mut msg_size),
                    Operation::Read(data),
                ],
            )
            .await
            .map_err(|i2c_err| i2c_err.kind())?;
            Ok(())
        }
    }

    /// Block Write / Block Read / Process Call
    ///
    /// Performs a combined transaction that first writes a block payload,
    /// then reads back a block response. The semantics are analogous to a
    /// block write followed by a block read in a single transaction; when
    /// `use_pec` is true the PEC is verified for the entire exchange.
    ///
    /// Parameters:
    /// - `write_data`: data to send as the write block payload.
    /// - `read_data`: buffer where the incoming block payload is stored.
    /// - The sum of `write_data.len()` and `read_data.len()` must be <= 255.
    /// - `use_pec`: when true, a PEC byte is read after the response and
    ///   validated. If PEC support is unavailable or on mismatch, an
    ///   `ErrorKind::Pec` is returned.
    async fn block_write_block_read_process_call(
        &mut self,
        address: u8,
        register: u8,
        write_data: &[u8],
        read_data: &mut [u8],
        use_pec: bool,
    ) -> Result<(), <Self as crate::smbus::bus::ErrorType>::Error> {
        if write_data.len() + read_data.len() > crate::smbus::bus::MAX_BLOCK_SIZE {
            return Err(<Self as crate::smbus::bus::ErrorType>::Error::to_kind(
                crate::smbus::bus::ErrorKind::TooLargeBlockTransaction,
            ));
        }
        let mut read_msg_size = [0u8];
        if use_pec {
            let mut pec_buf = [0u8];
            let mut pec = Self::pec_calc_with_write_addr(address)?;
            pec.write_u8(register);
            pec.write_u8(write_data.len() as u8);
            pec.write(write_data);
            pec.write_u8(crate::smbus::bus::read_address_byte(address));
            self.transaction(
                address,
                &mut [
                    Operation::Write(&[register]),
                    Operation::Write(&[write_data.len() as u8]),
                    Operation::Write(write_data),
                    Operation::Read(&mut read_msg_size),
                    Operation::Read(read_data),
                    Operation::Read(&mut pec_buf),
                ],
            )
            .await
            .map_err(|i2c_err| i2c_err.kind())?;
            pec.write(&read_msg_size);
            pec.write(read_data);
            Self::check_pec(pec_buf[0], pec.finish())?;
            Ok(())
        } else {
            self.transaction(
                address,
                &mut [
                    Operation::Write(&[register]),
                    Operation::Write(&[write_data.len() as u8]),
                    Operation::Write(write_data),
                    Operation::Read(&mut read_msg_size),
                    Operation::Read(read_data),
                ],
            )
            .await
            .map_err(|i2c_err| i2c_err.kind())?;
            Ok(())
        }
    }
}

impl<T: Smbus + ?Sized> Smbus for &mut T {
    type PecCalc = T::PecCalc;

    #[inline]
    fn get_pec_calc() -> Option<Self::PecCalc> {
        T::get_pec_calc()
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::indexing_slicing, clippy::cast_possible_truncation)]
mod tests {
    use super::Smbus;
    use crate::smbus::bus::{
        read_address_byte, write_address_byte, Error as SmbusError, ErrorKind, ErrorType, MAX_BLOCK_SIZE, READ_BIT,
    };
    use core::hash::Hasher;
    use embedded_hal_async::i2c::{ErrorKind as I2cErrorKind, I2c, Operation};
    use embedded_hal_mock::eh1::i2c::{Mock as I2cMock, Transaction as Tx};
    use smbus_pec::{pec, Pec};

    const ADDR: u8 = 0x42;
    const REG: u8 = 0x07;

    /// Test SMBus error type.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    struct TestError(ErrorKind);

    impl From<I2cErrorKind> for TestError {
        fn from(k: I2cErrorKind) -> Self {
            Self(ErrorKind::I2c(k))
        }
    }

    impl SmbusError for TestError {
        fn kind(&self) -> ErrorKind {
            self.0
        }
        fn to_kind(kind: ErrorKind) -> Self {
            Self(kind)
        }
    }

    /// Compute the expected SMBus PEC byte over a flat concatenation of byte
    /// slices, using the `smbus-pec` crate as the reference implementation.
    fn expected_pec(parts: &[&[u8]]) -> u8 {
        let mut buf: std::vec::Vec<u8> = std::vec::Vec::new();
        for p in parts {
            buf.extend_from_slice(p);
        }
        pec(&buf)
    }

    /// Bus that wires `embedded_hal_mock::eh1::i2c::Mock` to the `Smbus` trait.
    struct TestBus {
        i2c: I2cMock,
    }

    impl embedded_hal_async::i2c::ErrorType for TestBus {
        type Error = I2cErrorKind;
    }

    impl I2c for TestBus {
        async fn transaction(&mut self, address: u8, ops: &mut [Operation<'_>]) -> Result<(), Self::Error> {
            <I2cMock as I2c>::transaction(&mut self.i2c, address, ops).await
        }
        async fn read(&mut self, address: u8, read: &mut [u8]) -> Result<(), Self::Error> {
            <I2cMock as I2c>::read(&mut self.i2c, address, read).await
        }
        async fn write(&mut self, address: u8, write: &[u8]) -> Result<(), Self::Error> {
            <I2cMock as I2c>::write(&mut self.i2c, address, write).await
        }
    }

    impl ErrorType for TestBus {
        type Error = TestError;
    }

    impl Smbus for TestBus {
        type PecCalc = Pec;
        fn get_pec_calc() -> Option<Self::PecCalc> {
            Some(Pec::new())
        }
    }

    /// Bus without PEC support, used to validate the unavailable-PEC error path.
    struct NoPecBus {
        i2c: I2cMock,
    }

    impl embedded_hal_async::i2c::ErrorType for NoPecBus {
        type Error = I2cErrorKind;
    }

    impl I2c for NoPecBus {
        async fn transaction(&mut self, address: u8, ops: &mut [Operation<'_>]) -> Result<(), Self::Error> {
            <I2cMock as I2c>::transaction(&mut self.i2c, address, ops).await
        }
        async fn read(&mut self, address: u8, read: &mut [u8]) -> Result<(), Self::Error> {
            <I2cMock as I2c>::read(&mut self.i2c, address, read).await
        }
        async fn write(&mut self, address: u8, write: &[u8]) -> Result<(), Self::Error> {
            <I2cMock as I2c>::write(&mut self.i2c, address, write).await
        }
    }

    impl ErrorType for NoPecBus {
        type Error = TestError;
    }

    impl Smbus for NoPecBus {
        type PecCalc = Pec;
        fn get_pec_calc() -> Option<Self::PecCalc> {
            None
        }
    }

    fn new_bus(expectations: &[Tx]) -> TestBus {
        TestBus {
            i2c: I2cMock::new(expectations),
        }
    }

    fn done(mut bus: TestBus) {
        bus.i2c.done();
    }

    // ---------- constants / helpers ----------

    #[test]
    fn constants() {
        assert_eq!(MAX_BLOCK_SIZE, 255);
        assert_eq!(READ_BIT, 0x01);
        assert_eq!(write_address_byte(0x42), 0x84);
        assert_eq!(read_address_byte(0x42), 0x85);
    }

    #[test]
    fn error_kind_display_and_kind() {
        let k = ErrorKind::Timeout;
        assert_eq!(k.kind(), ErrorKind::Timeout);
        // Display impls cover all branches.
        for k in [
            ErrorKind::I2c(I2cErrorKind::Bus),
            ErrorKind::Timeout,
            ErrorKind::Pec,
            ErrorKind::TooLargeBlockTransaction,
            ErrorKind::Other,
        ] {
            let s = std::format!("{}", k);
            assert!(!s.is_empty());
        }
    }

    #[test]
    fn error_kind_from_i2c_error_kind() {
        let k: ErrorKind = I2cErrorKind::Bus.into();
        assert_eq!(k, ErrorKind::I2c(I2cErrorKind::Bus));
    }

    #[test]
    fn infallible_error_to_kind_round_trip() {
        // Infallible cannot be constructed; we only check the trait wires up.
        fn _accepts<E: SmbusError>(_e: &E) {}
        let k = ErrorKind::Pec;
        _accepts(&k);
    }

    #[tokio::test]
    async fn check_pec_match() {
        let bus = new_bus(&[]);
        TestBus::check_pec(0x42, 0x42).unwrap();
        TestBus::check_pec(0x00, 0x00).unwrap();
        done(bus);
    }

    #[tokio::test]
    async fn check_pec_mismatch() {
        let bus = new_bus(&[]);
        let err = TestBus::check_pec(0x42, 0x43).unwrap_err();
        assert_eq!(err.kind(), ErrorKind::Pec);
        done(bus);
    }

    // ---------- write_buf / read_buf (low-level) ----------

    #[tokio::test]
    async fn write_buf_no_pec() {
        let mut bus = new_bus(&[Tx::write(ADDR, std::vec![0xAB, 0xCD])]);
        bus.write_buf(ADDR, false, &mut [0xAB, 0xCD]).await.unwrap();
        done(bus);
    }

    #[tokio::test]
    async fn write_buf_pec() {
        let payload = [0xAB, 0xCD];
        let pec = expected_pec(&[&[write_address_byte(ADDR)], &payload]);
        let mut buf = [0xAB, 0xCD, 0x00];
        let mut wire = std::vec![0xAB, 0xCD, pec];
        let mut bus = new_bus(&[Tx::write(ADDR, wire.clone())]);
        bus.write_buf(ADDR, true, &mut buf).await.unwrap();
        // Last byte should now be the PEC.
        assert_eq!(buf[2], pec);
        wire.clear();
        done(bus);
    }

    #[tokio::test]
    async fn read_buf_no_pec() {
        let mut bus = new_bus(&[Tx::read(ADDR, std::vec![0x11, 0x22])]);
        let mut buf = [0u8; 2];
        bus.read_buf(ADDR, false, &mut buf).await.unwrap();
        assert_eq!(buf, [0x11, 0x22]);
        done(bus);
    }

    #[tokio::test]
    async fn read_buf_pec() {
        let data = 0x11u8;
        let pec = expected_pec(&[&[write_address_byte(ADDR)], &[data]]);
        let mut bus = new_bus(&[Tx::read(ADDR, std::vec![data, pec])]);
        let mut buf = [0u8; 2];
        bus.read_buf(ADDR, true, &mut buf).await.unwrap();
        done(bus);
    }

    #[tokio::test]
    async fn read_buf_pec_mismatch() {
        let mut bus = new_bus(&[Tx::read(ADDR, std::vec![0x11, 0xFF])]); // wrong PEC
        let mut buf = [0u8; 2];
        let err = bus.read_buf(ADDR, true, &mut buf).await.unwrap_err();
        assert_eq!(err.kind(), ErrorKind::Pec);
        done(bus);
    }

    // ---------- quick_command ----------

    #[tokio::test]
    async fn quick_command_write() {
        let mut bus = new_bus(&[
            Tx::transaction_start(ADDR),
            Tx::write(ADDR, std::vec![]),
            Tx::transaction_end(ADDR),
        ]);
        bus.quick_command(ADDR, false).await.unwrap();
        done(bus);
    }

    #[tokio::test]
    async fn quick_command_read() {
        let mut bus = new_bus(&[
            Tx::transaction_start(ADDR),
            Tx::read(ADDR, std::vec![]),
            Tx::transaction_end(ADDR),
        ]);
        bus.quick_command(ADDR, true).await.unwrap();
        done(bus);
    }

    // ---------- send_byte / receive_byte ----------

    #[tokio::test]
    async fn send_byte_no_pec() {
        let mut bus = new_bus(&[Tx::write(ADDR, std::vec![0x55])]);
        bus.send_byte(ADDR, 0x55, false).await.unwrap();
        done(bus);
    }

    #[tokio::test]
    async fn send_byte_pec() {
        let pec = expected_pec(&[&[write_address_byte(ADDR), 0x55]]);
        let mut bus = new_bus(&[Tx::write(ADDR, std::vec![0x55, pec])]);
        bus.send_byte(ADDR, 0x55, true).await.unwrap();
        done(bus);
    }

    #[tokio::test]
    async fn receive_byte_no_pec() {
        let mut bus = new_bus(&[Tx::read(ADDR, std::vec![0x99])]);
        let b = bus.receive_byte(ADDR, false).await.unwrap();
        assert_eq!(b, 0x99);
        done(bus);
    }

    #[tokio::test]
    async fn receive_byte_pec() {
        let data = 0x99u8;
        let pec = expected_pec(&[&[write_address_byte(ADDR), data]]);
        let mut bus = new_bus(&[Tx::read(ADDR, std::vec![data, pec])]);
        let b = bus.receive_byte(ADDR, true).await.unwrap();
        assert_eq!(b, data);
        done(bus);
    }

    #[tokio::test]
    async fn receive_byte_pec_mismatch() {
        let mut bus = new_bus(&[Tx::read(ADDR, std::vec![0x99, 0xFF])]);
        let err = bus.receive_byte(ADDR, true).await.unwrap_err();
        assert_eq!(err.kind(), ErrorKind::Pec);
        done(bus);
    }

    // ---------- write_byte / write_word ----------

    #[tokio::test]
    async fn write_byte_no_pec() {
        let mut bus = new_bus(&[Tx::write(ADDR, std::vec![REG, 0x33])]);
        bus.write_byte(ADDR, REG, 0x33, false).await.unwrap();
        done(bus);
    }

    #[tokio::test]
    async fn write_byte_pec() {
        let pec = expected_pec(&[&[write_address_byte(ADDR), REG, 0x33]]);
        let mut bus = new_bus(&[Tx::write(ADDR, std::vec![REG, 0x33, pec])]);
        bus.write_byte(ADDR, REG, 0x33, true).await.unwrap();
        done(bus);
    }

    #[tokio::test]
    async fn write_word_no_pec() {
        let word: u16 = 0xBEEF;
        let bytes = word.to_le_bytes();
        let mut bus = new_bus(&[Tx::write(ADDR, std::vec![REG, bytes[0], bytes[1]])]);
        bus.write_word(ADDR, REG, word, false).await.unwrap();
        done(bus);
    }

    #[tokio::test]
    async fn write_word_pec() {
        let word: u16 = 0xBEEF;
        let bytes = word.to_le_bytes();
        let pec = expected_pec(&[&[write_address_byte(ADDR), REG, bytes[0], bytes[1]]]);
        let mut bus = new_bus(&[Tx::write(ADDR, std::vec![REG, bytes[0], bytes[1], pec])]);
        bus.write_word(ADDR, REG, word, true).await.unwrap();
        done(bus);
    }

    // ---------- read_byte / read_word ----------

    #[tokio::test]
    async fn read_byte_no_pec() {
        let mut bus = new_bus(&[
            Tx::transaction_start(ADDR),
            Tx::write(ADDR, std::vec![REG]),
            Tx::read(ADDR, std::vec![0x77]),
            Tx::transaction_end(ADDR),
        ]);
        let b = bus.read_byte(ADDR, REG, false).await.unwrap();
        assert_eq!(b, 0x77);
        done(bus);
    }

    #[tokio::test]
    async fn read_byte_pec() {
        let data = 0x77u8;
        let pec = expected_pec(&[&[write_address_byte(ADDR), REG, read_address_byte(ADDR), data]]);
        let mut bus = new_bus(&[
            Tx::transaction_start(ADDR),
            Tx::write(ADDR, std::vec![REG]),
            Tx::read(ADDR, std::vec![data, pec]),
            Tx::transaction_end(ADDR),
        ]);
        let b = bus.read_byte(ADDR, REG, true).await.unwrap();
        assert_eq!(b, data);
        done(bus);
    }

    #[tokio::test]
    async fn read_byte_pec_mismatch() {
        let mut bus = new_bus(&[
            Tx::transaction_start(ADDR),
            Tx::write(ADDR, std::vec![REG]),
            Tx::read(ADDR, std::vec![0x77, 0xFF]),
            Tx::transaction_end(ADDR),
        ]);
        let err = bus.read_byte(ADDR, REG, true).await.unwrap_err();
        assert_eq!(err.kind(), ErrorKind::Pec);
        done(bus);
    }

    #[tokio::test]
    async fn read_word_no_pec() {
        let lo = 0x12u8;
        let hi = 0x34u8;
        let mut bus = new_bus(&[
            Tx::transaction_start(ADDR),
            Tx::write(ADDR, std::vec![REG]),
            Tx::read(ADDR, std::vec![lo, hi]),
            Tx::transaction_end(ADDR),
        ]);
        let w = bus.read_word(ADDR, REG, false).await.unwrap();
        assert_eq!(w, u16::from_le_bytes([lo, hi]));
        done(bus);
    }

    #[tokio::test]
    async fn read_word_pec() {
        let lo = 0x12u8;
        let hi = 0x34u8;
        let pec = expected_pec(&[&[write_address_byte(ADDR), REG, read_address_byte(ADDR), lo, hi]]);
        let mut bus = new_bus(&[
            Tx::transaction_start(ADDR),
            Tx::write(ADDR, std::vec![REG]),
            Tx::read(ADDR, std::vec![lo, hi, pec]),
            Tx::transaction_end(ADDR),
        ]);
        let w = bus.read_word(ADDR, REG, true).await.unwrap();
        assert_eq!(w, u16::from_le_bytes([lo, hi]));
        done(bus);
    }

    // ---------- process_call ----------

    #[tokio::test]
    async fn process_call_no_pec() {
        let word: u16 = 0x0102;
        let resp_lo = 0xAAu8;
        let resp_hi = 0xBBu8;
        let mut bus = new_bus(&[
            Tx::transaction_start(ADDR),
            Tx::write(ADDR, std::vec![REG]),
            Tx::write(ADDR, word.to_le_bytes().to_vec()),
            Tx::read(ADDR, std::vec![resp_lo, resp_hi]),
            Tx::transaction_end(ADDR),
        ]);
        let r = bus.process_call(ADDR, REG, word, false).await.unwrap();
        assert_eq!(r, u16::from_le_bytes([resp_lo, resp_hi]));
        done(bus);
    }

    #[tokio::test]
    async fn process_call_pec() {
        let word: u16 = 0x0102;
        let resp_lo = 0xAAu8;
        let resp_hi = 0xBBu8;
        let mut hasher = Pec::new();
        hasher.write_u8(write_address_byte(ADDR));
        hasher.write_u8(REG);
        hasher.write_u16(word);
        hasher.write_u8(read_address_byte(ADDR));
        hasher.write(&[resp_lo, resp_hi]);
        let pec = hasher.finish() as u8;
        let mut bus = new_bus(&[
            Tx::transaction_start(ADDR),
            Tx::write(ADDR, std::vec![REG]),
            Tx::write(ADDR, word.to_le_bytes().to_vec()),
            Tx::read(ADDR, std::vec![resp_lo, resp_hi, pec]),
            Tx::transaction_end(ADDR),
        ]);
        let r = bus.process_call(ADDR, REG, word, true).await.unwrap();
        assert_eq!(r, u16::from_le_bytes([resp_lo, resp_hi]));
        done(bus);
    }

    // ---------- block_write ----------

    #[tokio::test]
    async fn block_write_no_pec() {
        let data = [0xDE, 0xAD, 0xBE, 0xEF];
        let mut bus = new_bus(&[
            Tx::transaction_start(ADDR),
            Tx::write(ADDR, std::vec![REG]),
            Tx::write(ADDR, std::vec![data.len() as u8]),
            Tx::write(ADDR, data.to_vec()),
            Tx::transaction_end(ADDR),
        ]);
        bus.block_write(ADDR, REG, &data, false).await.unwrap();
        done(bus);
    }

    #[tokio::test]
    async fn block_write_pec() {
        let data = [0xDE, 0xAD, 0xBE, 0xEF];
        let pec = expected_pec(&[&[write_address_byte(ADDR), REG, data.len() as u8], &data]);
        let mut bus = new_bus(&[
            Tx::transaction_start(ADDR),
            Tx::write(ADDR, std::vec![REG]),
            Tx::write(ADDR, std::vec![data.len() as u8]),
            Tx::write(ADDR, data.to_vec()),
            Tx::write(ADDR, std::vec![pec]),
            Tx::transaction_end(ADDR),
        ]);
        bus.block_write(ADDR, REG, &data, true).await.unwrap();
        done(bus);
    }

    #[tokio::test]
    async fn block_write_too_large() {
        let mut bus = new_bus(&[]);
        let data = std::vec![0u8; MAX_BLOCK_SIZE + 1];
        let err = bus.block_write(ADDR, REG, &data, false).await.unwrap_err();
        assert_eq!(err.kind(), ErrorKind::TooLargeBlockTransaction);
        done(bus);
    }

    // ---------- block_read ----------

    #[tokio::test]
    async fn block_read_no_pec() {
        let mut buf = [0u8; 3];
        let mut bus = new_bus(&[
            Tx::transaction_start(ADDR),
            Tx::write(ADDR, std::vec![REG]),
            Tx::read(ADDR, std::vec![3]),
            Tx::read(ADDR, std::vec![0x10, 0x20, 0x30]),
            Tx::transaction_end(ADDR),
        ]);
        bus.block_read(ADDR, REG, &mut buf, false).await.unwrap();
        assert_eq!(buf, [0x10, 0x20, 0x30]);
        done(bus);
    }

    #[tokio::test]
    async fn block_read_pec() {
        let payload = [0x10u8, 0x20, 0x30];
        let len = payload.len() as u8;
        // PEC source matches the implementation: addr+W, reg, addr+R, then msg_size, then data.
        let mut hasher = Pec::new();
        hasher.write_u8(write_address_byte(ADDR));
        hasher.write_u8(REG);
        hasher.write_u8(read_address_byte(ADDR));
        hasher.write(&[len]);
        hasher.write(&payload);
        let pec = hasher.finish() as u8;
        let mut buf = [0u8; 3];
        let mut bus = new_bus(&[
            Tx::transaction_start(ADDR),
            Tx::write(ADDR, std::vec![REG]),
            Tx::read(ADDR, std::vec![len]),
            Tx::read(ADDR, payload.to_vec()),
            Tx::read(ADDR, std::vec![pec]),
            Tx::transaction_end(ADDR),
        ]);
        bus.block_read(ADDR, REG, &mut buf, true).await.unwrap();
        assert_eq!(buf, payload);
        done(bus);
    }

    #[tokio::test]
    async fn block_read_too_large() {
        let mut bus = new_bus(&[]);
        let mut buf = std::vec![0u8; MAX_BLOCK_SIZE + 1];
        let err = bus.block_read(ADDR, REG, &mut buf, false).await.unwrap_err();
        assert_eq!(err.kind(), ErrorKind::TooLargeBlockTransaction);
        done(bus);
    }

    // ---------- block_write_block_read_process_call ----------

    #[tokio::test]
    async fn bwbr_no_pec() {
        let write_data = [0x01u8, 0x02];
        let read_payload = [0xAAu8, 0xBB];
        let mut read_buf = [0u8; 2];
        let mut bus = new_bus(&[
            Tx::transaction_start(ADDR),
            Tx::write(ADDR, std::vec![REG]),
            Tx::write(ADDR, std::vec![write_data.len() as u8]),
            Tx::write(ADDR, write_data.to_vec()),
            Tx::read(ADDR, std::vec![read_payload.len() as u8]),
            Tx::read(ADDR, read_payload.to_vec()),
            Tx::transaction_end(ADDR),
        ]);
        bus.block_write_block_read_process_call(ADDR, REG, &write_data, &mut read_buf, false)
            .await
            .unwrap();
        assert_eq!(read_buf, read_payload);
        done(bus);
    }

    #[tokio::test]
    async fn bwbr_pec() {
        let write_data = [0x01u8, 0x02];
        let read_payload = [0xAAu8, 0xBB];
        let mut read_buf = [0u8; 2];
        let mut hasher = Pec::new();
        hasher.write_u8(write_address_byte(ADDR));
        hasher.write_u8(REG);
        hasher.write_u8(write_data.len() as u8);
        hasher.write(&write_data);
        hasher.write_u8(read_address_byte(ADDR));
        hasher.write(&[read_payload.len() as u8]);
        hasher.write(&read_payload);
        let pec = hasher.finish() as u8;
        let mut bus = new_bus(&[
            Tx::transaction_start(ADDR),
            Tx::write(ADDR, std::vec![REG]),
            Tx::write(ADDR, std::vec![write_data.len() as u8]),
            Tx::write(ADDR, write_data.to_vec()),
            Tx::read(ADDR, std::vec![read_payload.len() as u8]),
            Tx::read(ADDR, read_payload.to_vec()),
            Tx::read(ADDR, std::vec![pec]),
            Tx::transaction_end(ADDR),
        ]);
        bus.block_write_block_read_process_call(ADDR, REG, &write_data, &mut read_buf, true)
            .await
            .unwrap();
        assert_eq!(read_buf, read_payload);
        done(bus);
    }

    #[tokio::test]
    async fn bwbr_too_large() {
        let mut bus = new_bus(&[]);
        let write_data = std::vec![0u8; 200];
        let mut read_buf = std::vec![0u8; 60]; // 200 + 60 > 255
        let err = bus
            .block_write_block_read_process_call(ADDR, REG, &write_data, &mut read_buf, false)
            .await
            .unwrap_err();
        assert_eq!(err.kind(), ErrorKind::TooLargeBlockTransaction);
        done(bus);
    }

    // ---------- PEC unavailable ----------

    fn new_no_pec_bus(expectations: &[Tx]) -> NoPecBus {
        NoPecBus {
            i2c: I2cMock::new(expectations),
        }
    }

    fn done_no_pec(mut bus: NoPecBus) {
        bus.i2c.done();
    }

    #[test]
    fn no_pec_bus_get_pec_calc_returns_none() {
        assert!(NoPecBus::get_pec_calc().is_none());
    }

    #[tokio::test]
    async fn no_pec_bus_non_pec_ops_still_work() {
        // All `use_pec = false` paths must succeed even though `get_pec_calc`
        // returns `None`: the trait must not consult the PEC calculator unless
        // PEC was actually requested.
        let mut bus = new_no_pec_bus(&[
            Tx::write(ADDR, std::vec![0x55]),
            Tx::read(ADDR, std::vec![0x99]),
            Tx::write(ADDR, std::vec![REG, 0x33]),
            Tx::transaction_start(ADDR),
            Tx::write(ADDR, std::vec![REG]),
            Tx::read(ADDR, std::vec![0x77]),
            Tx::transaction_end(ADDR),
        ]);
        bus.send_byte(ADDR, 0x55, false).await.unwrap();
        assert_eq!(bus.receive_byte(ADDR, false).await.unwrap(), 0x99);
        bus.write_byte(ADDR, REG, 0x33, false).await.unwrap();
        assert_eq!(bus.read_byte(ADDR, REG, false).await.unwrap(), 0x77);
        done_no_pec(bus);
    }

    #[tokio::test]
    async fn pec_unavailable_returns_pec_error() {
        let mut bus = NoPecBus { i2c: I2cMock::new(&[]) };
        // Any PEC-requiring path should fail without touching the bus.
        let err = bus.send_byte(ADDR, 0x55, true).await.unwrap_err();
        assert_eq!(err.kind(), ErrorKind::Pec);
        let err = bus.receive_byte(ADDR, true).await.unwrap_err();
        assert_eq!(err.kind(), ErrorKind::Pec);
        let err = bus.read_byte(ADDR, REG, true).await.unwrap_err();
        assert_eq!(err.kind(), ErrorKind::Pec);
        let err = bus.read_word(ADDR, REG, true).await.unwrap_err();
        assert_eq!(err.kind(), ErrorKind::Pec);
        let err = bus.process_call(ADDR, REG, 0, true).await.unwrap_err();
        assert_eq!(err.kind(), ErrorKind::Pec);
        let err = bus.block_write(ADDR, REG, &[1, 2], true).await.unwrap_err();
        assert_eq!(err.kind(), ErrorKind::Pec);
        let mut rb = [0u8; 2];
        let err = bus.block_read(ADDR, REG, &mut rb, true).await.unwrap_err();
        assert_eq!(err.kind(), ErrorKind::Pec);
        let err = bus
            .block_write_block_read_process_call(ADDR, REG, &[1], &mut rb, true)
            .await
            .unwrap_err();
        assert_eq!(err.kind(), ErrorKind::Pec);
        bus.i2c.done();
    }

    // ---------- &mut T forwarding ----------

    #[tokio::test]
    async fn mut_ref_smbus_forwards() {
        let mut bus = new_bus(&[Tx::write(ADDR, std::vec![0x55])]);
        let r: &mut TestBus = &mut bus;
        r.send_byte(ADDR, 0x55, false).await.unwrap();
        assert!(<&mut TestBus as Smbus>::get_pec_calc().is_some());
        done(bus);
    }

    // ---------- error propagation from underlying I2C ----------

    #[tokio::test]
    async fn i2c_error_propagates() {
        let mut bus = new_bus(&[Tx::write(ADDR, std::vec![0x55]).with_error(I2cErrorKind::Bus)]);
        let err = bus.send_byte(ADDR, 0x55, false).await.unwrap_err();
        assert_eq!(err.kind(), ErrorKind::I2c(I2cErrorKind::Bus));
        done(bus);
    }
}
