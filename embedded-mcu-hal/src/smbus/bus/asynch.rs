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
    fn write_buf(
        &mut self,
        address: u8,
        use_pec: bool,
        operations: &mut [u8],
    ) -> impl core::future::Future<Output = Result<(), <Self as crate::smbus::bus::ErrorType>::Error>> {
        async move {
            if use_pec {
                let mut pec = Self::get_pec_calc().ok_or(<Self as crate::smbus::bus::ErrorType>::Error::to_kind(
                    crate::smbus::bus::ErrorKind::Pec,
                ))?;

                pec.write_u8(address << 1);
                pec.write(&operations[..operations.len() - 1]);
                let pec_elem = operations.get_mut(operations.len() - 1).ok_or(
                    <Self as crate::smbus::bus::ErrorType>::Error::to_kind(crate::smbus::bus::ErrorKind::Pec),
                )?;
                *pec_elem = pec.finish().try_into().map_err(|_| {
                    <Self as crate::smbus::bus::ErrorType>::Error::to_kind(crate::smbus::bus::ErrorKind::Pec)
                })?;

                self.write(address, operations)
                    .await
                    .map_err(|i2c_err| i2c_err.kind())?;
            } else {
                self.write(address, operations)
                    .await
                    .map_err(|i2c_err| i2c_err.kind())?;
            }
            Ok(())
        }
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
    fn read_buf(
        &mut self,
        address: u8,
        use_pec: bool,
        read: &mut [u8],
    ) -> impl core::future::Future<Output = Result<(), <Self as crate::smbus::bus::ErrorType>::Error>> {
        async move {
            if use_pec {
                let mut pec = Self::get_pec_calc().ok_or(<Self as crate::smbus::bus::ErrorType>::Error::to_kind(
                    crate::smbus::bus::ErrorKind::Pec,
                ))?;
                pec.write_u8(address << 1);
                self.read(address, read).await.map_err(|i2c_err| i2c_err.kind())?;
                pec.write(&read[..read.len() - 1]);

                Self::check_pec(read[read.len() - 1], pec.finish())?;
            } else {
                self.read(address, read).await.map_err(|i2c_err| i2c_err.kind())?;
            }

            Ok(())
        }
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
    fn quick_command(
        &mut self,
        address: u8,
        read: bool,
    ) -> impl core::future::Future<Output = Result<(), <Self as crate::smbus::bus::ErrorType>::Error>> {
        async move {
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
    fn send_byte(
        &mut self,
        address: u8,
        byte: u8,
        use_pec: bool,
    ) -> impl core::future::Future<Output = Result<(), <Self as crate::smbus::bus::ErrorType>::Error>> {
        async move {
            if use_pec {
                self.write_buf(address, true, &mut [byte, 0]).await
            } else {
                self.write_buf(address, true, &mut [byte]).await
            }
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
    fn receive_byte(
        &mut self,
        address: u8,
        use_pec: bool,
    ) -> impl core::future::Future<Output = Result<u8, <Self as crate::smbus::bus::ErrorType>::Error>> {
        async move {
            if use_pec {
                let mut buf = [0u8, 2];
                self.read_buf(address, use_pec, &mut buf).await?;
                Ok(buf[0])
            } else {
                let mut buf = [0u8];
                self.read_buf(address, use_pec, &mut buf).await?;
                Ok(buf[0])
            }
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
    fn write_byte(
        &mut self,
        address: u8,
        register: u8,
        byte: u8,
        use_pec: bool,
    ) -> impl core::future::Future<Output = Result<(), <Self as crate::smbus::bus::ErrorType>::Error>> {
        async move {
            if use_pec {
                self.write_buf(address, use_pec, &mut [register, byte, 0]).await
            } else {
                self.write_buf(address, use_pec, &mut [register, byte]).await
            }
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
    fn write_word(
        &mut self,
        address: u8,
        register: u8,
        word: u16,
        use_pec: bool,
    ) -> impl core::future::Future<Output = Result<(), <Self as crate::smbus::bus::ErrorType>::Error>> {
        async move {
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
    fn read_byte(
        &mut self,
        address: u8,
        register: u8,
        use_pec: bool,
    ) -> impl core::future::Future<Output = Result<u8, <Self as crate::smbus::bus::ErrorType>::Error>> {
        async move {
            if use_pec {
                let mut buf = [0u8; 2];
                let mut pec = Self::get_pec_calc().ok_or(<Self as crate::smbus::bus::ErrorType>::Error::to_kind(
                    crate::smbus::bus::ErrorKind::Pec,
                ))?;
                pec.write_u8(address << 1);
                pec.write_u8(register);
                pec.write_u8((address << 1) | 0x01);
                self.transaction(address, &mut [Operation::Write(&[register]), Operation::Read(&mut buf)])
                    .await
                    .map_err(|i2c_err| i2c_err.kind())?;
                pec.write_u8(buf[0]);
                Self::check_pec(buf[1], pec.finish())?;
                Ok(buf[0])
            } else {
                let mut buf = [0u8];
                self.transaction(address, &mut [Operation::Write(&[register]), Operation::Read(&mut buf)])
                    .await
                    .map_err(|i2c_err| i2c_err.kind())?;
                Ok(buf[0])
            }
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
    fn read_word(
        &mut self,
        address: u8,
        register: u8,
        use_pec: bool,
    ) -> impl core::future::Future<Output = Result<u16, <Self as crate::smbus::bus::ErrorType>::Error>> {
        async move {
            if use_pec {
                let mut buf = [0u8; 3];
                let mut pec = Self::get_pec_calc().ok_or(<Self as crate::smbus::bus::ErrorType>::Error::to_kind(
                    crate::smbus::bus::ErrorKind::Pec,
                ))?;
                pec.write_u8(address << 1);
                pec.write_u8(register);
                pec.write_u8((address << 1) | 0x01);
                self.transaction(address, &mut [Operation::Write(&[register]), Operation::Read(&mut buf)])
                    .await
                    .map_err(|i2c_err| i2c_err.kind())?;
                pec.write(&buf[..2]);
                Self::check_pec(buf[1], pec.finish())?;
                Ok(u16::from_le_bytes(buf[..2].try_into().unwrap()))
            } else {
                let mut buf = [0u8; 2];
                self.transaction(address, &mut [Operation::Write(&[register]), Operation::Read(&mut buf)])
                    .await
                    .map_err(|i2c_err| i2c_err.kind())?;
                Ok(u16::from_le_bytes(buf))
            }
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
    fn process_call(
        &mut self,
        address: u8,
        register: u8,
        word: u16,
        use_pec: bool,
    ) -> impl core::future::Future<Output = Result<u16, <Self as crate::smbus::bus::ErrorType>::Error>> {
        async move {
            if use_pec {
                let mut buf = [0u8; 3];
                let mut pec = Self::get_pec_calc().ok_or(<Self as crate::smbus::bus::ErrorType>::Error::to_kind(
                    crate::smbus::bus::ErrorKind::Pec,
                ))?;
                pec.write_u8(address << 1);
                pec.write_u8(register);
                pec.write_u16(word);
                pec.write_u8((address << 1) | 0x01);
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
                pec.write(&buf[..2]);
                Self::check_pec(buf[2], pec.finish())?;
                Ok(u16::from_le_bytes(buf[..2].try_into().unwrap()))
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
    fn block_write(
        &mut self,
        address: u8,
        register: u8,
        data: &[u8],
        use_pec: bool,
    ) -> impl core::future::Future<Output = Result<(), <Self as crate::smbus::bus::ErrorType>::Error>> {
        async move {
            if data.len() > 255 {
                return Err(<Self as crate::smbus::bus::ErrorType>::Error::to_kind(
                    crate::smbus::bus::ErrorKind::TooLargeBlockTransaction,
                ));
            }
            if use_pec {
                let mut pec = Self::get_pec_calc().ok_or(<Self as crate::smbus::bus::ErrorType>::Error::to_kind(
                    crate::smbus::bus::ErrorKind::Pec,
                ))?;
                pec.write_u8(address << 1);
                pec.write_u8(register);
                pec.write_u8(data.len() as u8);
                pec.write(data);
                let pec: u8 = pec.finish().try_into().map_err(|_| {
                    <Self as crate::smbus::bus::ErrorType>::Error::to_kind(crate::smbus::bus::ErrorKind::Pec)
                })?;
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
    fn block_read(
        &mut self,
        address: u8,
        register: u8,
        data: &mut [u8],
        use_pec: bool,
    ) -> impl core::future::Future<Output = Result<(), <Self as crate::smbus::bus::ErrorType>::Error>> {
        async move {
            if data.len() > 255 {
                return Err(<Self as crate::smbus::bus::ErrorType>::Error::to_kind(
                    crate::smbus::bus::ErrorKind::TooLargeBlockTransaction,
                ));
            }
            let mut msg_size = [0u8];
            if use_pec {
                let mut pec_buf = [0u8];
                let mut pec = Self::get_pec_calc().ok_or(<Self as crate::smbus::bus::ErrorType>::Error::to_kind(
                    crate::smbus::bus::ErrorKind::Pec,
                ))?;
                pec.write_u8(address << 1);
                pec.write_u8(register);
                pec.write_u8((address << 1) | 0x01);
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
    fn block_write_block_read_process_call(
        &mut self,
        address: u8,
        register: u8,
        write_data: &[u8],
        read_data: &mut [u8],
        use_pec: bool,
    ) -> impl core::future::Future<Output = Result<(), <Self as crate::smbus::bus::ErrorType>::Error>> {
        async move {
            if write_data.len() + read_data.len() > 255 {
                return Err(<Self as crate::smbus::bus::ErrorType>::Error::to_kind(
                    crate::smbus::bus::ErrorKind::TooLargeBlockTransaction,
                ));
            }
            let mut read_msg_size = [0u8];
            if use_pec {
                let mut pec_buf = [0u8];
                let mut pec = Self::get_pec_calc().ok_or(<Self as crate::smbus::bus::ErrorType>::Error::to_kind(
                    crate::smbus::bus::ErrorKind::Pec,
                ))?;
                pec.write_u8(address << 1);
                pec.write_u8(register);
                pec.write_u8(write_data.len() as u8);
                pec.write(write_data);
                pec.write_u8((address << 1) | 0x01);
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
}
