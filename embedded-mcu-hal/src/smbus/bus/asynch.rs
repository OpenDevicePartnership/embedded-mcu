//! Async SMBus controller trait and software implementation.
//!
//! This module defines the [`Smbus`] async controller trait describing the
//! SMBus protocol surface. The trait declares the protocol-level
//! operations as required methods plus two associated items —
//! [`Smbus::PecCalc`] and [`Smbus::get_pec_calc`] — and a
//! default-implemented helper [`Smbus::check_pec`].
//!
//! Concrete bit-banging of the protocol on top of an
//! [`embedded_hal_async::i2c::I2c`] bus is provided by [`SwSmbusI2c`].
//! HAL authors with a hardware SMBus peripheral may instead implement
//! [`Smbus`] directly.
//!
//! See the [parent module](super) for the protocol overview, PEC handling,
//! and driver/HAL guidance.

use core::hash::Hasher;
use core::marker::PhantomData;

use crate::smbus::bus::Error as SMBusError;
use embedded_hal_async::i2c::{Error as I2cError, I2c, Operation};

/// PEC calculator factory for [`SwSmbusI2c`].
///
/// Decouples [`SwSmbusI2c`] from a particular PEC implementation. Provide
/// a type implementing this trait as the `P` type parameter of
/// [`SwSmbusI2c`] to describe what PEC calculator (if any) the bus should
/// use.
pub trait PecProvider {
    /// PEC calculator type.
    type Calc: Hasher;

    /// Construct a fresh PEC calculator, or return `None` when PEC is
    /// unsupported on this bus. When `None` is returned, any operation
    /// invoked with `use_pec = true` fails with
    /// [`ErrorKind::Pec`](crate::smbus::bus::ErrorKind::Pec).
    fn new_calc() -> Option<Self::Calc>;
}

/// Async SMBus controller trait.
///
/// Declares the SMBus protocol surface. Implementations may either be a
/// software protocol-basher over a generic I²C bus (see [`SwSmbusI2c`])
/// or a HAL-level wrapper around a hardware SMBus peripheral.
#[allow(async_fn_in_trait)]
pub trait Smbus: crate::smbus::bus::ErrorType {
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
    /// Returns `Some(calculator)` if PEC support is available, or `None` if
    /// not. When `None` is returned, any operation with `use_pec = true`
    /// fails with an error of kind
    /// [`ErrorKind::Pec`](crate::smbus::bus::ErrorKind::Pec).
    fn get_pec_calc() -> Option<Self::PecCalc>;

    /// Check PEC (Packet Error Code) validity.
    ///
    /// Compares a received PEC byte against a computed PEC value. Only the
    /// low byte of `computed_pec` is used.
    fn check_pec(received_pec: u8, computed_pec: u64) -> Result<(), <Self as crate::smbus::bus::ErrorType>::Error> {
        computed_pec
            .eq(&received_pec.into())
            .then_some(())
            .ok_or_else(|| <Self as crate::smbus::bus::ErrorType>::Error::from_kind(crate::smbus::bus::ErrorKind::Pec))
    }

    /// Quick Command.
    async fn quick_command(
        &mut self,
        address: u8,
        read: bool,
    ) -> Result<(), <Self as crate::smbus::bus::ErrorType>::Error>;

    /// Send Byte.
    async fn send_byte(&mut self, address: u8, byte: u8) -> Result<(), <Self as crate::smbus::bus::ErrorType>::Error>;

    /// Send Byte with PEC.
    async fn send_byte_with_pec(
        &mut self,
        address: u8,
        byte: u8,
    ) -> Result<(), <Self as crate::smbus::bus::ErrorType>::Error>;

    /// Receive Byte.
    async fn receive_byte(&mut self, address: u8) -> Result<u8, <Self as crate::smbus::bus::ErrorType>::Error>;

    /// Receive Byte with PEC.
    async fn receive_byte_with_pec(&mut self, address: u8)
        -> Result<u8, <Self as crate::smbus::bus::ErrorType>::Error>;

    /// Write Byte.
    async fn write_byte(
        &mut self,
        address: u8,
        register: u8,
        byte: u8,
    ) -> Result<(), <Self as crate::smbus::bus::ErrorType>::Error>;

    /// Write Byte with PEC.
    async fn write_byte_with_pec(
        &mut self,
        address: u8,
        register: u8,
        byte: u8,
    ) -> Result<(), <Self as crate::smbus::bus::ErrorType>::Error>;

    /// Write Word (little-endian on the wire).
    async fn write_word(
        &mut self,
        address: u8,
        register: u8,
        word: u16,
    ) -> Result<(), <Self as crate::smbus::bus::ErrorType>::Error>;

    /// Write Word with PEC (little-endian on the wire).
    async fn write_word_with_pec(
        &mut self,
        address: u8,
        register: u8,
        word: u16,
    ) -> Result<(), <Self as crate::smbus::bus::ErrorType>::Error>;

    /// Read Byte.
    async fn read_byte(
        &mut self,
        address: u8,
        register: u8,
    ) -> Result<u8, <Self as crate::smbus::bus::ErrorType>::Error>;

    /// Read Byte with PEC.
    async fn read_byte_with_pec(
        &mut self,
        address: u8,
        register: u8,
    ) -> Result<u8, <Self as crate::smbus::bus::ErrorType>::Error>;

    /// Read Word (little-endian on the wire).
    async fn read_word(
        &mut self,
        address: u8,
        register: u8,
    ) -> Result<u16, <Self as crate::smbus::bus::ErrorType>::Error>;

    /// Read Word with PEC (little-endian on the wire).
    async fn read_word_with_pec(
        &mut self,
        address: u8,
        register: u8,
    ) -> Result<u16, <Self as crate::smbus::bus::ErrorType>::Error>;

    /// Process Call.
    async fn process_call(
        &mut self,
        address: u8,
        register: u8,
        word: u16,
    ) -> Result<u16, <Self as crate::smbus::bus::ErrorType>::Error>;

    /// Process Call with PEC.
    async fn process_call_with_pec(
        &mut self,
        address: u8,
        register: u8,
        word: u16,
    ) -> Result<u16, <Self as crate::smbus::bus::ErrorType>::Error>;

    /// Block Write.
    async fn block_write(
        &mut self,
        address: u8,
        register: u8,
        data: &[u8],
    ) -> Result<(), <Self as crate::smbus::bus::ErrorType>::Error>;

    /// Block Write with PEC.
    async fn block_write_with_pec(
        &mut self,
        address: u8,
        register: u8,
        data: &[u8],
    ) -> Result<(), <Self as crate::smbus::bus::ErrorType>::Error>;

    /// Block Read.
    async fn block_read(
        &mut self,
        address: u8,
        register: u8,
        data: &mut [u8],
    ) -> Result<(), <Self as crate::smbus::bus::ErrorType>::Error>;

    /// Block Read with PEC.
    async fn block_read_with_pec(
        &mut self,
        address: u8,
        register: u8,
        data: &mut [u8],
    ) -> Result<(), <Self as crate::smbus::bus::ErrorType>::Error>;

    /// Block Write / Block Read / Process Call.
    async fn block_write_block_read_process_call(
        &mut self,
        address: u8,
        register: u8,
        write_data: &[u8],
        read_data: &mut [u8],
    ) -> Result<(), <Self as crate::smbus::bus::ErrorType>::Error>;

    /// Block Write / Block Read / Process Call with PEC.
    async fn block_write_block_read_process_call_with_pec(
        &mut self,
        address: u8,
        register: u8,
        write_data: &[u8],
        read_data: &mut [u8],
    ) -> Result<(), <Self as crate::smbus::bus::ErrorType>::Error>;
}

impl<T: Smbus + ?Sized> Smbus for &mut T {
    type PecCalc = T::PecCalc;

    #[inline]
    fn get_pec_calc() -> Option<Self::PecCalc> {
        T::get_pec_calc()
    }

    #[inline]
    async fn quick_command(
        &mut self,
        address: u8,
        read: bool,
    ) -> Result<(), <Self as crate::smbus::bus::ErrorType>::Error> {
        T::quick_command(*self, address, read).await
    }

    #[inline]
    async fn send_byte(&mut self, address: u8, byte: u8) -> Result<(), <Self as crate::smbus::bus::ErrorType>::Error> {
        T::send_byte(*self, address, byte).await
    }

    #[inline]
    async fn send_byte_with_pec(
        &mut self,
        address: u8,
        byte: u8,
    ) -> Result<(), <Self as crate::smbus::bus::ErrorType>::Error> {
        T::send_byte_with_pec(*self, address, byte).await
    }

    #[inline]
    async fn receive_byte(&mut self, address: u8) -> Result<u8, <Self as crate::smbus::bus::ErrorType>::Error> {
        T::receive_byte(*self, address).await
    }

    #[inline]
    async fn receive_byte_with_pec(
        &mut self,
        address: u8,
    ) -> Result<u8, <Self as crate::smbus::bus::ErrorType>::Error> {
        T::receive_byte_with_pec(*self, address).await
    }

    #[inline]
    async fn write_byte(
        &mut self,
        address: u8,
        register: u8,
        byte: u8,
    ) -> Result<(), <Self as crate::smbus::bus::ErrorType>::Error> {
        T::write_byte(*self, address, register, byte).await
    }

    #[inline]
    async fn write_byte_with_pec(
        &mut self,
        address: u8,
        register: u8,
        byte: u8,
    ) -> Result<(), <Self as crate::smbus::bus::ErrorType>::Error> {
        T::write_byte_with_pec(*self, address, register, byte).await
    }

    #[inline]
    async fn write_word(
        &mut self,
        address: u8,
        register: u8,
        word: u16,
    ) -> Result<(), <Self as crate::smbus::bus::ErrorType>::Error> {
        T::write_word(*self, address, register, word).await
    }

    #[inline]
    async fn write_word_with_pec(
        &mut self,
        address: u8,
        register: u8,
        word: u16,
    ) -> Result<(), <Self as crate::smbus::bus::ErrorType>::Error> {
        T::write_word_with_pec(*self, address, register, word).await
    }

    #[inline]
    async fn read_byte(
        &mut self,
        address: u8,
        register: u8,
    ) -> Result<u8, <Self as crate::smbus::bus::ErrorType>::Error> {
        T::read_byte(*self, address, register).await
    }

    #[inline]
    async fn read_byte_with_pec(
        &mut self,
        address: u8,
        register: u8,
    ) -> Result<u8, <Self as crate::smbus::bus::ErrorType>::Error> {
        T::read_byte_with_pec(*self, address, register).await
    }

    #[inline]
    async fn read_word(
        &mut self,
        address: u8,
        register: u8,
    ) -> Result<u16, <Self as crate::smbus::bus::ErrorType>::Error> {
        T::read_word(*self, address, register).await
    }

    #[inline]
    async fn read_word_with_pec(
        &mut self,
        address: u8,
        register: u8,
    ) -> Result<u16, <Self as crate::smbus::bus::ErrorType>::Error> {
        T::read_word_with_pec(*self, address, register).await
    }

    #[inline]
    async fn process_call(
        &mut self,
        address: u8,
        register: u8,
        word: u16,
    ) -> Result<u16, <Self as crate::smbus::bus::ErrorType>::Error> {
        T::process_call(*self, address, register, word).await
    }

    #[inline]
    async fn process_call_with_pec(
        &mut self,
        address: u8,
        register: u8,
        word: u16,
    ) -> Result<u16, <Self as crate::smbus::bus::ErrorType>::Error> {
        T::process_call_with_pec(*self, address, register, word).await
    }

    #[inline]
    async fn block_write(
        &mut self,
        address: u8,
        register: u8,
        data: &[u8],
    ) -> Result<(), <Self as crate::smbus::bus::ErrorType>::Error> {
        T::block_write(*self, address, register, data).await
    }

    #[inline]
    async fn block_write_with_pec(
        &mut self,
        address: u8,
        register: u8,
        data: &[u8],
    ) -> Result<(), <Self as crate::smbus::bus::ErrorType>::Error> {
        T::block_write_with_pec(*self, address, register, data).await
    }

    #[inline]
    async fn block_read(
        &mut self,
        address: u8,
        register: u8,
        data: &mut [u8],
    ) -> Result<(), <Self as crate::smbus::bus::ErrorType>::Error> {
        T::block_read(*self, address, register, data).await
    }

    #[inline]
    async fn block_read_with_pec(
        &mut self,
        address: u8,
        register: u8,
        data: &mut [u8],
    ) -> Result<(), <Self as crate::smbus::bus::ErrorType>::Error> {
        T::block_read_with_pec(*self, address, register, data).await
    }

    #[inline]
    async fn block_write_block_read_process_call(
        &mut self,
        address: u8,
        register: u8,
        write_data: &[u8],
        read_data: &mut [u8],
    ) -> Result<(), <Self as crate::smbus::bus::ErrorType>::Error> {
        T::block_write_block_read_process_call(*self, address, register, write_data, read_data).await
    }

    #[inline]
    async fn block_write_block_read_process_call_with_pec(
        &mut self,
        address: u8,
        register: u8,
        write_data: &[u8],
        read_data: &mut [u8],
    ) -> Result<(), <Self as crate::smbus::bus::ErrorType>::Error> {
        T::block_write_block_read_process_call_with_pec(*self, address, register, write_data, read_data).await
    }
}

/// Software SMBus controller built on top of an async I²C bus.
///
/// `SwSmbusI2c<I, P>` implements [`Smbus`] by bit-banging the SMBus
/// protocol on top of an [`embedded_hal_async::i2c::I2c`] bus `I`. PEC
/// support is delegated to the [`PecProvider`] `P`.
pub struct SwSmbusI2c<I, P> {
    i2c: I,
    _pec: PhantomData<P>,
}

impl<I, P> SwSmbusI2c<I, P> {
    /// Wrap an I²C bus to form a software SMBus controller.
    #[inline]
    pub const fn new(i2c: I) -> Self {
        Self { i2c, _pec: PhantomData }
    }

    /// Consume the wrapper and return the underlying I²C bus.
    #[inline]
    pub fn into_inner(self) -> I {
        self.i2c
    }

    /// Borrow the underlying I²C bus.
    #[inline]
    pub fn inner(&self) -> &I {
        &self.i2c
    }

    /// Mutably borrow the underlying I²C bus.
    #[inline]
    pub fn inner_mut(&mut self) -> &mut I {
        &mut self.i2c
    }
}

impl<I, P> crate::smbus::bus::ErrorType for SwSmbusI2c<I, P> {
    type Error = crate::smbus::bus::ErrorKind;
}

impl<I, P> SwSmbusI2c<I, P>
where
    P: PecProvider,
{
    /// Obtain a fresh PEC calculator pre-fed with the write-address byte,
    /// or [`ErrorKind::Pec`](crate::smbus::bus::ErrorKind::Pec) if the
    /// provider returns `None`.
    fn pec_calc_with_write_addr(address: u8) -> Result<P::Calc, crate::smbus::bus::ErrorKind> {
        let mut pec = P::new_calc().ok_or(crate::smbus::bus::ErrorKind::Pec)?;
        pec.write_u8(crate::smbus::bus::write_address_byte(address));
        Ok(pec)
    }

    /// Obtain a fresh PEC calculator pre-fed with the read-address byte,
    /// or [`ErrorKind::Pec`](crate::smbus::bus::ErrorKind::Pec) if the
    /// provider returns `None`. Used by pure-read transactions (e.g.
    /// Receive Byte) whose first wire byte is the read-direction address.
    fn pec_calc_with_read_addr(address: u8) -> Result<P::Calc, crate::smbus::bus::ErrorKind> {
        let mut pec = P::new_calc().ok_or(crate::smbus::bus::ErrorKind::Pec)?;
        pec.write_u8(crate::smbus::bus::read_address_byte(address));
        Ok(pec)
    }

    /// Truncate a finished PEC value to its low byte.
    fn finalize_pec_byte(pec: u64) -> Result<u8, crate::smbus::bus::ErrorKind> {
        pec.try_into().map_err(|_| crate::smbus::bus::ErrorKind::Pec)
    }
}

impl<I, P> SwSmbusI2c<I, P>
where
    I: I2c,
    P: PecProvider,
{
    /// Write a buffer of data with optional PEC computation.
    ///
    /// When `use_pec` is true, the caller must size `operations` to include
    /// one extra trailing byte for the PEC; that byte is filled in with the
    /// computed PEC before the I²C write.
    async fn write_buf(
        &mut self,
        address: u8,
        use_pec: bool,
        operations: &mut [u8],
    ) -> Result<(), crate::smbus::bus::ErrorKind> {
        if use_pec {
            let mut pec = Self::pec_calc_with_write_addr(address)?;
            let (pec_elem, rest) = operations.split_last_mut().ok_or(crate::smbus::bus::ErrorKind::Pec)?;
            pec.write(rest);
            *pec_elem = Self::finalize_pec_byte(pec.finish())?;
        }
        self.i2c
            .write(address, operations)
            .await
            .map_err(|e| crate::smbus::bus::ErrorKind::from(e.kind()))?;
        Ok(())
    }

    /// Read a buffer of data with optional PEC verification.
    ///
    /// When `use_pec` is true, the caller must size `read` to include one
    /// extra trailing byte for the PEC byte; it is verified after the read.
    /// The PEC is seeded with the read-direction address byte because this
    /// helper drives a pure-read SMBus transaction (e.g. Receive Byte).
    async fn read_buf(
        &mut self,
        address: u8,
        use_pec: bool,
        read: &mut [u8],
    ) -> Result<(), crate::smbus::bus::ErrorKind> {
        if use_pec {
            let mut pec = Self::pec_calc_with_read_addr(address)?;
            self.i2c
                .read(address, read)
                .await
                .map_err(|e| crate::smbus::bus::ErrorKind::from(e.kind()))?;
            let (pec_byte, rest) = read.split_last().ok_or(crate::smbus::bus::ErrorKind::Pec)?;
            pec.write(rest);
            <Self as Smbus>::check_pec(*pec_byte, pec.finish())?;
        } else {
            self.i2c
                .read(address, read)
                .await
                .map_err(|e| crate::smbus::bus::ErrorKind::from(e.kind()))?;
        }
        Ok(())
    }

    /// Write a buffer and then read a buffer, with optional PEC verification.
    ///
    /// When `use_pec` is true, the caller must size `read` to include one
    /// extra trailing byte for the PEC byte; it is verified against a
    /// locally computed PEC.
    async fn write_read_buf(
        &mut self,
        address: u8,
        use_pec: bool,
        write: &[u8],
        read: &mut [u8],
    ) -> Result<(), crate::smbus::bus::ErrorKind> {
        // When PEC is requested, fail fast without touching the bus if no
        // PEC calculator is available.
        let mut pec = if use_pec {
            Some(Self::pec_calc_with_write_addr(address)?)
        } else {
            None
        };
        self.i2c
            .transaction(address, &mut [Operation::Write(write), Operation::Read(read)])
            .await
            .map_err(|e| crate::smbus::bus::ErrorKind::from(e.kind()))?;
        if let Some(pec) = pec.as_mut() {
            pec.write(write);
            pec.write_u8(crate::smbus::bus::read_address_byte(address));
            let (pec_byte, rest) = read.split_last().ok_or(crate::smbus::bus::ErrorKind::Pec)?;
            pec.write(rest);
            <Self as Smbus>::check_pec(*pec_byte, pec.finish())?;
        }
        Ok(())
    }
}

impl<I, P> Smbus for SwSmbusI2c<I, P>
where
    I: I2c,
    P: PecProvider,
{
    type PecCalc = P::Calc;

    #[inline]
    fn get_pec_calc() -> Option<Self::PecCalc> {
        P::new_calc()
    }

    #[inline]
    async fn quick_command(&mut self, address: u8, read: bool) -> Result<(), crate::smbus::bus::ErrorKind> {
        self.i2c
            .transaction(
                address,
                &mut if read {
                    [Operation::Read(&mut [])]
                } else {
                    [Operation::Write(&[])]
                },
            )
            .await
            .map_err(|e| crate::smbus::bus::ErrorKind::from(e.kind()))?;
        Ok(())
    }

    async fn send_byte(&mut self, address: u8, byte: u8) -> Result<(), crate::smbus::bus::ErrorKind> {
        self.write_buf(address, false, &mut [byte]).await
    }

    async fn send_byte_with_pec(&mut self, address: u8, byte: u8) -> Result<(), crate::smbus::bus::ErrorKind> {
        self.write_buf(address, true, &mut [byte, 0]).await
    }

    async fn receive_byte(&mut self, address: u8) -> Result<u8, crate::smbus::bus::ErrorKind> {
        let mut buf = [0u8; 1];
        self.read_buf(address, false, &mut buf).await?;
        Ok(buf[0])
    }

    async fn receive_byte_with_pec(&mut self, address: u8) -> Result<u8, crate::smbus::bus::ErrorKind> {
        let mut buf = [0u8; 2];
        self.read_buf(address, true, &mut buf).await?;
        Ok(buf[0])
    }

    async fn write_byte(&mut self, address: u8, register: u8, byte: u8) -> Result<(), crate::smbus::bus::ErrorKind> {
        self.write_buf(address, false, &mut [register, byte]).await
    }

    async fn write_byte_with_pec(
        &mut self,
        address: u8,
        register: u8,
        byte: u8,
    ) -> Result<(), crate::smbus::bus::ErrorKind> {
        self.write_buf(address, true, &mut [register, byte, 0]).await
    }

    async fn write_word(&mut self, address: u8, register: u8, word: u16) -> Result<(), crate::smbus::bus::ErrorKind> {
        let b = u16::to_le_bytes(word);
        self.write_buf(address, false, &mut [register, b[0], b[1]]).await
    }

    async fn write_word_with_pec(
        &mut self,
        address: u8,
        register: u8,
        word: u16,
    ) -> Result<(), crate::smbus::bus::ErrorKind> {
        let b = u16::to_le_bytes(word);
        self.write_buf(address, true, &mut [register, b[0], b[1], 0]).await
    }

    async fn read_byte(&mut self, address: u8, register: u8) -> Result<u8, crate::smbus::bus::ErrorKind> {
        let mut buf = [0u8; 1];
        self.write_read_buf(address, false, &[register], &mut buf).await?;
        Ok(buf[0])
    }

    async fn read_byte_with_pec(&mut self, address: u8, register: u8) -> Result<u8, crate::smbus::bus::ErrorKind> {
        let mut buf = [0u8; 2];
        self.write_read_buf(address, true, &[register], &mut buf).await?;
        Ok(buf[0])
    }

    async fn read_word(&mut self, address: u8, register: u8) -> Result<u16, crate::smbus::bus::ErrorKind> {
        let mut buf = [0u8; 2];
        self.write_read_buf(address, false, &[register], &mut buf).await?;
        Ok(u16::from_le_bytes(buf))
    }

    async fn read_word_with_pec(&mut self, address: u8, register: u8) -> Result<u16, crate::smbus::bus::ErrorKind> {
        let mut buf = [0u8; 3];
        self.write_read_buf(address, true, &[register], &mut buf).await?;
        Ok(u16::from_le_bytes([buf[0], buf[1]]))
    }

    async fn process_call(
        &mut self,
        address: u8,
        register: u8,
        word: u16,
    ) -> Result<u16, crate::smbus::bus::ErrorKind> {
        let mut buf = [0u8; 2];
        self.i2c
            .transaction(
                address,
                &mut [
                    Operation::Write(&[register]),
                    Operation::Write(&word.to_le_bytes()),
                    Operation::Read(&mut buf),
                ],
            )
            .await
            .map_err(|e| crate::smbus::bus::ErrorKind::from(e.kind()))?;
        Ok(u16::from_le_bytes(buf))
    }

    async fn process_call_with_pec(
        &mut self,
        address: u8,
        register: u8,
        word: u16,
    ) -> Result<u16, crate::smbus::bus::ErrorKind> {
        let mut buf = [0u8; 3];
        let mut pec = Self::pec_calc_with_write_addr(address)?;
        pec.write_u8(register);
        pec.write(&word.to_le_bytes());
        pec.write_u8(crate::smbus::bus::read_address_byte(address));
        self.i2c
            .transaction(
                address,
                &mut [
                    Operation::Write(&[register]),
                    Operation::Write(&word.to_le_bytes()),
                    Operation::Read(&mut buf),
                ],
            )
            .await
            .map_err(|e| crate::smbus::bus::ErrorKind::from(e.kind()))?;
        let (recvd_pec, data) = buf.split_last().ok_or(crate::smbus::bus::ErrorKind::Pec)?;
        pec.write(data);
        Self::check_pec(*recvd_pec, pec.finish())?;
        Ok(u16::from_le_bytes([buf[0], buf[1]]))
    }

    async fn block_write(
        &mut self,
        address: u8,
        register: u8,
        data: &[u8],
    ) -> Result<(), crate::smbus::bus::ErrorKind> {
        if data.len() > crate::smbus::bus::MAX_BLOCK_SIZE {
            return Err(crate::smbus::bus::ErrorKind::TooLargeBlockTransaction);
        }
        self.i2c
            .transaction(
                address,
                &mut [
                    Operation::Write(&[register]),
                    Operation::Write(&[data.len() as u8]),
                    Operation::Write(data),
                ],
            )
            .await
            .map_err(|e| crate::smbus::bus::ErrorKind::from(e.kind()))?;
        Ok(())
    }

    async fn block_write_with_pec(
        &mut self,
        address: u8,
        register: u8,
        data: &[u8],
    ) -> Result<(), crate::smbus::bus::ErrorKind> {
        if data.len() > crate::smbus::bus::MAX_BLOCK_SIZE {
            return Err(crate::smbus::bus::ErrorKind::TooLargeBlockTransaction);
        }
        let mut pec = Self::pec_calc_with_write_addr(address)?;
        pec.write_u8(register);
        pec.write_u8(data.len() as u8);
        pec.write(data);
        let pec: u8 = Self::finalize_pec_byte(pec.finish())?;
        self.i2c
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
            .map_err(|e| crate::smbus::bus::ErrorKind::from(e.kind()))?;
        Ok(())
    }

    async fn block_read(
        &mut self,
        address: u8,
        register: u8,
        data: &mut [u8],
    ) -> Result<(), crate::smbus::bus::ErrorKind> {
        if data.len() > crate::smbus::bus::MAX_BLOCK_SIZE {
            return Err(crate::smbus::bus::ErrorKind::TooLargeBlockTransaction);
        }
        let mut msg_size = [0u8];
        self.i2c
            .transaction(
                address,
                &mut [
                    Operation::Write(&[register]),
                    Operation::Read(&mut msg_size),
                    Operation::Read(data),
                ],
            )
            .await
            .map_err(|e| crate::smbus::bus::ErrorKind::from(e.kind()))?;
        if usize::from(msg_size[0]) != data.len() {
            return Err(crate::smbus::bus::ErrorKind::BlockSizeMismatch);
        }
        Ok(())
    }

    async fn block_read_with_pec(
        &mut self,
        address: u8,
        register: u8,
        data: &mut [u8],
    ) -> Result<(), crate::smbus::bus::ErrorKind> {
        if data.len() > crate::smbus::bus::MAX_BLOCK_SIZE {
            return Err(crate::smbus::bus::ErrorKind::TooLargeBlockTransaction);
        }
        let mut msg_size = [0u8];
        let mut pec_buf = [0u8];
        let mut pec = Self::pec_calc_with_write_addr(address)?;
        pec.write_u8(register);
        pec.write_u8(crate::smbus::bus::read_address_byte(address));
        self.i2c
            .transaction(
                address,
                &mut [
                    Operation::Write(&[register]),
                    Operation::Read(&mut msg_size),
                    Operation::Read(data),
                    Operation::Read(&mut pec_buf),
                ],
            )
            .await
            .map_err(|e| crate::smbus::bus::ErrorKind::from(e.kind()))?;
        if usize::from(msg_size[0]) != data.len() {
            return Err(crate::smbus::bus::ErrorKind::BlockSizeMismatch);
        }
        pec.write(&msg_size);
        pec.write(data);
        Self::check_pec(pec_buf[0], pec.finish())?;
        Ok(())
    }

    async fn block_write_block_read_process_call(
        &mut self,
        address: u8,
        register: u8,
        write_data: &[u8],
        read_data: &mut [u8],
    ) -> Result<(), crate::smbus::bus::ErrorKind> {
        if write_data.len() + read_data.len() > crate::smbus::bus::MAX_BLOCK_SIZE {
            return Err(crate::smbus::bus::ErrorKind::TooLargeBlockTransaction);
        }
        let mut read_msg_size = [0u8];
        self.i2c
            .transaction(
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
            .map_err(|e| crate::smbus::bus::ErrorKind::from(e.kind()))?;
        if usize::from(read_msg_size[0]) != read_data.len() {
            return Err(crate::smbus::bus::ErrorKind::BlockSizeMismatch);
        }
        Ok(())
    }

    async fn block_write_block_read_process_call_with_pec(
        &mut self,
        address: u8,
        register: u8,
        write_data: &[u8],
        read_data: &mut [u8],
    ) -> Result<(), crate::smbus::bus::ErrorKind> {
        if write_data.len() + read_data.len() > crate::smbus::bus::MAX_BLOCK_SIZE {
            return Err(crate::smbus::bus::ErrorKind::TooLargeBlockTransaction);
        }
        let mut read_msg_size = [0u8];
        let mut pec_buf = [0u8];
        let mut pec = Self::pec_calc_with_write_addr(address)?;
        pec.write_u8(register);
        pec.write_u8(write_data.len() as u8);
        pec.write(write_data);
        pec.write_u8(crate::smbus::bus::read_address_byte(address));
        self.i2c
            .transaction(
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
            .map_err(|e| crate::smbus::bus::ErrorKind::from(e.kind()))?;
        if usize::from(read_msg_size[0]) != read_data.len() {
            return Err(crate::smbus::bus::ErrorKind::BlockSizeMismatch);
        }
        pec.write(&read_msg_size);
        pec.write(read_data);
        Self::check_pec(pec_buf[0], pec.finish())?;
        Ok(())
    }
}
#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::indexing_slicing, clippy::cast_possible_truncation)]
mod tests {
    use super::Smbus;
    use crate::smbus::bus::{
        read_address_byte, write_address_byte, Error as SmbusError, ErrorKind, MAX_BLOCK_SIZE, READ_BIT,
    };
    use core::hash::Hasher;
    use embedded_hal_async::i2c::ErrorKind as I2cErrorKind;
    use embedded_hal_mock::eh1::i2c::{Mock as I2cMock, Transaction as Tx};
    use smbus_pec::{pec, Pec};

    const ADDR: u8 = 0x42;
    const REG: u8 = 0x07;

    /// Compute the expected SMBus PEC byte over a flat concatenation of byte
    /// slices, using the `smbus-pec` crate as the reference implementation.
    fn expected_pec(parts: &[&[u8]]) -> u8 {
        let mut buf: std::vec::Vec<u8> = std::vec::Vec::new();
        for p in parts {
            buf.extend_from_slice(p);
        }
        pec(&buf)
    }

    /// PEC provider that exposes the `smbus-pec` calculator.
    struct TestPec;
    impl super::PecProvider for TestPec {
        type Calc = Pec;
        fn new_calc() -> Option<Self::Calc> {
            Some(Pec::new())
        }
    }

    /// PEC provider that reports PEC as unavailable.
    struct NoPec;
    impl super::PecProvider for NoPec {
        type Calc = Pec;
        fn new_calc() -> Option<Self::Calc> {
            None
        }
    }

    type TestBus = super::SwSmbusI2c<I2cMock, TestPec>;
    type NoPecBus = super::SwSmbusI2c<I2cMock, NoPec>;

    fn new_bus(expectations: &[Tx]) -> TestBus {
        super::SwSmbusI2c::new(I2cMock::new(expectations))
    }

    fn done(mut bus: TestBus) {
        bus.inner_mut().done();
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
            ErrorKind::BlockSizeMismatch,
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
        let pec = expected_pec(&[&[read_address_byte(ADDR)], &[data]]);
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
        bus.send_byte(ADDR, 0x55).await.unwrap();
        done(bus);
    }

    #[tokio::test]
    async fn send_byte_pec() {
        let pec = expected_pec(&[&[write_address_byte(ADDR), 0x55]]);
        let mut bus = new_bus(&[Tx::write(ADDR, std::vec![0x55, pec])]);
        bus.send_byte_with_pec(ADDR, 0x55).await.unwrap();
        done(bus);
    }

    #[tokio::test]
    async fn receive_byte_no_pec() {
        let mut bus = new_bus(&[Tx::read(ADDR, std::vec![0x99])]);
        let b = bus.receive_byte(ADDR).await.unwrap();
        assert_eq!(b, 0x99);
        done(bus);
    }

    #[tokio::test]
    async fn receive_byte_pec() {
        let data = 0x99u8;
        let pec = expected_pec(&[&[read_address_byte(ADDR), data]]);
        let mut bus = new_bus(&[Tx::read(ADDR, std::vec![data, pec])]);
        let b = bus.receive_byte_with_pec(ADDR).await.unwrap();
        assert_eq!(b, data);
        done(bus);
    }

    #[tokio::test]
    async fn receive_byte_pec_mismatch() {
        let mut bus = new_bus(&[Tx::read(ADDR, std::vec![0x99, 0xFF])]);
        let err = bus.receive_byte_with_pec(ADDR).await.unwrap_err();
        assert_eq!(err.kind(), ErrorKind::Pec);
        done(bus);
    }

    // ---------- write_byte / write_word ----------

    #[tokio::test]
    async fn write_byte_no_pec() {
        let mut bus = new_bus(&[Tx::write(ADDR, std::vec![REG, 0x33])]);
        bus.write_byte(ADDR, REG, 0x33).await.unwrap();
        done(bus);
    }

    #[tokio::test]
    async fn write_byte_pec() {
        let pec = expected_pec(&[&[write_address_byte(ADDR), REG, 0x33]]);
        let mut bus = new_bus(&[Tx::write(ADDR, std::vec![REG, 0x33, pec])]);
        bus.write_byte_with_pec(ADDR, REG, 0x33).await.unwrap();
        done(bus);
    }

    #[tokio::test]
    async fn write_word_no_pec() {
        let word: u16 = 0xBEEF;
        let bytes = word.to_le_bytes();
        let mut bus = new_bus(&[Tx::write(ADDR, std::vec![REG, bytes[0], bytes[1]])]);
        bus.write_word(ADDR, REG, word).await.unwrap();
        done(bus);
    }

    #[tokio::test]
    async fn write_word_pec() {
        let word: u16 = 0xBEEF;
        let bytes = word.to_le_bytes();
        let pec = expected_pec(&[&[write_address_byte(ADDR), REG, bytes[0], bytes[1]]]);
        let mut bus = new_bus(&[Tx::write(ADDR, std::vec![REG, bytes[0], bytes[1], pec])]);
        bus.write_word_with_pec(ADDR, REG, word).await.unwrap();
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
        let b = bus.read_byte(ADDR, REG).await.unwrap();
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
        let b = bus.read_byte_with_pec(ADDR, REG).await.unwrap();
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
        let err = bus.read_byte_with_pec(ADDR, REG).await.unwrap_err();
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
        let w = bus.read_word(ADDR, REG).await.unwrap();
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
        let w = bus.read_word_with_pec(ADDR, REG).await.unwrap();
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
        let r = bus.process_call(ADDR, REG, word).await.unwrap();
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
        hasher.write(&word.to_le_bytes());
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
        let r = bus.process_call_with_pec(ADDR, REG, word).await.unwrap();
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
        bus.block_write(ADDR, REG, &data).await.unwrap();
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
        bus.block_write_with_pec(ADDR, REG, &data).await.unwrap();
        done(bus);
    }

    #[tokio::test]
    async fn block_write_too_large() {
        let mut bus = new_bus(&[]);
        let data = std::vec![0u8; MAX_BLOCK_SIZE + 1];
        let err = bus.block_write(ADDR, REG, &data).await.unwrap_err();
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
        bus.block_read(ADDR, REG, &mut buf).await.unwrap();
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
        bus.block_read_with_pec(ADDR, REG, &mut buf).await.unwrap();
        assert_eq!(buf, payload);
        done(bus);
    }

    #[tokio::test]
    async fn block_read_too_large() {
        let mut bus = new_bus(&[]);
        let mut buf = std::vec![0u8; MAX_BLOCK_SIZE + 1];
        let err = bus.block_read(ADDR, REG, &mut buf).await.unwrap_err();
        assert_eq!(err.kind(), ErrorKind::TooLargeBlockTransaction);
        done(bus);
    }

    #[tokio::test]
    async fn block_read_size_mismatch_no_pec() {
        // Device reports `2` but the caller expected `3`.
        let mut buf = [0u8; 3];
        let mut bus = new_bus(&[
            Tx::transaction_start(ADDR),
            Tx::write(ADDR, std::vec![REG]),
            Tx::read(ADDR, std::vec![2]),
            Tx::read(ADDR, std::vec![0x10, 0x20, 0x30]),
            Tx::transaction_end(ADDR),
        ]);
        let err = bus.block_read(ADDR, REG, &mut buf).await.unwrap_err();
        assert_eq!(err.kind(), ErrorKind::BlockSizeMismatch);
        done(bus);
    }

    #[tokio::test]
    async fn block_read_size_mismatch_pec() {
        // Device reports `2` but the caller expected `3`. The mismatch must be
        // reported as `BlockSizeMismatch` rather than `Pec`, even though the
        // received PEC byte would not match either.
        let mut buf = [0u8; 3];
        let mut bus = new_bus(&[
            Tx::transaction_start(ADDR),
            Tx::write(ADDR, std::vec![REG]),
            Tx::read(ADDR, std::vec![2]),
            Tx::read(ADDR, std::vec![0x10, 0x20, 0x30]),
            Tx::read(ADDR, std::vec![0x00]),
            Tx::transaction_end(ADDR),
        ]);
        let err = bus.block_read_with_pec(ADDR, REG, &mut buf).await.unwrap_err();
        assert_eq!(err.kind(), ErrorKind::BlockSizeMismatch);
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
        bus.block_write_block_read_process_call(ADDR, REG, &write_data, &mut read_buf)
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
        bus.block_write_block_read_process_call_with_pec(ADDR, REG, &write_data, &mut read_buf)
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
            .block_write_block_read_process_call(ADDR, REG, &write_data, &mut read_buf)
            .await
            .unwrap_err();
        assert_eq!(err.kind(), ErrorKind::TooLargeBlockTransaction);
        done(bus);
    }

    #[tokio::test]
    async fn bwbr_size_mismatch_no_pec() {
        let write_data = [0x01u8, 0x02];
        let mut read_buf = [0u8; 2];
        // Device returns count `1` but caller expected `2`.
        let mut bus = new_bus(&[
            Tx::transaction_start(ADDR),
            Tx::write(ADDR, std::vec![REG]),
            Tx::write(ADDR, std::vec![write_data.len() as u8]),
            Tx::write(ADDR, write_data.to_vec()),
            Tx::read(ADDR, std::vec![1]),
            Tx::read(ADDR, std::vec![0xAA, 0xBB]),
            Tx::transaction_end(ADDR),
        ]);
        let err = bus
            .block_write_block_read_process_call(ADDR, REG, &write_data, &mut read_buf)
            .await
            .unwrap_err();
        assert_eq!(err.kind(), ErrorKind::BlockSizeMismatch);
        done(bus);
    }

    #[tokio::test]
    async fn bwbr_size_mismatch_pec() {
        let write_data = [0x01u8, 0x02];
        let mut read_buf = [0u8; 2];
        // Device returns count `1` but caller expected `2`. Must be reported
        // as `BlockSizeMismatch` rather than `Pec`.
        let mut bus = new_bus(&[
            Tx::transaction_start(ADDR),
            Tx::write(ADDR, std::vec![REG]),
            Tx::write(ADDR, std::vec![write_data.len() as u8]),
            Tx::write(ADDR, write_data.to_vec()),
            Tx::read(ADDR, std::vec![1]),
            Tx::read(ADDR, std::vec![0xAA, 0xBB]),
            Tx::read(ADDR, std::vec![0x00]),
            Tx::transaction_end(ADDR),
        ]);
        let err = bus
            .block_write_block_read_process_call_with_pec(ADDR, REG, &write_data, &mut read_buf)
            .await
            .unwrap_err();
        assert_eq!(err.kind(), ErrorKind::BlockSizeMismatch);
        done(bus);
    }

    // ---------- PEC unavailable ----------

    fn new_no_pec_bus(expectations: &[Tx]) -> NoPecBus {
        super::SwSmbusI2c::new(I2cMock::new(expectations))
    }

    fn done_no_pec(mut bus: NoPecBus) {
        bus.inner_mut().done();
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
        bus.send_byte(ADDR, 0x55).await.unwrap();
        assert_eq!(bus.receive_byte(ADDR).await.unwrap(), 0x99);
        bus.write_byte(ADDR, REG, 0x33).await.unwrap();
        assert_eq!(bus.read_byte(ADDR, REG).await.unwrap(), 0x77);
        done_no_pec(bus);
    }

    #[tokio::test]
    async fn pec_unavailable_returns_pec_error() {
        let mut bus = super::SwSmbusI2c::<I2cMock, NoPec>::new(I2cMock::new(&[]));
        // Any PEC-requiring path should fail without touching the bus.
        let err = bus.send_byte_with_pec(ADDR, 0x55).await.unwrap_err();
        assert_eq!(err.kind(), ErrorKind::Pec);
        let err = bus.receive_byte_with_pec(ADDR).await.unwrap_err();
        assert_eq!(err.kind(), ErrorKind::Pec);
        let err = bus.read_byte_with_pec(ADDR, REG).await.unwrap_err();
        assert_eq!(err.kind(), ErrorKind::Pec);
        let err = bus.read_word_with_pec(ADDR, REG).await.unwrap_err();
        assert_eq!(err.kind(), ErrorKind::Pec);
        let err = bus.process_call_with_pec(ADDR, REG, 0).await.unwrap_err();
        assert_eq!(err.kind(), ErrorKind::Pec);
        let err = bus.block_write_with_pec(ADDR, REG, &[1, 2]).await.unwrap_err();
        assert_eq!(err.kind(), ErrorKind::Pec);
        let mut rb = [0u8; 2];
        let err = bus.block_read_with_pec(ADDR, REG, &mut rb).await.unwrap_err();
        assert_eq!(err.kind(), ErrorKind::Pec);
        let err = bus
            .block_write_block_read_process_call_with_pec(ADDR, REG, &[1], &mut rb)
            .await
            .unwrap_err();
        assert_eq!(err.kind(), ErrorKind::Pec);
        bus.inner_mut().done();
    }

    // ---------- &mut T forwarding ----------

    #[tokio::test]
    async fn mut_ref_smbus_forwards() {
        let mut bus = new_bus(&[Tx::write(ADDR, std::vec![0x55])]);
        let r: &mut TestBus = &mut bus;
        r.send_byte(ADDR, 0x55).await.unwrap();
        assert!(<&mut TestBus as Smbus>::get_pec_calc().is_some());
        done(bus);
    }

    // ---------- error propagation from underlying I2C ----------

    #[tokio::test]
    async fn i2c_error_propagates() {
        let mut bus = new_bus(&[Tx::write(ADDR, std::vec![0x55]).with_error(I2cErrorKind::Bus)]);
        let err = bus.send_byte(ADDR, 0x55).await.unwrap_err();
        assert_eq!(err.kind(), ErrorKind::I2c(I2cErrorKind::Bus));
        done(bus);
    }
}
