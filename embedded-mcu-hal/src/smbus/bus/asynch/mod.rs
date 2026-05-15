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
mod tests;
