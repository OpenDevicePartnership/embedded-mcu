//! Traits for interacting with I2c controllers and slaves

pub use embedded_hal::i2c::{AddressMode, SevenBitAddress, TenBitAddress};

pub mod target;
