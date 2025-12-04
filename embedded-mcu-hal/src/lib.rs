#![cfg_attr(not(test), no_std)]

pub mod time;

pub mod smbus;

/// Traits for NVRAM (Non-Volatile Random Access Memory) storage and management.
mod nvram;
pub use nvram::{Nvram, NvramStorage};
