#![no_std]

/// Implementation of a wall-clock date-time.
pub mod datetime;

/// Traits for a datetime-based clock (e.g. real-time clock).
mod datetime_clock;
pub use datetime_clock::{DatetimeClock, DatetimeClockError};

/// Traits for NVRAM (Non-Volatile Random Access Memory) storage and management.
mod nvram;
pub use nvram::{Nvram, NvramStorage};
