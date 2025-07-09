//! Traits for datetime-based clocks (e.g. real-time clocks).

use crate::datetime::Datetime;

#[cfg_attr(feature = "defmt", derive(defmt::Format))]
#[derive(PartialEq, Debug)]
pub enum DatetimeClockError {
    /// The operation could not be completed because the clock hardware is not enabled.
    NotEnabled,

    /// The operation could not be completed because the Datetime provided is out of the range that the hardware can support.
    UnsupportedDatetime,

    /// The operation could not be completed due to an unspecified error.
    Unknown,
}

/// Trait for datetime-based clock (e.g. real-time clock).
/// This trait provides methods to get and set the current wall-clock date and time in a structured format.
/// Typical usage would be setting the current UTC time, periodically syncing it with an external time source (e.g. host OS with NTP daemon) to account for leap seconds.
pub trait DatetimeClock {
    /// Returns the current structured date and time.
    fn get_current_datetime(&self) -> Result<Datetime, DatetimeClockError>;

    /// Sets the current structured date and time.
    /// If a Datetime with greater precision than MAX_RESOLUTION_HZ is provided, it will be truncated to the maximum resolution.
    fn set_current_datetime(&mut self, datetime: &Datetime) -> Result<(), DatetimeClockError>;

    /// The resolution of the RTC in Hz.  Typical values are 1hz and 1000hz.
    const MAX_RESOLUTION_HZ: u32;
}
