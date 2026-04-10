//! The [`DatetimeClock`] trait and its associated error type
//! [`DatetimeClockError`].
//!
//! See the [`time`](super) module documentation for an overview.

use super::datetime::Datetime;

/// Errors that can occur when reading from or writing to a [`DatetimeClock`].
#[cfg_attr(all(feature = "defmt", not(test)), derive(defmt::Format))]
#[derive(PartialEq, Debug)]
pub enum DatetimeClockError {
    /// The operation could not be completed because the clock hardware is not enabled.
    NotEnabled,

    /// The operation could not be completed because the Datetime provided is out of the range that the hardware can support.
    UnsupportedDatetime,

    /// The operation could not be completed due to an unspecified error.
    Unknown,
}

/// Trait for a hardware real-time clock (RTC) peripheral.
///
/// An RTC is a typically low-power clock that tracks wall-clock time
/// independently of the main processor, often while the rest of the system is
/// in a low-power or powered-off state.  This trait provides a
/// hardware-agnostic interface for reading and setting the current date and
/// time.
///
/// # Precision
///
/// The finest time granularity the hardware can store is reported by
/// [`max_resolution_hz`].  Any sub-second information in a [`Datetime`] that
/// exceeds this resolution will be silently truncated when written to the
/// hardware.  Applications that require sub-second accuracy should consult
/// `max_resolution_hz` before relying on the nanosecond field returned by
/// [`get_current_datetime`].
///
/// # Typical usage
///
/// Set the clock once at startup (e.g. from a host-provided timestamp or an
/// NTP-synchronised value), then read it as needed.  If long-term accuracy
/// matters, periodically re-sync with an authoritative time source to correct
/// for RTC crystal drift.
///
/// [`max_resolution_hz`]: DatetimeClock::max_resolution_hz
/// [`get_current_datetime`]: DatetimeClock::get_current_datetime
pub trait DatetimeClock {
    /// Reads the current date and time from the hardware clock.
    ///
    /// Returns a [`Datetime`] representing the current wall-clock time as
    /// maintained by the RTC peripheral.  The nanosecond field of the returned
    /// value reflects the hardware's actual resolution; components finer than
    /// [`max_resolution_hz`] will be zero.
    ///
    /// # Errors
    ///
    /// * [`DatetimeClockError::NotEnabled`] — the clock hardware has not been
    ///   started or has been disabled.
    /// * [`DatetimeClockError::Unknown`] — an unspecified hardware error
    ///   occurred.
    ///
    /// [`max_resolution_hz`]: DatetimeClock::max_resolution_hz
    fn get_current_datetime(&self) -> Result<Datetime, DatetimeClockError>;

    /// Sets the hardware clock to the given date and time.
    ///
    /// After a successful call, subsequent reads via [`get_current_datetime`]
    /// should return times no earlier than `datetime` (accounting for any time
    /// elapsed since the call).
    ///
    /// If `datetime` has a nanosecond value that exceeds the precision
    /// supported by the hardware (see [`max_resolution_hz`]), the sub-second
    /// component will be truncated to the nearest representable value.
    ///
    /// # Errors
    ///
    /// * [`DatetimeClockError::NotEnabled`] — the clock hardware has not been
    ///   started or has been disabled.
    /// * [`DatetimeClockError::UnsupportedDatetime`] — the provided
    ///   [`Datetime`] is outside the range the hardware can represent (e.g. a
    ///   year that exceeds the RTC's register width).
    /// * [`DatetimeClockError::Unknown`] — an unspecified hardware error
    ///   occurred.
    ///
    /// [`get_current_datetime`]: DatetimeClock::get_current_datetime
    /// [`max_resolution_hz`]: DatetimeClock::max_resolution_hz
    fn set_current_datetime(&mut self, datetime: &Datetime) -> Result<(), DatetimeClockError>;

    /// Returns the maximum resolution of this RTC in Hz.
    ///
    /// This value represents the finest time granularity the hardware can
    /// store.  Common values are:
    ///
    /// * `1` — 1 Hz resolution (whole seconds only; nanoseconds always 0).
    /// * `1_000` — 1 kHz resolution (millisecond precision).
    ///
    /// Use this value to determine how much of the nanosecond field in a
    /// [`Datetime`] is meaningful after a round-trip through the hardware.
    /// For example, a 1 Hz RTC will always return a nanosecond value of 0 and
    /// will truncate any sub-second information passed to
    /// [`set_current_datetime`].
    ///
    /// [`set_current_datetime`]: DatetimeClock::set_current_datetime
    fn max_resolution_hz(&self) -> u32;
}
