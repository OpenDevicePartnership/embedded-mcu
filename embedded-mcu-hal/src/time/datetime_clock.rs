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
/// [`resolution_hz`].  Any sub-second information in a [`Datetime`] that
/// exceeds this resolution will be silently truncated when written to the
/// hardware.  Applications that require sub-second accuracy should consult
/// `resolution_hz` before relying on the nanosecond field returned by [`now`].
///
/// # Typical usage
///
/// Set the clock once at startup (e.g. from a host-provided timestamp or an
/// NTP-synchronised value), then read it as needed.  If long-term accuracy
/// matters, periodically re-sync with an authoritative time source to correct
/// for RTC crystal drift.
///
/// [`resolution_hz`]: DatetimeClock::resolution_hz
/// [`now`]: DatetimeClock::now
pub trait DatetimeClock {
    /// Reads the current date and time from the hardware clock.
    ///
    /// Returns a [`Datetime`] representing the current wall-clock time as
    /// maintained by the RTC peripheral.  The nanosecond field of the returned
    /// value reflects the hardware's actual resolution; components finer than
    /// [`resolution_hz`] will be zero.
    ///
    /// # Errors
    ///
    /// * [`DatetimeClockError::NotEnabled`] — the clock hardware has not been
    ///   started or has been disabled.
    /// * [`DatetimeClockError::Unknown`] — an unspecified hardware error
    ///   occurred.
    ///
    /// [`resolution_hz`]: DatetimeClock::resolution_hz
    fn now(&self) -> Result<Datetime, DatetimeClockError>;

    /// Sets the hardware clock to the given date and time.
    ///
    /// After a successful call, subsequent reads via [`now`] should return
    /// times no earlier than `datetime` (accounting for any time elapsed since
    /// the call).
    ///
    /// If `datetime` has a nanosecond value that exceeds the precision
    /// supported by the hardware (see [`resolution_hz`]), the sub-second
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
    /// [`now`]: DatetimeClock::now
    /// [`resolution_hz`]: DatetimeClock::resolution_hz
    fn set(&mut self, datetime: Datetime) -> Result<(), DatetimeClockError>;

    /// Returns the resolution of this RTC in Hz.
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
    /// will truncate any sub-second information passed to [`set`].
    ///
    /// [`set`]: DatetimeClock::set
    fn resolution_hz(&self) -> u32;
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used, clippy::expect_used)]

    use super::*;
    use crate::time::{DatetimeFields, Month};

    // ── Mock implementation ──

    /// A software mock RTC for use in tests.
    ///
    /// Starts enabled at the Unix epoch.  Use [`MockDatetimeClock::disabled`]
    /// to construct one in the not-enabled state, and
    /// [`MockDatetimeClock::with_max_year`] to simulate hardware that cannot
    /// represent years beyond a fixed limit.
    struct MockDatetimeClock {
        enabled: bool,
        current: Datetime,
        resolution_hz: u32,
        max_year: u16,
    }

    impl MockDatetimeClock {
        fn new(resolution_hz: u32) -> Self {
            Self {
                enabled: true,
                current: Datetime::from_unix_timestamp(0),
                resolution_hz,
                max_year: u16::MAX,
            }
        }

        fn disabled(resolution_hz: u32) -> Self {
            Self {
                enabled: false,
                ..Self::new(resolution_hz)
            }
        }

        fn with_max_year(mut self, max_year: u16) -> Self {
            self.max_year = max_year;
            self
        }
    }

    impl DatetimeClock for MockDatetimeClock {
        fn now(&self) -> Result<Datetime, DatetimeClockError> {
            if !self.enabled {
                return Err(DatetimeClockError::NotEnabled);
            }
            Ok(self.current)
        }

        fn set(&mut self, datetime: Datetime) -> Result<(), DatetimeClockError> {
            if !self.enabled {
                return Err(DatetimeClockError::NotEnabled);
            }
            if datetime.year() > self.max_year {
                return Err(DatetimeClockError::UnsupportedDatetime);
            }
            // Truncate nanoseconds to the nearest representable tick.
            let nanos_per_tick = 1_000_000_000u32 / self.resolution_hz;
            let truncated_nanos = (datetime.nanoseconds() / nanos_per_tick) * nanos_per_tick;
            self.current = Datetime::new(DatetimeFields {
                year: datetime.year(),
                month: datetime.month(),
                day: datetime.day(),
                hour: datetime.hour(),
                minute: datetime.minute(),
                second: datetime.second(),
                nanosecond: truncated_nanos,
            })
            .expect("truncated datetime derived from a valid Datetime is always valid");
            Ok(())
        }

        fn resolution_hz(&self) -> u32 {
            self.resolution_hz
        }
    }

    fn sample_datetime() -> Datetime {
        Datetime::new(DatetimeFields {
            year: 2025,
            month: Month::April,
            day: 10,
            hour: 12,
            minute: 30,
            second: 45,
            nanosecond: 123_456_789,
        })
        .expect("sample datetime is valid")
    }

    // ── now() tests ──

    #[test]
    fn now_returns_datetime_after_set() {
        let mut clock = MockDatetimeClock::new(1_000_000_000);
        let dt = sample_datetime();
        let set_result = clock.set(dt);
        assert!(set_result.is_ok());
        let now_result = clock.now();
        assert!(now_result.is_ok());
        assert_eq!(now_result.unwrap(), dt);
    }

    #[test]
    fn now_on_disabled_clock_returns_not_enabled() {
        let clock = MockDatetimeClock::disabled(1);
        assert_eq!(clock.now(), Err(DatetimeClockError::NotEnabled));
    }

    // ── set() tests ──

    #[test]
    fn set_on_disabled_clock_returns_not_enabled() {
        let mut clock = MockDatetimeClock::disabled(1);
        assert_eq!(clock.set(sample_datetime()), Err(DatetimeClockError::NotEnabled));
    }

    #[test]
    fn set_with_unsupported_year_returns_unsupported_datetime() {
        let mut clock = MockDatetimeClock::new(1).with_max_year(2099);
        let far_future = Datetime::new(DatetimeFields {
            year: 2100,
            month: Month::January,
            day: 1,
            ..Default::default()
        })
        .expect("year 2100 is a valid Datetime");
        assert_eq!(clock.set(far_future), Err(DatetimeClockError::UnsupportedDatetime));
    }

    // ── resolution_hz() tests ──

    #[test]
    fn resolution_hz_returns_configured_value() {
        assert_eq!(MockDatetimeClock::new(1).resolution_hz(), 1);
        assert_eq!(MockDatetimeClock::new(1_000).resolution_hz(), 1_000);
        assert_eq!(MockDatetimeClock::new(1_000_000_000).resolution_hz(), 1_000_000_000);
    }

    // ── Sub-second truncation tests ──

    #[test]
    fn set_at_1hz_truncates_nanoseconds_to_zero() {
        let mut clock = MockDatetimeClock::new(1);
        let set_result = clock.set(sample_datetime());
        assert!(set_result.is_ok());
        let now_result = clock.now();
        assert!(now_result.is_ok());
        assert_eq!(now_result.unwrap().nanoseconds(), 0);
    }

    #[test]
    fn set_at_1khz_truncates_to_milliseconds() {
        let mut clock = MockDatetimeClock::new(1_000);
        let set_result = clock.set(sample_datetime());
        assert!(set_result.is_ok());
        // 123_456_789 ns → truncated to nearest ms → 123_000_000 ns
        let now_result = clock.now();
        assert!(now_result.is_ok());
        assert_eq!(now_result.unwrap().nanoseconds(), 123_000_000);
    }

    #[test]
    fn set_at_nanosecond_resolution_preserves_nanoseconds() {
        let mut clock = MockDatetimeClock::new(1_000_000_000);
        let set_result = clock.set(sample_datetime());
        assert!(set_result.is_ok());
        let now_result = clock.now();
        assert!(now_result.is_ok());
        assert_eq!(now_result.unwrap().nanoseconds(), 123_456_789);
    }
}
