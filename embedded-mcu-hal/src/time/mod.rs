//! Wall-clock date/time types and real-time clock (RTC) traits.
//!
//! This module provides two things:
//!
//! 1. **Value types** for representing a point in time: [`Datetime`],
//!    [`DatetimeFields`], [`Month`], and [`DatetimeError`].
//! 2. **A peripheral trait** for driving an RTC: [`DatetimeClock`] and its
//!    associated error type [`DatetimeClockError`].
//!
//! # Representing time
//!
//! The central type is [`Datetime`], a validated, timezone-neutral date/time
//! value with nanosecond precision.  It is constructed through
//! [`Datetime::new`], which accepts a [`DatetimeFields`] and validates all
//! fields before returning `Ok(Datetime)`.  This two-step approach lets
//! callers build up a datetime from raw numeric fields (e.g. values read
//! directly from hardware registers) without the risk of creating an invalid
//! value that violates calendar rules.
//!
//! Conversion between [`Datetime`] and Unix timestamps (seconds since
//! 1970-01-01 00:00:00, ignoring leap seconds) is provided by
//! [`Datetime::timestamp`] and [`Datetime::from_timestamp`],
//! both of which are `const fn`.
//!
//! When the **`chrono`** Cargo feature is enabled, `TryFrom<chrono::NaiveDateTime>`
//! and `Into<chrono::NaiveDateTime>` are implemented on [`Datetime`], making
//! it easy to interoperate with `chrono`-based application code running on a
//! host or in tests.
//!
//! # Driving an RTC peripheral
//!
//! [`DatetimeClock`] is implemented by drivers for hardware RTC peripherals.
//! It exposes three methods: reading the current time, setting the current
//! time, and querying the hardware's maximum resolution.  See the
//! [`DatetimeClock`] documentation for details on precision handling and
//! error conditions.

/// Implementation of a wall-clock date-time.
mod datetime;
pub use datetime::{Datetime, DatetimeError, DatetimeFields, Month};

/// Traits for a datetime-based clock (e.g. real-time clock).
mod datetime_clock;
pub use datetime_clock::{DatetimeClock, DatetimeClockError};
