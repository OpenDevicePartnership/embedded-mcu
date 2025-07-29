/// Implementation of a wall-clock date-time.
mod datetime;
pub use datetime::{Datetime, DatetimeError, UncheckedDatetime};

/// Traits for a datetime-based clock (e.g. real-time clock).
mod datetime_clock;
pub use datetime_clock::{DatetimeClock, DatetimeClockError};
