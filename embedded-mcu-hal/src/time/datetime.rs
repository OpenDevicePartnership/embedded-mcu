//! The [`Datetime`] type and its supporting types: [`DatetimeFields`],
//! [`Month`], and [`DatetimeError`].
//!
//! See the [`time`](super) module documentation for an overview.

#[cfg(feature = "chrono")]
use chrono::{Datelike, Timelike};

/// A date/time value whose fields have not yet been validated.
///
/// This struct acts as a staging area for building a [`Datetime`].  Its fields
/// are intentionally `pub` so they can be populated from raw hardware register
/// values, deserialised data, or any other source without requiring an
/// intermediate allocation.  Once all fields are set, pass the struct to
/// [`Datetime::new`] to validate it and obtain a verified [`Datetime`].
///
/// The [`Default`] implementation returns 1970-01-01 00:00:00.000000000 (the
/// Unix epoch).
#[cfg_attr(all(feature = "defmt", not(test)), derive(defmt::Format))]
#[derive(PartialEq, Debug, Copy, Clone)]
pub struct DatetimeFields {
    /// The year component of the date.
    pub year: u16,
    /// The month component of the date (1-12).
    pub month: Month,
    /// The day component of the date (1-31).
    pub day: u8,
    /// The hour component of the time (0-23).
    pub hour: u8,
    /// The minute component of the time (0-59).
    pub minute: u8,
    /// The second component of the time (0-59).
    pub second: u8,
    /// The nanosecond component of the time (0-999_999_999).
    pub nanosecond: u32,
}

/// A calendar month, represented as a `u8` discriminant in the range 1–12.
///
/// The numeric value matches the conventional month number (January = 1,
/// December = 12), which makes conversions to and from hardware register
/// values straightforward via the `num_enum` derives (`IntoPrimitive` and
/// `TryFromPrimitive`).
///
/// `Month` implements `PartialOrd` so months can be compared chronologically.
#[cfg_attr(all(feature = "defmt", not(test)), derive(defmt::Format))]
#[derive(num_enum::IntoPrimitive, num_enum::TryFromPrimitive, Copy, Clone, Debug, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum Month {
    January = 1,
    February = 2,
    March = 3,
    April = 4,
    May = 5,
    June = 6,
    July = 7,
    August = 8,
    September = 9,
    October = 10,
    November = 11,
    December = 12,
}

impl Month {
    /// Returns the number of days in this month for the given `year`.
    ///
    /// February returns 29 in a leap year and 28 otherwise.  All other months
    /// return their standard Gregorian calendar day counts.  The `year`
    /// parameter is only significant for February.
    ///
    /// This method is `const`, so it can be used in compile-time calculations.
    pub const fn days_in_month(&self, year: u16) -> u8 {
        match self {
            Month::January => 31,
            Month::February => {
                if is_leap_year(year) {
                    29
                } else {
                    28
                }
            }
            Month::March => 31,
            Month::April => 30,
            Month::May => 31,
            Month::June => 30,
            Month::July => 31,
            Month::August => 31,
            Month::September => 30,
            Month::October => 31,
            Month::November => 30,
            Month::December => 31,
        }
    }

    /// Returns the month that follows this one.
    ///
    /// December wraps around to January.  This is a `const fn` so it can be
    /// used in compile-time or loop-free iteration over months.
    pub const fn next(&self) -> Month {
        match self {
            Month::January => Month::February,
            Month::February => Month::March,
            Month::March => Month::April,
            Month::April => Month::May,
            Month::May => Month::June,
            Month::June => Month::July,
            Month::July => Month::August,
            Month::August => Month::September,
            Month::September => Month::October,
            Month::October => Month::November,
            Month::November => Month::December,
            Month::December => Month::January,
        }
    }

    /// Returns true if equal, false otherwise. Equivalent to PartialEq, but usable in const contexts.
    pub const fn eq(&self, other: &Month) -> bool {
        (*self as u8) == (*other as u8)
    }
}

/// Check if a year is a leap year.
const fn is_leap_year(year: u16) -> bool {
    (year.is_multiple_of(4) && !year.is_multiple_of(100)) || year.is_multiple_of(400)
}

/// Errors returned by [`Datetime::new`] when a field value is out of range.
///
/// Each variant identifies the first field that failed validation.  The valid
/// range for each field is:
///
/// | Variant | Valid range |
/// |---------|-------------|
/// | `Year` | ≥ 1970 |
/// | `Month` | 1–12 (via `TryFromPrimitive` on [`Month`]; `Datetime::new` always receives a valid `Month` variant) |
/// | `Day` | 1 through the last day of the given month (leap-year-aware) |
/// | `Hour` | 0–23 |
/// | `Minute` | 0–59 |
/// | `Second` | 0–59 |
/// | `Nanosecond` | 0–999,999,999 |
#[cfg_attr(all(feature = "defmt", not(test)), derive(defmt::Format))]
#[derive(PartialEq, Debug)]
pub enum DatetimeError {
    /// The year is invalid.
    Year,
    /// The month is invalid.
    Month,
    /// The day is invalid.
    Day,
    /// The hour is invalid.
    Hour,
    /// The minute is invalid.
    Minute,
    /// The second is invalid.
    Second,
    /// The nanosecond is invalid.
    Nanosecond,
}

/// Default implementation for `Datetime`.
impl Default for DatetimeFields {
    fn default() -> Self {
        DatetimeFields {
            year: 1970,
            month: Month::January,
            day: 1,
            hour: 0,
            minute: 0,
            second: 0,
            nanosecond: 0,
        }
    }
}

/// A validated, timezone-neutral wall-clock date and time.
///
/// `Datetime` wraps a [`DatetimeFields`] whose fields have been verified
/// by [`Datetime::new`].  Once constructed, the value is guaranteed to
/// represent a real point in time: the year is ≥ 1970, the day is within the
/// correct range for the month (taking leap years into account), and every
/// time component is within its valid range.
///
/// # Precision
///
/// The type stores time down to nanosecond precision, but most hardware RTCs
/// operate at a much coarser resolution (typically 1 Hz or 1 000 Hz).
/// [`super::DatetimeClock::resolution_hz`] reports the hardware's actual
/// resolution; sub-second precision beyond that will be silently truncated by
/// the driver.
///
/// # Leap seconds
///
/// Leap seconds are not modelled.  All calculations treat every minute as
/// exactly 60 seconds and every day as exactly 86 400 seconds.  This matches
/// POSIX time semantics and how most embedded RTC hardware behaves.
///
/// # `chrono` interoperability
///
/// When the **`chrono`** Cargo feature is enabled, `Datetime` implements
/// `TryFrom<chrono::NaiveDateTime>` (fails if the year is before 1970) and
/// `From<Datetime> for chrono::NaiveDateTime`.  `chrono`'s partial
/// leap-second representation is handled by dropping the extra second, which
/// is consistent with `chrono`'s own arithmetic semantics.
#[cfg_attr(all(feature = "defmt", not(test)), derive(defmt::Format))]
#[derive(PartialEq, Debug, Default, Copy, Clone)]
pub struct Datetime {
    data: DatetimeFields,
}

impl Datetime {
    /// Returns the number of whole seconds elapsed since the Unix epoch
    /// (1970-01-01 00:00:00 UTC), ignoring leap seconds.
    ///
    /// The calculation accumulates full years from 1970, then full months, then
    /// the remaining days, and finally the sub-day seconds.  Leap years are
    /// accounted for when counting days.
    ///
    /// The nanosecond field is **not** included in the result; only whole
    /// seconds are returned.  This is intentional — Unix time is defined in
    /// whole seconds.
    ///
    /// This method is `const`, which allows for compile-time
    /// calculations of Unix timestamps from hardcoded date/time
    /// values.
    pub const fn unix_timestamp(&self) -> u64 {
        const EPOCH_OFFSET: u64 = 1969 / 4 - 1969 / 100 + 1969 / 400;

        let y = self.data.year as u64;
        let leap_years = (y - 1) / 4 - (y - 1) / 100 + (y - 1) / 400 - EPOCH_OFFSET;
        let mut days = (y - 1970) * 365 + leap_years;

        let mut month = Month::January;
        while !month.eq(&self.data.month) {
            days += month.days_in_month(self.data.year) as u64;
            month = month.next();
        }

        days += self.data.day as u64 - 1;

        let secs = (self.data.hour as u64 * 60 + self.data.minute as u64) * 60 + self.data.second as u64;

        days * 86400 + secs
    }

    /// Constructs a `Datetime` from a Unix timestamp (seconds since
    /// 1970-01-01 00:00:00, ignoring leap seconds).
    ///
    /// This is the inverse of [`unix_timestamp`].  The resulting `Datetime` always
    /// has its nanosecond field set to zero because Unix timestamps do not
    /// carry sub-second information.
    ///
    /// The valid input range is `0` through approximately
    /// `2_005_949_145_599` (year 65 535, December 31, 23:59:59).  Values
    /// beyond this range will cause the internal year counter to overflow
    /// `u16`.
    ///
    /// This method is `const`, so it can used to create compile-time
    /// constant `Datetime` values from hardcoded Unix timestamps.
    ///
    /// [`unix_timestamp`]: Datetime::unix_timestamp
    pub const fn from_unix_timestamp(secs: u64) -> Datetime {
        let mut days = secs / 86400;
        let mut secs = secs % 86400;

        let mut year = 1970;
        let mut day = 1;

        // Calculate year
        while days >= 365 {
            if is_leap_year(year) {
                if days >= 366 {
                    days -= 366;
                } else {
                    break;
                }
            } else {
                days -= 365;
            }
            year += 1;
        }

        // Calculate month
        let mut month = Month::January;
        {
            loop {
                let current_month_days = month.days_in_month(year) as u64;
                if days < current_month_days {
                    break;
                }

                days -= current_month_days;
                month = month.next();
            }
        }

        // Calculate day
        day += days;

        // Calculate hour, minute, and second
        let hour = secs / 3600;
        secs %= 3600;
        let minute = secs / 60;
        let second = secs % 60;

        Datetime {
            data: DatetimeFields {
                year,
                month,
                day: day as u8,
                hour: hour as u8,
                minute: minute as u8,
                second: second as u8,
                nanosecond: 0, // unix time does not have a nanosecond component
            },
        }
    }

    /// Constructs a validated `Datetime` from a [`DatetimeFields`].
    ///
    /// All fields are checked against their valid ranges:
    ///
    /// * `year` must be ≥ 1970.
    /// * `day` must be ≥ 1 and ≤ the number of days in the given month and
    ///   year (leap-year-aware).
    /// * `hour` must be in 0–23.
    /// * `minute` must be in 0–59.
    /// * `second` must be in 0–59.
    /// * `nanosecond` must be in 0–999,999,999.
    ///
    /// Returns `Err(`[`DatetimeError`]`)` with the variant identifying the
    /// first invalid field encountered.
    ///
    /// This method is `const`, so it can be used to create compile-time
    /// constant `Datetime` values.
    pub const fn new(data: DatetimeFields) -> Result<Datetime, DatetimeError> {
        if data.year < 1970 {
            return Err(DatetimeError::Year);
        }

        if data.day < 1 {
            return Err(DatetimeError::Day);
        }

        if data.day > data.month.days_in_month(data.year) {
            return Err(DatetimeError::Day);
        }

        if data.hour > 23 {
            return Err(DatetimeError::Hour);
        }

        if data.minute > 59 {
            return Err(DatetimeError::Minute);
        }

        if data.second > 59 {
            return Err(DatetimeError::Second);
        }

        if data.nanosecond > 999_999_999 {
            return Err(DatetimeError::Nanosecond);
        }

        Ok(Datetime { data })
    }

    /// Returns the year component (≥ 1970).
    pub const fn year(&self) -> u16 {
        self.data.year
    }
    /// Returns the month component.
    pub const fn month(&self) -> Month {
        self.data.month
    }
    /// Returns the day-of-month component (1 through the last day of the stored month).
    pub const fn day(&self) -> u8 {
        self.data.day
    }
    /// Returns the hour component of the time (0-23).
    pub const fn hour(&self) -> u8 {
        self.data.hour
    }
    /// Returns the minute component of the time (0-59).
    pub const fn minute(&self) -> u8 {
        self.data.minute
    }
    /// Returns the second component of the time (0-59).
    pub const fn second(&self) -> u8 {
        self.data.second
    }
    /// Returns the nanosecond component (0–999,999,999).
    ///
    /// Most RTC hardware operates at a resolution of 1 Hz or 1 000 Hz, which
    /// means sub-second components will be zero after a round-trip through
    /// [`super::DatetimeClock::now`].  Consult
    /// [`super::DatetimeClock::resolution_hz`] to determine the finest granularity
    /// the hardware supports before relying on this value.
    pub const fn nanoseconds(&self) -> u32 {
        self.data.nanosecond
    }
}

#[cfg(feature = "chrono")]
impl TryFrom<chrono::NaiveDateTime> for Datetime {
    type Error = DatetimeError;

    fn try_from(date_time: chrono::NaiveDateTime) -> Result<Datetime, DatetimeError> {
        if date_time.year() < 1970 {
            return Err(DatetimeError::Year);
        }

        // chrono::NaiveDateTime has partial support for leap seconds, which it expresses
        // as a nanosecond value that is >= 1_000_000_000. It assumes that no leap seconds exist
        // except if one of the operands is a leap second, in which case it will assume that that's
        // the only leap second that exists.
        //
        // The Datetime type does not support leap seconds, however, so we need to adjust if
        // we're asked to convert from a NaiveDateTime that has leap seconds.
        // We do this by dropping the leap second if it exists.
        // Dropping the leap second in this way is consistent with how chrono::NaiveDateTime's leap
        // second handling works: 02:00:59 + 1 second and 2:00:60 + 1 second both return 02:01:00.
        //
        let mut ns_without_leap = date_time.and_utc().timestamp_subsec_nanos();
        if ns_without_leap >= 1_000_000_000 {
            ns_without_leap -= 1_000_000_000;
        }

        Ok(Self {
            data: DatetimeFields {
                year: date_time.year() as u16,
                month: (date_time.month() as u8).try_into().map_err(|_| DatetimeError::Month)?,
                day: date_time.day() as u8,
                hour: date_time.hour() as u8,
                minute: date_time.minute() as u8,
                second: date_time.second() as u8,
                nanosecond: ns_without_leap,
            },
        })
    }
}

#[cfg(feature = "chrono")]
impl From<Datetime> for chrono::NaiveDateTime {
    fn from(date_time: Datetime) -> Self {
        // Panic safety: unwraps here are safe because our datetime constructor upholds a superset
        // of the invariants that chrono::NaiveDateTime does.  Specifically, chrono::NaiveDateTime
        // has a broader range of years supported and has partial support for leap seconds while
        // our datetime type does not.
        //
        #[allow(clippy::expect_used)]
        chrono::NaiveDate::from_ymd_opt(
            date_time.data.year as i32,
            date_time.data.month as u32,
            date_time.data.day as u32,
        )
        .expect("Datetime has stricter validation than chrono::NaiveDate")
        .and_hms_nano_opt(
            date_time.data.hour as u32,
            date_time.data.minute as u32,
            date_time.data.second as u32,
            date_time.data.nanosecond,
        )
        .expect("Datetime has stricter validation than chrono::NaiveDateTime")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    fn verify_unix_timestamp_roundtrip(data: DatetimeFields) {
        let dt = Datetime::new(data).expect("Datetime should be valid");
        let secs = dt.unix_timestamp();
        let dt2 = Datetime::from_unix_timestamp(secs);
        assert_eq!(dt, dt2, "Datetime roundtrip failed for {:?}", data);
    }

    proptest! {
        #[test]
        fn valid_seconds_always_work(secs in 0u64..=2005949145599) {
            let dt = Datetime::from_unix_timestamp(secs);
            let secs2 = dt.unix_timestamp();
            prop_assert_eq!(secs, secs2, "Datetime roundtrip failed");
        }

        #[test]
        fn valid_years_always_work(year in 1970u16..=65535) {
            let data = DatetimeFields {
                year, ..Default::default()
            };
            let dt = Datetime::new(data).expect("Datetime should be valid");
            let secs = dt.unix_timestamp();
            let dt2 = Datetime::from_unix_timestamp(secs);
            prop_assert_eq!(dt, dt2, "Datetime roundtrip failed for {:?}", data);
        }

        #[test]
        fn valid_months_always_work(month in 1u8..=12) {
            let month_res: Result<Month, _> = month.try_into();
            prop_assert!(month_res.is_ok());
            let data = DatetimeFields {
                month: month_res.unwrap(), ..Default::default()
            };
            let dt = Datetime::new(data).expect("Datetime should be valid");
            let secs = dt.unix_timestamp();
            let dt2 = Datetime::from_unix_timestamp(secs);
            prop_assert_eq!(dt, dt2, "Datetime roundtrip failed for {:?}", data);
        }

        #[test]
        fn valid_days_always_work(day in 1u8..=31) {
            let data = DatetimeFields {
                day, ..Default::default()
            };
            let dt = Datetime::new(data).expect("Datetime should be valid");
            let secs = dt.unix_timestamp();
            let dt2 = Datetime::from_unix_timestamp(secs);
            prop_assert_eq!(dt, dt2, "Datetime roundtrip failed for {:?}", data);
        }

        #[test]
        fn valid_hours_always_work(hour in 0u8..=23) {
            let data = DatetimeFields {
                hour, ..Default::default()
            };
            let dt = Datetime::new(data).expect("Datetime should be valid");
            let secs = dt.unix_timestamp();
            let dt2 = Datetime::from_unix_timestamp(secs);
            prop_assert_eq!(dt, dt2, "Datetime roundtrip failed for {:?}", data);
        }

        #[test]
        fn valid_minutes_always_work(minute in 0u8..=59) {
            let data = DatetimeFields {
                minute, ..Default::default()
            };
            let dt = Datetime::new(data).expect("Datetime should be valid");
            let secs = dt.unix_timestamp();
            let dt2 = Datetime::from_unix_timestamp(secs);
            prop_assert_eq!(dt, dt2, "Datetime roundtrip failed for {:?}", data);
        }

        #[test]
        fn all_leap_years_have_29_days_in_february(year in (1970u16..=65535).
                                                   prop_filter("Leap years", |y| is_leap_year(*y) )) {
            let data = DatetimeFields {
                year, month: Month::February, day: 29, ..Default::default()
            };
            let dt = Datetime::new(data);
            prop_assert!(dt.is_ok());
        }
    }

    #[test]
    fn test_all_date_roundtrip() {
        for year in 1970..=2500 {
            for month in 1..=12 {
                let month: Month = month.try_into().expect("Months from 1-12 should always convert");
                let days_in_month = month.days_in_month(year);
                for day in 1..=days_in_month as u8 {
                    verify_unix_timestamp_roundtrip(DatetimeFields {
                        year,
                        month,
                        day,
                        ..Default::default()
                    });
                }
            }
        }
    }

    #[test]
    fn test_unix_timestamp_roundtrip() {
        verify_unix_timestamp_roundtrip(DatetimeFields {
            year: 1979,
            month: Month::January,
            day: 1,
            ..Default::default()
        });

        verify_unix_timestamp_roundtrip(DatetimeFields {
            year: 2023,
            month: Month::October,
            day: 4,
            hour: 16,
            ..Default::default()
        });

        verify_unix_timestamp_roundtrip(DatetimeFields {
            year: 2024,
            month: Month::March,
            day: 2,
            ..Default::default()
        });

        verify_unix_timestamp_roundtrip(DatetimeFields {
            year: 2024,
            month: Month::March,
            day: 1,
            ..Default::default()
        });

        verify_unix_timestamp_roundtrip(DatetimeFields {
            year: 2024,
            month: Month::February,
            day: 29,
            ..Default::default()
        });

        verify_unix_timestamp_roundtrip(DatetimeFields {
            year: 2024,
            month: Month::February,
            day: 28,
            ..Default::default()
        });

        verify_unix_timestamp_roundtrip(DatetimeFields {
            year: 2024,
            month: Month::January,
            day: 31,
            ..Default::default()
        });

        verify_unix_timestamp_roundtrip(DatetimeFields {
            year: 2024,
            month: Month::January,
            day: 1,
            ..Default::default()
        });

        verify_unix_timestamp_roundtrip(DatetimeFields {
            year: 2024,
            month: Month::February,
            day: 1,
            ..Default::default()
        });

        verify_unix_timestamp_roundtrip(DatetimeFields {
            year: 2024,
            month: Month::October,
            day: 4,
            hour: 16,
            ..Default::default()
        });

        verify_unix_timestamp_roundtrip(DatetimeFields {
            year: 2024,
            month: Month::December,
            day: 31,
            ..Default::default()
        });
    }

    #[test]
    fn test_datetime_bounds() {
        // Years
        assert_eq!(
            Datetime::new(DatetimeFields {
                year: 1969,
                month: Month::January,
                day: 1,
                ..Default::default()
            }),
            Err(DatetimeError::Year)
        );

        // Leap year stuff
        assert_eq!(
            Datetime::new(DatetimeFields {
                year: 2100,
                month: Month::February,
                day: 29,
                ..Default::default()
            }),
            Err(DatetimeError::Day)
        );

        assert_eq!(
            Datetime::new(DatetimeFields {
                year: 2015,
                month: Month::February,
                day: 29,
                ..Default::default()
            }),
            Err(DatetimeError::Day)
        );

        if let Err(_) = Datetime::new(DatetimeFields {
            year: 2000,
            month: Month::February,
            day: 29,
            ..Default::default()
        }) {
            assert!(false, "2000-02-29 should be a valid date");
        }

        if let Err(_) = Datetime::new(DatetimeFields {
            year: 2004,
            month: Month::February,
            day: 29,
            ..Default::default()
        }) {
            assert!(false, "2004-02-29 should be a valid date");
        }

        // Normal Days
        assert_eq!(
            Datetime::new(DatetimeFields {
                year: 2025,
                month: Month::January,
                day: 0,
                ..Default::default()
            }),
            Err(DatetimeError::Day)
        );

        assert_eq!(
            Datetime::new(DatetimeFields {
                year: 2025,
                month: Month::January,
                day: 32,
                ..Default::default()
            }),
            Err(DatetimeError::Day)
        );

        assert_eq!(
            Datetime::new(DatetimeFields {
                year: 2025,
                month: Month::December,
                day: 32,
                ..Default::default()
            }),
            Err(DatetimeError::Day)
        );

        assert_eq!(
            Datetime::new(DatetimeFields {
                year: 2025,
                month: Month::September,
                day: 31,
                ..Default::default()
            }),
            Err(DatetimeError::Day)
        );

        // Hours
        assert_eq!(
            Datetime::new(DatetimeFields {
                year: 2025,
                month: Month::January,
                day: 1,
                hour: 24,
                ..Default::default()
            }),
            Err(DatetimeError::Hour)
        );

        if let Err(_) = Datetime::new(DatetimeFields {
            year: 2025,
            month: Month::January,
            day: 1,
            hour: 23,
            ..Default::default()
        }) {
            assert!(false, "23 should be a valid hour");
        }

        if let Err(_) = Datetime::new(DatetimeFields {
            year: 2025,
            month: Month::January,
            day: 1,
            hour: 0,
            ..Default::default()
        }) {
            assert!(false, "23 should be a valid hour");
        }

        // Minutes
        assert_eq!(
            Datetime::new(DatetimeFields {
                year: 2025,
                month: Month::January,
                day: 1,
                hour: 0,
                minute: 60,
                ..Default::default()
            }),
            Err(DatetimeError::Minute)
        );

        if let Err(_) = Datetime::new(DatetimeFields {
            year: 2025,
            month: Month::January,
            day: 1,
            hour: 0,
            minute: 59,
            ..Default::default()
        }) {
            assert!(false, "59 should be a valid minute");
        }

        // Seconds
        assert_eq!(
            Datetime::new(DatetimeFields {
                year: 2025,
                month: Month::January,
                day: 1,
                hour: 0,
                minute: 59,
                second: 60,
                ..Default::default()
            }),
            Err(DatetimeError::Second)
        );

        // This is an actual leap second, but we don't support leap seconds in the Datetime type.
        assert_eq!(
            Datetime::new(DatetimeFields {
                year: 2016,
                month: Month::December,
                day: 31,
                hour: 23,
                minute: 59,
                second: 60,
                ..Default::default()
            }),
            Err(DatetimeError::Second)
        );

        if let Err(_) = Datetime::new(DatetimeFields {
            year: 2025,
            month: Month::January,
            day: 1,
            hour: 0,
            minute: 59,
            second: 59,
            ..Default::default()
        }) {
            assert!(false, "59 should be a valid second");
        }

        // Nanoseconds
        if let Err(_) = Datetime::new(DatetimeFields {
            year: 2025,
            month: Month::January,
            day: 1,
            hour: 0,
            minute: 59,
            second: 59,
            nanosecond: 999_999_999,
        }) {
            assert!(false, "999_999_999 should be a valid second");
        }

        assert_eq!(
            Datetime::new(DatetimeFields {
                year: 2025,
                month: Month::January,
                day: 1,
                hour: 0,
                minute: 59,
                second: 59,
                nanosecond: 1_000_000_000,
            }),
            Err(DatetimeError::Nanosecond)
        );

        // This is how chrono represents leap seconds.  This was an actual leap second, but we don't support leap seconds in the Datetime type.
        assert_eq!(
            Datetime::new(DatetimeFields {
                year: 2016,
                month: Month::December,
                day: 31,
                hour: 23,
                minute: 59,
                second: 59,
                nanosecond: 1_999_999_999,
            }),
            Err(DatetimeError::Nanosecond)
        );
    }

    #[test]
    fn test_unix_time_conversion() {
        let dt = Datetime::from_unix_timestamp(0);
        assert_eq!(dt.year(), 1970);
        assert_eq!(dt.month(), Month::January);
        assert_eq!(dt.day(), 1);
        assert_eq!(dt.hour(), 0);
        assert_eq!(dt.minute(), 0);
        assert_eq!(dt.second(), 0);
        assert_eq!(dt.nanoseconds(), 0);

        let dt = Datetime::from_unix_timestamp(86400); // 1 day later
        assert_eq!(dt.year(), 1970);
        assert_eq!(dt.month(), Month::January);
        assert_eq!(dt.day(), 2);
        assert_eq!(dt.hour(), 0);
        assert_eq!(dt.minute(), 0);
        assert_eq!(dt.second(), 0);
        assert_eq!(dt.nanoseconds(), 0);
    }

    // ── Month::days_in_month() ──

    #[test]
    fn month_days_in_non_leap_year() {
        let year = 2025; // not a leap year
        assert_eq!(Month::January.days_in_month(year), 31);
        assert_eq!(Month::February.days_in_month(year), 28);
        assert_eq!(Month::March.days_in_month(year), 31);
        assert_eq!(Month::April.days_in_month(year), 30);
        assert_eq!(Month::May.days_in_month(year), 31);
        assert_eq!(Month::June.days_in_month(year), 30);
        assert_eq!(Month::July.days_in_month(year), 31);
        assert_eq!(Month::August.days_in_month(year), 31);
        assert_eq!(Month::September.days_in_month(year), 30);
        assert_eq!(Month::October.days_in_month(year), 31);
        assert_eq!(Month::November.days_in_month(year), 30);
        assert_eq!(Month::December.days_in_month(year), 31);
    }

    #[test]
    fn february_has_29_days_in_leap_year() {
        assert_eq!(Month::February.days_in_month(2024), 29); // divisible by 4, not by 100
        assert_eq!(Month::February.days_in_month(2000), 29); // divisible by 400
    }

    #[test]
    fn february_has_28_days_when_not_leap_year() {
        assert_eq!(Month::February.days_in_month(2025), 28); // not divisible by 4
        assert_eq!(Month::February.days_in_month(1900), 28); // divisible by 100, not 400
        assert_eq!(Month::February.days_in_month(2100), 28); // divisible by 100, not 400
    }

    // ── Month::next() ──

    #[test]
    fn month_next_produces_full_calendar_sequence() {
        let expected = [
            Month::January,
            Month::February,
            Month::March,
            Month::April,
            Month::May,
            Month::June,
            Month::July,
            Month::August,
            Month::September,
            Month::October,
            Month::November,
            Month::December,
        ];
        for i in 0..12 {
            assert_eq!(expected[i].next(), expected[(i + 1) % 12]);
        }
    }

    // ── is_leap_year() century rule ──

    #[test]
    fn leap_year_century_rule() {
        assert!(is_leap_year(2024)); // divisible by 4, not by 100
        assert!(is_leap_year(2000)); // divisible by 400
        assert!(!is_leap_year(2025)); // not divisible by 4
        assert!(!is_leap_year(1900)); // divisible by 100, not 400
        assert!(!is_leap_year(2100)); // divisible by 100, not 400
    }

    // ── DatetimeFields::default() ──

    #[test]
    fn datetime_fields_default_is_unix_epoch() {
        let fields = DatetimeFields::default();
        assert_eq!(fields.year, 1970);
        assert_eq!(fields.month, Month::January);
        assert_eq!(fields.day, 1);
        assert_eq!(fields.hour, 0);
        assert_eq!(fields.minute, 0);
        assert_eq!(fields.second, 0);
        assert_eq!(fields.nanosecond, 0);
    }

    #[cfg(feature = "chrono")]
    mod chrono_test {
        use super::*;
        use chrono::{NaiveDate, NaiveDateTime};

        #[test]
        fn test_detailed_chrono_conversion() {
            let dt = Datetime::new(DatetimeFields {
                year: 2023,
                month: Month::October,
                day: 4,
                hour: 16,
                minute: 30,
                second: 45,
                nanosecond: 123_456_789,
            })
            .expect("Datetime should be valid");

            let chrono_dt: NaiveDateTime = dt.into();
            assert_eq!(
                chrono_dt,
                NaiveDate::from_ymd_opt(2023, 10, 4)
                    .expect("Should be a valid NaiveDate")
                    .and_hms_nano_opt(16, 30, 45, 123_456_789)
                    .expect("Should be a valid NaiveTime")
            );

            let dt_from_chrono = Datetime::try_from(chrono_dt).expect("Should convert back to Datetime");
            assert_eq!(dt, dt_from_chrono);
        }

        #[test]
        fn test_leap_seconds() {
            let chrono_leap_dt: NaiveDateTime = NaiveDate::from_ymd_opt(2016, 12, 31)
                    .expect("Should be a valid NaiveDate")
                    .and_hms_nano_opt(23, 59, 59, 1_999_999_999)
                    .expect("NaiveDateTime has partial support for leap seconds - this should be a valid NaiveTime, but not a valid Datetime. Truncation is expected in conversion.");

            let dt_from_chrono_leap = Datetime::try_from(chrono_leap_dt);
            assert_eq!(
                dt_from_chrono_leap,
                Datetime::new(DatetimeFields {
                    year: 2016,
                    month: Month::December,
                    day: 31,
                    hour: 23,
                    minute: 59,
                    second: 59,
                    nanosecond: 999_999_999, // We expect that the 'overflow nanoseconds' from the leap second have been truncated in the conversion.
                })
            );
        }

        #[test]
        fn test_bounds() {
            let chrono_early_dt: NaiveDateTime = NaiveDate::from_ymd_opt(1969, 12, 31)
                .expect("Should be a valid NaiveDate")
                .and_hms_nano_opt(23, 59, 59, 999_999_999)
                .expect("Should be a valid NaiveTime");

            assert_eq!(Datetime::try_from(chrono_early_dt), Err(DatetimeError::Year));

            let chrono_start_dt: NaiveDateTime = NaiveDate::from_ymd_opt(1970, 1, 1)
                .expect("Should be a valid NaiveDate")
                .and_hms_opt(0, 0, 0)
                .expect("Should be a valid NaiveTime");

            assert_eq!(
                Datetime::try_from(chrono_start_dt),
                Ok(Datetime::from_unix_timestamp(0))
            );
        }

        #[test]
        fn test_many_days() {
            const SECONDS_IN_DAY: u64 = 24 * 60 * 60;
            let mut chrono_dt = NaiveDate::from_ymd_opt(1970, 1, 1)
                .expect("Should be a valid NaiveDate")
                .and_hms_nano_opt(0, 0, 0, 0)
                .expect("Should be a valid NaiveTime");

            let mut native_dt = Datetime::from_unix_timestamp(0);

            // ~200 years of days, not accounting for leap years
            for _ in 0..(365 * 200) {
                let native_dt_as_chrono: NaiveDateTime = native_dt.into();
                assert_eq!(native_dt_as_chrono, chrono_dt, "Datetime to Chrono conversion failed");

                let chrono_dt_as_native = Datetime::try_from(chrono_dt).expect("Chrono to Datetime conversion failed");
                assert_eq!(chrono_dt_as_native, native_dt, "Chrono to Datetime conversion failed");

                chrono_dt += core::time::Duration::new(SECONDS_IN_DAY, 0);
                native_dt = Datetime::from_unix_timestamp(native_dt.unix_timestamp() + SECONDS_IN_DAY as u64);
            }
        }
    }
}
