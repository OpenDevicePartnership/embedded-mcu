//! Rudimentary date/time object.

#[cfg(feature = "chrono")]
use chrono::{Datelike, Timelike};

/// Represents a date and time without validation.
/// This struct is used to make it easier to construct a validated datetime.
#[cfg_attr(all(feature = "defmt", not(test)), derive(defmt::Format))]
#[derive(PartialEq, Debug, Copy, Clone)]
pub struct UncheckedDatetime {
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

#[cfg_attr(all(feature = "defmt", not(test)), derive(defmt::Format))]
#[derive(num_enum::IntoPrimitive, num_enum::TryFromPrimitive, Copy, Clone, Debug, PartialEq)]
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
    pub const fn get_days_in_month(&self, year: u16) -> u8 {
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

    pub const fn next_month(&self) -> Month {
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
        return (*self as u8) == (*other as u8);
    }
}

/// Check if a year is a leap year.
const fn is_leap_year(year: u16) -> bool {
    (year % 4 == 0 && year % 100 != 0) || (year % 400 == 0)
}

#[cfg_attr(all(feature = "defmt", not(test)), derive(defmt::Format))]
#[derive(PartialEq, Debug)]
/// Represents errors that can occur when constructing a Datetime.
pub enum DatetimeError {
    /// The year is invalid.
    Year,
    /// The day is invalid.
    Day,
    /// The month is invalid.
    Month,
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
impl Default for UncheckedDatetime {
    fn default() -> Self {
        UncheckedDatetime {
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

/// Represents a date and time.
/// Does not support leap seconds.
#[cfg_attr(all(feature = "defmt", not(test)), derive(defmt::Format))]
#[derive(PartialEq, Debug, Default, Copy, Clone)]
pub struct Datetime {
    data: UncheckedDatetime,
}

impl Datetime {
    /// Convert a datetime to seconds since 1970-01-01 00:00:00, ignoring leap seconds.
    pub const fn to_unix_time_seconds(&self) -> u64 {
        let mut days: u64 = 0;

        // Calculate days from full years from 1970 to the current year
        {
            let mut year = 1970;
            while year < self.data.year {
                days += 365;
                if is_leap_year(year) {
                    days += 1;
                }

                year += 1;
            }
        }

        // Calculate days from January to the current month
        {
            let mut month = Month::January;
            while !month.eq(&self.data.month) {
                days += month.get_days_in_month(self.data.year) as u64;
                month = month.next_month();
            }
        }

        // Calculate days from the first day of the month to the current day
        days += self.data.day as u64 - 1;

        // Calculate seconds from the first day of the month to the current day
        let secs = self.data.second as u64 + self.data.minute as u64 * 60 + self.data.hour as u64 * 3600;

        days * 86400 + secs
    }

    /// Convert seconds since 1970-01-01 00:00:00 (ignoring leap seconds) to a datetime.
    pub const fn from_unix_time_seconds(secs: u64) -> Datetime {
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
                let current_month_days = month.get_days_in_month(year) as u64;
                if days < current_month_days {
                    break;
                }

                days -= current_month_days;
                month = month.next_month();
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
            data: UncheckedDatetime {
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

    /// Creates a `Datetime` from the given time components.
    pub const fn new(data: UncheckedDatetime) -> Result<Datetime, DatetimeError> {
        if data.year < 1970 {
            return Err(DatetimeError::Year);
        }

        if data.day < 1 {
            return Err(DatetimeError::Day);
        }

        if data.day > data.month.get_days_in_month(data.year) {
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

    /// Returns the year component of the date.
    pub const fn year(&self) -> u16 {
        self.data.year
    }
    /// Returns the month component of the date (1-12).
    pub const fn month(&self) -> Month {
        self.data.month
    }
    /// Returns the day component of the date (1-31).
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
    /// Returns the nanosecond component of the time (0-999_999_999).
    /// Many clock implementations do not support nanosecond resolution, so it's likely that this will be rounded
    /// or dropped entirely depending on your HAL implementation.  Check e.g. DatetimeClock::MAX_RESOLUTION_HZ
    /// to see what the maximum resolution is.
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
            data: UncheckedDatetime {
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
        // of the invariants that chrono::NaiveDateTime does.  Specifically, chrono::NaviveDateTime
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

    fn verify_unix_timestamp_roundtrip(data: UncheckedDatetime) {
        let dt = Datetime::new(data).expect("Datetime should be valid");
        let secs = dt.to_unix_time_seconds();
        let dt2 = Datetime::from_unix_time_seconds(secs);
        assert_eq!(dt, dt2, "Datetime roundtrip failed for {:?}", data);
    }

    proptest! {
        #[test]
        fn valid_seconds_always_work(secs in 0u64..=2005949145599) {
            let dt = Datetime::from_unix_time_seconds(secs);
            let secs2 = dt.to_unix_time_seconds();
            prop_assert_eq!(secs, secs2, "Datetime roundtrip failed");
        }

        #[test]
        fn valid_years_always_work(year in 1970u16..=65535) {
            let data = UncheckedDatetime {
                year, ..Default::default()
            };
            let dt = Datetime::new(data).expect("Datetime should be valid");
            let secs = dt.to_unix_time_seconds();
            let dt2 = Datetime::from_unix_time_seconds(secs);
            prop_assert_eq!(dt, dt2, "Datetime roundtrip failed for {:?}", data);
        }

        #[test]
        fn valid_months_always_work(month in 1u8..=12) {
            let data = UncheckedDatetime {
                month: month.try_into().unwrap(), ..Default::default()
            };
            let dt = Datetime::new(data).expect("Datetime should be valid");
            let secs = dt.to_unix_time_seconds();
            let dt2 = Datetime::from_unix_time_seconds(secs);
            prop_assert_eq!(dt, dt2, "Datetime roundtrip failed for {:?}", data);
        }

        #[test]
        fn valid_days_always_work(day in 1u8..=31) {
            let data = UncheckedDatetime {
                day, ..Default::default()
            };
            let dt = Datetime::new(data).expect("Datetime should be valid");
            let secs = dt.to_unix_time_seconds();
            let dt2 = Datetime::from_unix_time_seconds(secs);
            prop_assert_eq!(dt, dt2, "Datetime roundtrip failed for {:?}", data);
        }

        #[test]
        fn valid_hours_always_work(hour in 0u8..=23) {
            let data = UncheckedDatetime {
                hour, ..Default::default()
            };
            let dt = Datetime::new(data).expect("Datetime should be valid");
            let secs = dt.to_unix_time_seconds();
            let dt2 = Datetime::from_unix_time_seconds(secs);
            prop_assert_eq!(dt, dt2, "Datetime roundtrip failed for {:?}", data);
        }

        #[test]
        fn valid_minutes_always_work(minute in 0u8..=59) {
            let data = UncheckedDatetime {
                minute, ..Default::default()
            };
            let dt = Datetime::new(data).expect("Datetime should be valid");
            let secs = dt.to_unix_time_seconds();
            let dt2 = Datetime::from_unix_time_seconds(secs);
            prop_assert_eq!(dt, dt2, "Datetime roundtrip failed for {:?}", data);
        }

        #[test]
        fn all_leap_years_have_29_days_in_february(year in (1970u16..=65535).
                                                   prop_filter("Leap years", |y| is_leap_year(*y) )) {
            let data = UncheckedDatetime {
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
                let days_in_month = month.get_days_in_month(year);
                for day in 1..=days_in_month as u8 {
                    verify_unix_timestamp_roundtrip(UncheckedDatetime {
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
        verify_unix_timestamp_roundtrip(UncheckedDatetime {
            year: 1979,
            month: Month::January,
            day: 1,
            ..Default::default()
        });

        verify_unix_timestamp_roundtrip(UncheckedDatetime {
            year: 2023,
            month: Month::October,
            day: 4,
            hour: 16,
            ..Default::default()
        });

        verify_unix_timestamp_roundtrip(UncheckedDatetime {
            year: 2024,
            month: Month::March,
            day: 2,
            ..Default::default()
        });

        verify_unix_timestamp_roundtrip(UncheckedDatetime {
            year: 2024,
            month: Month::March,
            day: 1,
            ..Default::default()
        });

        verify_unix_timestamp_roundtrip(UncheckedDatetime {
            year: 2024,
            month: Month::February,
            day: 29,
            ..Default::default()
        });

        verify_unix_timestamp_roundtrip(UncheckedDatetime {
            year: 2024,
            month: Month::February,
            day: 28,
            ..Default::default()
        });

        verify_unix_timestamp_roundtrip(UncheckedDatetime {
            year: 2024,
            month: Month::January,
            day: 31,
            ..Default::default()
        });

        verify_unix_timestamp_roundtrip(UncheckedDatetime {
            year: 2024,
            month: Month::January,
            day: 1,
            ..Default::default()
        });

        verify_unix_timestamp_roundtrip(UncheckedDatetime {
            year: 2024,
            month: Month::February,
            day: 1,
            ..Default::default()
        });

        verify_unix_timestamp_roundtrip(UncheckedDatetime {
            year: 2024,
            month: Month::October,
            day: 4,
            hour: 16,
            ..Default::default()
        });

        verify_unix_timestamp_roundtrip(UncheckedDatetime {
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
            Datetime::new(UncheckedDatetime {
                year: 1969,
                month: Month::January,
                day: 1,
                ..Default::default()
            }),
            Err(DatetimeError::Year)
        );

        // Leap year stuff
        assert_eq!(
            Datetime::new(UncheckedDatetime {
                year: 2100,
                month: Month::February,
                day: 29,
                ..Default::default()
            }),
            Err(DatetimeError::Day)
        );

        assert_eq!(
            Datetime::new(UncheckedDatetime {
                year: 2015,
                month: Month::February,
                day: 29,
                ..Default::default()
            }),
            Err(DatetimeError::Day)
        );

        if let Err(_) = Datetime::new(UncheckedDatetime {
            year: 2000,
            month: Month::February,
            day: 29,
            ..Default::default()
        }) {
            assert!(false, "2000-02-29 should be a valid date");
        }

        if let Err(_) = Datetime::new(UncheckedDatetime {
            year: 2004,
            month: Month::February,
            day: 29,
            ..Default::default()
        }) {
            assert!(false, "2004-02-29 should be a valid date");
        }

        // Normal Days
        assert_eq!(
            Datetime::new(UncheckedDatetime {
                year: 2025,
                month: Month::January,
                day: 0,
                ..Default::default()
            }),
            Err(DatetimeError::Day)
        );

        assert_eq!(
            Datetime::new(UncheckedDatetime {
                year: 2025,
                month: Month::January,
                day: 32,
                ..Default::default()
            }),
            Err(DatetimeError::Day)
        );

        assert_eq!(
            Datetime::new(UncheckedDatetime {
                year: 2025,
                month: Month::December,
                day: 32,
                ..Default::default()
            }),
            Err(DatetimeError::Day)
        );

        assert_eq!(
            Datetime::new(UncheckedDatetime {
                year: 2025,
                month: Month::September,
                day: 31,
                ..Default::default()
            }),
            Err(DatetimeError::Day)
        );

        // Hours
        assert_eq!(
            Datetime::new(UncheckedDatetime {
                year: 2025,
                month: Month::January,
                day: 1,
                hour: 24,
                ..Default::default()
            }),
            Err(DatetimeError::Hour)
        );

        if let Err(_) = Datetime::new(UncheckedDatetime {
            year: 2025,
            month: Month::January,
            day: 1,
            hour: 23,
            ..Default::default()
        }) {
            assert!(false, "23 should be a valid hour");
        }

        if let Err(_) = Datetime::new(UncheckedDatetime {
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
            Datetime::new(UncheckedDatetime {
                year: 2025,
                month: Month::January,
                day: 1,
                hour: 0,
                minute: 60,
                ..Default::default()
            }),
            Err(DatetimeError::Minute)
        );

        if let Err(_) = Datetime::new(UncheckedDatetime {
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
            Datetime::new(UncheckedDatetime {
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
            Datetime::new(UncheckedDatetime {
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

        if let Err(_) = Datetime::new(UncheckedDatetime {
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
        if let Err(_) = Datetime::new(UncheckedDatetime {
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
            Datetime::new(UncheckedDatetime {
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
            Datetime::new(UncheckedDatetime {
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
        let dt = Datetime::from_unix_time_seconds(0);
        assert_eq!(dt.year(), 1970);
        assert_eq!(dt.month(), Month::January);
        assert_eq!(dt.day(), 1);
        assert_eq!(dt.hour(), 0);
        assert_eq!(dt.minute(), 0);
        assert_eq!(dt.second(), 0);
        assert_eq!(dt.nanoseconds(), 0);

        let dt = Datetime::from_unix_time_seconds(86400); // 1 day later
        assert_eq!(dt.year(), 1970);
        assert_eq!(dt.month(), Month::January);
        assert_eq!(dt.day(), 2);
        assert_eq!(dt.hour(), 0);
        assert_eq!(dt.minute(), 0);
        assert_eq!(dt.second(), 0);
        assert_eq!(dt.nanoseconds(), 0);
    }

    #[cfg(feature = "chrono")]
    mod chrono_test {
        use super::*;
        use chrono::{NaiveDate, NaiveDateTime};

        #[test]
        fn test_detailed_chrono_conversion() {
            let dt = Datetime::new(UncheckedDatetime {
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
                Datetime::new(UncheckedDatetime {
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
                Ok(Datetime::from_unix_time_seconds(0))
            );
        }

        #[test]
        fn test_many_days() {
            const SECONDS_IN_DAY: u64 = 24 * 60 * 60;
            let mut chrono_dt = NaiveDate::from_ymd_opt(1970, 1, 1)
                .expect("Should be a valid NaiveDate")
                .and_hms_nano_opt(0, 0, 0, 0)
                .expect("Should be a valid NaiveTime");

            let mut native_dt = Datetime::from_unix_time_seconds(0);

            // ~200 years of days, not accounting for leap years
            for _ in 0..(365 * 200) {
                let native_dt_as_chrono: NaiveDateTime = native_dt.into();
                assert_eq!(native_dt_as_chrono, chrono_dt, "Datetime to Chrono conversion failed");

                let chrono_dt_as_native = Datetime::try_from(chrono_dt).expect("Chrono to Datetime conversion failed");
                assert_eq!(chrono_dt_as_native, native_dt, "Chrono to Datetime conversion failed");

                chrono_dt += core::time::Duration::new(SECONDS_IN_DAY, 0);
                native_dt = Datetime::from_unix_time_seconds(native_dt.to_unix_time_seconds() + SECONDS_IN_DAY as u64);
            }
        }
    }
}
