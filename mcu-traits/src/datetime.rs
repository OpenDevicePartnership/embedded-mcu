//! Rudimentary date/time object.

/// Represents a date and time without validation.
/// This struct is used to make it easier to construct a validated datetime.
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
#[derive(PartialEq, Debug, Copy, Clone)]
pub struct UncheckedDatetime {
    /// The year component of the date.
    pub year: u16,
    /// The month component of the date (1-12).
    pub month: u8,
    /// The day component of the date (1-31).
    pub day: u8,
    /// The hour component of the time (0-23).
    pub hour: u8,
    /// The minute component of the time (0-59).
    pub minute: u8,
    /// The second component of the time (0-59).
    pub second: u8,
}

#[cfg_attr(feature = "defmt", derive(defmt::Format))]
#[derive(PartialEq, Debug)]
/// Represents errors that can occur when constructing a Datetime.
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
}

/// Default implementation for `Datetime`.
impl Default for UncheckedDatetime {
    fn default() -> Self {
        UncheckedDatetime {
            year: 1970,
            month: 1,
            day: 1,
            hour: 0,
            minute: 0,
            second: 0,
        }
    }
}

/// Represents a date and time.
/// Does not support leap seconds.
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
#[derive(PartialEq, Debug, Default)]
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
                if Self::is_leap_year(year) {
                    days += 1;
                }

                year += 1;
            }
        }

        // Calculate days from January to the current month
        const DAYS_IN_MONTH: [u64; 12] = [0, 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30];
        {
            let mut month = 1;
            while month < self.data.month {
                days += DAYS_IN_MONTH[month as usize];
                if month == 2 && Self::is_leap_year(self.data.year) {
                    days += 1;
                }

                month += 1;
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
        let mut month = 1;
        let mut day = 1;

        // Calculate year
        while days >= 365 {
            if Self::is_leap_year(year) {
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
        let days_in_month = [0, 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30];
        while days >= days_in_month[month as usize] {
            if month == 2 && Self::is_leap_year(year) {
                if days >= 29 {
                    days -= 29;
                } else {
                    break;
                }
            } else {
                days -= days_in_month[month as usize];
            }
            month += 1;
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
            },
        }
    }

    /// Creates a `Datetime` from the given time components.
    pub const fn new(data: UncheckedDatetime) -> Result<Datetime, DatetimeError> {
        // Validate year
        if data.year < 1970 {
            return Err(DatetimeError::Year);
        }

        // Validate month
        if data.month < 1 || data.month > 12 {
            return Err(DatetimeError::Month);
        }

        // Validate day
        if data.day < 1 {
            return Err(DatetimeError::Day);
        }

        match data.month {
            1 | 3 | 5 | 7 | 8 | 10 | 12 => {
                if data.day > 31 {
                    return Err(DatetimeError::Day);
                }
            }
            4 | 6 | 9 | 11 => {
                if data.day > 30 {
                    return Err(DatetimeError::Day);
                }
            }
            2 => {
                if Self::is_leap_year(data.year) {
                    if data.day > 29 {
                        return Err(DatetimeError::Day);
                    }
                } else if data.day > 28 {
                    return Err(DatetimeError::Day);
                }
            }
            _ => return Err(DatetimeError::Day),
        }

        // Validate hour
        if data.hour > 23 {
            return Err(DatetimeError::Hour);
        }

        // Validate minute
        if data.minute > 59 {
            return Err(DatetimeError::Minute);
        }

        // Validate second
        if data.second > 59 {
            return Err(DatetimeError::Second);
        }

        Ok(Datetime { data })
    }

    /// Returns the year component of the date.
    pub const fn year(&self) -> u16 {
        self.data.year
    }
    /// Returns the month component of the date (1-12).
    pub const fn month(&self) -> u8 {
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

    /// Check if a year is a leap year.
    const fn is_leap_year(year: u16) -> bool {
        (year % 4 == 0 && year % 100 != 0) || (year % 400 == 0)
    }
}
