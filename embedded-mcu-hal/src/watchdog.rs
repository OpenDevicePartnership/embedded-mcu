//! Traits for interactions with a processor's watchdog timer.

/// Feeds an existing watchdog to ensure the processor isn't reset.
pub trait Watchdog {
    /// An enumeration of `Watchdog` errors.
    ///
    type Error: core::fmt::Debug;

    /// Restarts the countdown on the watchdog. This must be done once the watchdog is started
    /// to prevent the processor being reset.
    ///
    fn feed(&mut self) -> Result<(), Self::Error>;
}
