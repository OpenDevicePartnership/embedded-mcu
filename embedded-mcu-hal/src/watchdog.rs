//! Traits for interacting with a processor's hardware watchdog timer.
//!
//! A watchdog timer is a hardware counter that continuously counts down.  If
//! the counter reaches zero the processor is reset, which allows the system to
//! recover automatically from software hangs or unresponsive tasks.  To
//! prevent the reset, software must periodically *feed* (also called *kick* or
//! *pet*) the watchdog before the counter expires.
//!
//! # Scope
//!
//! This module covers only the *feeding* half of the watchdog lifecycle.
//! Starting the watchdog, configuring its timeout period, and any one-time
//! hardware setup are considered peripheral initialisation and are therefore
//! out of scope for this HAL (see the crate-level documentation).
//!
//! # Safety considerations
//!
//! * Feeding the watchdog too infrequently (or not at all) will reset the
//!   processor.
//! * On many MCUs a started watchdog **cannot be stopped**.  Ensure that the
//!   task or thread responsible for feeding it will always make forward
//!   progress.

/// Trait for feeding a hardware watchdog timer.
///
/// Implementations wrap a started watchdog peripheral and expose a single
/// [`feed`] method that restarts the hardware countdown.  The watchdog is
/// assumed to be already started and configured before an implementor of this
/// trait is constructed; this trait does not cover starting, stopping, or
/// reconfiguring the watchdog.
///
/// The trait is intentionally minimal: one method, one associated error type.
/// Higher-level abstractions (e.g. a periodic task that calls `feed` on a
/// fixed interval) can be built on top without coupling them to any specific
/// MCU.
///
/// [`feed`]: Watchdog::feed
pub trait Watchdog {
    /// The error type returned when a feed attempt fails.
    ///
    /// Hardware watchdog peripherals rarely fail to accept a feed operation,
    /// but this associated type exists so that implementations can surface
    /// errors from underlying register writes or bus transactions if needed.
    /// Implementations that can never fail may use
    /// [`core::convert::Infallible`] as this type.
    type Error: core::fmt::Debug;

    /// Restarts the watchdog countdown, preventing an imminent processor reset.
    ///
    /// This method must be called before the watchdog timer expires.  The
    /// required call frequency depends on the configured timeout period, which
    /// is established during hardware initialisation outside the scope of this
    /// trait.
    ///
    /// Returns `Ok(())` on success.  Returns `Err(Self::Error)` if the
    /// underlying hardware indicates a failure (e.g. a bus error during the
    /// register write).
    fn feed(&mut self) -> Result<(), Self::Error>;
}
