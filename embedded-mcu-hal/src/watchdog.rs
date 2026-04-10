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

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used, clippy::expect_used)]

    use super::*;
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::{Arc, Mutex};
    use std::time::{Duration, Instant};
    use tokio::time::sleep;

    /// A software mock of a hardware watchdog, for use in tests only.
    ///
    /// Call [`spawn_monitor`] after construction to start the background task
    /// that enforces the timeout.  Feed the watchdog by calling [`feed`] before
    /// the timeout elapses.  Once the timeout fires the [`has_expired`] flag is
    /// set and the monitor task exits.
    ///
    /// [`spawn_monitor`]: MockWatchdog::spawn_monitor
    /// [`has_expired`]: MockWatchdog::has_expired
    /// [`feed`]: Watchdog::feed
    struct MockWatchdog {
        last_fed: Arc<Mutex<Instant>>,
        timeout: Duration,
        expired: Arc<AtomicBool>,
    }

    impl MockWatchdog {
        fn new(timeout: Duration) -> Self {
            Self {
                last_fed: Arc::new(Mutex::new(Instant::now())),
                timeout,
                expired: Arc::new(AtomicBool::new(false)),
            }
        }

        /// Spawns a background task that sets the [`has_expired`] flag if the
        /// watchdog is not fed within the configured timeout.  The task exits
        /// after setting the flag; abort the handle to stop an unexpired monitor.
        ///
        /// [`has_expired`]: MockWatchdog::has_expired
        fn spawn_monitor(&self) -> tokio::task::JoinHandle<()> {
            let last_fed = Arc::clone(&self.last_fed);
            let expired = Arc::clone(&self.expired);
            let timeout = self.timeout;
            let check_interval = timeout / 10;
            tokio::spawn(async move {
                loop {
                    sleep(check_interval).await;
                    if last_fed.lock().unwrap().elapsed() >= timeout {
                        expired.store(true, Ordering::Release);
                        return;
                    }
                }
            })
        }

        fn has_expired(&self) -> bool {
            self.expired.load(Ordering::Acquire)
        }
    }

    impl Watchdog for MockWatchdog {
        type Error = core::convert::Infallible;

        fn feed(&mut self) -> Result<(), Self::Error> {
            *self.last_fed.lock().unwrap() = Instant::now();
            Ok(())
        }
    }

    /// Verify the watchdog does not expire when fed regularly within the
    /// timeout window.
    #[tokio::test]
    async fn watchdog_does_not_expire_when_fed_regularly() {
        let mut watchdog = MockWatchdog::new(Duration::from_millis(100));
        let monitor = watchdog.spawn_monitor();

        // Feed every 40 ms — well within the 100 ms timeout.
        for _ in 0..10 {
            sleep(Duration::from_millis(40)).await;
            let feed_result = watchdog.feed();
            assert!(feed_result.is_ok());
        }

        monitor.abort();
        let res = monitor.await;

        // Aborted tasks return an error from `await`.
        assert!(res.is_err());

        // Verify the error is from an abort, not a panic.
        assert!(res.unwrap_err().is_cancelled());

        // Verify the watchdog did not expire.
        assert!(!watchdog.has_expired());
    }

    /// Verify the watchdog sets the expired flag when never fed.
    #[tokio::test]
    async fn watchdog_expires_when_not_fed() {
        let watchdog = MockWatchdog::new(Duration::from_millis(100));
        let monitor = watchdog.spawn_monitor();

        // Wait well beyond the timeout without feeding.
        sleep(Duration::from_millis(300)).await;

        let join_result = monitor.await;
        assert!(join_result.is_ok());
        assert!(watchdog.has_expired());
    }
}
