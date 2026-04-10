//! A Hardware Abstraction Layer (HAL) for embedded microcontrollers.
//!
//! > MCU-agnostic traits and types for embedded peripherals where
//! > embedded-hal leaves off.
//!
//! This crate complements
//! [`embedded-hal`](https://docs.rs/embedded-hal) by covering other
//! peripheral abstractions — such as real-time clocks, non-volatile
//! RAM, and watchdog timers.  Traits that gain sufficient community
//! alignment may be upstreamed to `embedded-hal` in the future.
//!
//! Concrete, MCU-specific implementations belong in separate board or chip
//! support crates; this crate only defines the contracts they must satisfy.
//!
//! # Design goals
//!
//! * **Device-agnostic** — no register addresses, magic values, or
//!   MCU-specific types appear in any public API.
//!
//! * **Trait-only** — the crate ships no runtime code beyond the
//!   [`time::Datetime`] value type and its helpers.  Keeping implementations
//!   out-of-crate means zero overhead: you only pay for what you use.
//!
//! * **`no_std` first** — every public item is usable in bare-metal firmware
//!   with no heap allocator.  The standard library is only linked during
//!   `cfg(test)`.
//!
//! * **Fallible by default** — all trait methods return `Result` so that
//!   generic drivers can handle hardware errors without panicking.
//!   Platform-specific crates may expose infallible wrappers on top when
//!   appropriate.
//!
//! # Out of scope
//!
//! * **Peripheral initialisation and pin configuration** — the HAL assumes the
//!   peripheral is already clocked, pinned, and enabled before a trait object
//!   is constructed.
//!
//! * **Low-level bus primitives** (SPI, I²C, UART, GPIO) — use
//!   [`embedded-hal`](https://docs.rs/embedded-hal) for those.
//!
//! # Modules
//!
//! | Module | What it covers |
//! |--------|----------------|
//! | [`time`] | Wall-clock date/time types and real-time clock (RTC) traits |
//! | [`nvram`] | Non-Volatile RAM storage traits |
//! | [`watchdog`] | Watchdog timer trait |
//!
//! # Optional Cargo features
//!
//! | Feature | Effect |
//! |---------|--------|
//! | `chrono` | Enables `TryFrom`/`Into` conversions between [`time::Datetime`] and `chrono::NaiveDateTime` |
//! | `defmt` | Derives `defmt::Format` on all public types for use with the [`defmt`](https://docs.rs/defmt) logging framework |
//!
//! # Minimum Supported Rust Version (MSRV)
//!
//! This crate requires **Rust 1.90** or newer.  It uses `u16::is_multiple_of`,
//! which was stabilised in that release.
//!
//! The MSRV may be increased in a minor version bump if a newly-stabilised
//! language or library feature significantly simplifies the implementation.
//!
//! # License
//!
//! Licensed under the [MIT license](https://opensource.org/licenses/MIT).

#![cfg_attr(not(test), no_std)]

pub mod nvram;
pub mod time;
pub mod watchdog;
