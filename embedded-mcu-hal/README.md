# embedded-mcu-hal

[![crates.io](https://img.shields.io/crates/v/embedded-mcu-hal.svg)](https://crates.io/crates/embedded-mcu-hal)
[![docs.rs](https://docs.rs/embedded-mcu-hal/badge.svg)](https://docs.rs/embedded-mcu-hal)
[![License: MIT](https://img.shields.io/badge/License-MIT-blue.svg)](https://opensource.org/licenses/MIT)
![Minimum Supported Rust Version](https://img.shields.io/badge/rustc-1.90+-blue.svg)

> MCU-agnostic traits for high-level embedded peripherals.

`embedded-mcu-hal` complements [`embedded-hal`](https://docs.rs/embedded-hal) by covering
higher-level peripheral abstractions that sit above raw bus and GPIO primitives — things like
real-time clocks, non-volatile RAM, and watchdog timers. It is part of the
[Open Device Partnership](https://github.com/OpenDevicePartnership/embedded-mcu) Embedded
Controller project.

Concrete, MCU-specific implementations belong in separate board or chip support crates.
This crate only defines the contracts they must satisfy.

## What's included

| Module | Traits | Description |
|--------|--------|-------------|
| `time` | `DatetimeClock` | Read and set wall-clock date/time on an RTC peripheral |
| `time` | — | `Datetime`, `UncheckedDatetime`, `Month` value types with Unix timestamp conversion |
| `nvram` | `Nvram`, `NvramStorage` | Access individually-addressable non-volatile RAM cells |
| `watchdog` | `Watchdog` | Feed a hardware watchdog timer to prevent processor reset |

## Design goals

- **Device-agnostic** — no register addresses or MCU-specific types in any public API.
- **Trait-only** — zero runtime overhead; you only pay for what you implement.
- **`no_std` first** — every item is usable in bare-metal firmware with no heap allocator.
- **Fallible by default** — all trait methods return `Result`, keeping generic drivers panic-free.

## Optional features

| Feature | Effect |
|---------|--------|
| `chrono` | `TryFrom<chrono::NaiveDateTime>` and `Into<chrono::NaiveDateTime>` for `Datetime` |
| `defmt` | Derives `defmt::Format` on all public types for use with the [`defmt`](https://docs.rs/defmt) logging framework |

## MSRV

Rust **1.90** or newer is required.

## License

Licensed under the [MIT license](https://opensource.org/licenses/MIT).
