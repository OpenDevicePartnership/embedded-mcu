//! Traits for NVRAM (Non-Volatile Random Access Memory) peripherals.
//!
//! NVRAM is persistent storage that retains its contents across power cycles.
//! Common hardware implementations include battery-backed SRAM and dedicated
//! non-volatile register banks found on many MCUs.
//!
//! # Design
//!
//! Storage is modelled at two levels of abstraction:
//!
//! * [`NvramStorage`] — a single, individually-addressable storage cell
//!   holding one value of type `T`.
//! * [`Nvram`] — a fixed-size array of [`NvramStorage`] cells, keyed by a
//!   const `CELL_COUNT`.
//!
//! This separation lets callers hold typed references to individual cells
//! without carrying a reference to the parent peripheral, while still letting
//! the peripheral implementation enforce the hardware's addressing rules.
//!
//! # Initialisation pattern
//!
//! The recommended initialisation sequence is:
//!
//! 1. Call [`Nvram::storage`] once to obtain the cell array.
//! 2. Keep the cell references for the lifetime of the application; the
//!    borrow prevents the peripheral from being reconfigured underneath you.
//!
//! [`Nvram::dump_storage`] is available at any time for integrity validation
//! without consuming the `storage` borrow.

/// An individual NVRAM storage cell holding a single value of type `T`.
///
/// Each cell maps to one independently-readable and independently-writable
/// location in the underlying hardware.  The `'a` lifetime parameter ties
/// the cell reference to the lifetime of the parent [`Nvram`] peripheral,
/// preventing the hardware from being reconfigured while cells are in use.
pub trait NvramStorage<'a, T> {
    /// Reads and returns the current value of this storage cell.
    ///
    /// This operation is non-destructive; the stored value is unchanged after
    /// the read.
    fn read(&self) -> T;

    /// Writes `value` into this storage cell, replacing any previously stored value.
    fn write(&mut self, value: T);
}

/// A fixed-size collection of individually-addressable NVRAM storage cells.
///
/// The three type parameters describe the hardware layout:
///
/// * `StorageType` — the concrete [`NvramStorage`] implementation used for
///   each cell.
/// * `StoredType` — the value type held in each cell.  This is typically the
///   platform's natural word size (e.g. `u32` on a 32-bit MCU) because many
///   NVRAM peripherals are word-addressed.
/// * `CELL_COUNT` — the number of cells available, fixed at compile time.
///
/// [`storage`]: Nvram::storage
pub trait Nvram<'a, StorageType, StoredType, const CELL_COUNT: usize>
where
    StorageType: NvramStorage<'a, StoredType>,
    StoredType: Copy,
{
    /// Borrows the peripheral for its entire lifetime and returns a mutable
    /// reference to all `CELL_COUNT` storage cells.
    ///
    /// The exclusive lifetime borrow (`&'a mut self` returning `&'a mut …`)
    /// means the peripheral cannot be accessed through any other path while
    /// the cell array is live.  In practice this means `storage` should be
    /// called once during initialisation and the resulting reference kept for
    /// the lifetime of the application.
    fn storage(&'a mut self) -> &'a mut [StorageType; CELL_COUNT];

    /// Returns a snapshot of all storage cell values as a plain array.
    ///
    /// Unlike [`storage`], this method takes a shared reference and does not
    /// consume the lifetime borrow, so it can be called at any time — including
    /// after [`storage`] has already been called.  It is intended for integrity
    /// checks (e.g. verifying a checksum over the NVRAM contents) and should
    /// not be used as a substitute for accessing cells through [`storage`].
    ///
    /// [`storage`]: Nvram::storage
    fn dump_storage(&self) -> [StoredType; CELL_COUNT];

    /// Resets all storage cells to an implementation-defined cleared state.
    ///
    /// For numeric `StoredType`s such as `u32` the cleared state is typically
    /// zero, but implementations must document their specific clearing
    /// behaviour.
    ///
    /// This method requires `&mut self` and therefore cannot be called after
    /// [`storage`] has been called (since that borrow prevents further mutable
    /// access through `self`).
    fn clear_storage(&mut self);
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used, clippy::expect_used, clippy::indexing_slicing)]

    use super::*;

    // ── Mock implementations ──

    struct MockNvramStorage<T> {
        value: T,
    }

    impl<T: Copy + Default> MockNvramStorage<T> {
        fn new() -> Self {
            Self { value: T::default() }
        }
    }

    impl<'a, T: Copy> NvramStorage<'a, T> for MockNvramStorage<T> {
        fn read(&self) -> T {
            self.value
        }
        fn write(&mut self, value: T) {
            self.value = value;
        }
    }

    struct MockNvram<T, const N: usize> {
        cells: [MockNvramStorage<T>; N],
    }

    impl<T: Copy + Default, const N: usize> MockNvram<T, N> {
        fn new() -> Self {
            Self {
                cells: core::array::from_fn(|_| MockNvramStorage::new()),
            }
        }
    }

    impl<'a, T: Copy + Default, const N: usize> Nvram<'a, MockNvramStorage<T>, T, N> for MockNvram<T, N> {
        fn storage(&'a mut self) -> &'a mut [MockNvramStorage<T>; N] {
            &mut self.cells
        }

        fn dump_storage(&self) -> [T; N] {
            self.cells.each_ref().map(|c| c.value)
        }

        fn clear_storage(&mut self) {
            for cell in &mut self.cells {
                cell.value = T::default();
            }
        }
    }

    // ── NvramStorage tests ──

    #[test]
    fn storage_read_on_fresh_cell_returns_default() {
        let cell: MockNvramStorage<u32> = MockNvramStorage::new();
        assert_eq!(cell.read(), 0);
    }

    #[test]
    fn storage_write_then_read_returns_written_value() {
        let mut cell: MockNvramStorage<u32> = MockNvramStorage::new();
        cell.write(42);
        assert_eq!(cell.read(), 42);
    }

    #[test]
    fn storage_second_write_overwrites_first() {
        let mut cell: MockNvramStorage<u32> = MockNvramStorage::new();
        cell.write(1);
        cell.write(2);
        assert_eq!(cell.read(), 2);
    }

    // ── Nvram tests ──

    #[test]
    fn nvram_cells_are_independently_addressable() {
        let mut nvram: MockNvram<u32, 4> = MockNvram::new();
        let cells = nvram.storage();
        cells[0].write(10);
        cells[1].write(20);
        cells[2].write(30);
        cells[3].write(40);
        assert_eq!(cells[0].read(), 10);
        assert_eq!(cells[1].read(), 20);
        assert_eq!(cells[2].read(), 30);
        assert_eq!(cells[3].read(), 40);
    }

    #[test]
    fn nvram_writing_one_cell_does_not_affect_others() {
        let mut nvram: MockNvram<u32, 3> = MockNvram::new();
        let cells = nvram.storage();
        cells[1].write(99);
        assert_eq!(cells[0].read(), 0);
        assert_eq!(cells[2].read(), 0);
    }

    #[test]
    fn nvram_dump_storage_on_fresh_nvram_is_all_zeros() {
        let nvram: MockNvram<u32, 4> = MockNvram::new();
        assert_eq!(nvram.dump_storage(), [0u32; 4]);
    }

    #[test]
    fn nvram_dump_storage_reflects_values_written_via_storage() {
        let mut nvram: MockNvram<u32, 3> = MockNvram::new();
        let cells = nvram.storage();
        cells[0].write(1);
        cells[1].write(2);
        cells[2].write(3);
        assert_eq!(nvram.dump_storage(), [1, 2, 3]);
    }

    #[test]
    fn nvram_clear_storage_resets_all_cells_to_zero() {
        let mut nvram: MockNvram<u32, 3> = MockNvram::new();
        let cells = nvram.storage();
        cells[0].write(1);
        cells[1].write(2);
        cells[2].write(3);
        nvram.clear_storage();
        assert_eq!(nvram.dump_storage(), [0u32; 3]);
    }

    #[test]
    fn nvram_clear_storage_on_fresh_nvram_is_idempotent() {
        let mut nvram: MockNvram<u32, 2> = MockNvram::new();
        nvram.clear_storage();
        assert_eq!(nvram.dump_storage(), [0u32; 2]);
    }
}
