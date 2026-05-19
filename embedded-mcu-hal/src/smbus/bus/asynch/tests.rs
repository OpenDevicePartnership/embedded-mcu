use super::Smbus;
use crate::smbus::bus::{
    read_address_byte, write_address_byte, Error as SmbusError, ErrorKind, MAX_BLOCK_SIZE, READ_BIT,
};
use core::hash::Hasher;
use embedded_hal_async::i2c::ErrorKind as I2cErrorKind;
use embedded_hal_mock::eh1::i2c::{Mock as I2cMock, Transaction as Tx};
use smbus_pec::{pec, Pec};

const ADDR: u8 = 0x42;
const REG: u8 = 0x07;

/// Compute the expected SMBus PEC byte over a flat concatenation of byte
/// slices, using the `smbus-pec` crate as the reference implementation.
fn expected_pec(parts: &[&[u8]]) -> u8 {
    let mut buf: std::vec::Vec<u8> = std::vec::Vec::new();
    for p in parts {
        buf.extend_from_slice(p);
    }
    pec(&buf)
}

/// PEC provider that exposes the `smbus-pec` calculator.
struct TestPec;
impl super::PecProvider for TestPec {
    type Calc = Pec;
    fn new_calc() -> Option<Self::Calc> {
        Some(Pec::new())
    }
}

/// PEC provider that reports PEC as unavailable.
struct NoPec;
impl super::PecProvider for NoPec {
    type Calc = Pec;
    fn new_calc() -> Option<Self::Calc> {
        None
    }
}

type TestBus = super::SwSmbusI2c<I2cMock, TestPec>;
type NoPecBus = super::SwSmbusI2c<I2cMock, NoPec>;

fn new_bus(expectations: &[Tx]) -> TestBus {
    super::SwSmbusI2c::new(I2cMock::new(expectations))
}

fn done(mut bus: TestBus) {
    bus.inner_mut().done();
}

// ---------- constants / helpers ----------

#[test]
fn constants() {
    assert_eq!(MAX_BLOCK_SIZE, 255);
    assert_eq!(READ_BIT, 0x01);
    assert_eq!(write_address_byte(0x42), 0x84);
    assert_eq!(read_address_byte(0x42), 0x85);
}

#[test]
fn error_kind_display_and_kind() {
    let k = ErrorKind::Timeout;
    assert_eq!(k.kind(), ErrorKind::Timeout);
    // Display impls cover all branches.
    for k in [
        ErrorKind::I2c(I2cErrorKind::Bus),
        ErrorKind::Timeout,
        ErrorKind::Pec,
        ErrorKind::TooLargeBlockTransaction,
        ErrorKind::BlockSizeMismatch(2, 3),
        ErrorKind::Other,
    ] {
        let s = std::format!("{}", k);
        assert!(!s.is_empty());
    }
    // The Display impl for `BlockSizeMismatch` must surface both the
    // received byte count and the caller's expected buffer length.
    let s = std::format!("{}", ErrorKind::BlockSizeMismatch(2, 5));
    assert!(s.contains('2'));
    assert!(s.contains('5'));
}

#[test]
fn error_kind_from_i2c_error_kind() {
    let k: ErrorKind = I2cErrorKind::Bus.into();
    assert_eq!(k, ErrorKind::I2c(I2cErrorKind::Bus));
}

#[test]
fn infallible_error_to_kind_round_trip() {
    // Infallible cannot be constructed; we only check the trait wires up.
    fn _accepts<E: SmbusError>(_e: &E) {}
    let k = ErrorKind::Pec;
    _accepts(&k);
}

#[tokio::test]
async fn check_pec_match() {
    let bus = new_bus(&[]);
    TestBus::check_pec(0x42, 0x42).unwrap();
    TestBus::check_pec(0x00, 0x00).unwrap();
    done(bus);
}

#[tokio::test]
async fn check_pec_mismatch() {
    let bus = new_bus(&[]);
    let err = TestBus::check_pec(0x42, 0x43).unwrap_err();
    assert_eq!(err.kind(), ErrorKind::Pec);
    done(bus);
}

// ---------- write_buf / read_buf (low-level) ----------

#[tokio::test]
async fn write_buf_no_pec() {
    let mut bus = new_bus(&[Tx::write(ADDR, std::vec![0xAB, 0xCD])]);
    bus.write_buf(ADDR, false, &mut [0xAB, 0xCD]).await.unwrap();
    done(bus);
}

#[tokio::test]
async fn write_buf_pec() {
    let payload = [0xAB, 0xCD];
    let pec = expected_pec(&[&[write_address_byte(ADDR)], &payload]);
    let mut buf = [0xAB, 0xCD, 0x00];
    let mut wire = std::vec![0xAB, 0xCD, pec];
    let mut bus = new_bus(&[Tx::write(ADDR, wire.clone())]);
    bus.write_buf(ADDR, true, &mut buf).await.unwrap();
    // Last byte should now be the PEC.
    assert_eq!(buf[2], pec);
    wire.clear();
    done(bus);
}

#[tokio::test]
async fn read_buf_no_pec() {
    let mut bus = new_bus(&[Tx::read(ADDR, std::vec![0x11, 0x22])]);
    let mut buf = [0u8; 2];
    bus.read_buf(ADDR, false, &mut buf).await.unwrap();
    assert_eq!(buf, [0x11, 0x22]);
    done(bus);
}

#[tokio::test]
async fn read_buf_pec() {
    let data = 0x11u8;
    let pec = expected_pec(&[&[read_address_byte(ADDR)], &[data]]);
    let mut bus = new_bus(&[Tx::read(ADDR, std::vec![data, pec])]);
    let mut buf = [0u8; 2];
    bus.read_buf(ADDR, true, &mut buf).await.unwrap();
    done(bus);
}

#[tokio::test]
async fn read_buf_pec_mismatch() {
    let mut bus = new_bus(&[Tx::read(ADDR, std::vec![0x11, 0xFF])]); // wrong PEC
    let mut buf = [0u8; 2];
    let err = bus.read_buf(ADDR, true, &mut buf).await.unwrap_err();
    assert_eq!(err.kind(), ErrorKind::Pec);
    done(bus);
}

// ---------- quick_command ----------

#[tokio::test]
async fn quick_command_write() {
    let mut bus = new_bus(&[
        Tx::transaction_start(ADDR),
        Tx::write(ADDR, std::vec![]),
        Tx::transaction_end(ADDR),
    ]);
    bus.quick_command(ADDR, false).await.unwrap();
    done(bus);
}

#[tokio::test]
async fn quick_command_read() {
    let mut bus = new_bus(&[
        Tx::transaction_start(ADDR),
        Tx::read(ADDR, std::vec![]),
        Tx::transaction_end(ADDR),
    ]);
    bus.quick_command(ADDR, true).await.unwrap();
    done(bus);
}

// ---------- send_byte / receive_byte ----------

#[tokio::test]
async fn send_byte_no_pec() {
    let mut bus = new_bus(&[Tx::write(ADDR, std::vec![0x55])]);
    bus.send_byte(ADDR, 0x55).await.unwrap();
    done(bus);
}

#[tokio::test]
async fn send_byte_pec() {
    let pec = expected_pec(&[&[write_address_byte(ADDR), 0x55]]);
    let mut bus = new_bus(&[Tx::write(ADDR, std::vec![0x55, pec])]);
    bus.send_byte_with_pec(ADDR, 0x55).await.unwrap();
    done(bus);
}

#[tokio::test]
async fn receive_byte_no_pec() {
    let mut bus = new_bus(&[Tx::read(ADDR, std::vec![0x99])]);
    let b = bus.receive_byte(ADDR).await.unwrap();
    assert_eq!(b, 0x99);
    done(bus);
}

#[tokio::test]
async fn receive_byte_pec() {
    let data = 0x99u8;
    let pec = expected_pec(&[&[read_address_byte(ADDR), data]]);
    let mut bus = new_bus(&[Tx::read(ADDR, std::vec![data, pec])]);
    let b = bus.receive_byte_with_pec(ADDR).await.unwrap();
    assert_eq!(b, data);
    done(bus);
}

#[tokio::test]
async fn receive_byte_pec_mismatch() {
    let mut bus = new_bus(&[Tx::read(ADDR, std::vec![0x99, 0xFF])]);
    let err = bus.receive_byte_with_pec(ADDR).await.unwrap_err();
    assert_eq!(err.kind(), ErrorKind::Pec);
    done(bus);
}

// ---------- write_byte / write_word ----------

#[tokio::test]
async fn write_byte_no_pec() {
    let mut bus = new_bus(&[Tx::write(ADDR, std::vec![REG, 0x33])]);
    bus.write_byte(ADDR, REG, 0x33).await.unwrap();
    done(bus);
}

#[tokio::test]
async fn write_byte_pec() {
    let pec = expected_pec(&[&[write_address_byte(ADDR), REG, 0x33]]);
    let mut bus = new_bus(&[Tx::write(ADDR, std::vec![REG, 0x33, pec])]);
    bus.write_byte_with_pec(ADDR, REG, 0x33).await.unwrap();
    done(bus);
}

#[tokio::test]
async fn write_word_no_pec() {
    let word: u16 = 0xBEEF;
    let bytes = word.to_le_bytes();
    let mut bus = new_bus(&[Tx::write(ADDR, std::vec![REG, bytes[0], bytes[1]])]);
    bus.write_word(ADDR, REG, word).await.unwrap();
    done(bus);
}

#[tokio::test]
async fn write_word_pec() {
    let word: u16 = 0xBEEF;
    let bytes = word.to_le_bytes();
    let pec = expected_pec(&[&[write_address_byte(ADDR), REG, bytes[0], bytes[1]]]);
    let mut bus = new_bus(&[Tx::write(ADDR, std::vec![REG, bytes[0], bytes[1], pec])]);
    bus.write_word_with_pec(ADDR, REG, word).await.unwrap();
    done(bus);
}

// ---------- read_byte / read_word ----------

#[tokio::test]
async fn read_byte_no_pec() {
    let mut bus = new_bus(&[
        Tx::transaction_start(ADDR),
        Tx::write(ADDR, std::vec![REG]),
        Tx::read(ADDR, std::vec![0x77]),
        Tx::transaction_end(ADDR),
    ]);
    let b = bus.read_byte(ADDR, REG).await.unwrap();
    assert_eq!(b, 0x77);
    done(bus);
}

#[tokio::test]
async fn read_byte_pec() {
    let data = 0x77u8;
    let pec = expected_pec(&[&[write_address_byte(ADDR), REG, read_address_byte(ADDR), data]]);
    let mut bus = new_bus(&[
        Tx::transaction_start(ADDR),
        Tx::write(ADDR, std::vec![REG]),
        Tx::read(ADDR, std::vec![data, pec]),
        Tx::transaction_end(ADDR),
    ]);
    let b = bus.read_byte_with_pec(ADDR, REG).await.unwrap();
    assert_eq!(b, data);
    done(bus);
}

#[tokio::test]
async fn read_byte_pec_mismatch() {
    let mut bus = new_bus(&[
        Tx::transaction_start(ADDR),
        Tx::write(ADDR, std::vec![REG]),
        Tx::read(ADDR, std::vec![0x77, 0xFF]),
        Tx::transaction_end(ADDR),
    ]);
    let err = bus.read_byte_with_pec(ADDR, REG).await.unwrap_err();
    assert_eq!(err.kind(), ErrorKind::Pec);
    done(bus);
}

#[tokio::test]
async fn read_word_no_pec() {
    let lo = 0x12u8;
    let hi = 0x34u8;
    let mut bus = new_bus(&[
        Tx::transaction_start(ADDR),
        Tx::write(ADDR, std::vec![REG]),
        Tx::read(ADDR, std::vec![lo, hi]),
        Tx::transaction_end(ADDR),
    ]);
    let w = bus.read_word(ADDR, REG).await.unwrap();
    assert_eq!(w, u16::from_le_bytes([lo, hi]));
    done(bus);
}

#[tokio::test]
async fn read_word_pec() {
    let lo = 0x12u8;
    let hi = 0x34u8;
    let pec = expected_pec(&[&[write_address_byte(ADDR), REG, read_address_byte(ADDR), lo, hi]]);
    let mut bus = new_bus(&[
        Tx::transaction_start(ADDR),
        Tx::write(ADDR, std::vec![REG]),
        Tx::read(ADDR, std::vec![lo, hi, pec]),
        Tx::transaction_end(ADDR),
    ]);
    let w = bus.read_word_with_pec(ADDR, REG).await.unwrap();
    assert_eq!(w, u16::from_le_bytes([lo, hi]));
    done(bus);
}

// ---------- process_call ----------

#[tokio::test]
async fn process_call_no_pec() {
    let word: u16 = 0x0102;
    let resp_lo = 0xAAu8;
    let resp_hi = 0xBBu8;
    let mut bus = new_bus(&[
        Tx::transaction_start(ADDR),
        Tx::write(ADDR, std::vec![REG]),
        Tx::write(ADDR, word.to_le_bytes().to_vec()),
        Tx::read(ADDR, std::vec![resp_lo, resp_hi]),
        Tx::transaction_end(ADDR),
    ]);
    let r = bus.process_call(ADDR, REG, word).await.unwrap();
    assert_eq!(r, u16::from_le_bytes([resp_lo, resp_hi]));
    done(bus);
}

#[tokio::test]
async fn process_call_pec() {
    let word: u16 = 0x0102;
    let resp_lo = 0xAAu8;
    let resp_hi = 0xBBu8;
    let mut hasher = Pec::new();
    hasher.write_u8(write_address_byte(ADDR));
    hasher.write_u8(REG);
    hasher.write(&word.to_le_bytes());
    hasher.write_u8(read_address_byte(ADDR));
    hasher.write(&[resp_lo, resp_hi]);
    let pec = hasher.finish() as u8;
    let mut bus = new_bus(&[
        Tx::transaction_start(ADDR),
        Tx::write(ADDR, std::vec![REG]),
        Tx::write(ADDR, word.to_le_bytes().to_vec()),
        Tx::read(ADDR, std::vec![resp_lo, resp_hi, pec]),
        Tx::transaction_end(ADDR),
    ]);
    let r = bus.process_call_with_pec(ADDR, REG, word).await.unwrap();
    assert_eq!(r, u16::from_le_bytes([resp_lo, resp_hi]));
    done(bus);
}

// ---------- block_write ----------

#[tokio::test]
async fn block_write_no_pec() {
    let data = [0xDE, 0xAD, 0xBE, 0xEF];
    let mut bus = new_bus(&[
        Tx::transaction_start(ADDR),
        Tx::write(ADDR, std::vec![REG]),
        Tx::write(ADDR, std::vec![data.len() as u8]),
        Tx::write(ADDR, data.to_vec()),
        Tx::transaction_end(ADDR),
    ]);
    bus.block_write(ADDR, REG, &data).await.unwrap();
    done(bus);
}

#[tokio::test]
async fn block_write_pec() {
    let data = [0xDE, 0xAD, 0xBE, 0xEF];
    let pec = expected_pec(&[&[write_address_byte(ADDR), REG, data.len() as u8], &data]);
    let mut bus = new_bus(&[
        Tx::transaction_start(ADDR),
        Tx::write(ADDR, std::vec![REG]),
        Tx::write(ADDR, std::vec![data.len() as u8]),
        Tx::write(ADDR, data.to_vec()),
        Tx::write(ADDR, std::vec![pec]),
        Tx::transaction_end(ADDR),
    ]);
    bus.block_write_with_pec(ADDR, REG, &data).await.unwrap();
    done(bus);
}

#[tokio::test]
async fn block_write_too_large() {
    let mut bus = new_bus(&[]);
    let data = std::vec![0u8; MAX_BLOCK_SIZE + 1];
    let err = bus.block_write(ADDR, REG, &data).await.unwrap_err();
    assert_eq!(err.kind(), ErrorKind::TooLargeBlockTransaction);
    done(bus);
}

// ---------- block_read ----------

#[tokio::test]
async fn block_read_no_pec() {
    let mut buf = [0u8; 3];
    let mut bus = new_bus(&[
        Tx::transaction_start(ADDR),
        Tx::write(ADDR, std::vec![REG]),
        Tx::read(ADDR, std::vec![3]),
        Tx::read(ADDR, std::vec![0x10, 0x20, 0x30]),
        Tx::transaction_end(ADDR),
    ]);
    bus.block_read(ADDR, REG, &mut buf).await.unwrap();
    assert_eq!(buf, [0x10, 0x20, 0x30]);
    done(bus);
}

#[tokio::test]
async fn block_read_pec() {
    let payload = [0x10u8, 0x20, 0x30];
    let len = payload.len() as u8;
    // PEC source matches the implementation: addr+W, reg, addr+R, then msg_size, then data.
    let mut hasher = Pec::new();
    hasher.write_u8(write_address_byte(ADDR));
    hasher.write_u8(REG);
    hasher.write_u8(read_address_byte(ADDR));
    hasher.write(&[len]);
    hasher.write(&payload);
    let pec = hasher.finish() as u8;
    let mut buf = [0u8; 3];
    let mut bus = new_bus(&[
        Tx::transaction_start(ADDR),
        Tx::write(ADDR, std::vec![REG]),
        Tx::read(ADDR, std::vec![len]),
        Tx::read(ADDR, payload.to_vec()),
        Tx::read(ADDR, std::vec![pec]),
        Tx::transaction_end(ADDR),
    ]);
    bus.block_read_with_pec(ADDR, REG, &mut buf).await.unwrap();
    assert_eq!(buf, payload);
    done(bus);
}

#[tokio::test]
async fn block_read_too_large() {
    let mut bus = new_bus(&[]);
    let mut buf = std::vec![0u8; MAX_BLOCK_SIZE + 1];
    let err = bus.block_read(ADDR, REG, &mut buf).await.unwrap_err();
    assert_eq!(err.kind(), ErrorKind::TooLargeBlockTransaction);
    done(bus);
}

#[tokio::test]
async fn block_read_size_mismatch_no_pec() {
    // Device reports `2` but the caller expected `3`.
    let mut buf = [0u8; 3];
    let mut bus = new_bus(&[
        Tx::transaction_start(ADDR),
        Tx::write(ADDR, std::vec![REG]),
        Tx::read(ADDR, std::vec![2]),
        Tx::read(ADDR, std::vec![0x10, 0x20, 0x30]),
        Tx::transaction_end(ADDR),
    ]);
    let err = bus.block_read(ADDR, REG, &mut buf).await.unwrap_err();
    assert_eq!(err.kind(), ErrorKind::BlockSizeMismatch(2, 3));
    done(bus);
}

#[tokio::test]
async fn block_read_size_mismatch_pec() {
    // Device reports `2` but the caller expected `3`. The mismatch must be
    // reported as `BlockSizeMismatch` rather than `Pec`, even though the
    // received PEC byte would not match either.
    let mut buf = [0u8; 3];
    let mut bus = new_bus(&[
        Tx::transaction_start(ADDR),
        Tx::write(ADDR, std::vec![REG]),
        Tx::read(ADDR, std::vec![2]),
        Tx::read(ADDR, std::vec![0x10, 0x20, 0x30]),
        Tx::read(ADDR, std::vec![0x00]),
        Tx::transaction_end(ADDR),
    ]);
    let err = bus.block_read_with_pec(ADDR, REG, &mut buf).await.unwrap_err();
    assert_eq!(err.kind(), ErrorKind::BlockSizeMismatch(2, 3));
    done(bus);
}

// ---------- block_write_block_read_process_call ----------

#[tokio::test]
async fn bwbr_no_pec() {
    let write_data = [0x01u8, 0x02];
    let read_payload = [0xAAu8, 0xBB];
    let mut read_buf = [0u8; 2];
    let mut bus = new_bus(&[
        Tx::transaction_start(ADDR),
        Tx::write(ADDR, std::vec![REG]),
        Tx::write(ADDR, std::vec![write_data.len() as u8]),
        Tx::write(ADDR, write_data.to_vec()),
        Tx::read(ADDR, std::vec![read_payload.len() as u8]),
        Tx::read(ADDR, read_payload.to_vec()),
        Tx::transaction_end(ADDR),
    ]);
    bus.block_write_block_read_process_call(ADDR, REG, &write_data, &mut read_buf)
        .await
        .unwrap();
    assert_eq!(read_buf, read_payload);
    done(bus);
}

#[tokio::test]
async fn bwbr_pec() {
    let write_data = [0x01u8, 0x02];
    let read_payload = [0xAAu8, 0xBB];
    let mut read_buf = [0u8; 2];
    let mut hasher = Pec::new();
    hasher.write_u8(write_address_byte(ADDR));
    hasher.write_u8(REG);
    hasher.write_u8(write_data.len() as u8);
    hasher.write(&write_data);
    hasher.write_u8(read_address_byte(ADDR));
    hasher.write(&[read_payload.len() as u8]);
    hasher.write(&read_payload);
    let pec = hasher.finish() as u8;
    let mut bus = new_bus(&[
        Tx::transaction_start(ADDR),
        Tx::write(ADDR, std::vec![REG]),
        Tx::write(ADDR, std::vec![write_data.len() as u8]),
        Tx::write(ADDR, write_data.to_vec()),
        Tx::read(ADDR, std::vec![read_payload.len() as u8]),
        Tx::read(ADDR, read_payload.to_vec()),
        Tx::read(ADDR, std::vec![pec]),
        Tx::transaction_end(ADDR),
    ]);
    bus.block_write_block_read_process_call_with_pec(ADDR, REG, &write_data, &mut read_buf)
        .await
        .unwrap();
    assert_eq!(read_buf, read_payload);
    done(bus);
}

#[tokio::test]
async fn bwbr_too_large() {
    let mut bus = new_bus(&[]);
    let write_data = std::vec![0u8; 200];
    let mut read_buf = std::vec![0u8; 60]; // 200 + 60 > 255
    let err = bus
        .block_write_block_read_process_call(ADDR, REG, &write_data, &mut read_buf)
        .await
        .unwrap_err();
    assert_eq!(err.kind(), ErrorKind::TooLargeBlockTransaction);
    done(bus);
}

#[tokio::test]
async fn bwbr_size_mismatch_no_pec() {
    let write_data = [0x01u8, 0x02];
    let mut read_buf = [0u8; 2];
    // Device returns count `1` but caller expected `2`.
    let mut bus = new_bus(&[
        Tx::transaction_start(ADDR),
        Tx::write(ADDR, std::vec![REG]),
        Tx::write(ADDR, std::vec![write_data.len() as u8]),
        Tx::write(ADDR, write_data.to_vec()),
        Tx::read(ADDR, std::vec![1]),
        Tx::read(ADDR, std::vec![0xAA, 0xBB]),
        Tx::transaction_end(ADDR),
    ]);
    let err = bus
        .block_write_block_read_process_call(ADDR, REG, &write_data, &mut read_buf)
        .await
        .unwrap_err();
    assert_eq!(err.kind(), ErrorKind::BlockSizeMismatch(1, 2));
    done(bus);
}

#[tokio::test]
async fn bwbr_size_mismatch_pec() {
    let write_data = [0x01u8, 0x02];
    let mut read_buf = [0u8; 2];
    // Device returns count `1` but caller expected `2`. Must be reported
    // as `BlockSizeMismatch` rather than `Pec`.
    let mut bus = new_bus(&[
        Tx::transaction_start(ADDR),
        Tx::write(ADDR, std::vec![REG]),
        Tx::write(ADDR, std::vec![write_data.len() as u8]),
        Tx::write(ADDR, write_data.to_vec()),
        Tx::read(ADDR, std::vec![1]),
        Tx::read(ADDR, std::vec![0xAA, 0xBB]),
        Tx::read(ADDR, std::vec![0x00]),
        Tx::transaction_end(ADDR),
    ]);
    let err = bus
        .block_write_block_read_process_call_with_pec(ADDR, REG, &write_data, &mut read_buf)
        .await
        .unwrap_err();
    assert_eq!(err.kind(), ErrorKind::BlockSizeMismatch(1, 2));
    done(bus);
}

// ---------- PEC unavailable ----------

fn new_no_pec_bus(expectations: &[Tx]) -> NoPecBus {
    super::SwSmbusI2c::new(I2cMock::new(expectations))
}

fn done_no_pec(mut bus: NoPecBus) {
    bus.inner_mut().done();
}

#[test]
fn no_pec_bus_get_pec_calc_returns_none() {
    assert!(NoPecBus::get_pec_calc().is_none());
}

#[tokio::test]
async fn no_pec_bus_non_pec_ops_still_work() {
    // All `use_pec = false` paths must succeed even though `get_pec_calc`
    // returns `None`: the trait must not consult the PEC calculator unless
    // PEC was actually requested.
    let mut bus = new_no_pec_bus(&[
        Tx::write(ADDR, std::vec![0x55]),
        Tx::read(ADDR, std::vec![0x99]),
        Tx::write(ADDR, std::vec![REG, 0x33]),
        Tx::transaction_start(ADDR),
        Tx::write(ADDR, std::vec![REG]),
        Tx::read(ADDR, std::vec![0x77]),
        Tx::transaction_end(ADDR),
    ]);
    bus.send_byte(ADDR, 0x55).await.unwrap();
    assert_eq!(bus.receive_byte(ADDR).await.unwrap(), 0x99);
    bus.write_byte(ADDR, REG, 0x33).await.unwrap();
    assert_eq!(bus.read_byte(ADDR, REG).await.unwrap(), 0x77);
    done_no_pec(bus);
}

#[tokio::test]
async fn pec_unavailable_returns_pec_error() {
    let mut bus = super::SwSmbusI2c::<I2cMock, NoPec>::new(I2cMock::new(&[]));
    // Any PEC-requiring path should fail without touching the bus.
    let err = bus.send_byte_with_pec(ADDR, 0x55).await.unwrap_err();
    assert_eq!(err.kind(), ErrorKind::Pec);
    let err = bus.receive_byte_with_pec(ADDR).await.unwrap_err();
    assert_eq!(err.kind(), ErrorKind::Pec);
    let err = bus.read_byte_with_pec(ADDR, REG).await.unwrap_err();
    assert_eq!(err.kind(), ErrorKind::Pec);
    let err = bus.read_word_with_pec(ADDR, REG).await.unwrap_err();
    assert_eq!(err.kind(), ErrorKind::Pec);
    let err = bus.process_call_with_pec(ADDR, REG, 0).await.unwrap_err();
    assert_eq!(err.kind(), ErrorKind::Pec);
    let err = bus.block_write_with_pec(ADDR, REG, &[1, 2]).await.unwrap_err();
    assert_eq!(err.kind(), ErrorKind::Pec);
    let mut rb = [0u8; 2];
    let err = bus.block_read_with_pec(ADDR, REG, &mut rb).await.unwrap_err();
    assert_eq!(err.kind(), ErrorKind::Pec);
    let err = bus
        .block_write_block_read_process_call_with_pec(ADDR, REG, &[1], &mut rb)
        .await
        .unwrap_err();
    assert_eq!(err.kind(), ErrorKind::Pec);
    bus.inner_mut().done();
}

// ---------- &mut T forwarding ----------

#[tokio::test]
async fn mut_ref_smbus_forwards() {
    let mut bus = new_bus(&[Tx::write(ADDR, std::vec![0x55])]);
    let r: &mut TestBus = &mut bus;
    r.send_byte(ADDR, 0x55).await.unwrap();
    assert!(<&mut TestBus as Smbus>::get_pec_calc().is_some());
    done(bus);
}

// ---------- error propagation from underlying I2C ----------

#[tokio::test]
async fn i2c_error_propagates() {
    let mut bus = new_bus(&[Tx::write(ADDR, std::vec![0x55]).with_error(I2cErrorKind::Bus)]);
    let err = bus.send_byte(ADDR, 0x55).await.unwrap_err();
    assert_eq!(err.kind(), ErrorKind::I2c(I2cErrorKind::Bus));
    done(bus);
}
