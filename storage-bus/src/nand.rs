/// Blocking NAND Storage Driver. The trait introduces a method to send command to the bus
/// The NAND device driver should use this trait APIs to send command to the bus
pub trait BlockingNandStorageBusDriver {}

/// Async NAND Storage Driver. The trait introduces a method to send command to the bus
/// The NAND device driver should use this trait APIs to send command to the bus
pub trait AsyncNandStorageBusDriver {}
