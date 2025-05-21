#[derive(Debug, Copy, Clone, PartialEq)]
/// Storage Mode
pub enum NorStorageCmdMode {
    /// Double Data Rate mode for data transfer
    DDR,
    /// Single Data Rate mode for data transfer
    SDR,
}
#[derive(Debug, Copy, Clone)]
/// Storage Command Type
pub enum NorStorageCmdType {
    /// Read transfer type
    Read,
    /// Write transfer type
    Write,
}

#[derive(Debug, Copy, Clone)]
/// Bus Width
pub enum NorStorageBusWidth {
    /// 1 bit bus width
    Single,
    /// 2 bit bus width
    Dual,
    /// 4 bit bus width
    Quad,
    /// 8 bit bus width
    Octal,
}

#[derive(Debug, Copy, Clone)]
/// enum for dummy cycles
pub enum NorStorageDummyCycles {
    /// Dummy cycles in terms of clock cycles
    Clocks(u8),
    /// Dummy cycles in terms of bytes
    Bytes(u8),
}

#[derive(Debug, Copy, Clone)]
/// NOR Storage Command to be passed by NOR based storage device drivers
pub struct NorStorageCmd {
    /// Nor Storage Command lower byte
    pub cmd_lb: u8,
    /// Nor Storage Command upper byte                       
    pub cmd_ub: Option<u8>,
    /// Address of the command
    pub addr: Option<u32>,
    /// Address width in bytes              
    pub addr_width: Option<u8>,
    /// DDR or SDR mode             
    pub mode: NorStorageCmdMode,
    /// Number of Dummy clock cycles. Assuming max 256 dummy cycles beyond which its impractical           
    pub dummy: NorStorageDummyCycles,
    /// Command type - Reading data or writing data
    pub cmdtype: Option<NorStorageCmdType>,
    /// Bus Width - This represents width in terms of signals
    ///     SPI - Single
    ///     QSPI - Quad
    ///     OctalSPI - Octal
    ///     I2C - 1
    pub bus_width: NorStorageBusWidth,
    /// Number of data bytes to be transferred for this command
    pub data_bytes: Option<u32>,
}

/// Enum with storage errors
pub enum NorStorageBusError {
    /// Bus not available could be used for example
    /// 1. Bus is not available due to arbitration lost in multi master bus
    /// 2. Bus is not powered up
    StorageBusNotAvailable,
    /// Bus IO error while sending command
    /// Could be used for example
    /// 1 - Bus read error
    /// 2 - Bus write error
    StorageBusIoError,
    /// Bus internal error
    StorageBusInternalError,
}

/// Blocking NOR Storage Driver. The trait introduces a method to send command to the bus
/// The NOR device driver should use this trait to send command to the bus
/// NOR Storage Bus driver shall implement this trait to support NOR storage access over the bus
/// Bus Examples -
///    - SPI
///    - FlexSPI
///    - Hyperbus
pub trait BlockingNorStorageBusDriver {
    /// Send Command to the bus
    /// Parameters:
    ///    cmd - Command to be sent to the bus
    ///    read_buf - Read buffer to store the data read from the bus
    ///    write_buf - Write buffer to write the data to the bus
    /// Returns:
    ///    Result<(), NorStorageBusError> - Result of the command sent to the bus
    ///    NorStorageBusError - Error code if the command failed
    fn send_command(
        &mut self,
        cmd: NorStorageCmd,
        read_buf: Option<&mut [u8]>,
        write_buf: Option<&[u8]>,
    ) -> Result<(), NorStorageBusError>;
}

#[allow(async_fn_in_trait)]
/// Async NOR Storage Driver. The trait introduces a method to send command to the bus
/// The NOR Storage device driver should use this trait to send command to the bus
/// NOR Storage Bus driver shall implement this trait to support NOR storage access over the bus
/// Bus Examples -
///    - SPI
///    - FlexSPI
///    - Hyperbus
pub trait AsyncNorStorageBusDriver {
    /// Send Command to the bus
    /// Parameters:
    ///   cmd - Command to be sent to the bus
    ///   read_buf - Read buffer to store the data read from the bus
    ///   write_buf - Write buffer to write the data to the bus
    /// Returns:
    ///   Result<(), NorStorageBusError> - Result of the command sent to the bus
    ///   NorStorageBusError - Error code if the command failed
    async fn send_command(
        &mut self,
        cmd: NorStorageCmd,
        read_buf: Option<&mut [u8]>,
        write_buf: Option<&[u8]>,
    ) -> Result<(), NorStorageBusError>;
}
