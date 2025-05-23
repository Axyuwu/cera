use std::{
    fs::File,
    io::{Read, Stderr, Stdin, Stdout, Write},
    net::{TcpListener, TcpStream, UdpSocket},
    process::{ChildStderr, ChildStdin, ChildStdout},
    thread::JoinHandle,
};

use anyhow::{bail, Result};
use parking_lot::Mutex;

use crate::builtins::{usize_to_val, Value};

#[derive(Debug)]
pub enum Io {
    File(File),
    Stdin(Stdin),
    Stdout(Stdout),
    Stderr(Stderr),
    ChildStdin(ChildStdin),
    ChildStdout(Mutex<ChildStdout>),
    ChildStderr(Mutex<ChildStderr>),
    TcpStream(TcpStream),
    TcpListener(TcpListener),
    UdpSocket(UdpSocket),
    Thread(JoinHandle<Result<Value>>),
    AtomicCell(Mutex<Value>),
}

fn io_err_to_val(error: std::io::Error) -> Value {
    Value::bytes_const(match error.kind() {
        std::io::ErrorKind::NotFound => b"not_found",
        std::io::ErrorKind::PermissionDenied => b"permission_denied",
        std::io::ErrorKind::ConnectionReset => b"connection_reset",
        std::io::ErrorKind::HostUnreachable => b"host_unreachable",
        std::io::ErrorKind::NetworkUnreachable => b"network_unreachable",
        std::io::ErrorKind::ConnectionAborted => b"connection_aborted",
        std::io::ErrorKind::NotConnected => b"not_connected",
        std::io::ErrorKind::AddrInUse => b"addr_in_use",
        std::io::ErrorKind::AddrNotAvailable => b"addr_not_available",
        std::io::ErrorKind::NetworkDown => b"network_down",
        std::io::ErrorKind::BrokenPipe => b"broken_pipe",
        std::io::ErrorKind::AlreadyExists => b"already_exists",
        std::io::ErrorKind::WouldBlock => b"would_block",
        std::io::ErrorKind::NotADirectory => b"not_a_directory",
        std::io::ErrorKind::IsADirectory => b"is_a_directory",
        std::io::ErrorKind::DirectoryNotEmpty => b"directory_not_empty",
        std::io::ErrorKind::ReadOnlyFilesystem => b"read_only_filesystem",
        std::io::ErrorKind::StaleNetworkFileHandle => b"stale_network_file_handle",
        std::io::ErrorKind::InvalidInput => b"invalid_input",
        std::io::ErrorKind::InvalidData => b"invalid_data",
        std::io::ErrorKind::TimedOut => b"timed_out",
        std::io::ErrorKind::WriteZero => b"write_zero",
        std::io::ErrorKind::StorageFull => b"storage_full",
        std::io::ErrorKind::NotSeekable => b"not_seekable",
        std::io::ErrorKind::FileTooLarge => b"file_too_large",
        std::io::ErrorKind::ResourceBusy => b"resource_busy",
        std::io::ErrorKind::ExecutableFileBusy => b"executable_file_busy",
        std::io::ErrorKind::Deadlock => b"deadlock",
        std::io::ErrorKind::TooManyLinks => b"too_many_links",
        std::io::ErrorKind::ArgumentListTooLong => b"argument_list_too_long",
        std::io::ErrorKind::Interrupted => b"interrupted",
        std::io::ErrorKind::Unsupported => b"unsupported",
        std::io::ErrorKind::UnexpectedEof => b"unexpected_eof",
        std::io::ErrorKind::OutOfMemory => b"out_of_memory",
        std::io::ErrorKind::Other => b"other",
        _ => b"other_unknown",
    })
}

impl Io {
    pub fn name(&self) -> &'static str {
        match self {
            Io::File(_) => "file",
            Io::Stdin(_) => "stdin",
            Io::Stdout(_) => "stdout",
            Io::Stderr(_) => "stderr",
            Io::ChildStdin(_) => "child stdin",
            Io::ChildStdout(_) => "child stdout",
            Io::ChildStderr(_) => "child stderr",
            Io::TcpStream(_) => "tcp stream",
            Io::TcpListener(_) => "tcp listener",
            Io::UdpSocket(_) => "udp socket",
            Io::Thread(_) => "thread",
            Io::AtomicCell(_) => "atomic cell",
        }
    }
    pub fn read(&self, buf: &mut [u8]) -> Result<Value> {
        fn read<T: Read>(mut val: T, buf: &mut [u8]) -> std::io::Result<usize> {
            val.read(buf)
        }
        let res = match self {
            Io::File(file) => read(file, buf),
            Io::Stdin(stdin) => read(stdin, buf),
            Io::ChildStdout(child_stdout) => read(&mut *child_stdout.lock(), buf),
            Io::ChildStderr(child_stderr) => read(&mut *child_stderr.lock(), buf),
            Io::TcpStream(tcp_stream) => read(tcp_stream, buf),
            o => bail!("attempted to read {}", o.name()),
        };
        Ok(Value::from_res(res, usize_to_val, io_err_to_val))
    }
    pub fn write(&self, buf: &[u8]) -> Result<Value> {
        fn write<T: Write>(mut val: T, buf: &[u8]) -> std::io::Result<usize> {
            val.write(buf)
        }
        let res = match self {
            Io::File(file) => write(file, buf),
            Io::Stdout(stdout) => write(stdout, buf),
            Io::Stderr(stderr) => write(stderr, buf),
            Io::ChildStdin(child_stdin) => write(child_stdin, buf),
            Io::TcpStream(tcp_stream) => write(tcp_stream, buf),
            o => bail!("attempted to write {}", o.name()),
        };
        Ok(Value::from_res(res, usize_to_val, io_err_to_val))
    }
    pub fn flush(&self) -> Result<Value> {
        fn flush<T: Write>(mut val: T) -> std::io::Result<()> {
            val.flush()
        }
        let res = match self {
            Io::File(file) => flush(file),
            Io::Stdout(stdout) => flush(stdout),
            Io::Stderr(stderr) => flush(stderr),
            Io::ChildStdin(child_stdin) => flush(child_stdin),
            Io::TcpStream(tcp_stream) => flush(tcp_stream),
            o => bail!("attempted to flush {}", o.name()),
        };
        Ok(Value::from_res(res, |()| Value::unit(), io_err_to_val))
    }
    pub fn cell_clone(&self) -> Result<Value> {
        match self {
            Io::AtomicCell(mutex) => Ok(mutex.lock().clone()),
            o => bail!("attempted to cell_clone {}", o.name()),
        }
    }
    pub fn cell_swap(&self, new: Value) -> Result<Value> {
        match self {
            Io::AtomicCell(mutex) => Ok(std::mem::replace(&mut mutex.lock(), new)),
            o => bail!("attempted to cell_swap {}", o.name()),
        }
    }
    /// Only superficial equality check, checks whether the value points to the same address for
    /// borrowed types, or if it is equal for inline storage
    pub fn cell_cas(&self, expected: Value, new: Value) -> Result<Value> {
        let res = match self {
            Io::AtomicCell(mutex) => {
                let mut lock = mutex.lock();
                let value = &mut *lock;
                if !value.addr_eq(&expected) {
                    Err(value.clone())
                } else {
                    *value = new;
                    Ok(())
                }
            }
            o => bail!("attempted to cell_cas {}", o.name()),
        };
        Ok(Value::from_res(
            res,
            |()| Value::unit(),
            std::convert::identity,
        ))
    }
}
