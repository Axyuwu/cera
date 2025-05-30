use std::{
    fs::File,
    io::{Read, Stderr, Stdin, Stdout, Write},
    net::{TcpListener, TcpStream, UdpSocket},
    process::{Child, ChildStderr, ChildStdin, ChildStdout},
    thread::JoinHandle,
};

use crate::{
    builtins::{usize_to_val, Cache, Value},
    utils::sync::spinmutex::SpinMutex,
};

#[derive(Debug)]
pub enum Io {
    File(File),
    Stdin(Stdin),
    Stdout(Stdout),
    Stderr(Stderr),
    Child(Child),
    ChildStdin(ChildStdin),
    ChildStdout(SpinMutex<Option<ChildStdout>>),
    ChildStderr(SpinMutex<Option<ChildStderr>>),
    TcpStream(TcpStream),
    TcpListener(TcpListener),
    UdpSocket(UdpSocket),
    Thread(Thread),
    AtomicCell(SpinMutex<Value>),
}

// When an new thread is created, this handle should always be created, including for the initial
// eval thread
#[derive(Debug)]
pub struct Thread {
    join_handle: SpinMutex<Option<JoinHandle<Value>>>,
    thread: std::thread::Thread,
}

impl Thread {
    pub fn current() -> Self {
        Self {
            join_handle: SpinMutex::new(None),
            thread: std::thread::current(),
        }
    }
    pub fn new(handle: JoinHandle<Value>) -> Self {
        Self {
            thread: handle.thread().clone(),
            join_handle: SpinMutex::new(Some(handle)),
        }
    }
}

fn io_err_to_val(error: std::io::Error) -> Value {
    match error.kind() {
        std::io::ErrorKind::NotFound => {
            static RESULT_CACHE: Cache = Cache::new();
            static RESULT: Value = Value::bytes_const(&RESULT_CACHE, b"not_found");
            RESULT.static_copy()
        }
        std::io::ErrorKind::PermissionDenied => {
            static RESULT_CACHE: Cache = Cache::new();
            static RESULT: Value = Value::bytes_const(&RESULT_CACHE, b"permission_denied");
            RESULT.static_copy()
        }
        std::io::ErrorKind::ConnectionReset => {
            static RESULT_CACHE: Cache = Cache::new();
            static RESULT: Value = Value::bytes_const(&RESULT_CACHE, b"connection_reset");
            RESULT.static_copy()
        }
        std::io::ErrorKind::HostUnreachable => {
            static RESULT_CACHE: Cache = Cache::new();
            static RESULT: Value = Value::bytes_const(&RESULT_CACHE, b"host_unreachable");
            RESULT.static_copy()
        }
        std::io::ErrorKind::NetworkUnreachable => {
            static RESULT_CACHE: Cache = Cache::new();
            static RESULT: Value = Value::bytes_const(&RESULT_CACHE, b"network_unreachable");
            RESULT.static_copy()
        }
        std::io::ErrorKind::ConnectionAborted => {
            static RESULT_CACHE: Cache = Cache::new();
            static RESULT: Value = Value::bytes_const(&RESULT_CACHE, b"connection_aborted");
            RESULT.static_copy()
        }
        std::io::ErrorKind::NotConnected => {
            static RESULT_CACHE: Cache = Cache::new();
            static RESULT: Value = Value::bytes_const(&RESULT_CACHE, b"not_connected");
            RESULT.static_copy()
        }
        std::io::ErrorKind::AddrInUse => {
            static RESULT_CACHE: Cache = Cache::new();
            static RESULT: Value = Value::bytes_const(&RESULT_CACHE, b"addr_in_use");
            RESULT.static_copy()
        }
        std::io::ErrorKind::AddrNotAvailable => {
            static RESULT_CACHE: Cache = Cache::new();
            static RESULT: Value = Value::bytes_const(&RESULT_CACHE, b"addr_not_available");
            RESULT.static_copy()
        }
        std::io::ErrorKind::NetworkDown => {
            static RESULT_CACHE: Cache = Cache::new();
            static RESULT: Value = Value::bytes_const(&RESULT_CACHE, b"network_down");
            RESULT.static_copy()
        }
        std::io::ErrorKind::BrokenPipe => {
            static RESULT_CACHE: Cache = Cache::new();
            static RESULT: Value = Value::bytes_const(&RESULT_CACHE, b"broken_pipe");
            RESULT.static_copy()
        }
        std::io::ErrorKind::AlreadyExists => {
            static RESULT_CACHE: Cache = Cache::new();
            static RESULT: Value = Value::bytes_const(&RESULT_CACHE, b"already_exists");
            RESULT.static_copy()
        }
        std::io::ErrorKind::WouldBlock => {
            static RESULT_CACHE: Cache = Cache::new();
            static RESULT: Value = Value::bytes_const(&RESULT_CACHE, b"would_block");
            RESULT.static_copy()
        }
        std::io::ErrorKind::NotADirectory => {
            static RESULT_CACHE: Cache = Cache::new();
            static RESULT: Value = Value::bytes_const(&RESULT_CACHE, b"not_a_directory");
            RESULT.static_copy()
        }
        std::io::ErrorKind::IsADirectory => {
            static RESULT_CACHE: Cache = Cache::new();
            static RESULT: Value = Value::bytes_const(&RESULT_CACHE, b"is_a_directory");
            RESULT.static_copy()
        }
        std::io::ErrorKind::DirectoryNotEmpty => {
            static RESULT_CACHE: Cache = Cache::new();
            static RESULT: Value = Value::bytes_const(&RESULT_CACHE, b"directory_not_empty");
            RESULT.static_copy()
        }
        std::io::ErrorKind::ReadOnlyFilesystem => {
            static RESULT_CACHE: Cache = Cache::new();
            static RESULT: Value = Value::bytes_const(&RESULT_CACHE, b"read_only_filesystem");
            RESULT.static_copy()
        }
        std::io::ErrorKind::StaleNetworkFileHandle => {
            static RESULT_CACHE: Cache = Cache::new();
            static RESULT: Value = Value::bytes_const(&RESULT_CACHE, b"stale_network_file_handle");
            RESULT.static_copy()
        }
        std::io::ErrorKind::InvalidInput => {
            static RESULT_CACHE: Cache = Cache::new();
            static RESULT: Value = Value::bytes_const(&RESULT_CACHE, b"invalid_input");
            RESULT.static_copy()
        }
        std::io::ErrorKind::InvalidData => {
            static RESULT_CACHE: Cache = Cache::new();
            static RESULT: Value = Value::bytes_const(&RESULT_CACHE, b"invalid_data");
            RESULT.static_copy()
        }
        std::io::ErrorKind::TimedOut => {
            static RESULT_CACHE: Cache = Cache::new();
            static RESULT: Value = Value::bytes_const(&RESULT_CACHE, b"timed_out");
            RESULT.static_copy()
        }
        std::io::ErrorKind::WriteZero => {
            static RESULT_CACHE: Cache = Cache::new();
            static RESULT: Value = Value::bytes_const(&RESULT_CACHE, b"write_zero");
            RESULT.static_copy()
        }
        std::io::ErrorKind::StorageFull => {
            static RESULT_CACHE: Cache = Cache::new();
            static RESULT: Value = Value::bytes_const(&RESULT_CACHE, b"storage_full");
            RESULT.static_copy()
        }
        std::io::ErrorKind::NotSeekable => {
            static RESULT_CACHE: Cache = Cache::new();
            static RESULT: Value = Value::bytes_const(&RESULT_CACHE, b"not_seekable");
            RESULT.static_copy()
        }
        std::io::ErrorKind::FileTooLarge => {
            static RESULT_CACHE: Cache = Cache::new();
            static RESULT: Value = Value::bytes_const(&RESULT_CACHE, b"file_too_large");
            RESULT.static_copy()
        }
        std::io::ErrorKind::ResourceBusy => {
            static RESULT_CACHE: Cache = Cache::new();
            static RESULT: Value = Value::bytes_const(&RESULT_CACHE, b"resource_busy");
            RESULT.static_copy()
        }
        std::io::ErrorKind::ExecutableFileBusy => {
            static RESULT_CACHE: Cache = Cache::new();
            static RESULT: Value = Value::bytes_const(&RESULT_CACHE, b"executable_file_busy");
            RESULT.static_copy()
        }
        std::io::ErrorKind::Deadlock => {
            static RESULT_CACHE: Cache = Cache::new();
            static RESULT: Value = Value::bytes_const(&RESULT_CACHE, b"deadlock");
            RESULT.static_copy()
        }
        std::io::ErrorKind::TooManyLinks => {
            static RESULT_CACHE: Cache = Cache::new();
            static RESULT: Value = Value::bytes_const(&RESULT_CACHE, b"too_many_links");
            RESULT.static_copy()
        }
        std::io::ErrorKind::ArgumentListTooLong => {
            static RESULT_CACHE: Cache = Cache::new();
            static RESULT: Value = Value::bytes_const(&RESULT_CACHE, b"argument_list_too_long");
            RESULT.static_copy()
        }
        std::io::ErrorKind::Interrupted => {
            static RESULT_CACHE: Cache = Cache::new();
            static RESULT: Value = Value::bytes_const(&RESULT_CACHE, b"interrupted");
            RESULT.static_copy()
        }
        std::io::ErrorKind::Unsupported => {
            static RESULT_CACHE: Cache = Cache::new();
            static RESULT: Value = Value::bytes_const(&RESULT_CACHE, b"unsupported");
            RESULT.static_copy()
        }
        std::io::ErrorKind::UnexpectedEof => {
            static RESULT_CACHE: Cache = Cache::new();
            static RESULT: Value = Value::bytes_const(&RESULT_CACHE, b"unexpected_eof");
            RESULT.static_copy()
        }
        std::io::ErrorKind::OutOfMemory => {
            static RESULT_CACHE: Cache = Cache::new();
            static RESULT: Value = Value::bytes_const(&RESULT_CACHE, b"out_of_memory");
            RESULT.static_copy()
        }
        std::io::ErrorKind::Other => {
            static RESULT_CACHE: Cache = Cache::new();
            static RESULT: Value = Value::bytes_const(&RESULT_CACHE, b"other");
            RESULT.static_copy()
        }
        _ => {
            static RESULT_CACHE: Cache = Cache::new();
            static RESULT: Value = Value::bytes_const(&RESULT_CACHE, b"other_unknown");
            RESULT.static_copy()
        }
    }
}

impl Io {
    pub fn name(&self) -> &'static str {
        match self {
            Io::File(_) => "file",
            Io::Stdin(_) => "stdin",
            Io::Stdout(_) => "stdout",
            Io::Stderr(_) => "stderr",
            Io::Child(_) => "child",
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
    pub fn read(&self, buf: &mut [u8]) -> Value {
        fn read<T: Read>(mut val: T, buf: &mut [u8]) -> std::io::Result<usize> {
            val.read(buf)
        }
        let res = match self {
            Io::File(file) => read(file, buf),
            Io::Stdin(stdin) => read(stdin, buf),
            Io::ChildStdout(child_stdout) => {
                let stdout = child_stdout.apply(Option::take);
                let Some(mut stdout) = stdout else {
                    panic!(
                        "attempted to use child stdout while already in use from another thread"
                    );
                };
                let res = read(&mut stdout, buf);
                child_stdout.apply(|dst| *dst = Some(stdout));
                res
            }
            Io::ChildStderr(child_stderr) => {
                let stderr = child_stderr.apply(Option::take);
                let Some(mut stderr) = stderr else {
                    panic!(
                        "attempted to use child stderr while already in use from another thread"
                    );
                };
                let res = read(&mut stderr, buf);
                child_stderr.apply(|dst| *dst = Some(stderr));
                res
            }
            Io::TcpStream(tcp_stream) => read(tcp_stream, buf),
            o => panic!("attempted to read {}", o.name()),
        };
        Value::from_res(res, usize_to_val, io_err_to_val)
    }
    pub fn write(&self, buf: &[u8]) -> Value {
        fn write<T: Write>(mut val: T, buf: &[u8]) -> std::io::Result<usize> {
            val.write(buf)
        }
        let res = match self {
            Io::File(file) => write(file, buf),
            Io::Stdout(stdout) => write(stdout, buf),
            Io::Stderr(stderr) => write(stderr, buf),
            Io::ChildStdin(child_stdin) => write(child_stdin, buf),
            Io::TcpStream(tcp_stream) => write(tcp_stream, buf),
            o => panic!("attempted to write {}", o.name()),
        };
        Value::from_res(res, usize_to_val, io_err_to_val)
    }
    pub fn flush(&self) -> Value {
        fn flush<T: Write>(mut val: T) -> std::io::Result<()> {
            val.flush()
        }
        let res = match self {
            Io::File(file) => flush(file),
            Io::Stdout(stdout) => flush(stdout),
            Io::Stderr(stderr) => flush(stderr),
            Io::ChildStdin(child_stdin) => flush(child_stdin),
            Io::TcpStream(tcp_stream) => flush(tcp_stream),
            o => panic!("attempted to flush {}", o.name()),
        };
        Value::from_res(res, |()| Value::unit(), io_err_to_val)
    }
    pub fn thread_join(&self) -> Value {
        match self {
            Io::Thread(Thread { join_handle, .. }) => join_handle
                .apply(Option::take)
                .unwrap()
                .join()
                .map_err(std::panic::resume_unwind)
                .unwrap(),
            o => panic!("attempted to thread_join {}", o.name()),
        }
    }
    pub fn thread_is_finished(&self) -> bool {
        match self {
            Io::Thread(Thread { join_handle, .. }) => join_handle.apply(|join_handle| {
                join_handle
                    .as_ref()
                    .map(JoinHandle::is_finished)
                    .unwrap_or(false)
            }),
            o => panic!("attempted to thread_is_finished {}", o.name()),
        }
    }
    pub fn thread_unpark(&self) {
        match self {
            Io::Thread(Thread { thread, .. }) => thread.unpark(),
            o => panic!("attempted to thread_is_finished {}", o.name()),
        }
    }
    pub fn cell_clone(&self) -> Value {
        match self {
            Io::AtomicCell(spin_mutex) => spin_mutex.apply(|e| e.clone()),
            o => panic!("attempted to cell_clone {}", o.name()),
        }
    }
    pub fn cell_swap(&self, new: Value) -> Value {
        match self {
            Io::AtomicCell(spin_mutex) => spin_mutex.apply(|dst| std::mem::replace(dst, new)),
            o => panic!("attempted to cell_swap {}", o.name()),
        }
    }
    /// Only superficial equality check, checks whether the value points to the same address for
    /// borrowed types, or if it is equal for inline storage
    pub fn cell_cas(&self, expected: Value, new: Value) -> Value {
        let res = match self {
            Io::AtomicCell(mutex) => mutex.apply(|value| {
                if !value.addr_eq(&expected) {
                    Err(value.clone())
                } else {
                    *value = new;
                    Ok(())
                }
            }),
            o => panic!("attempted to cell_cas {}", o.name()),
        };
        Value::from_res(res, |()| Value::unit(), std::convert::identity)
    }
}
