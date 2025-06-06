mod resources;

use std::cell::Cell;
use std::sync::Arc;
use std::time::Duration;

use resources::{Io, Thread};

use crate::builtins::get_u128;
use crate::utils::sync::sync_map::{SyncMap, SyncMapKey};

use super::get_usize;
use super::FuncThunk;
use super::Value;
use super::{get_args, BuiltinFunc};

#[derive(Debug)]
pub struct World {
    generation: Cell<WorldGeneration>,
    io_resources: SyncMap<Arc<Io>>,
    curr_thread: Cell<SyncMapKey>,
}

pub trait AsWorld {
    fn as_world(&mut self) -> &mut World;
}

impl AsWorld for World {
    fn as_world(&mut self) -> &mut World {
        self
    }
}

#[derive(Debug)]
pub struct PureWorld;
impl AsWorld for PureWorld {
    fn as_world(&mut self) -> &mut World {
        panic!("cannot access world in pure world")
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct WorldGeneration(u128);

impl<'t> From<&'t Value> for WorldGeneration {
    fn from(value: &'t Value) -> Self {
        let bytes = &**value.as_bytes();
        Self(u128::from_le_bytes(bytes.try_into().unwrap()))
    }
}
impl From<WorldGeneration> for Value {
    fn from(value: WorldGeneration) -> Self {
        Value::bytes_move(value.0.to_le_bytes())
    }
}

impl World {
    pub fn new() -> (Self, Value) {
        let io_resources = SyncMap::new();
        let curr_thread = Cell::new(io_resources.insert(Arc::new(Io::Thread(Thread::current()))));
        let res = Self {
            generation: Cell::new(WorldGeneration(0)),
            io_resources,
            curr_thread,
        };
        let gen = res.generation.get();
        (res, gen.into())
    }
    fn new_thread(&self, func: impl FnOnce(Self) -> Value + Send + 'static) -> SyncMapKey {
        let io_resources = self.io_resources.clone();
        let (key, cb) = self.io_resources.reserve();

        let world = Self {
            generation: Cell::new(WorldGeneration(0)),
            io_resources,
            curr_thread: Cell::new(key),
        };

        cb(Arc::new(Io::Thread(Thread::new(std::thread::spawn(
            || func(world),
        )))));

        key
    }
}

#[derive(Clone, Copy, Debug)]
pub enum WorldIo {
    /// (world, io, (offset, len, buf)) -> (
    ///     world,
    ///     (
    ///         (offset, len, buf),
    ///         ("ok", read) | ("err", err_kind)
    ///     )
    /// )
    IoRead,
    IoReadVectored,
    /// (world, io, (offset, len, buf)) -> (world, ("ok", written) | ("err", err_kind))
    IoWrite,
    IoWriteVectored,
    /// (world, io) -> (world, ("ok", ()) | ("err", err_kind))
    IoFlush,
    /// (world, io) -> world
    IoDrop,

    IoStdin,
    IoStdout,
    IoStdErr,

    IoIsTerminal,

    ProcessChildSpawn,
    ProcessChildKill,
    ProcessChildId,
    ProcessChildWait,
    ProcessChildHasExited,
    /// world -> !
    ProcessAbort,
    ProcessExit,
    ProcessId,

    FsFileOpen,
    FsFileUpdate,
    FsFileSync,
    FsDirLs,
    FsCreate,
    FsInfo,
    FsUpdate,
    FsRemove,

    NetTakeError,
    NetTryClone,
    NetInfo,
    NetUpdate,

    NetTcpListenerBind,
    NetTcpListenerAccept,

    NetTcpStreamConnect, // Timeout option
    NetTcpStreamPeek,

    NetUdpBind,
    NetUdpConnect,
    NetUdpRecv,
    NetUdpRecvFrom,
    NetUdpSend,
    NetUdpSendTo,
    NetUdpPeek,
    NetUdpPeekFrom,

    ThreadAvailableParallelism,
    /// world -> (world, thread)
    ThreadCurrent,
    /// (world, () | timeout) -> world
    ThreadPark,
    ThreadSleep,
    /// (world, expression) -> (world, thread)
    ThreadSpawn,
    ThreadYieldNow,
    ThreadUnpark,
    /// (world, thread) -> (world, value)
    ThreadJoin,
    ThreadIsFinished,

    CellNew,
    /// (world, cell) -> (world, value)
    CellClone,
    /// (world, cell, new) -> (world, previous)
    CellSwap,
    /// (world, cell, (expected, new)) -> (world, ("ok", ()) | ("err", current))
    CellCas,

    TimeInstantNow,

    EnvArgs,
    EnvVars,
    EnvCurrentDir,
    EnvConstants, // std::env::consts

    HintSpinLoop,
}

impl WorldIo {
    pub fn from_ident(ident: &[u8]) -> Option<Self> {
        Some(match ident {
            b"io_read" => Self::IoRead,
            b"io_read_vectored" => Self::IoReadVectored,
            b"io_write" => Self::IoWrite,
            b"io_write_vectored" => Self::IoWriteVectored,
            b"io_flush" => Self::IoFlush,
            b"io_drop" => Self::IoDrop,
            b"io_stdin" => Self::IoStdin,
            b"io_stdout" => Self::IoStdout,
            b"io_std_err" => Self::IoStdErr,
            b"io_is_terminal" => Self::IoIsTerminal,
            b"process_child_spawn" => Self::ProcessChildSpawn,
            b"process_child_kill" => Self::ProcessChildKill,
            b"process_child_id" => Self::ProcessChildId,
            b"process_child_wait" => Self::ProcessChildWait,
            b"process_child_has_exited" => Self::ProcessChildHasExited,
            b"process_abort" => Self::ProcessAbort,
            b"process_exit" => Self::ProcessExit,
            b"process_id" => Self::ProcessId,
            b"fs_file_open" => Self::FsFileOpen,
            b"fs_file_update" => Self::FsFileUpdate,
            b"fs_file_sync" => Self::FsFileSync,
            b"fs_dir_ls" => Self::FsDirLs,
            b"fs_create" => Self::FsCreate,
            b"fs_info" => Self::FsInfo,
            b"fs_update" => Self::FsUpdate,
            b"fs_remove" => Self::FsRemove,
            b"net_take_error" => Self::NetTakeError,
            b"net_try_clone" => Self::NetTryClone,
            b"net_info" => Self::NetInfo,
            b"net_update" => Self::NetUpdate,
            b"net_tcp_listener_bind" => Self::NetTcpListenerBind,
            b"net_tcp_listener_accept" => Self::NetTcpListenerAccept,
            b"net_tcp_stream_connect" => Self::NetTcpStreamConnect,
            b"net_tcp_stream_peek" => Self::NetTcpStreamPeek,
            b"net_udp_bind" => Self::NetUdpBind,
            b"net_udp_connect" => Self::NetUdpConnect,
            b"net_udp_recv" => Self::NetUdpRecv,
            b"net_udp_recv_from" => Self::NetUdpRecvFrom,
            b"net_udp_send" => Self::NetUdpSend,
            b"net_udp_send_to" => Self::NetUdpSendTo,
            b"net_udp_peek" => Self::NetUdpPeek,
            b"net_udp_peek_from" => Self::NetUdpPeekFrom,
            b"thread_available_parallelism" => Self::ThreadAvailableParallelism,
            b"thread_current" => Self::ThreadCurrent,
            b"thread_park" => Self::ThreadPark,
            b"thread_sleep" => Self::ThreadSleep,
            b"thread_spawn" => Self::ThreadSpawn,
            b"thread_yield_now" => Self::ThreadYieldNow,
            b"thread_unpark" => Self::ThreadUnpark,
            b"thread_join" => Self::ThreadJoin,
            b"thread_is_finished" => Self::ThreadIsFinished,
            b"cell_new" => Self::CellNew,
            b"cell_clone" => Self::CellClone,
            b"cell_swap" => Self::CellSwap,
            b"cell_cas" => Self::CellCas,
            b"time_instant_now" => Self::TimeInstantNow,
            b"env_args" => Self::EnvArgs,
            b"env_vars" => Self::EnvVars,
            b"env_current_dir" => Self::EnvCurrentDir,
            b"env_constants" => Self::EnvConstants,
            b"hint_spin_loop" => Self::HintSpinLoop,
            _ => return None,
        })
    }
    pub fn name(&self) -> &'static str {
        match self {
            Self::IoRead => "io_read",
            Self::IoReadVectored => "io_read_vectored",
            Self::IoWrite => "io_write",
            Self::IoWriteVectored => "io_write_vectored",
            Self::IoFlush => "io_flush",
            Self::IoDrop => "io_drop",
            Self::IoStdin => "io_stdin",
            Self::IoStdout => "io_stdout",
            Self::IoStdErr => "io_std_err",
            Self::IoIsTerminal => "io_is_terminal",
            Self::ProcessChildSpawn => "process_child_spawn",
            Self::ProcessChildKill => "process_child_kill",
            Self::ProcessChildId => "process_child_id",
            Self::ProcessChildWait => "process_child_wait",
            Self::ProcessChildHasExited => "process_child_has_exited",
            Self::ProcessAbort => "process_abort",
            Self::ProcessExit => "process_exit",
            Self::ProcessId => "process_id",
            Self::FsFileOpen => "fs_file_open",
            Self::FsFileUpdate => "fs_file_update",
            Self::FsFileSync => "fs_file_sync",
            Self::FsDirLs => "fs_dir_ls",
            Self::FsCreate => "fs_create",
            Self::FsInfo => "fs_info",
            Self::FsUpdate => "fs_update",
            Self::FsRemove => "fs_remove",
            Self::NetTakeError => "net_take_error",
            Self::NetTryClone => "net_try_clone",
            Self::NetInfo => "net_info",
            Self::NetUpdate => "net_update",
            Self::NetTcpListenerBind => "net_tcp_listener_bind",
            Self::NetTcpListenerAccept => "net_tcp_listener_accept",
            Self::NetTcpStreamConnect => "net_tcp_stream_connect",
            Self::NetTcpStreamPeek => "net_tcp_stream_peek",
            Self::NetUdpBind => "net_udp_bind",
            Self::NetUdpConnect => "net_udp_connect",
            Self::NetUdpRecv => "net_udp_recv",
            Self::NetUdpRecvFrom => "net_udp_recv_from",
            Self::NetUdpSend => "net_udp_send",
            Self::NetUdpSendTo => "net_udp_send_to",
            Self::NetUdpPeek => "net_udp_peek",
            Self::NetUdpPeekFrom => "net_udp_peek_from",
            Self::ThreadAvailableParallelism => "thread_available_parallelism",
            Self::ThreadCurrent => "thread_current",
            Self::ThreadPark => "thread_park",
            Self::ThreadSleep => "thread_sleep",
            Self::ThreadSpawn => "thread_spawn",
            Self::ThreadYieldNow => "thread_yield_now",
            Self::ThreadUnpark => "thread_unpark",
            Self::ThreadJoin => "thread_join",
            Self::ThreadIsFinished => "thread_is_finished",
            Self::CellNew => "cell_new",
            Self::CellClone => "cell_clone",
            Self::CellSwap => "cell_swap",
            Self::CellCas => "cell_cas",
            Self::TimeInstantNow => "time_instant_now",
            Self::EnvArgs => "env_args",
            Self::EnvVars => "env_vars",
            Self::EnvCurrentDir => "env_current_dir",
            Self::EnvConstants => "env_constants",
            Self::HintSpinLoop => "hint_spin_loop",
        }
    }
    pub fn poll(self, value: Value, world: &mut impl AsWorld) -> FuncThunk {
        let world = world.as_world();
        FuncThunk::Done {
            value: match self {
                WorldIo::IoRead => world_map_io(world, value, |io, mut value| {
                    let res = io.read(val_to_offset_slice_mut(&mut value));
                    Value::aggregate_move([value, res])
                }),
                WorldIo::IoReadVectored => todo!(),
                WorldIo::IoWrite => world_map_io(world, value, |io, value| {
                    io.write(val_to_offset_slice(&value))
                }),
                WorldIo::IoWriteVectored => todo!(),
                WorldIo::IoFlush => world_map_io_no_arg(world, value, Io::flush),
                WorldIo::IoDrop => world_map_unit(world, value, |value| {
                    if world
                        .io_resources
                        .remove((&value).try_into().unwrap())
                        .is_none()
                    {
                        panic!("dropped non existant io resource {value}")
                    }
                }),
                WorldIo::IoStdin => todo!(),
                WorldIo::IoStdout => todo!(),
                WorldIo::IoStdErr => todo!(),
                WorldIo::IoIsTerminal => todo!(),
                WorldIo::ProcessChildSpawn => todo!(),
                WorldIo::ProcessChildKill => todo!(),
                WorldIo::ProcessChildId => todo!(),
                WorldIo::ProcessChildWait => todo!(),
                WorldIo::ProcessChildHasExited => todo!(),
                WorldIo::ProcessAbort => {
                    world_map_unit(world, value, |value| panic!("program aborted:\n{value}"))
                }
                WorldIo::ProcessExit => todo!(),
                WorldIo::ProcessId => todo!(),
                WorldIo::FsFileOpen => todo!(),
                WorldIo::FsFileUpdate => todo!(),
                WorldIo::FsFileSync => todo!(),
                WorldIo::FsDirLs => todo!(),
                WorldIo::FsCreate => todo!(),
                WorldIo::FsInfo => todo!(),
                WorldIo::FsUpdate => todo!(),
                WorldIo::FsRemove => todo!(),
                WorldIo::NetTakeError => todo!(),
                WorldIo::NetTryClone => todo!(),
                WorldIo::NetInfo => todo!(),
                WorldIo::NetUpdate => todo!(),
                WorldIo::NetTcpListenerBind => todo!(),
                WorldIo::NetTcpListenerAccept => todo!(),
                WorldIo::NetTcpStreamConnect => todo!(),
                WorldIo::NetTcpStreamPeek => todo!(),
                WorldIo::NetUdpBind => todo!(),
                WorldIo::NetUdpConnect => todo!(),
                WorldIo::NetUdpRecv => todo!(),
                WorldIo::NetUdpRecvFrom => todo!(),
                WorldIo::NetUdpSend => todo!(),
                WorldIo::NetUdpSendTo => todo!(),
                WorldIo::NetUdpPeek => todo!(),
                WorldIo::NetUdpPeekFrom => todo!(),
                WorldIo::ThreadAvailableParallelism => todo!(),
                WorldIo::ThreadCurrent => world_map_no_arg(&world, value, || {
                    if world.io_resources.get(world.curr_thread.get()).is_none() {
                        world.curr_thread.set(
                            world
                                .io_resources
                                .insert(Arc::new(Io::Thread(Thread::current()))),
                        );
                    }
                    world.curr_thread.get().into()
                }),
                WorldIo::ThreadPark => world_map_unit(world, value, |value| {
                    if value.is_unit() {
                        std::thread::park()
                    } else {
                        std::thread::park_timeout(value_to_duration(value))
                    }
                }),
                WorldIo::ThreadSleep => todo!(),
                WorldIo::ThreadSpawn => world_map(world, value, |value| {
                    world
                        .new_thread(|mut world| {
                            FuncThunk::Step {
                                func: BuiltinFunc::BuiltinEval,
                                value,
                            }
                            .eval::<false>(&mut world)
                        })
                        .into()
                }),
                WorldIo::ThreadYieldNow => todo!(),
                WorldIo::ThreadJoin => world_map_io_no_arg(world, value, Io::thread_join),
                WorldIo::ThreadIsFinished => todo!(),
                WorldIo::ThreadUnpark => todo!(),
                WorldIo::CellNew => todo!(),
                WorldIo::CellClone => world_map_io_no_arg(world, value, Io::cell_clone),
                WorldIo::CellSwap => world_map_io(world, value, Io::cell_swap),
                WorldIo::CellCas => world_map_io(world, value, |io, value| {
                    let [expected, new] = get_args(value);
                    io.cell_cas(expected, new)
                }),
                WorldIo::TimeInstantNow => todo!(),
                WorldIo::EnvArgs => todo!(),
                WorldIo::EnvVars => todo!(),
                WorldIo::EnvCurrentDir => todo!(),
                WorldIo::EnvConstants => todo!(),
                WorldIo::HintSpinLoop => todo!(),
            },
        }
    }
}

fn world_map_unit(world: &World, value: Value, func: impl FnOnce(Value)) -> Value {
    let (gen, value) = {
        let [gen, rem] = get_args(value);
        let gen = WorldGeneration::from(&gen);
        (gen, rem)
    };

    let mut world_gen = world.generation.get();

    if gen != world_gen {
        panic!(
            "mismatched world generation, given: {:?},\n current: {:?}",
            gen, world_gen
        )
    }

    world_gen.0 += 1;
    world.generation.set(world_gen);

    func(value);

    world_gen.into()
}
fn world_map(world: &World, value: Value, func: impl FnOnce(Value) -> Value) -> Value {
    let (gen, value) = {
        let [gen, rem] = get_args(value);
        let gen = WorldGeneration::from(&gen);
        (gen, rem)
    };

    let mut world_gen = world.generation.get();

    if gen != world_gen {
        panic!(
            "mismatched world generation, given: {:?},\n current: {:?}",
            gen, world_gen
        )
    }

    world_gen.0 += 1;
    world.generation.set(world_gen);

    Value::aggregate_move([world_gen.into(), func(value)])
}
fn world_map_no_arg(world: &World, value: Value, func: impl FnOnce() -> Value) -> Value {
    let gen = WorldGeneration::from(&value);

    let mut world_gen = world.generation.get();

    if gen != world_gen {
        panic!(
            "mismatched world generation, given: {:?},\n current: {:?}",
            gen, world_gen
        )
    }

    world_gen.0 += 1;
    world.generation.set(world_gen);

    Value::aggregate_move([world_gen.into(), func()])
}
fn world_map_io(world: &World, value: Value, func: impl FnOnce(&Io, Value) -> Value) -> Value {
    let (gen, io, value) = {
        let [gen, io, rem] = get_args(value);
        let gen = WorldGeneration::from(&gen);
        let io = SyncMapKey::from(&io);
        (gen, io, rem)
    };

    let mut world_gen = world.generation.get();

    if gen != world_gen {
        panic!(
            "mismatched world generation, given: {:?},\n current: {:?}",
            gen, world_gen
        )
    }

    world_gen.0 += 1;
    world.generation.set(world_gen);

    let io = world.io_resources.get(io).unwrap();

    Value::aggregate_move([world_gen.into(), func(&*io, value)])
}
fn world_map_io_no_arg(world: &World, value: Value, func: impl FnOnce(&Io) -> Value) -> Value {
    let (gen, io) = {
        let [gen, io] = get_args(value);
        let gen = WorldGeneration::from(&gen);
        let io = SyncMapKey::from(&io);
        (gen, io)
    };

    let mut world_gen = world.generation.get();

    if gen != world_gen {
        panic!(
            "mismatched world generation, given: {:?},\n current: {:?}",
            gen, world_gen
        )
    }

    world_gen.0 += 1;
    world.generation.set(world_gen);

    let io = world.io_resources.get(io).unwrap();

    Value::aggregate_move([world_gen.into(), func(&*io)])
}

fn val_to_offset_slice(value: &Value) -> &[u8] {
    let aggr = value.as_aggregate();
    if aggr.len() != 3 {
        panic!(
            "expected 3 values, a start, an end, and a buffer, found {} values instead",
            aggr.len()
        )
    }
    let (start, end, buf) = (
        get_usize(aggr[0].as_bytes()),
        get_usize(aggr[1].as_bytes()),
        aggr[2].as_bytes(),
    );
    buf.get(start..end).unwrap()
}
fn val_to_offset_slice_mut(value: &mut Value) -> &mut [u8] {
    let aggr = value.as_aggregate_mut().make_mut();
    if aggr.len() != 3 {
        panic!(
            "expected 3 values, a start, an end, and a buffer, found {} values instead",
            aggr.len()
        )
    }
    let (start, end, buf) = (
        get_usize(aggr[0].as_bytes()),
        get_usize(aggr[1].as_bytes()),
        aggr[2].as_bytes_mut().make_mut(),
    );
    buf.get_mut(start..end).unwrap()
}

fn value_to_duration(value: Value) -> Duration {
    const ONE_BILLION: u128 = 1_000_000_000;
    let nanos = get_u128(&**value.as_bytes());
    let secs = nanos / ONE_BILLION;
    let subsecs_nanos = nanos % ONE_BILLION;
    if secs > u64::MAX as u128 {
        panic!("duration exceeds the maximum number of seconds")
    }
    Duration::new(secs as u64, subsecs_nanos as u32)
}
