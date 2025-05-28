use std::cell::Cell;
use std::collections::BTreeMap;
use std::fmt::Debug;
use std::iter::repeat_with;
use std::num::NonZero;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

use ahash::RandomState;
use parking_lot::RwLock;

use crate::builtins::Value;

#[derive(Debug)]
pub struct SyncMap<V> {
    inner: Arc<SyncMapInner<V>>,
    keygen: LocalKeyGen,
    state: RandomState,
    mask: usize,
}

#[derive(Debug)]
pub struct SyncMapInner<V> {
    shards: Box<[Shard<V>]>,
    keygen: KeyGenerator,
}

impl<T> SyncMapInner<T> {
    #[cold]
    fn next_local_keygen(&self) -> LocalKeyGen {
        LocalKeyGen {
            low: Cell::new(0),
            high: Cell::new(self.keygen.next_key()),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SyncMapKey(u128);

impl<'t> From<&'t Value> for SyncMapKey {
    fn from(value: &'t Value) -> Self {
        let bytes = &**value.as_bytes();
        Self(u128::from_le_bytes(bytes.try_into().unwrap()))
    }
}

impl From<SyncMapKey> for Value {
    fn from(value: SyncMapKey) -> Self {
        Value::bytes_move(value.0.to_le_bytes())
    }
}

// Aligning cache so that adjacent rwlocks don't make each other's cache line dirty when their
// status doesn't change
#[repr(align(128))]
#[derive(Debug)]
// BTreeMap may seem like an odd choice, but it has non-amortized log n complexity at most on any
// opreation, meaning it is more suitable for realtime
struct Shard<V>(RwLock<BTreeMap<SyncMapKey, V>>);

// Same logic, preventing false sharing
#[repr(align(128))]
#[derive(Debug)]
struct KeyGenerator(AtomicU64);
impl KeyGenerator {
    fn next_key(&self) -> u64 {
        self.0.fetch_add(1, Ordering::Relaxed)
    }
}

// A local key generator to avoid doing shared memory accesses as often
#[derive(Debug)]
struct LocalKeyGen {
    low: Cell<u64>,
    high: Cell<u64>,
}

impl LocalKeyGen {
    fn next_key<T>(&self, far_gen: &SyncMapInner<T>) -> SyncMapKey {
        let res = SyncMapKey((self.low.get() as u128) | ((self.high.get() as u128) << 64));
        match self.low.get().checked_add(1) {
            Some(low) => self.low.set(low),
            None => {
                self.set_from(far_gen.next_local_keygen());
            }
        }
        res
    }
    fn set_from(&self, other: Self) {
        self.low.set(other.low.get());
        self.high.set(other.high.get());
    }
}

impl<V> Clone for SyncMap<V> {
    fn clone(&self) -> Self {
        let inner = self.inner.clone();
        Self {
            keygen: inner.next_local_keygen(),
            inner,
            state: self.state.clone(),
            mask: self.mask,
        }
    }
}

impl<V> SyncMap<V> {
    pub fn new() -> Self {
        fn get_shards_count() -> NonZero<usize> {
            std::thread::available_parallelism()
                .unwrap_or(const { NonZero::new(1).unwrap() })
                .saturating_mul(const { NonZero::new(4usize).unwrap() })
                .checked_next_power_of_two()
                .unwrap()
        }
        let shard_count = get_shards_count().into();
        let inner = Arc::new(SyncMapInner {
            shards: repeat_with(BTreeMap::new)
                .take(shard_count)
                .map(RwLock::new)
                .map(Shard)
                .collect(),
            keygen: KeyGenerator(AtomicU64::new(0)),
        });
        Self {
            keygen: inner.next_local_keygen(),
            state: RandomState::new(),
            mask: shard_count - 1,
            inner,
        }
    }
    pub fn get(&self, key: SyncMapKey) -> Option<V>
    where
        V: Clone,
    {
        self.shard(key).read().get(&key).cloned()
    }
    pub fn insert(&self, value: V) -> SyncMapKey {
        let key = self.next_key();
        if let Some(_) = self.shard(key).write().insert(key, value) {
            unreachable!()
        }
        key
    }
    pub fn remove(&self, key: SyncMapKey) -> Option<V> {
        self.shard(key).write().remove(&key)
    }
    pub fn reserve<'t>(&'t self) -> (SyncMapKey, impl FnOnce(V) + 't) {
        let key = self.next_key();
        (key, move |val| {
            if let Some(_) = self.shard(key).write().insert(key, val) {
                unreachable!()
            }
        })
    }
    fn shard(&self, key: SyncMapKey) -> &RwLock<BTreeMap<SyncMapKey, V>> {
        // Hashing to prevent possible shard collisions, lowering maximum lock contention
        let hash = self.hash_key(key) as usize;
        let idx = hash & self.mask;
        &self.inner.shards[idx].0
    }
    fn hash_key(&self, key: SyncMapKey) -> u64 {
        self.state.hash_one(key)
    }
    fn next_key(&self) -> SyncMapKey {
        self.keygen.next_key(&self.inner)
    }
}
