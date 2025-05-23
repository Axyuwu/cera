use std::collections::BTreeMap;
use std::fmt::Debug;
use std::iter::repeat_with;
use std::num::NonZero;
use std::sync::atomic::{AtomicU64, Ordering};

use ahash::RandomState;
use parking_lot::RwLock;

#[derive(Debug)]
pub struct SyncMap<V> {
    shards: Box<[Shard<V>]>,
    state: RandomState,
    mask: usize,
    keygen: KeyGenerator,
}

// Aligning cache so that adjacent rwlocks don't make each other's cache line dirty when their
// status doesn't change
#[repr(align(128))]
#[derive(Debug)]
// BTreeMap may seem like an odd choice, but it has non-amortized log n complexity at most on any
// opreation, meaning it is more suitable for realtime
struct Shard<V>(RwLock<BTreeMap<u64, V>>);

// Same logic, preventing false sharing
#[repr(align(128))]
#[derive(Debug)]
struct KeyGenerator(AtomicU64);

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
        Self {
            shards: repeat_with(BTreeMap::new)
                .take(shard_count)
                .map(RwLock::new)
                .map(Shard)
                .collect(),
            state: RandomState::new(),
            mask: (1 << shard_count) - 1,
            keygen: KeyGenerator(AtomicU64::new(0)),
        }
    }
    pub fn get(&self, key: u64) -> Option<V>
    where
        V: Clone,
    {
        self.shard(key).read().get(&key).cloned()
    }
    pub fn insert(&self, value: V) -> u64 {
        let key = self.next_key();
        if let Some(_) = self.shard(key).write().insert(key, value) {
            unreachable!()
        }
        key
    }
    pub fn remove(&self, key: u64) -> Option<V> {
        self.shard(key).write().remove(&key)
    }
    fn shard(&self, key: u64) -> &RwLock<BTreeMap<u64, V>> {
        // Hashing to prevent possible shard collisions, lowering maximum lock contention
        let hash = self.hash_key(key) as usize;
        let idx = hash & self.mask;
        &self.shards[idx].0
    }
    fn hash_key(&self, key: u64) -> u64 {
        self.state.hash_one(key)
    }
    fn next_key(&self) -> u64 {
        self.keygen.0.fetch_add(1, Ordering::Relaxed)
    }
}
