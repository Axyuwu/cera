mod resources;

use std::sync::Arc;

use resources::Io;

use crate::utils::sync::sync_map::SyncMap;

pub struct World {
    generation: u128,
    storage: Arc<WorldStorage>,
}

struct WorldStorage {
    io_resources: SyncMap<Arc<Io>>,
}
