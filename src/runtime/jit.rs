use std::{
    marker::PhantomData,
    ops::{Index, IndexMut},
};

use derive_more::From;

struct ID<T> {
    idx: usize,
    _phantom: PhantomData<T>,
}

impl<T> ID<T> {
    fn new(idx: usize) -> Self {
        ID {
            idx,
            _phantom: PhantomData,
        }
    }
}

impl<T> Clone for ID<T> {
    fn clone(&self) -> Self {
        Self {
            idx: self.idx.clone(),
            _phantom: self._phantom.clone(),
        }
    }
}

impl<T> Copy for ID<T> {}

struct Datastore<T> {
    store: Vec<T>,
}

impl<T> Default for Datastore<T> {
    fn default() -> Self {
        Self {
            store: Default::default(),
        }
    }
}

impl<T> Index<ID<T>> for Datastore<T> {
    type Output = T;

    fn index(&self, index: ID<T>) -> &Self::Output {
        &self.store[index.idx]
    }
}

impl<T> IndexMut<ID<T>> for Datastore<T> {
    fn index_mut(&mut self, index: ID<T>) -> &mut Self::Output {
        &mut self.store[index.idx]
    }
}

impl<T> Datastore<T> {
    fn insert(&mut self, val: T) -> ID<T> {
        let res = self.next_id();
        self.store.push(val);
        res
    }

    fn next_id(&self) -> ID<T> {
        ID::new(self.store.len())
    }

    fn remove(&mut self, id: ID<T>) -> (T, Option<Rename<ID<T>>>) {
        if id.idx == self.store.len() - 1 {
            return (self.store.pop().unwrap(), None);
        }
        let from = ID::new(self.store.len() - 1);
        let to = id;
        let moved = self.store.pop().unwrap();
        (
            std::mem::replace(&mut self.store[id.idx], moved),
            Some(Rename { to, from }),
        )
    }
}

struct Rename<T> {
    from: T,
    to: T,
}

#[derive(From)]
struct Pred(EdgeID);
type PredID = ID<Pred>;

#[derive(From)]
struct Succ(EdgeID);
type SuccID = ID<Succ>;

#[derive(Default)]
struct Node {
    pred: Datastore<Pred>,
    succ: Datastore<Succ>,
}
type NodeID = ID<Node>;

struct Edge {
    src: (NodeID, SuccID),
    dst: (NodeID, PredID),
}
type EdgeID = ID<Edge>;

#[derive(Default)]
struct Graph {
    nodes: Datastore<Node>,
    edges: Datastore<Edge>,
}

impl Graph {
    fn add_node(&mut self) -> NodeID {
        self.nodes.insert(Default::default())
    }
    fn add_edge(&mut self, src: NodeID, dst: NodeID) -> EdgeID {
        let edge_id = self.edges.next_id();
        let src_succ = self.nodes[src].succ.insert(edge_id.into());
        let dst_pred = self.nodes[dst].pred.insert(edge_id.into());
        let edge = Edge {
            src: (src, src_succ),
            dst: (dst, dst_pred),
        };
        self.edges.insert(edge)
    }
}

struct CodegenUnit {}

struct LinkableBlob {}
