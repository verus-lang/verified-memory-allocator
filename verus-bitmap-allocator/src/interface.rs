#![allow(unused_imports)]

use state_machines_macros::*;
use vstd::prelude::*;
use vstd::ptr::*;
use vstd::*;
use vstd::thread::*;
use vstd::vec::*;
use vstd::set_lib::*;

use crate::arena::*;

verus!{

pub struct Allocator {
    arena: Arena,
}

pub struct Allocation {
    pub p: PPtr<u8>,
    pub perm: Tracked<PointsToRaw>,
}

impl Allocation {
    pub closed spec fn from_allocator(&self, allocator: Allocator) -> bool {
        self.perm@@.pptr % ARENA_BLOCK_SIZE as int == 0
        && self.perm@@.size as int % ARENA_BLOCK_SIZE as int == 0
        && self.perm@@.pptr >= allocator.arena.arena_start()
        && self.perm@@.pptr + self.perm@@.size <= allocator.arena.arena_end()
    }

    pub open spec fn wf(&self) -> bool {
        self.perm@@.pptr == self.p.id()
    }

    pub open spec fn len(&self) -> nat {
        self.perm@@.size
    }
}

impl Allocator {
    pub closed spec fn wf(&self) -> bool {
        self.arena.wf()
    }

    pub fn new(
        start: PPtr<u8>,
        n_words: u64,
        Tracked(mem): Tracked<PointsToRaw>
    ) -> (allocator: Self)
    requires n_words % 64 == 0,
        start.id() % ARENA_BLOCK_SIZE as int == 0,
        mem@.pptr == start.id(),
        mem@.size == n_words * 8,
        0 < n_words < 0x4000_0000,
    ensures allocator.wf(),
    {
        let arena = Arena::new(n_words, start, Tracked(mem));
        Allocator { arena }
    }

    pub fn alloc(
        &self,
        n_words: u64
    ) -> (allocation_opt: Option<Allocation>)
    requires self.wf(), n_words >= 1,
    ensures (match allocation_opt {
        Some(allocation) => allocation.wf() && allocation.len() == n_words * 8
            && allocation.from_allocator(*self),
        None => true,
    })
    {
        let (ptr, Tracked(mem)) = self.arena.arena_alloc(n_words as usize);
        if ptr.to_usize() != 0 {
            Some(Allocation {
                p: ptr,
                perm: Tracked(mem),
            })
        } else {
            None
        }
    }

    pub fn dealloc(
        &self,
        allocation: Allocation,
        n_words: u64)
    requires self.wf(),
        allocation.wf(),
        allocation.from_allocator(*self),
        allocation.len() == n_words * ARENA_BLOCK_SIZE
    {
        self.arena.arena_dealloc(allocation.p, n_words as usize, allocation.perm);
    }
}

}
