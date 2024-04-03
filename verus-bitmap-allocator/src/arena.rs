#![allow(unused_imports)]

use state_machines_macros::*;
use vstd::prelude::*;
use vstd::ptr::*;
use vstd::*;
use vstd::thread::*;
use vstd::vec::*;
use vstd::set_lib::*;

use crate::bitmap::*;

verus!{

pub const ARENA_BLOCK_SIZE: usize = 8;

pub struct Arena {
    start: PPtr<u8>,
    bitmap: Bitmap,
}

impl Arena {
    pub closed spec fn wf(&self) -> bool {
        &&& self.bitmap.wf()
        &&& self.bitmap.constant() == self.start.id()
        &&& self.bitmap.data_len() >= 1
        &&& self.start.id() % ARENA_BLOCK_SIZE as int == 0
    }

    pub closed spec fn arena_start(&self) -> int {
        self.start.id()
    }

    pub closed spec fn arena_end(&self) -> int {
        self.start.id() + self.bitmap.user_len() * ARENA_BLOCK_SIZE
    }

    pub fn new(num_words: u64, start: PPtr<u8>, Tracked(perm): Tracked<PointsToRaw>) -> (arena: Arena)
        requires
            num_words % 64 == 0,
            perm@.pptr % ARENA_BLOCK_SIZE as int == 0,
            perm@.pptr == start.id(),
            perm@.size == num_words * 8,
            0 < num_words < 0x4000_0000,
        ensures
            arena.wf(),
            arena.arena_start() == start.id(),
            arena.arena_end() == start.id() + perm@.size
    {
        let bitmap = Bitmap::new(num_words as usize, Ghost(start.id()),
            Tracked(split_points_to_raw(perm, start.id(), 8, 0, num_words as int)));
        Arena { start, bitmap }
    }

    pub fn arena_alloc(&self, n_words: usize) -> (res: (PPtr<u8>, Tracked<PointsToRaw>))
        requires self.wf(),
            n_words >= 1,
        ensures ({
            let (ptr, points_to_raw) = res;
            ptr.id() != 0 ==> (
                points_to_raw@@.pptr == ptr.id()
                && points_to_raw@@.size == n_words * ARENA_BLOCK_SIZE
                && ptr.id() % ARENA_BLOCK_SIZE as int == 0
                && ptr.id() >= self.arena_start()
                && ptr.id() + points_to_raw@@.size <= self.arena_end()
            )
        })
    {
        if n_words > self.bitmap.get_user_len() {
            return (PPtr::from_usize(0), Tracked(PointsToRaw::empty()));
        }

        let (success, idx, tr_map) = self.bitmap.bitmap_try_find_from_claim_across(0, n_words);
        if success {
            let tracked points_to_raw;
            proof {
                points_to_raw = points_to_raw_map_to_singleton(
                    tr_map.get(), self.start.id(), ARENA_BLOCK_SIZE as int,
                    idx as int, idx as int + n_words);
                points_to_raw.is_in_bounds();
                assert(idx * ARENA_BLOCK_SIZE >= 0) by(nonlinear_arith)
                    requires idx >= 0, ARENA_BLOCK_SIZE >= 0 { }
            }

            let ptr = PPtr::from_usize(
                self.start.to_usize() + idx * ARENA_BLOCK_SIZE);

            (ptr, Tracked(points_to_raw))
        } else {
            (PPtr::from_usize(0), Tracked(PointsToRaw::empty()))
        }
    }

    pub fn arena_dealloc(&self,
            ptr: PPtr<u8>,
            count: usize,
            Tracked(points_to_raw): Tracked<PointsToRaw>,
    )
        requires self.wf(),
            points_to_raw@.pptr == ptr.id()
            && points_to_raw@.size == count * ARENA_BLOCK_SIZE
            && points_to_raw@.pptr >= self.arena_start()
            && points_to_raw@.pptr + points_to_raw@.size <= self.arena_end()
            && points_to_raw@.pptr as int % ARENA_BLOCK_SIZE as int == 0
            && points_to_raw@.size as int % ARENA_BLOCK_SIZE as int == 0
    {
        let user_idx = (ptr.to_usize() - self.start.to_usize()) / ARENA_BLOCK_SIZE;

        //assert(
        //    points_to_raw@.pptr == self.start.id() + (user_idx as int) * (ARENA_BLOCK_SIZE as int)
        //);
        let tracked m = split_points_to_raw(
            points_to_raw,
            self.start.id(),
            ARENA_BLOCK_SIZE as int,
            user_idx as int,
            user_idx + count);

        self.bitmap.bitmap_unclaim_range(user_idx, count, Tracked(m));
    }
}

proof fn split_points_to_raw(tracked points_to_raw: PointsToRaw,
    start: int, block_size: int, block_idx_start: int, block_idx_end: int)
        -> (tracked m: Map<int, PointsToRaw>)
  requires
      block_idx_start <= block_idx_end,
      block_size >= 0,
      points_to_raw@.pptr == start + block_idx_start * block_size,
      points_to_raw@.size == (block_idx_end - block_idx_start) * block_size,
  ensures
      forall |i: int| block_idx_start <= i < block_idx_end <==> m.dom().contains(i),
      forall |i: int| block_idx_start <= i < block_idx_end ==> m.index(i)@.size == block_size,
      forall |i: int| block_idx_start <= i < block_idx_end ==> m.index(i)@.pptr == start + i * block_size,
  decreases block_idx_end - block_idx_start
{
    if block_idx_end == block_idx_start {
        Map::tracked_empty()
    } else {
        let tracked (a, b) = points_to_raw.split((block_idx_end - block_idx_start - 1) * block_size);

        assert((block_idx_end - block_idx_start - 1) * block_size + block_size == (block_idx_end - block_idx_start) * block_size)
            by (nonlinear_arith);
        assert(b@.size == block_size);

        assert((block_idx_end - block_idx_start - 1) * block_size + block_idx_start * block_size == (block_idx_end - 1) * block_size)
            by (nonlinear_arith);

        let tracked mut m =
            split_points_to_raw(a, start, block_size, block_idx_start, block_idx_end - 1);
        let m0 = m;
        m.tracked_insert(block_idx_end - 1, b);

        return m;
    }
}

proof fn points_to_raw_map_to_singleton(tracked m: Map<int, PointsToRaw>, start: int, block_size: int, block_idx_start: int, block_idx_end: int) -> (tracked res: PointsToRaw)
    requires
        forall |i: int| block_idx_start <= i < block_idx_end ==> m.dom().contains(i),
        forall |i: int| block_idx_start <= i < block_idx_end ==> m.index(i)@.size == block_size,
        forall |i: int| block_idx_start <= i < block_idx_end ==> m.index(i)@.pptr == start + i * block_size,
    ensures
        block_idx_end - block_idx_start > 0 ==>
            res@.pptr == start + block_idx_start * block_size &&
            res@.size == (block_idx_end - block_idx_start) * block_size,
        block_idx_start * block_size + (block_idx_end - block_idx_start) * block_size
            == block_idx_end * block_size,
    decreases block_idx_end - block_idx_start,
{
    assert(block_idx_start * block_size + (block_idx_end - block_idx_start) * block_size
            == block_idx_end * block_size) by(nonlinear_arith);

    if block_idx_end <= block_idx_start {
        PointsToRaw::empty()
    } else {
        assert((block_idx_end - block_idx_start - 1) * block_size + block_size == (block_idx_end - block_idx_start) * block_size)
            by (nonlinear_arith);
        assert((block_idx_end - block_idx_start - 1) * block_size + block_idx_start * block_size == (block_idx_end - 1) * block_size)
            by (nonlinear_arith);

        let tracked mut m = m;
        let tracked b = m.tracked_remove(block_idx_end - 1);

        if block_idx_end == block_idx_start + 1 {
            return b;
        }

        let tracked raw = points_to_raw_map_to_singleton(m, start, block_size, block_idx_start, block_idx_end - 1);
        let tracked res = raw.join(b);

        return res;
    }
}

// TODO this would make a good fn for vstd?
/*
proof fn points_to_raw_map_to_singleton(tracked m: Map<int, PointsToRaw>, start: int, block_size: int, n_blocks: int) -> (res: PointsToRaw)
    requires
        forall |i: int| 0 <= i < n_blocks ==> m.dom().contains(i),
        forall |i: int| 0 <= i < n_blocks ==> m.index(i)@.size == block_size,
        forall |i: int| 0 <= i < n_blocks ==> m.index(i)@.pptr == start + i * block_size,
    ensures
        res.pptr == start,
        res.size == n_blocks * block_size,
{
    tracked_from_false()
}
*/

}
