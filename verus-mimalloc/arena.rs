#![allow(unused_imports)]

use state_machines_macros::*;
use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::*;
use vstd::set_lib::*;

use crate::os_mem::*;
use crate::os_alloc::*;
use crate::bitmap::*;
use crate::config::*;
use crate::types::*;

verus!{

pub type ArenaId = usize;
pub type MemId = usize;

pub fn arena_alloc_aligned(
    size: usize,
    alignment: usize,
    align_offset: usize,
    request_commit: bool,
    allow_large: bool,
    req_arena_id: ArenaId,
) -> (res: (*mut u8, Tracked<MemChunk>, bool, bool, bool, bool, usize))
    requires
        alignment as int % page_size() == 0,
        size as int % page_size() == 0,
        alignment + page_size() <= usize::MAX,
        size == SEGMENT_SIZE,
    ensures ({
        let (addr, mem, commit, large, is_pinned, is_zero, mem_id) = res;
        let addr = addr as int;
        addr != 0 ==> (
          mem@.wf()
            && mem@.os_exact_range(addr as int, size as int)
            && addr + size <= usize::MAX
            && (request_commit ==> commit)
            && (commit ==> mem@.os_has_range_read_write(addr as int, size as int))
            && (commit ==> mem@.pointsto_has_range(addr as int, size as int))
            && mem@.has_pointsto_for_all_read_write()

            && (alignment != 0 ==> (addr as int + align_offset as int) % alignment as int == 0)
        )
    })
    // commit: bool
    // large: bool
    // is_pinned: bool
    // is_zero: bool
    // mem_id: usize
{
    // TODO arena allocation
    let (p, is_large, Tracked(mem)) = os_alloc_aligned_offset(size, alignment, align_offset, request_commit, allow_large);
    let did_commit = request_commit;
    let is_pinned = is_large;
    let is_zero = true;
    let memid_os = 0;
    proof {
        if p as int != 0 {
            mem.os_restrict(p as int, size as int);
        }
    }
    (p, Tracked(mem), did_commit, is_large, is_pinned, is_zero, memid_os)
}

/*

pub const ARENA_BLOCK_SIZE: usize = SEGMENT_SIZE as usize;

pub struct Arena {
    start: PPtr<u8>,
    bitmap: Bitmap,
}

impl Arena {
    pub closed spec fn wf(&self) -> bool {
        &&& self.bitmap.wf()
        &&& self.bitmap.constant() == self.start.id()
        &&& self.bitmap.len() >= 1
    }

/*
    // TODO mimalloc's actual segment allocation is much more complicated
    pub fn arena_alloc_segment(&self) -> (res: (PPtr<u8>, Tracked<PointsToRaw>))
        requires self.wf(),
        ensures ({
            let (ptr, points_to_raw) = res;
            ptr.id() != 0 ==> (
                points_to_raw@@.pptr == ptr.id()
                && points_to_raw@@.size == ARENA_BLOCK_SIZE
            )
        })
    {
        let (success, idx, tr_map) = self.bitmap.bitmap_try_find_from_claim_across(0, 1);
        if success {
            let tracked points_to_raw;
            proof {
                points_to_raw = points_to_raw_map_to_singleton(
                    tr_map.get(), self.start.id(), ARENA_BLOCK_SIZE as int,
                    idx as int, idx as int + 1);
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
    */
}

proof fn points_to_raw_map_to_singleton(tracked m: Map<int, PointsToRaw>, start: int, block_size: int, block_idx_start: int, block_idx_end: int) -> (tracked res: PointsToRaw)
    requires
        forall |i: int| block_idx_start <= i < block_idx_end ==> m.dom().contains(i),
        forall |i: int| block_idx_start <= i < block_idx_end ==> m.index(i)@.size == block_size,
        forall |i: int| block_idx_start <= i < block_idx_end ==> m.index(i)@.pptr == start + i * block_size,
    ensures
        res@.pptr == start + block_idx_start * block_size,
        res@.size == (block_idx_end - block_idx_start) * block_size,
        block_idx_start * block_size + (block_idx_end - block_idx_start) * block_size
            == block_idx_end * block_size,
{
    assume(false);
    proof_from_false()
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

//fn arena_alloc_aligned(
//    size: usize,
//    alignment: usize,
//    align_offset: usize,

*/

}
