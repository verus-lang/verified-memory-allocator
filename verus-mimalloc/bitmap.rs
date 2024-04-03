#![allow(unused_imports)]

use state_machines_macros::*;
use vstd::prelude::*;
use vstd::ptr::*;
use vstd::*;
use vstd::set_lib::*;
use crate::atomic_ghost_modified::*;

verus!{

/*

type G = crate::os_mem::MemChunk;
type K = int;

pub open spec fn entry_inv(k: K, user_idx: int, g: G) -> bool {
    g.wf()
      && g.os_exact_range(
            k + user_idx * crate::arena::ARENA_BLOCK_SIZE,
            crate::arena::ARENA_BLOCK_SIZE as int
        )
      && g.has_pointsto_for_all_read_write()
}

pub open spec fn map_has_range(m: Map<int, G>, start: int, end: int, k: K) -> bool {
    (forall |i| start <= i < end ==> m.dom().contains(i))
    && (forall |i| start <= i < end ==> entry_inv(k, i, #[trigger] m.index(i)))
}

// field_idx = index into the data array (0 <= field_idx < data.len())
// bit_idx = index of a bit within a word (0 <= bit_idx < usize::BITS)
// user_idx = index of object from user perspective
//      (user_idx = field_idx * usize::BITS + bit_idx)

struct_with_invariants!{
    pub struct Bitmap {
        data: Vec<AtomicUsize<_, Map<int, G>, _>>,
        ghost k: K,
    }

    pub closed spec fn wf(&self) -> bool {
        predicate {
            self.data.len() < 0x1000000
        }

        invariant
            on data
            with (k)
            forall |field_idx: int|
            where (0 <= field_idx < self.data@.len())
            specifically (self.data@.index(field_idx))
            is (v: usize, gmap: Map<int, G>)
        {
            forall |bitidx: int| 
                ! #[trigger] has_bit(v, bitidx)
                ==> gmap.dom().contains(field_idx * usize::BITS + bitidx)
                    && entry_inv(k,
                        field_idx * usize::BITS + bitidx,
                        gmap.index(field_idx * usize::BITS + bitidx))
        }
    }
}

pub closed spec fn has_bit(v: usize, i: int) -> bool {
    (0 <= i < usize::BITS && ((v >> (i as usize)) & 1usize) != 0)
}

impl Bitmap {
    pub closed spec fn len(&self) -> nat {
        self.data@.len()
    }

    pub closed spec fn constant(&self) -> int {
        self.k
    }

    pub fn bitmap_try_find_from_claim_across(&self, start_field_idx: usize, count: usize)
        -> (res: (bool, usize, Tracked<Map<int, G>>))
    requires
        self.wf(),
        0 <= start_field_idx < self.len(),
        ensures ({
            let (success, user_idx, tr_map) = res;
            success ==> {
                &&& map_has_range(tr_map@, user_idx as int, user_idx + count, self.constant())
            }
        }),
    {
        if count == 1 {
            return self.bitmap_try_find_from_claim(start_field_idx, count);
        }

        assume(false); loop { }
    }

    fn bitmap_try_find_from_claim(&self, start_field_idx: usize, count: usize)
        -> (res: (bool, usize, Tracked<Map<int, G>>))
    requires
        self.wf(),
        0 <= start_field_idx < self.data@.len(),
        1 <= count < usize::BITS,
    ensures ({
        let (success, user_idx, tr_map) = res;
        success ==> {
            &&& map_has_range(tr_map@, user_idx as int, user_idx + count, self.constant())
        }
    }),
    {
        let mut idx = start_field_idx;
        let mut visited = 0;
        let bitmap_fields = self.data.len();
        while visited < bitmap_fields
            invariant
                self.wf(),
                0 <= start_field_idx < self.data@.len(),
                1 <= count < usize::BITS,
                visited <= bitmap_fields,
                bitmap_fields == self.data@.len(),
        {
            if idx >= bitmap_fields {
                idx = 0;
            }

            let (success, user_idx, tr_map) =
                self.bitmap_try_find_claim_field(idx, count);
            if success {
                return (true, user_idx, tr_map);
            }

            visited = visited + 1;
            idx = idx + 1;
        }

        return (false, 0, Tracked(Map::tracked_empty()));
    }

    fn bitmap_try_find_claim_field(&self, field_idx: usize, count: usize)
        -> (res: (bool, usize, Tracked<Map<int, G>>))
    requires
        self.wf(),
        0 <= field_idx < self.data@.len(),
        1 <= count < usize::BITS,
    ensures ({
        let (success, user_idx, tr_map) = res;
        success ==> {
            &&& usize::BITS * field_idx <= user_idx
            &&& user_idx + count <= usize::BITS * (field_idx + 1)
            &&& map_has_range(tr_map@, user_idx as int, user_idx + count, self.constant())
        }
    }),
    {
        let atomic = &self.data[field_idx];

        let mut map = atomic.load();
        if map == !(0usize) {
            return (false, 0, Tracked(Map::tracked_empty()));
        }

        assert((1usize << count) >= 1usize) by(bit_vector)
            requires count < 64usize { }

        let mask = (1usize << count) - 1;
        let bitidx_max = usize::BITS as usize - count;

        let mut bitidx = crate::bin_sizes::trailing_zeros(map) as usize;
        let mut m = mask << bitidx;

        while bitidx <= bitidx_max
            invariant
                self.wf(),
                atomic == self.data@.index(field_idx as int),
                0 <= field_idx < self.data@.len(),
                1 <= count <= usize::BITS,
                bitidx_max == usize::BITS - count,
                m == mask << bitidx,
                mask == (1usize << count) - 1,
        {
            let mapm = map & m;
            if mapm == 0 {
                let tracked mut res_map: Map<int, G>;
                proof { res_map = Map::tracked_empty(); }

                let newmap = map | m;
                let res = my_atomic_with_ghost!(
                    atomic => compare_exchange_weak(map, newmap);
                    update old_v -> new_v;
                    returning res;
                    ghost gmap =>
                {
                    if res.is_Ok() {
                        let range = set_int_range(
                            usize::BITS * field_idx + bitidx,
                            usize::BITS * field_idx + bitidx + count);

                        verus_proof_expr!({
                        assert forall |i| range.contains(i) implies #[trigger] gmap.dom().contains(i)
                        by {
                            assume(!has_bit(old_v, i - usize::BITS * field_idx));
                        }
                        });

                        res_map = gmap.tracked_remove_keys(range);

                        assume(bitidx + count < usize::BITS);

                        let bit = bitidx;

                        verus_proof_expr!({
                        assert forall |bitidx0: int| 
                            ! #[trigger] has_bit(new_v, bitidx0)
                            implies gmap.dom().contains(field_idx * usize::BITS + bitidx0)
                                && entry_inv(self.k,
                                    field_idx * usize::BITS + bitidx0,
                                    gmap.index(field_idx * usize::BITS + bitidx0))
                        by {
                            assert(m == sub(1usize << count,  1) << bitidx);
                            assert(new_v == old_v | m);
                            assert(old_v & m == 0);

                            if bitidx <= bitidx0 < bitidx + count {
                                let bi = bitidx0 as usize;

                                assert(((new_v >> bi) & 1usize) != 0usize)
                                  by(bit_vector)
                                requires
                                  bitidx <= bi < add(bitidx, count) < 64usize,
                                  new_v == old_v | m,
                                  m == sub(1usize << count, 1) << bitidx,
                                  old_v & m == 0usize,
                                  1usize <= count <= (64usize)
                                { }

                                assert(false);
                            } else {
                                if bitidx0 >= usize::BITS || bitidx0 < 0 {
                                    assert(!has_bit(old_v, bitidx0));
                                } else {
                                    let bi = bitidx0 as usize;
                                    assert(add(bitidx, count) == bitidx + count);

                                    if bit > bi {
                                        assert(((new_v >> bi) & 1usize) == ((old_v >> bi) & 1usize))
                                          by(bit_vector)
                                        requires
                                          bitidx > bi,
                                          add(bitidx, count) <= 64usize,
                                          bitidx <= 64usize,
                                          count <= 64usize,
                                          new_v == old_v | (sub(1usize << count, 1) << bitidx),
                                          1usize <= count <= (64usize)
                                        { }
                                    } else {
                                        assert(((new_v >> bi) & 1usize) == ((old_v >> bi) & 1usize))
                                          by(bit_vector)
                                        requires
                                          bi >= add(bitidx, count),
                                          add(bitidx, count) <= 64usize,
                                          bitidx <= 64usize,
                                          count <= 64usize,
                                          new_v == old_v | (sub(1usize << count, 1) << bitidx),
                                          1usize <= count <= (64usize)
                                        { }
                                    }
                                    assert(!has_bit(old_v, bitidx0));
                                }
                            }
                        }
                        });
                    }
                });

                match res {
                    Result::Ok(_) => {
                        let user_idx = usize::BITS as usize * field_idx + bitidx;
                        return (true, user_idx, Tracked(res_map));
                    }
                    Result::Err(updated_map) => {
                        map = updated_map;
                    }
                }
            } else {
                let shift = if count == 1 {
                    1
                } else {
                    let tz = crate::bin_sizes::trailing_zeros(mapm) as usize;
                    assume(tz + 1 >= bitidx);
                    tz + 1 - bitidx
                };

                assert(((mask << bitidx) << shift) == mask << add(bitidx, shift))
                  by(bit_vector)
                    requires
                        bitidx <= 64usize,
                        shift <= 64usize,
                        add(bitidx, shift) <= 64usize,
                    { }

                bitidx = bitidx + shift;
                m = m << shift;

            }
        }

        return (false, 0, Tracked(Map::tracked_empty()));
    }
        

    //pub bitmap_try_find_claim_field_across(&self, idx: usize, 
}

*/

}
