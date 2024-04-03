#![allow(unused_imports)]

use state_machines_macros::*;
use vstd::prelude::*;
use vstd::ptr::*;
use vstd::*;
use vstd::thread::*;
use vstd::vec::*;
use vstd::set_lib::*;
use vstd::atomic_ghost::*;
use vstd::invariant::*;

use crate::bit_support::*;

verus!{

type G = PointsToRaw;
type K = int;

pub open spec fn entry_inv(k: K, user_idx: int, g: G) -> bool {
    g@.pptr == k + user_idx * crate::arena::ARENA_BLOCK_SIZE
    && g@.size == crate::arena::ARENA_BLOCK_SIZE as int
}

pub open spec fn map_has_range(m: Map<int, G>, start: int, end: int, k: K) -> bool {
    (forall |i| start <= i < end ==> m.dom().contains(i))
    && (forall |i| start <= i < end ==> entry_inv(k, i, #[trigger] m.index(i)))
}

pub open spec fn map_has_range_only(m: Map<int, G>, start: int, end: int, k: K) -> bool {
    (forall |i| start <= i < end <==> m.dom().contains(i))
    && (forall |i| start <= i < end ==> entry_inv(k, i, #[trigger] m.index(i)))
}

// field_idx = index into the data array (0 <= field_idx < data.len())
// bit_idx = index of a bit within a word (0 <= bit_idx < usize::BITS)
// user_idx = index of object from user perspective
//      (user_idx = field_idx * usize::BITS + bit_idx)

struct_with_invariants!{
    pub struct Bitmap {
        data: Vec<AtomicUsize<_, Map<int, G>, _>>,
        k: Ghost<K>,
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
                (0 <= bitidx < usize::BITS) &&
                ! #[trigger] has_bit(v, bitidx)
                ==> gmap.dom().contains(field_idx * usize::BITS + bitidx)
                    && entry_inv(k@,
                        field_idx * usize::BITS + bitidx,
                        gmap.index(field_idx * usize::BITS + bitidx))
        }
    }
}

pub closed spec fn has_bit(v: usize, i: int) -> bool {
    (0 <= i < usize::BITS && ((v >> (i as usize)) & 1usize) != 0)
}

impl Bitmap {
    pub closed spec fn data_len(&self) -> nat {
        self.data@.len()
    }

    pub closed spec fn user_len(&self) -> nat {
        (self.data@.len() * usize::BITS) as nat
    }

    pub closed spec fn constant(&self) -> int {
        self.k@
    }

    pub fn get_user_len(&self) -> (l: usize)
        requires self.wf(),
        ensures l == self.user_len(),
    {
        self.data.len() * (usize::BITS as usize)
    }

    pub fn new(user_len: usize, Ghost(k): Ghost<K>, Tracked(contents): Tracked<Map<int, G>>)
        -> (bitmap: Bitmap)
    requires
        (user_len as int) % (usize::BITS as int) == 0,
        user_len < 0x4000_0000,
        map_has_range(contents, 0, user_len as int, k),
    ensures
        bitmap.wf(),
        bitmap.user_len() == user_len,
        bitmap.user_len() == bitmap.data_len() * usize::BITS,
        bitmap.constant() == k,
    {
        let mut data: Vec<AtomicUsize<_, _, _>> = Vec::new();
        let data_len = user_len / (usize::BITS as usize);

        let tracked mut contents = contents;

        let mut i = 0;
        while i < data_len
            invariant 0 <= i <= data_len,
                data@.len() == i,
                forall |j: int| 0 <= j < i ==> data@.index(j).well_formed(),
                forall |j: int| 0 <= j < i ==> equal(data@.index(j).constant(), (Ghost(k), j as int)),
                map_has_range(contents, i * usize::BITS, user_len as int, k),
                user_len == data_len * usize::BITS,
        {
            let ghost range = Set::new(|j: int|
                i * usize::BITS <= j < (i + 1) * usize::BITS);
            let tracked this_map = contents.tracked_remove_keys(range);

            proof {
                let field_idx = i as int;
                assert forall |bitidx: int| 
                    (0 <= bitidx < usize::BITS) &&
                    ! #[trigger] has_bit(0, bitidx)
                    implies this_map.dom().contains(field_idx * usize::BITS + bitidx)
                        && entry_inv(k,
                            field_idx * usize::BITS + bitidx,
                            this_map.index(field_idx * usize::BITS + bitidx))
                by {
                    assert(i * usize::BITS <= field_idx * usize::BITS + bitidx);
                    assert(field_idx * usize::BITS + bitidx < (i + 1) * usize::BITS);
                    assert(this_map.dom().contains(field_idx * usize::BITS + bitidx));
                    assert(entry_inv(k,
                            field_idx * usize::BITS + bitidx,
                            this_map.index(field_idx * usize::BITS + bitidx)));
                }
            }

            let ato = AtomicUsize::new(
                Ghost((Ghost(k), i as int)),
                0,
                Tracked(this_map));
            data.push(ato);

            i = i + 1;
        }

        Bitmap { data, k: Ghost(k) }
    }


    pub fn bitmap_try_find_from_claim_across(&self, start_field_idx: usize, count: usize)
        -> (res: (bool, usize, Tracked<Map<int, G>>))
    requires
        self.wf(),
        0 <= start_field_idx < self.data_len(),
        1 <= count <= self.user_len(),
    ensures ({
        let (success, user_idx, tr_map) = res;
        success ==> {
            &&& map_has_range(tr_map@, user_idx as int, user_idx + count, self.constant())
            &&& user_idx + count <= self.user_len()
        }
    }),
    {
        if count == 1 {
            return self.bitmap_try_find_from_claim(start_field_idx, count);
        }

        let mut idx = start_field_idx;
        let mut visited = 0;
        let len = self.data.len();
        while visited < len
            invariant
                self.wf(),
                len == self.data@.len(),
                1 <= count <= self.user_len(),
        {
            if idx >= len {
                idx = 0;
            }

            if count <= usize::BITS as usize {
                let (succ, user_idx, Tracked(m)) =
                    self.bitmap_try_find_claim_field(idx, count);
                if succ {
                    return (succ, user_idx, Tracked(m));
                }
            }

            let (succ, user_idx, Tracked(m)) =
                self.bitmap_try_find_claim_field_across(idx, count, 0);
            if succ {
                return (succ, user_idx, Tracked(m));
            }

            visited = visited + 1;
            idx = idx + 1;
        }
        return (false, 0, Tracked(Map::tracked_empty()));
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
            &&& user_idx + count <= self.user_len()
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
        1 <= count <= usize::BITS,
    ensures ({
        let (success, user_idx, tr_map) = res;
        success ==> {
            &&& usize::BITS * field_idx <= user_idx
            &&& user_idx + count <= usize::BITS * (field_idx + 1)
            &&& map_has_range(tr_map@, user_idx as int, user_idx + count, self.constant())
        }
    }),
    {
        let atomic = self.data.index(field_idx);

        let mut map = atomic_with_ghost!(atomic => load(); ghost g => { });
        if map == !(0usize) {
            return (false, 0, Tracked(Map::tracked_empty()));
        }

        let mask = if count == usize::BITS as usize {
            !0usize
        } else {
            assert((1usize << count) >= 1usize) by(bit_vector)
                requires count < 64usize { }
            (1usize << count) - 1
        };

        let bitidx_max = usize::BITS as usize - count;

        let mut bitidx = trailing_zeros(map) as usize;
        let mut m = mask << bitidx;

        while bitidx <= bitidx_max
            invariant
                self.wf(),
                atomic == self.data@.index(field_idx as int),
                0 <= field_idx < self.data@.len(),
                1 <= count <= usize::BITS,
                bitidx_max == usize::BITS - count,
                m == mask << bitidx,
                count == 64usize ==> mask == !0usize,
                count != 64usize ==> mask == sub(1usize << count, 1usize),
        {
            let mapm = map & m;
            if mapm == 0 {
                let tracked mut res_map: Map<int, G>;
                proof { res_map = Map::tracked_empty(); }

                let newmap = map | m;
                let res = atomic_with_ghost!(
                    atomic => compare_exchange_weak(map, newmap);
                    update old_v -> new_v;
                    returning res;
                    ghost gmap =>
                {
                    if res.is_Ok() {
                        let range = set_int_range(
                            usize::BITS * field_idx + bitidx,
                            usize::BITS * field_idx + bitidx + count);

                        assert forall |i| range.contains(i) implies #[trigger] gmap.dom().contains(i) && entry_inv(self.constant(), i, gmap.index(i))
                        by {
                            let bitidx1 = i - usize::BITS * field_idx;

                            let b0 = bitidx as usize;
                            let b1 = bitidx1 as usize;
                            assert(((map >> b1) & 1usize) == 0usize) by(bit_vector)
                              requires
                                0usize <= b0 < 64usize,
                                0usize <= b1 < 64usize,
                                b0 <= b1,
                                b1 < add(b0, count),
                                map & m == 0usize,
                                m == mask << b0,
                                count == 64usize ==> mask == !0usize,
                                count != 64usize ==> mask == sub(1usize << count, 1usize),
                                1usize <= count <= 64usize
                            {}

                            assert(!has_bit(old_v, bitidx1));
                            assert(field_idx * usize::BITS + bitidx1 == i);
                        }

                        res_map = gmap.tracked_remove_keys(range);

                        let bit = bitidx;

                        assert forall |bitidx0: int| 
                            (0 <= bitidx0 < usize::BITS) &&
                            ! #[trigger] has_bit(new_v, bitidx0)
                            implies gmap.dom().contains(field_idx * usize::BITS + bitidx0)
                                && entry_inv(self.k@,
                                    field_idx * usize::BITS + bitidx0,
                                    gmap.index(field_idx * usize::BITS + bitidx0))
                        by {
                            assert(new_v == old_v | m);
                            assert(old_v & m == 0);

                            if bitidx <= bitidx0 < bitidx + count {
                                let bi = bitidx0 as usize;

                                assert(((new_v >> bi) & 1usize) != 0usize)
                                  by(bit_vector)
                                requires
                                  bitidx <= bi < add(bitidx, count) <= 64usize,
                                  new_v == old_v | m,
                                  count == 64usize ==> m == (!0usize) << 0,
                                  count != 64usize ==> m == sub(1usize << count, 1) << bitidx,
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
                    }
                });

                match res {
                    Result::Ok(_) => {
                        let user_idx = usize::BITS as usize * field_idx + bitidx;

                        proof {
                            let success = true;
                            assert(usize::BITS * field_idx <= user_idx);
                            assert(user_idx + count <= usize::BITS * (field_idx + 1));
                            let m = res_map;
                            let start = user_idx as int;
                            let end = user_idx + count;
                            let k = self.constant();
                            assert(forall |i| start <= i < end ==> m.dom().contains(i));
                            assert forall |i| start <= i < end implies entry_inv(k, i, #[trigger] m.index(i))
                            by {
                                assert(m.dom().contains(i));
                            }
                            assert(map_has_range(res_map, user_idx as int, user_idx + count, self.constant()));
                        }

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
                    let tz = trailing_zeros(mapm) as usize;
                    proof {
                        assert (add(tz, 1) >= bitidx) by (bit_vector)
                            requires 0usize <= tz <= 64usize,
                                0usize <= bitidx <= 64usize,
                                mapm == map & (mask << bitidx),
                                tz != 64usize ==>
                                    ((mapm >> tz) & 1usize) != 0usize
                        {}
                    }
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
       
    fn bitmap_try_find_claim_field_across(
        &self,
        field_idx: usize, 
        count: usize,
        retries: usize)
      -> (res: (bool, usize, Tracked<Map<int, G>>))
    requires
        self.wf(),
        0 <= field_idx < self.data@.len(),
        1 <= count <= self.user_len(),
    ensures ({
        let (success, user_idx, tr_map) = res;
        success ==> {
            &&& usize::BITS * field_idx <= user_idx
            &&& user_idx + count <= self.user_len()
            &&& map_has_range(tr_map@, user_idx as int, user_idx + count, self.constant())
        }
    }),
    {
        let atomic = self.data.index(field_idx);
        let map = atomic_with_ghost!(atomic => load(); ghost g => { });

        let initial = leading_zeros(map) as usize;
        assert(initial <= usize::BITS);

        if initial == 0 {
            return (false, 0, Tracked(Map::tracked_empty()));
        }

        if initial >= count {
            return self.bitmap_try_find_claim_field(field_idx, count);
        }

        let entries_needed = (count - initial + (usize::BITS as usize) - 1) / (usize::BITS as usize);
        if entries_needed >= self.data.len() - field_idx {
            return (false, 0, Tracked(Map::tracked_empty()));
        }

        // scan ahead

        let mut found = initial;
        let mut mask_bits = 0;
        let mut cur_field = field_idx;
        while found < count
            invariant
                self.wf(),
                0 <= field_idx < self.data@.len(),
                count <= self.user_len(),
                field_idx <= cur_field,
                (count - initial + (usize::BITS as usize) - 1) / (usize::BITS as int)
                    < self.data@.len() - field_idx,
                found < count ==>
                    found == initial + usize::BITS * (cur_field - field_idx),
                found <= count,
                found == count ==>
                    1 <= mask_bits <= usize::BITS,
                found == count ==>
                    found == initial + usize::BITS * (cur_field - field_idx - 1) + mask_bits,
        {
            cur_field = cur_field + 1;

            let atomic = self.data.index(cur_field);
            let map = atomic_with_ghost!(atomic => load(); ghost g => { });

            mask_bits = if found + (usize::BITS as usize) <= count { usize::BITS as usize } else { count - found };

            let mask = if mask_bits == usize::BITS as usize {
                !0usize
            } else {
                assert((1usize << mask_bits) >= 1usize) by(bit_vector)
                    requires mask_bits < 64usize { }

                (1usize << mask_bits) - 1
            };

            if (map & mask) != 0 {
                return (false, 0, Tracked(Map::tracked_empty()));
            }

            found = found + mask_bits;
        }

        let final_field = cur_field;
        let final_mask_bits = mask_bits;

        assert(final_field * usize::BITS + final_mask_bits
            == field_idx * usize::BITS + (usize::BITS as int - initial) + count);
        assert(final_field < self.data@.len());

        // initial field 

        let (succ, Tracked(first_map)) = self.try_fixed_range(
            field_idx, usize::BITS as usize - initial, initial);

        if !succ {
            if retries < 4 {
                return self.bitmap_try_find_claim_field_across(field_idx, count, retries + 1);
            } else {
                return (false, 0, Tracked(Map::tracked_empty()));
            }
        }

        let tracked mut full_map = first_map;
        let mut field = field_idx + 1;
        let ghost user_idx = field_idx * (usize::BITS as usize) + (usize::BITS as usize) - initial;
        while field < final_field
            invariant
                self.wf(),
                field <= final_field,
                0 <= field_idx < self.data@.len(),
                1 <= count <= self.user_len(),
                final_field < self.data@.len(),
                0 <= initial <= usize::BITS,
                user_idx == field_idx * (usize::BITS as usize) + (usize::BITS as usize) - initial,
                user_idx < field * usize::BITS,
                map_has_range_only(full_map, user_idx, field * usize::BITS, self.constant()),
        {
            let (succ, Tracked(mid_map)) = self.try_fixed_range_full(field);

            if !succ {
                let user_idx = field_idx * (usize::BITS as usize) + (usize::BITS as usize) - initial;
                let uc_count = field * (usize::BITS as usize) - user_idx;
                self.bitmap_unclaim_range(user_idx, uc_count, Tracked(full_map));

                if retries < 4 {
                    return self.bitmap_try_find_claim_field_across(field_idx, count, retries + 1);
                } else {
                    return (false, 0, Tracked(Map::tracked_empty()));
                }
            }

            proof {
                let m0 = full_map;
                full_map.tracked_union_prefer_right(mid_map);
                let start = user_idx;
                let end = (field + 1) * usize::BITS;
                assert forall |i| start <= i < end implies full_map.dom().contains(i)
                by {
                }
                assert forall |i| start <= i < end implies entry_inv(self.constant(), i, #[trigger] full_map.index(i))
                by {
                    assert(full_map.dom().contains(i));
                    assert(entry_inv(self.constant(), i, m0.index(i))
                        || entry_inv(self.constant(), i, full_map.index(i)));
                }
            }

            field = field + 1;
        }

        // final field

        let (succ, Tracked(final_map)) = self.try_fixed_range(
            final_field, 0, final_mask_bits);

        if !succ {
            let user_idx = field_idx * (usize::BITS as usize) + (usize::BITS as usize) - initial;
            let uc_count = field * (usize::BITS as usize) - user_idx;
            self.bitmap_unclaim_range(user_idx, uc_count, Tracked(full_map));

            if retries < 4 {
                return self.bitmap_try_find_claim_field_across(field_idx, count, retries + 1);
            } else {
                return (false, 0, Tracked(Map::tracked_empty()));
            }
        }

        proof {
            full_map.tracked_union_prefer_right(final_map);
            //let user_idx = field_idx * (usize::BITS as usize) + (usize::BITS as usize) - initial;
            //let tr_map = full_map;
            //assert(usize::BITS * field_idx <= user_idx);
            //assert(map_has_range(tr_map, user_idx as int, user_idx + count, self.constant()));
        }

        (true, field_idx * (usize::BITS as usize) + (usize::BITS as usize) - initial, Tracked(full_map))
    }

    #[inline(always)]
    fn try_fixed_range(
        &self,
        field_idx: usize,
        bitidx: usize,
        count: usize
    ) -> (res: (bool, Tracked<Map<int, G>>))
        requires 
            self.wf(),
            0 <= field_idx < self.data@.len(),
            0 <= bitidx < usize::BITS,
            1 <= count,
            0 <= bitidx + count <= usize::BITS,
        ensures ({
            let (success, tr_map) = res;
            let user_idx = field_idx * usize::BITS + bitidx;
            success ==> {
                &&& map_has_range_only(tr_map@, user_idx as int, user_idx + count, self.constant())
            }
        }),
    {
        let atomic = self.data.index(field_idx);

        loop
            invariant
                self.wf(),
                0 <= field_idx < self.data@.len(),
                0 <= bitidx < usize::BITS,
                1 <= count,
                0 <= bitidx + count <= usize::BITS,
                *atomic == self.data@[field_idx as int],
        {
            let mask = if count == usize::BITS as usize {
                !0usize
            } else {
                assert((1usize << count) >= 1usize) by (bit_vector)
                    requires 0usize <= count < 64usize { }

                ((1usize << count) - 1) << bitidx
            };

            let map = atomic_with_ghost!(atomic => load(); ghost g => { });

            if (map & mask) != 0 {
                return (false, Tracked(Map::tracked_empty()));
            }

            let newmap = map | mask;

            let tracked res_map;

            let res = atomic_with_ghost!(
                atomic => compare_exchange_weak(map, newmap);
                update old_v -> new_v;
                returning res;
                ghost gmap =>
            {
                if res.is_Ok() {
                    let range = set_int_range(
                        usize::BITS * field_idx + bitidx,
                        usize::BITS * field_idx + bitidx + count);

                    assert forall |i| range.contains(i) implies #[trigger] gmap.dom().contains(i) && entry_inv(self.constant(), i, gmap.index(i))
                    by {
                        let bitidx1 = i - usize::BITS * field_idx;

                        let b0 = bitidx as usize;
                        let b1 = bitidx1 as usize;
                        assert(((map >> b1) & 1usize) == 0usize) by(bit_vector)
                          requires
                            0usize <= b0 < 64usize,
                            0usize <= b1 < 64usize,
                            b0 <= b1,
                            b1 < add(b0, count),
                            map & mask == 0usize,
                            count == 64usize ==> mask == !0usize,
                            count != 64usize ==>
                                mask == sub(1usize << count, 1usize) << b0,
                            1usize <= count <= 64usize
                        {}

                        assert(!has_bit(old_v, bitidx1));
                        assert(field_idx * usize::BITS + bitidx1 == i);
                    }

                    res_map = gmap.tracked_remove_keys(range);

                    let bit = bitidx;

                    assert forall |bitidx0: int| 
                        (0 <= bitidx0 < usize::BITS) &&
                        ! #[trigger] has_bit(new_v, bitidx0)
                        implies gmap.dom().contains(field_idx * usize::BITS + bitidx0)
                            && entry_inv(self.k@,
                                field_idx * usize::BITS + bitidx0,
                                gmap.index(field_idx * usize::BITS + bitidx0))
                    by {
                        if bitidx <= bitidx0 < bitidx + count {
                            let bi = bitidx0 as usize;

                            assert(((new_v >> bi) & 1usize) != 0usize)
                              by(bit_vector)
                            requires
                              bitidx <= bi < add(bitidx, count) <= 64usize,
                              new_v == old_v | mask,
                              count == 64usize ==> mask == !0usize,
                              count != 64usize ==>
                                  mask == sub(1usize << count, 1usize) << bitidx,
                              old_v & mask == 0usize,
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
                }
            });

            match res {
                Result::Ok(_) => {
                    proof {
                        let user_idx = field_idx * usize::BITS + bitidx;
                        assert(usize::BITS * field_idx <= user_idx);
                        assert(user_idx + count <= usize::BITS * (field_idx + 1));
                        let m = res_map;
                        let start = user_idx as int;
                        let end = user_idx + count;
                        let k = self.constant();
                        assert(forall |i| start <= i < end ==> m.dom().contains(i));
                        assert forall |i| start <= i < end implies entry_inv(k, i, #[trigger] m.index(i))
                        by {
                            assert(m.dom().contains(i));
                        }
                        assert(map_has_range(res_map, user_idx as int, user_idx + count, self.constant()));
                    }

                    return (true, Tracked(res_map))                
                }
                Result::Err(_) => { }
            }
        }
    }

    #[inline(always)]
    fn try_fixed_range_full(
        &self,
        field_idx: usize,
    ) -> (res: (bool, Tracked<Map<int, G>>))
        requires 
            self.wf(),
            0 <= field_idx < self.data@.len(),
        ensures ({
            let (success, tr_map) = res;
            let user_idx = field_idx * usize::BITS;
            let count = usize::BITS as int;
            success ==> {
                &&& map_has_range_only(tr_map@, user_idx as int, user_idx + count, self.constant())
            }
        }),
    {
        let atomic = self.data.index(field_idx);

        let tracked res_map;

        let res = atomic_with_ghost!(
            atomic => compare_exchange_weak(0usize, !0usize);
            update old_v -> new_v;
            returning res;
            ghost gmap =>
        {
            if res.is_Ok() {
                let range = set_int_range(
                    usize::BITS * field_idx,
                    usize::BITS * field_idx + usize::BITS);

                assert forall |i| range.contains(i) implies #[trigger] gmap.dom().contains(i) && entry_inv(self.constant(), i, gmap.index(i))
                by {
                    let bitidx1 = i - usize::BITS * field_idx;

                    let b1 = bitidx1 as usize;
                    assert(((0usize >> b1) & 1usize) == 0usize) by(bit_vector);

                    assert(!has_bit(old_v, bitidx1));
                    assert(field_idx * usize::BITS + bitidx1 == i);
                }

                res_map = gmap.tracked_remove_keys(range);

                assert forall |bitidx0: int| 
                    (0 <= bitidx0 < usize::BITS) &&
                    ! #[trigger] has_bit(new_v, bitidx0)
                    implies gmap.dom().contains(field_idx * usize::BITS + bitidx0)
                        && entry_inv(self.k@,
                            field_idx * usize::BITS + bitidx0,
                            gmap.index(field_idx * usize::BITS + bitidx0))
                by {
                    let bi = bitidx0 as usize;

                    assert((((!0usize) >> bi) & 1usize) != 0usize) by(bit_vector)
                    requires 0usize <= bi < 64usize,
                    { }

                    assert(false);
                }
            }
        });

        match res {
            Result::Ok(_) => {
                proof {
                    let user_idx = field_idx * usize::BITS;
                    assert(usize::BITS * field_idx <= user_idx);
                    assert(user_idx + usize::BITS <= usize::BITS * (field_idx + 1));
                    let m = res_map;
                    let start = user_idx as int;
                    let end = user_idx + usize::BITS;
                    let k = self.constant();
                    assert(forall |i| start <= i < end ==> m.dom().contains(i));
                    assert forall |i| start <= i < end implies entry_inv(k, i, #[trigger] m.index(i))
                    by {
                        assert(m.dom().contains(i));
                    }
                    assert(map_has_range(res_map, user_idx as int, user_idx + usize::BITS, self.constant()));
                }

                return (true, Tracked(res_map))                
            }
            Result::Err(_) => {
                return (false, Tracked(Map::tracked_empty()))                
            }
        }
    }


    fn bitmap_unclaim_field(
        &self,
        field_idx: usize,
        bitidx: usize,
        count: usize,
        Tracked(g): Tracked<Map<int, G>>
    )
        requires self.wf(),
            map_has_range_only(g,
                field_idx * usize::BITS + bitidx,
                field_idx * usize::BITS + bitidx + count,
                self.constant()),
            0 < count,
            0 <= field_idx < self.data@.len(),
            0 <= bitidx,
            bitidx + count <= usize::BITS,
    {
        let atomic = self.data.index(field_idx);

        let m = if count == usize::BITS as usize {
            // special case because shifting by usize::BITS would be an overflow
            0usize
        } else {
            assert((1usize << count) >= 1usize) by (bit_vector)
                requires 0usize <= count < 64usize { }
            
            !(((1usize << count) - 1) << bitidx)
        };

        atomic_with_ghost!(
            atomic => fetch_and(m);
            update old_v -> new_v;
            returning res;
            ghost gmap =>
        {
            let ghost gmap_old = gmap;
            gmap.tracked_union_prefer_right(g);

            assert forall |bitidx0: int| 
                (0 <= bitidx0 < usize::BITS) &&
                ! #[trigger] has_bit(new_v, bitidx0)
                implies gmap.dom().contains(field_idx * usize::BITS + bitidx0)
                    && entry_inv(self.constant(),
                        field_idx * usize::BITS + bitidx0,
                        gmap.index(field_idx * usize::BITS + bitidx0))
            by {
                let b0 = bitidx0 as usize;
                assert(
                    (bitidx <= b0 < add(bitidx, count))
                      || (((old_v >> (b0 as usize)) & 1usize) == 0usize)) by (bit_vector)
                requires
                    (0usize <= b0 < 64usize),
                    0usize <= bitidx <= 64usize,
                    1usize <= count <= 64usize,
                    add(bitidx, count) <= 64usize,
                    new_v == old_v & m,
                    m == (if count == 64usize {
                        0usize
                    } else {
                        !(sub(1usize << count, 1) << bitidx)
                    }),
                    (((new_v >> (b0 as usize)) & 1usize) == 0usize)
                { }
                
                let j = field_idx * usize::BITS + bitidx0;
                if bitidx <= b0 < bitidx + count {
                    assert(gmap.dom().contains(j));
                    assert(entry_inv(self.constant(), j, gmap.index(j)));
                } else {
                    assert(!has_bit(old_v, bitidx0));
                    assert(gmap.dom().contains(j));
                    assert(entry_inv(self.constant(), j, gmap_old.index(j)));
                    assert(gmap_old.index(j) == gmap.index(j));
                    assert(entry_inv(self.constant(), j, gmap.index(j)));
                }
            }
        });
    }

    pub fn bitmap_unclaim_range(
        &self,
        user_idx: usize,
        count: usize,
        Tracked(g): Tracked<Map<int, G>>
    )
        requires self.wf(),
            map_has_range_only(g,
                user_idx as int,
                user_idx + count,
                self.constant()),
            0 <= user_idx,
            user_idx + count <= self.user_len(),
    {
        let field_idx1 = user_idx / usize::BITS as usize;
        let bit_idx1 = user_idx % usize::BITS as usize;

        let field_idx2 = (user_idx + count) / usize::BITS as usize;
        let bit_idx2 = (user_idx + count) % usize::BITS as usize;

        if field_idx2 == field_idx1 {
            if count > 0 {
                self.bitmap_unclaim_field(field_idx1, bit_idx1, count, Tracked(g));
            }
        } else {
            let tracked mut g = g;

            let ghost range_first = set_int_range(
                user_idx as int,
                user_idx + usize::BITS - bit_idx1);
            let tracked g_first = g.tracked_remove_keys(range_first);
            self.bitmap_unclaim_field(field_idx1, bit_idx1,
                usize::BITS as usize - bit_idx1, Tracked(g_first));

            let mut i = field_idx1 + 1;
            while i < field_idx2
                invariant
                    self.wf(),
                    field_idx1 < i <= field_idx2,
                    field_idx2 * usize::BITS <= user_idx + count,
                    map_has_range_only(g,
                        i * usize::BITS,
                        user_idx + count,
                        self.constant()),
                    0 <= user_idx,
                    user_idx + count <= self.user_len(),
            {
                let ghost range_mid = set_int_range(i * usize::BITS, (i+1) * usize::BITS);
                let tracked g_mid = g.tracked_remove_keys(range_mid);

                self.bitmap_unclaim_field(i, 0, usize::BITS as usize, Tracked(g_mid));

                i = i + 1;
            }

            let tracked g_last = g;
            if bit_idx2 > 0 {
                self.bitmap_unclaim_field(field_idx2, 0, bit_idx2, Tracked(g_last));
            }
        }
    }
}

}
