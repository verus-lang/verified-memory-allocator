#![allow(unused_imports)]

use core::intrinsics::{unlikely, likely};

use vstd::prelude::*;
use vstd::ptr::*;
use vstd::*;
use vstd::modes::*;
use vstd::set_lib::*;

use crate::atomic_ghost_modified::*;

use crate::tokens::{Mim, BlockId, DelayState, PageId};
use crate::types::*;
use crate::config::*;
use crate::layout::*;
use crate::linked_list::*;
use crate::dealloc_token::*;
use crate::os_mem_util::*;

verus!{

pub fn malloc_generic(
    heap: HeapPtr,
    size: usize,
    zero: bool,
    huge_alignment: usize,
    Tracked(local): Tracked<&mut Local>,
) -> (t: (PPtr<u8>, Tracked<PointsToRaw>, Tracked<MimDealloc>))
    requires
        old(local).wf(),
        heap.wf(),
        heap.is_in(*old(local)),
    ensures
        local.wf(),
        ({
            let (ptr, points_to_raw, dealloc) = t;

            dealloc@.wf()
              && points_to_raw@.is_range(ptr.id(), size as int)
              && ptr.id() == dealloc@.ptr()
              && dealloc@.instance() == local.instance
              && dealloc@.size == size
        }),
        common_preserves(*old(local), *local),

{
    // TODO heap initialization

    // TODO deferred free?

    heap_delayed_free_partial(heap, Tracked(&mut *local));

    let page = crate::page::find_page(heap, size, huge_alignment, Tracked(&mut *local));
    if unlikely(page.is_null()) {
        todo();
    }

    if unlikely(zero && page.get_block_size(Tracked(&*local)) == 0) {
        todo(); loop{}
    } else {
        crate::alloc_fast::page_malloc(heap, page, size, zero, Tracked(&mut *local))
    }
}

pub fn page_free_collect(
    page_ptr: PagePtr,
    force: bool, 
    Tracked(local): Tracked<&mut Local>
)
    requires
        old(local).wf(),
        page_ptr.wf(),
        page_ptr.is_used_and_primary(*old(local)),
        old(local).page_organization.pages[page_ptr.page_id@].is_used == true,
    ensures local.wf(),
        page_ptr.is_used_and_primary(*local),
        old(local).page_organization == local.page_organization,
        common_preserves(*old(local), *local),
        old(local).thread_token == local.thread_token,
{
    if force || page_ptr.get_ref(Tracked(&*local)).xthread_free.atomic.load() != 0 {
        page_thread_free_collect(page_ptr, Tracked(&mut *local));
    }

    let ghost old_local = *local;

    page_get_mut_inner!(page_ptr, local, page_inner => {
        if !page_inner.local_free.is_empty() {
            if likely(page_inner.free.is_empty()) {
                // Move local_free to free
                let mut ll = LL::new(Ghost(page_inner.local_free.page_id()), Ghost(page_inner.local_free.fixed_page()), Ghost(page_inner.local_free.instance()), Ghost(page_inner.local_free.block_size()), Ghost(None));
                core::mem::swap(&mut ll, &mut page_inner.local_free);
                page_inner.free = ll;
            } else if force {
                page_inner.free.append(&mut page_inner.local_free);
            }
        }
    });

    proof { preserves_mem_chunk_good(old_local, *local); }
}

fn page_thread_free_collect(
    page_ptr: PagePtr,
    Tracked(local): Tracked<&mut Local>,
)
    requires
        old(local).wf(),
        page_ptr.wf(),
        page_ptr.is_used_and_primary(*old(local)),
    ensures local.wf(),
        local.pages.dom() == old(local).pages.dom(),
        page_ptr.is_used_and_primary(*local),
        old(local).page_organization == local.page_organization,
        common_preserves(*old(local), *local),
        old(local).thread_token == local.thread_token,
{
    let mut ll = page_ptr.get_ref(Tracked(&*local)).xthread_free.take();

    if ll.is_empty() { return; }

    page_get_mut_inner!(page_ptr, local, page_inner => {
        bound_on_1_lists(Tracked(local.instance.clone()), Tracked(&local.thread_token), &mut ll);
        let count = page_inner.local_free.append(&mut ll);
        
        // this relies on counting the block tokens
        // (this is a no-op)
        bound_on_2_lists(Tracked(local.instance.clone()), Tracked(&local.thread_token),
            &mut page_inner.local_free, &mut page_inner.free);
        //assert(page_inner.used >= count);

        page_inner.used = page_inner.used - count;
    });

    proof { preserves_mem_chunk_good(*old(local), *local); }
}

#[verifier::spinoff_prover]
fn page_free_list_extend(
    page_ptr: PagePtr,
    bsize: usize,
    extend: usize,
    Tracked(local): Tracked<&mut Local>
)
    requires
        old(local).wf_main(),
        page_ptr.wf(),
        page_ptr.is_used_and_primary(*old(local)),

        old(local).page_capacity(page_ptr.page_id@) + extend as int
            <= old(local).page_reserved(page_ptr.page_id@),
        // TODO this should have a special case for huge-page handling:
        bsize == old(local).page_inner(page_ptr.page_id@).xblock_size,
        bsize % 8 == 0,
        extend >= 1,
    ensures
        local.wf_main(),
        page_ptr.is_used_and_primary(*local),
        local.page_organization == old(local).page_organization,
        common_preserves(*old(local), *local),
{
    let ghost page_id = page_ptr.page_id@;
    proof {
        const_facts();
        let reserved = local.page_reserved(page_id);
        let capacity = local.page_capacity(page_id);
        let count = local.page_organization.pages[page_id].count.unwrap();

        local.page_organization.get_count_bound(page_id);
        //assert(local.page_organization.pages.dom().contains(page_id));
        local.page_organization.used_offset0_has_count(page_id);
        //assert(count + page_id.idx <= SLICES_PER_SEGMENT);
        assert(capacity * bsize <= reserved * bsize) by(nonlinear_arith)
            requires capacity <= reserved, bsize >= 0;
        assert((capacity + extend - 1) * bsize <= reserved * bsize) by(nonlinear_arith)
            requires capacity + extend - 1 <= reserved, bsize >= 0;
        assert((capacity + extend) * bsize <= reserved * bsize) by(nonlinear_arith)
            requires capacity + extend <= reserved, bsize >= 0;
        //assert(bsize == local.thread_token@.value.pages[page_id].block_size);
        //assert(count == local.pages[page_id].count@.value.unwrap());
    }

    let capacity = page_ptr.get_inner_ref(Tracked(&*local)).capacity;

    let pag_start = calculate_page_start(page_ptr, bsize);
    let start = calculate_page_block_at(pag_start, bsize, capacity as usize,
        Ghost(page_ptr.page_id@));

    //assert((capacity + extend) as usize as int == capacity + extend);
    let x = capacity as usize + extend - 1;

    let last = calculate_page_block_at(pag_start, bsize, x,
        Ghost(page_ptr.page_id@));

    let ghost rng_start = block_start_at(page_id, bsize as int, capacity as int);
    let ghost rng_size = extend * bsize;
    let ghost segment_id = page_id.segment_id;
    let tracked mut seg = local.segments.tracked_remove(segment_id);
    proof {
        assert(extend * bsize >= 0) by(nonlinear_arith) requires extend >= 0, bsize >= 0;
        segment_mem_has_reserved_range(*old(local), page_id, capacity + extend);
        assert(seg.mem.pointsto_has_range(rng_start, rng_size));
    }
    let tracked mut pt = seg.mem.take_points_to_range(rng_start, rng_size);
    proof { local.segments.tracked_insert(segment_id, seg); }

    let tracked mut thread_token = local.take_thread_token();
    let tracked mut checked_token = local.take_checked_token();

    let ghost mut cap_nat;
    let ghost mut extend_nat;

    //assert(page_inner.wf(page_ptr.page_id@,
    //    local.thread_token@.value.pages.index(page_ptr.page_id@),
    //    local.instance));

    proof {
        cap_nat = capacity as nat;
        extend_nat = extend as nat;

        let reserved = local.page_reserved(page_id);

        // PAPER CUT: this kind of assert is flaky
        sub_distribute(reserved as int - capacity as int, extend as int, bsize as int);

        assert((reserved as int - capacity as int) * bsize as int
            >= extend as int * bsize as int) by(nonlinear_arith)
          requires (reserved as int - capacity as int) >= extend
          { }

        assert((capacity as int) * (bsize as int) + (extend as int - 1) * (bsize as int)
            == (capacity as int + extend as int - 1) * (bsize as int)) by (nonlinear_arith);
        /*assert(capacity as int + extend as int - 1
            == capacity as int + (extend as int - 1));
        assert(start.id() == pag_start.id() + capacity as int * bsize as int);
        assert(last.id() == pag_start.id() + (x as int) * bsize as int);
        assert(x as int == (capacity as int + extend as int - 1));
        assert(last.id() - start.id() == 
            (x as int) * (bsize as int)
            - (capacity as int) * (bsize as int));
        assert(last.id() - start.id() == 
            (x as int) * (bsize as int)
            - (capacity as int) * (bsize as int));
        assert(last.id() - start.id() == 
            (x as int) * (bsize as int)
            - (capacity as int) * (bsize as int));
        assert(last.id() - start.id() == 
            (capacity as int + extend as int - 1) * (bsize as int)
            - (capacity as int) * (bsize as int));
        assert(last.id() == start.id() + ((extend as int - 1) * bsize as int));*/

        block_start_at_diff(page_ptr.page_id@, bsize as nat, cap_nat, cap_nat + extend_nat);

        let page_id = page_ptr.page_id@;
        let block_size = bsize as nat;
        let ts = thread_token@.value;
        assert forall |i: nat| cap_nat <= i < cap_nat + extend_nat
            implies Mim::State::okay_to_add_block(ts, page_id, i, block_size)
        by {
            let slice_id = PageId {
                segment_id: page_id.segment_id,
                idx: BlockId::get_slice_idx(page_id, i, block_size),
            };
            start_offset_le_slice_size(bsize as int);
            assert(i * block_size >= 0) by(nonlinear_arith)
                requires i >= 0, block_size >= 0;
            let reserved = local.page_reserved(page_id);
            let capacity = local.page_capacity(page_id);
            assert(i * block_size < reserved * block_size) by(nonlinear_arith)
                requires i < reserved, block_size > 0;
            //assert(page_id.idx <= slice_id.idx);
            let count = local.page_organization.pages[page_id].count.unwrap();
            //assert(slice_id.idx < page_id.idx + count);

            local.page_organization.get_count_bound(page_id);
            //assert(page_id.idx + count <= SLICES_PER_SEGMENT);
            local.page_organization.get_offset_for_something_in_used_range(page_id, slice_id);
            //assert(local.page_organization.pages.dom().contains(slice_id));
            //assert(local.page_organization.pages[slice_id].is_used);
            //assert(local.page_organization.pages[slice_id].offset.is_some());
            //assert(local.page_organization.pages[slice_id].offset.unwrap()
            //    == slice_id.idx - page_id.idx);

            //assert(ts.pages.dom().contains(slice_id));
        }
    }

    let tracked (Tracked(_thread_token), Tracked(block_tokens), Ghost(_s), Tracked(_checked_token)) = local.instance.page_mk_block_tokens(
        // params
        local.thread_id,
        page_ptr.page_id@,
        cap_nat as nat,
        cap_nat as nat + extend_nat as nat,
        bsize as nat,
        // input ghost state
        thread_token,
        checked_token,
    );
    proof { local.thread_token = _thread_token; local.checked_token = _checked_token; }
    let tracked mut block_tokens = Map::tracked_map_keys(block_tokens,
        Map::<int, BlockId>::new(
          |i: int| cap_nat <= i < cap_nat + extend_nat,
          |i: int| BlockId {
              page_id: page_ptr.page_id@,
              idx: i as nat,
              slice_idx: BlockId::get_slice_idx(page_ptr.page_id@, i as nat, bsize as nat),
              block_size: bsize as nat
          }
        ));

    // TODO

    proof {
        assert(start.id() % 8 == 0) by {
            block_ptr_aligned_to_word();
            crate::linked_list::size_of_node();
            segment_start_mult8(page_id.segment_id);
            start_offset_le_slice_size(bsize as int);
            //assert(segment_start(page_id.segment_id) % 8 == 0);
            assert(page_start(page_id) % 8 == 0);
            assert(start_offset(bsize as int) % 8 == 0);
            assert(pag_start % 8 == 0);
            mod_mul(capacity as int, bsize as int, 8);
            //assert((capacity * bsize) % 8 == 0) by(nonlinear_arith)
            //    requires bsize % 8 == 0;
        }
        assert forall |i: int| cap_nat <= i < cap_nat + extend_nat
            implies is_block_ptr(
                block_start(block_tokens.index(i)@.key),
                block_tokens.index(i)@.key,
            )
        by {
            let block_id = block_tokens.index(i)@.key;
            let block_size = bsize as int;
            reveal(is_block_ptr);
            get_block_start_defn(block_id);
            crate::linked_list::size_of_node();
            start_offset_le_slice_size(block_size);
            //assert(block_size >= 8);
            //assert(block_id.page_id == page_id);
            //assert(block_id.block_size == block_size);
            //assert(page_id.segment_id == segment_id);
            let reserved = local.page_reserved(page_id);
            let capacity = local.page_capacity(page_id);
            assert(i * block_size <= reserved * block_size) by(nonlinear_arith)
                requires i <= reserved, block_size >= 0;
            //assert(i * block_size <= capacity * block_size);
            //assert(block_start_at(page_id, block_size, block_id.idx as int) >
            //    segment_start(segment_id));
            //assert(block_start_at(page_id, block_size, block_id.idx as int) <=
            //    segment_start(segment_id) + SEGMENT_SIZE as int);
            //assert(segment_start(segment_id) + (block_id.slice_idx * SLICE_SIZE)
            //    <= block_start_at(page_id, block_size, block_id.idx as int));
            //assert(i * block_size <
            //  i * block_size / SLICE_SIZE as int * SLICE_SIZE + SLICE_SIZE);
            //assert(block_start_at(page_id, block_size, block_id.idx as int)
            //  < segment_start(segment_id) + (block_id.slice_idx * SLICE_SIZE) + SLICE_SIZE);

        }
    }

    page_get_mut_inner!(page_ptr, local, page_inner => {
        page_inner.free.prepend_contiguous_blocks(
            start, last, bsize,
            // ghost args:
            Ghost(cap_nat), Ghost(extend_nat),
            // tracked args:
            Tracked(&mut pt),
            Tracked(&mut block_tokens));

        // note: mimalloc has this line in the parent function, mi_page_extend_free,
        // but it's easier to just do it here to preserve local.wf()
        page_inner.capacity = page_inner.capacity + extend as u16;
    });


    proof {
        /*assert forall |pid|
            #[trigger] local.pages.dom().contains(pid) &&
              local.thread_token@.value.pages.dom().contains(pid) implies
                local.pages.index(pid).wf(
                  pid,
                  local.thread_token@.value.pages.index(pid),
                  local.instance,
                )
        by {
            if pid.idx == page_ptr.page_id@.idx {
                assert(local.pages.index(pid).wf(pid, local.thread_token@.value.pages.index(pid), local.instance));
            } else {
                assert(old(local).pages.index(pid).wf(pid, old(local).thread_token@.value.pages.index(pid), old(local).instance));
                assert(old(local).pages.index(pid) == local.pages.index(pid));
                assert(old(local).thread_token@.value.pages.index(pid)
                    == local.thread_token@.value.pages.index(pid));
                assert(local.pages.index(pid).wf(pid, local.thread_token@.value.pages.index(pid), local.instance));
            }
        }*/

        /*let blocksize = bsize as int;
        assert((capacity + extend) * blocksize == capacity * blocksize + extend * blocksize);
        assert(local.page_capacity(page_id) == capacity + extend);
        assert(block_start_at(page_id, bsize as int, capacity as int + extend as int)
            == rng_start + rng_size);
        assert(rng_start == 
                page_start(page_id)
                    + start_offset(old(local).block_size(page_id))
                    + old(local).page_capacity(page_id) * old(local).block_size(page_id));
        assert(rng_start + rng_size == 
                page_start(page_id)
                    + start_offset(old(local).block_size(page_id))
                    + local.page_capacity(page_id) * old(local).block_size(page_id));*/
        block_start_at_diff(page_id, bsize as nat, capacity as nat, (capacity + extend) as nat);

        preserves_mem_chunk_good_on_transfer_to_capacity(*old(local), *local, page_id);
        assert(local.mem_chunk_good(segment_id));
        preserves_mem_chunk_good_except(*old(local), *local, segment_id);

        assert(local.wf_main());
    }
}

const MIN_EXTEND: usize = 4;
const MAX_EXTEND_SIZE: u32 = 4096;

pub fn page_extend_free(
    page_ptr: PagePtr,
    Tracked(local): Tracked<&mut Local>,
)
    requires
        old(local).wf_main(),
        page_ptr.wf(),
        old(local).is_used_primary(page_ptr.page_id@),
        old(local).pages[page_ptr.page_id@].inner@.value.unwrap().xblock_size % 8 == 0,
    ensures
        local.wf_main(),
        local.is_used_primary(page_ptr.page_id@),
        local.page_organization == old(local).page_organization,
        common_preserves(*old(local), *local),
{
    let page_inner = page_ptr.get_inner_ref(Tracked(&*local));

    /*proof {
        assert(page_inner.wf(page_ptr.page_id@,
            local.thread_token@.value.pages.index(page_ptr.page_id@),
            local.instance));
    }*/

    let reserved = page_inner.reserved;
    let capacity = page_inner.capacity;

    if capacity >= reserved { return; }

    // Calculate the block size
    // TODO should have special handling for huge blocks
    let bsize: usize = page_ptr.get_inner_ref(Tracked(&*local)).xblock_size as usize;

    /*proof {
        let ghost page_id = page_ptr.page_id@;
        assert(local.page_organization.pages.dom().contains(page_id));
        assert(page_organization_matches_token_page(
            local.page_organization.pages[page_id],
            local.thread_token@.value.pages[page_id]));
        assert(local.is_used_primary(page_id));
        assert(bsize != 0);
    }*/

    // Calculate extend amount

    let mut max_extend: usize = if bsize >= MAX_EXTEND_SIZE as usize {
        MIN_EXTEND
    } else {
        (MAX_EXTEND_SIZE / bsize as u32) as usize
    };
    if max_extend < MIN_EXTEND {
        max_extend = MIN_EXTEND;
    }

    let mut extend: usize = (reserved - capacity) as usize;
    if extend > max_extend {
        extend = max_extend;
    }

    page_free_list_extend(page_ptr, bsize, extend, Tracked(local));

    // page capacity is modified in page_free_list_extend, no need to do it here
}

fn heap_delayed_free_partial(heap: HeapPtr, Tracked(local): Tracked<&mut Local>) -> (b: bool)
    requires
        old(local).wf(),
        heap.wf(), heap.is_in(*old(local)),
    ensures
        local.wf(),
        common_preserves(*old(local), *local),
{
    let mut ll = heap.get_ref(Tracked(&*local)).thread_delayed_free.take();
    let mut all_freed = true;
    while !ll.is_empty()
        invariant
            local.wf(),
            heap.wf(), heap.is_in(*local),
            ll.wf(), common_preserves(*old(local), *local),
            ll.instance() == local.instance,
            ll.heap_id() == Some(local.thread_token@.value.heap_id)
    {
        let (ptr, Tracked(perm), Tracked(block)) = ll.pop_block();
        proof {
            //assert(block@.value.heap_id == Some(local.thread_token@.value.heap_id));
            local.instance.block_in_heap_has_valid_page(
                local.thread_token@.key, block@.key,
                &local.thread_token, &block);
            local.instance.get_block_properties(
                local.thread_token@.key, block@.key,
                &local.thread_token, &block);
            //assert(valid_block_token(block, local.instance));
        }
        let tracked dealloc_inner = MimDeallocInner {
            mim_instance: local.instance.clone(),
            mim_block: block,
            ptr: ptr.id(),
        };
        let (success, Tracked(p_opt), Tracked(d_opt)) =
                crate::free::free_delayed_block(ptr, Tracked(perm),
                    Tracked(dealloc_inner), Tracked(&mut *local));
        if !success {
            all_freed = false;
            let tracked perm = p_opt.tracked_unwrap();
            let tracked dealloc = d_opt.tracked_unwrap();
            let tracked block = dealloc.mim_block;

            let ptr = PPtr::from_usize(ptr.to_usize());
            heap.get_ref(Tracked(&*local)).thread_delayed_free
                .atomic_insert_block(ptr, Tracked(perm), Tracked(block));
        }
    }
    return all_freed;
}

}
