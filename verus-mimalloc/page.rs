#![allow(unused_imports)]

use core::intrinsics::{unlikely, likely};

use vstd::prelude::*;
use vstd::ptr::*;
use vstd::*;
use vstd::modes::*;
use vstd::set_lib::*;
use vstd::pervasive::*;
use vstd::atomic_ghost::*;

use crate::tokens::{Mim, BlockId, DelayState, PageId, PageState};
use crate::types::*;
use crate::layout::*;
use crate::bin_sizes::*;
use crate::config::*;
use crate::page_organization::*;
use crate::linked_list::LL;
use crate::os_mem_util::*;
use crate::commit_segment::*;
use crate::segment::good_count_for_block_size;
use crate::queues::*;

verus!{

pub fn find_page(heap_ptr: HeapPtr, size: usize, huge_alignment: usize, Tracked(local): Tracked<&mut Local>) -> (page: PagePtr)
    requires
        old(local).wf(),
        heap_ptr.wf(),
        heap_ptr.is_in(*old(local)),
    ensures
        local.wf(),
        common_preserves(*old(local), *local),
        page.page_ptr.id() != 0 ==> page.wf() && page.is_in(*local)
            && page.is_used_and_primary(*local),
        page.page_ptr.id() != 0 ==> 
            local.pages.index(page.page_id@).inner@.value.unwrap().xblock_size >= size,
{
    proof { const_facts(); }

    let req_size = size;
    if unlikely(req_size > MEDIUM_OBJ_SIZE_MAX as usize || huge_alignment > 0) {
        if unlikely(req_size > MAX_ALLOC_SIZE) {
            return PagePtr::null();
        } else {
            todo(); loop { }
        }
    } else {
        return find_free_page(heap_ptr, size, Tracked(&mut *local));
    }
}

fn find_free_page(heap_ptr: HeapPtr, size: usize, Tracked(local): Tracked<&mut Local>) -> (page: PagePtr)
    requires
        old(local).wf(),
        heap_ptr.wf(),
        heap_ptr.is_in(*old(local)),
        size <= MEDIUM_OBJ_SIZE_MAX,
    ensures
        local.wf(),
        common_preserves(*old(local), *local),
        page.page_ptr.id() != 0 ==> page.wf() && page.is_in(*local)
            && page.is_used_and_primary(*local),
        page.page_ptr.id() != 0 ==> 
            local.pages.index(page.page_id@).inner@.value.unwrap().xblock_size >= size,
{
    proof { const_facts(); }
    let pq = bin(size) as usize;

    proof {
        local.page_organization.used_first_is_in(pq as int);
        crate::bin_sizes::bin_size_result(size); 
    }

    let mut page = PagePtr { page_ptr: heap_ptr.get_pages(Tracked(&*local))[pq].first, page_id: Ghost(local.page_organization.used_dlist_headers[pq as int].first.get_Some_0()) };

    if page.page_ptr.to_usize() != 0 {
        crate::alloc_generic::page_free_collect(page, false, Tracked(&mut *local));

        if !page.get_inner_ref(Tracked(&*local)).free.is_empty() {
            return page;
        }
    }

    page_queue_find_free_ex(heap_ptr, pq, true, Tracked(&mut *local))
}

fn page_queue_find_free_ex(heap_ptr: HeapPtr, pq: usize, first_try: bool, Tracked(local): Tracked<&mut Local>) -> (page: PagePtr)
    requires
        old(local).wf(),
        heap_ptr.wf(),
        heap_ptr.is_in(*old(local)),
        valid_bin_idx(pq as int),
        size_of_bin(pq as int) <= MEDIUM_OBJ_SIZE_MAX,
    ensures
        local.wf(),
        common_preserves(*old(local), *local),
        page.page_ptr.id() != 0 ==> page.wf() && page.is_in(*local)
            && page.is_used_and_primary(*local),
        page.page_ptr.id() != 0 ==> 
            local.pages.index(page.page_id@).inner@.value.unwrap().xblock_size == size_of_bin(pq as int)
{
    let mut page = PagePtr { page_ptr: heap_ptr.get_pages(Tracked(&*local))[pq].first, page_id: Ghost(local.page_organization.used_dlist_headers[pq as int].first.get_Some_0()) };
    let ghost mut list_idx = 0;
    proof {
        local.page_organization.used_first_is_in(pq as int);
    }

    loop
        invariant
            local.wf(),
            heap_ptr.wf(),
            heap_ptr.is_in(*local),
            common_preserves(*old(local), *local),
            0 <= pq <= BIN_HUGE,
            size_of_bin(pq as int) <= MEDIUM_OBJ_SIZE_MAX,
            page.page_ptr.id() != 0 ==>
                page.wf()
                && local.page_organization.valid_used_page(page.page_id@, pq as int, list_idx),
    {
        if page.page_ptr.to_usize() == 0 {
            break;
        }

        let next_ptr = page.get_next(Tracked(&*local));
        let ghost page_id = page.page_id@;
        let ghost next_id = local.page_organization.pages[page_id].dlist_entry.unwrap().next.unwrap();
        proof {
            /*assert(local.page_organization.pages.dom().contains(page_id));
            assert(page_organization_pages_match_data(local.page_organization.pages[page_id], local.pages[page_id], local.psa[page_id]));
            assert(is_page_ptr_opt(next_ptr, local.page_organization.pages[page_id].dlist_entry.unwrap().next));
            if next_ptr.id() != 0 {
                assert(local.page_organization.pages[page_id].dlist_entry.unwrap().next.is_some());
                assert(is_page_ptr(next_ptr.id(), next_id));
            }*/
            local.page_organization.used_next_is_in(page.page_id@, pq as int, list_idx);
            size_of_bin_mult_word_size(pq as int);
        }

        crate::alloc_generic::page_free_collect(page, false, Tracked(&mut *local));

        if !page.get_inner_ref(Tracked(&*local)).free.is_empty() {
            break;
        }

        if page.get_inner_ref(Tracked(&*local)).capacity < page.get_inner_ref(Tracked(&*local)).reserved {
            //let tld_ptr = heap_ptr.get_ref(Tracked(&*local)).tld_ptr;
            //assert(local.is_used_primary(page.page_id@));
            crate::alloc_generic::page_extend_free(page, Tracked(&mut *local));
            break;
        }

        page_to_full(page, heap_ptr, pq, Tracked(&mut *local), Ghost(list_idx), Ghost(next_id));

        page = PagePtr { page_ptr: next_ptr, page_id: Ghost(next_id) };

        proof {
            //list_idx = list_idx + 1;
            /*if next_ptr.id() != 0 {
                assert(page.wf());
                assert(local.page_organization.valid_used_page(page.page_id@, pq as int, list_idx));
            }*/
        }
    }

    if page.page_ptr.to_usize() == 0 {
        let page = page_fresh(heap_ptr, pq, Tracked(&mut *local));
        if page.page_ptr.to_usize() == 0 && first_try {
            return page_queue_find_free_ex(heap_ptr, pq, false, Tracked(&mut *local))
        } else {
            return page;
        }
    } else {
        let ghost old_local = *local;
        page_get_mut_inner!(page, local, inner => {
            inner.set_retire_expire(0);
        });
        proof { preserves_mem_chunk_good(old_local, *local); }
        return page;
    }
}

fn page_fresh(heap_ptr: HeapPtr, pq: usize, Tracked(local): Tracked<&mut Local>) -> (page: PagePtr)
    requires
        old(local).wf(),
        heap_ptr.wf(),
        heap_ptr.is_in(*old(local)),
        valid_bin_idx(pq as int),
        size_of_bin(pq as int) <= MEDIUM_OBJ_SIZE_MAX,
    ensures
        local.wf(),
        common_preserves(*old(local), *local),
        page.page_ptr.id() != 0 ==> page.wf() && page.is_in(*local)
            && page.is_used_and_primary(*local),
        page.page_ptr.id() != 0 ==> 
            local.pages.index(page.page_id@).inner@.value.unwrap().xblock_size == size_of_bin(pq as int)

{
    proof { size_of_bin_bounds(pq as int); }
    let block_size = heap_ptr.get_pages(Tracked(&*local))[pq].block_size;
    page_fresh_alloc(heap_ptr, pq, block_size, 0, Tracked(&mut *local))
}

fn page_fresh_alloc(heap_ptr: HeapPtr, pq: usize, block_size: usize, page_alignment: usize, Tracked(local): Tracked<&mut Local>) -> (page: PagePtr)
    requires
        old(local).wf(),
        heap_ptr.wf(),
        heap_ptr.is_in(*old(local)),
        2 <= block_size,
        valid_bin_idx(pq as int),
        block_size == size_of_bin(pq as int),
        block_size <= MEDIUM_OBJ_SIZE_MAX,
    ensures
        local.wf(),
        common_preserves(*old(local), *local),
        page.page_ptr.id() != 0 ==> page.wf() && page.is_in(*local)
            && page.is_used_and_primary(*local),
        page.page_ptr.id() != 0 ==> 
            local.pages.index(page.page_id@).inner@.value.unwrap().xblock_size == block_size,
{
    let tld_ptr = heap_ptr.get_ref(Tracked(&*local)).tld_ptr;
    let page_ptr = crate::segment::segment_page_alloc(heap_ptr, block_size, page_alignment, tld_ptr, Tracked(&mut *local));
    if page_ptr.page_ptr.to_usize() == 0 {
        return page_ptr;
    }

    let full_block_size: usize = block_size; // TODO handle pq == NULL or huge pages
    let tld_ptr = heap_ptr.get_ref(Tracked(&*local)).tld_ptr;

    proof {
        smallest_bin_fitting_size_size_of_bin(pq as int);
        size_of_bin_mult_word_size(pq as int);
        if pq != BIN_HUGE {
            size_of_bin_bounds_not_huge(pq as int);
        }
        lemma_bin_sizes_constants();
    }

    page_init(heap_ptr, page_ptr, full_block_size, tld_ptr, Tracked(&mut *local), Ghost(pq as int));
    page_queue_push(heap_ptr, pq, page_ptr, Tracked(&mut *local));

    return page_ptr;
}

// READY --> USED
fn page_init(heap_ptr: HeapPtr, page_ptr: PagePtr, block_size: usize, tld_ptr: TldPtr, Tracked(local): Tracked<&mut Local>, Ghost(pq): Ghost<int>)
    requires
        old(local).wf_main(),
        heap_ptr.wf(),
        heap_ptr.is_in(*old(local)),
        page_ptr.wf(),
        page_ptr.is_in(*old(local)),
        old(local).page_organization.popped == Popped::Ready(page_ptr.page_id@, true),
        block_size != 0,
        block_size % 8 == 0,
        block_size <= u32::MAX,
        valid_bin_idx(pq),
        size_of_bin(pq) == block_size,
        //old(local).page_organization[page_ptr.page_id@].block_size == Some(block_
        //old(local).page_inner(page_ptr.page_id@).xblock_size == block_size
        //old(local).segments[page_ptr.page_id@.segment_id]
        //  .mem.committed_pointsto_has_range(
        //    segment_start(page_ptr.page_id@.segment_id) + page_ptr.page_id@.idx * SLICE_SIZE,
        //    local.page_organization.pages[page_ptr.page_id@].count.unwrap() * SLIZE_SIZE),
        page_init_is_committed(page_ptr.page_id@, *old(local)),
        good_count_for_block_size(block_size as int,
              old(local).page_organization.pages[page_ptr.page_id@].count.unwrap() as int),
    ensures
        local.wf_main(),
        common_preserves(*old(local), *local),
        page_ptr.is_used(*local),
        local.page_organization.popped == Popped::Used(page_ptr.page_id@, true),
        local.page_organization.pages[page_ptr.page_id@].page_header_kind == Some(PageHeaderKind::Normal(pq as int, block_size as int)),
{
    let ghost mut next_state;
    proof {
        next_state = PageOrg::take_step::set_range_to_used(local.page_organization, PageHeaderKind::Normal(pq as int, block_size as int));
    }

    let ghost page_id = page_ptr.page_id@;
    let ghost n_slices = local.page_organization.pages[page_id].count.unwrap();
    let ghost n_blocks = n_slices * SLICE_SIZE / block_size as int;
    let ghost range = page_id.range_from(0, n_slices as int);
    assert forall |pid| range.contains(pid) implies local.unused_pages.dom().contains(pid) by {
        assert(local.page_organization.pages.dom().contains(pid));
        assert(local.page_organization.pages[pid].is_used == false);
    }
    let ghost new_page_state_map = Map::new(
            |pid: PageId| range.contains(pid),
            |pid: PageId| PageState {
                offset: pid.idx - page_id.idx,
                block_size: block_size as nat,
                num_blocks: 0,
                shared_access: arbitrary(),
                is_enabled: false,
            });
    assert(n_slices > 0);
    assert(range.contains(page_id));

    let count = page_ptr.get_count(Tracked(&*local));

    let tracked thread_token = local.take_thread_token();
    let tracked (
        Tracked(thread_token),
        Tracked(delay_token),
        Tracked(heap_of_page_token),
    ) = local.instance.create_page_mk_tokens(
            // params
            local.thread_id,
            page_id,
            n_slices as nat,
            block_size as nat,
            new_page_state_map,
            // input ghost state
            thread_token,
        );

    unused_page_get_mut!(page_ptr, local, page => {
        let tracked (Tracked(emp_inst), Tracked(emp_x), Tracked(emp_y)) = BoolAgree::Instance::initialize(false);
        let ghost g = (Ghost(local.instance), Ghost(page_ptr.page_id@), Tracked(emp_x), Tracked(emp_inst));
        page.xheap = AtomicHeapPtr {
            atomic: AtomicUsize::new(Ghost(g), heap_ptr.heap_ptr.to_usize(), Tracked((emp_y, Some(heap_of_page_token)))),
            instance: Ghost(local.instance), page_id: Ghost(page_ptr.page_id@), emp: Tracked(emp_x), emp_inst: Tracked(emp_inst), };
        page.xthread_free.enable(Ghost(block_size as nat), Ghost(page_ptr.page_id@),
            Tracked(local.instance.clone()), Tracked(delay_token));
        //assert(page.xheap.wf(local.instance, page_ptr.page_id@));
    });

    unused_page_get_mut_inner!(page_ptr, local, inner => {
        proof {
            const_facts();
            //assert(block_size as u32 == block_size);

            local.page_organization.get_count_bound(page_ptr.page_id@);
            //assert(count <= SLICES_PER_SEGMENT);
            //assert(count * SLICE_SIZE <= SLICES_PER_SEGMENT * SLICE_SIZE);
            //assert(0 <= count * SLICE_SIZE < u32::MAX);
            //assert(block_size as u32 != 0);

            // prove that reserved will fit in u16
            // should follow from good_count_for_block_size
            //assert(count == old(local).page_organization.pages[page_ptr.page_id@].count.unwrap());
            let start_offs = start_offset(block_size as int);
            start_offset_le_slice_size(block_size as int);
            assert((count * SLICE_SIZE - start_offs) / block_size as int <= u16::MAX) by(nonlinear_arith)
                requires (count * SLICE_SIZE) <= block_size * u16::MAX,
                  count >= 0, SLICE_SIZE >= 0, block_size > 0, start_offs >= 0;
        }

        inner.xblock_size = block_size as u32;
        let start_offs = calculate_start_offset(block_size);
        //proof {
        //    assert(count * SLICE_SIZE as u32 >= start_offs);
        //}
        let page_size = count * SLICE_SIZE as u32 - start_offs;
        inner.reserved = (page_size / block_size as u32) as u16;

        inner.free.set_ghost_data(
            Ghost(page_id), Ghost(true), Ghost(local.instance), Ghost(block_size as nat), Ghost(None));
        inner.local_free.set_ghost_data(
            Ghost(page_id), Ghost(true), Ghost(local.instance), Ghost(block_size as nat), Ghost(None));

        /*assert(inner.capacity == 0);
        assert(inner.free.wf());
        assert(inner.local_free.wf());
        assert(inner.free.block_size() == block_size);
        assert(inner.local_free.block_size() == block_size);
        assert(inner.free.len() == 0);
        assert(inner.local_free.len() == 0);
        assert(inner.free.fixed_page());
        assert(inner.local_free.fixed_page());
        assert(inner.free.page_id() == page_id);
        assert(inner.local_free.page_id() == page_id);
        assert(inner.free.instance() == local.instance);
        assert(inner.local_free.instance() == local.instance);
        assert(inner.used == 0);

        assert(inner.reserved == page_size as int / block_size as int);*/
        assert(page_size as int / block_size as int * block_size as int <= page_size) by(nonlinear_arith)
            requires page_size >= 0, block_size > 0;
    });

    proof {
        let tracked new_psa_map = local.unused_pages.tracked_remove_keys(range);
        let ghost new_page_state_map2 = Map::new(
            |pid: PageId| range.contains(pid),
            |pid: PageId| PageState {
                //offset: pid.idx - page_id.idx,
                //block_size: block_size as nat,
                //num_blocks: 0,
                is_enabled: true,
                shared_access: new_psa_map[pid],
                .. thread_token@.value.pages[pid]
            });
        /*assert forall |pid: PageId| #[trigger] new_page_state_map2.dom().contains(pid) implies
                new_page_state_map2[pid] == PageState {
                    is_enabled: true,
                    shared_access: new_psa_map[pid],
                    .. thread_token@.value.pages[pid]
                }
        by {
            let a = new_page_state_map2[pid];
            let llama = PageState {
                    is_enabled: true,
                    shared_access: new_psa_map[pid],
                    .. thread_token@.value.pages[pid]
                };
            assert(llama.offset == thread_token@.value.pages[pid].offset);
            assert(new_page_state_map2[pid].is_enabled == true);
            assert(new_page_state_map2[pid].shared_access == new_psa_map[pid]);
            assert(new_page_state_map2[pid].num_blocks == thread_token@.value.pages[pid].num_blocks);
            assert(new_page_state_map2[pid].offset == thread_token@.value.pages[pid].offset);
            assert(new_page_state_map2[pid].block_size == thread_token@.value.pages[pid].block_size);
            assert(a == llama);
            assert(a.offset == llama.offset);
            assert(a.block_size == llama.block_size);
            assert(a.num_blocks == llama.num_blocks);
            assert(a.shared_access == llama.shared_access);
            assert(a.is_enabled == llama.is_enabled);
            assert(a == llama);
        }*/

        let tracked thread_token = local.instance.page_enable(
                // params
                local.thread_id,
                page_id,
                n_slices as nat,
                new_page_state_map2,
                new_psa_map,
                // input ghost state
                thread_token,
                new_psa_map,
            );

        local.thread_token = thread_token;
        local.page_organization = next_state;
        local.psa = local.psa.insert(page_id, new_psa_map[page_id]);

        /*assert forall |pid|
            #[trigger] local.pages.dom().contains(pid) &&
              local.thread_token@.value.pages.dom().contains(pid) implies
                local.pages.index(pid).wf(
                  pid,
                  local.thread_token@.value.pages.index(pid),
                  local.instance,
                )
        by {
            if range.contains(pid) {
                if pid.idx == page_id.idx {
                    assert(local.pages.index(pid).wf(pid, local.thread_token@.value.pages.index(pid), local.instance));
                } else {
                    assert(old(local).pages.index(pid).wf_unused(pid, 
                        old(local).unused_pages[pid], old(local).page_organization.popped, old(local).instance));
                    assert(old(local).unused_pages[pid] ==
                        local.thread_token@.value.pages.index(pid).shared_access);
                    assert(old(local).pages.index(pid).wf_unused(pid, 
                        local.thread_token@.value.pages.index(pid).shared_access, local.page_organization.popped, local.instance));
                    assert(local.pages.index(pid).wf(pid, local.thread_token@.value.pages.index(pid), local.instance));
                }
            } else {
                assert(local.pages.index(pid).wf(pid, local.thread_token@.value.pages.index(pid), local.instance));
            }
        }*/

        /*assert forall |segment_id|
            #[trigger] local.segments.dom().contains(segment_id) ==>
              local.segments[segment_id].wf(
                segment_id,
                local.thread_token@.value.segments.index(segment_id),
                local.instance,
              )
        by {
            let seg = local.segments[segment_id];
            let old_seg = old(local).segments[segment_id];
            if segment_id == page_ptr.page_id@.segment_id {
                assert(local.mem_chunk_good(segment_id));
            } else {
                //mem_chunk_good_preserved_one(old(local).page_organization,
                //    local.page_organization, segment_id);
                //assert(mem_chunk_good(old_seg.mem, segment_id,
                //    old_seg.main@.value.unwrap().commit_mask@, old(local).page_organization));
                assert(local.mem_chunk_good(segment_id));
            }
        }*/

        //let org_pages = local.page_organization.pages;
        //let pages = local.pages;
        //let psa = local.psa;
        /*assert forall |pid| #[trigger] org_pages.dom().contains(pid) implies
            page_organization_pages_match_data(org_pages[pid], pages[pid], psa[pid], pid, local.page_organization.popped)
        by {
            if pid == page_id {
                assert(page_organization_pages_match_data(org_pages[pid], pages[pid], psa[pid], pid, local.page_organization.popped));
            } else {
                assert(page_organization_pages_match_data(org_pages[pid], pages[pid], psa[pid], pid, local.page_organization.popped));
            }
        }*/

        preserves_mem_chunk_good_except(*old(local), *local, page_id.segment_id);
        preserves_mem_chunk_on_set_used(*old(local), *local, page_id);

        /*assert(page_organization_pages_match(local.page_organization.pages,
              local.pages, local.psa, local.page_organization.popped));
        assert(local.page_organization_valid());
        assert(local.wf_main());*/
    }

    //assert(local.is_used_primary(page_ptr.page_id@));
    crate::alloc_generic::page_extend_free(page_ptr, Tracked(&mut *local))
}

fn page_queue_of(page: PagePtr, Tracked(local): Tracked<&Local>) -> (res: (HeapPtr, usize, Ghost<int>))
    requires local.wf(),
        page.wf(), page.is_in(*local),
        page.is_used_and_primary(*local),
    ensures ({ let (heap, pq, list_idx) = res; {
        &&& heap.wf()
        &&& heap.is_in(*local)
        &&& (valid_bin_idx(pq as int) || pq == BIN_FULL)
        &&& local.page_organization.valid_used_page(page.page_id@, pq as int, list_idx@)
    }}),
        
{
    let is_in_full = page.get_inner_ref(Tracked(&*local)).get_in_full();

    let ghost mut list_idx;
    proof {
        if is_in_full {
            list_idx = local.page_organization.marked_full_is_in(page.page_id@);
            //assert(local.page_organization.valid_used_page(page.page_id@, bin as int, list_idx));
        } else {
            list_idx = local.page_organization.marked_unfull_is_in(page.page_id@);
            /*smallest_bin_fitting_size_size_of_bin(bin as int);
            assert(local.block_size(page.page_id@) == 
                local.page_organization.pages[page.page_id@].page_header_kind.unwrap().get_Normal_1());
            assert(bin == smallest_bin_fitting_size(
                local.block_size(page.page_id@)));
            assert(bin == smallest_bin_fitting_size(
                size_of_bin());
            assert(bin == local.page_organization.pages[page.page_id@].page_header_kind.unwrap().get_Normal_0());
            assert(local.page_organization.valid_used_page(page.page_id@, bin as int, list_idx));*/
        }
        const_facts();
    }

    let bin = if is_in_full {
        BIN_FULL as usize
    } else {
        bin(page.get_inner_ref(Tracked(&*local)).xblock_size as usize) as usize
    };

    let heap = page.get_heap(Tracked(&*local));
    (heap, bin, Ghost(list_idx))
}

const MAX_RETIRE_SIZE: u32 = MEDIUM_OBJ_SIZE_MAX as u32;

pub fn page_retire(page: PagePtr, Tracked(local): Tracked<&mut Local>)
    requires old(local).wf(), page.wf(), page.is_in(*old(local)),
        page.is_used_and_primary(*old(local)),
        old(local).pages[page.page_id@].inner@.value.unwrap().used == 0,
    ensures
        local.wf(),
        common_preserves(*old(local), *local),
{
    let (heap, pq, Ghost(list_idx)) = page_queue_of(page, Tracked(&*local));
    if likely(
        page.get_inner_ref(Tracked(&*local)).xblock_size <= MAX_RETIRE_SIZE
          && !(heap.get_pages(Tracked(&*local))[pq].block_size > MEDIUM_OBJ_SIZE_MAX as usize)
    )
    {
        if heap.get_pages(Tracked(&*local))[pq].last.to_usize() == page.page_ptr.to_usize() &&
            heap.get_pages(Tracked(&*local))[pq].first.to_usize() == page.page_ptr.to_usize()
        {
            let RETIRE_CYCLES = 8;
            page_get_mut_inner!(page, local, inner => {
                let xb = inner.xblock_size as u64;
                inner.set_retire_expire(1 + (if xb <= SMALL_OBJ_SIZE_MAX { RETIRE_CYCLES } else { RETIRE_CYCLES/4 }));
            });

            if pq < heap.get_page_retired_min(Tracked(&*local)) {
                heap.set_page_retired_min(Tracked(&mut *local), pq);
            }
            if pq > heap.get_page_retired_max(Tracked(&*local)) {
                heap.set_page_retired_max(Tracked(&mut *local), pq);
            }

            proof { preserves_mem_chunk_good(*old(local), *local); }
            return;
        }
    }

    page_free(page, pq, false, Tracked(&mut *local), Ghost(list_idx));
}

fn page_free(page: PagePtr, pq: usize, force: bool, Tracked(local): Tracked<&mut Local>, Ghost(list_idx): Ghost<int>)
    requires old(local).wf(), page.wf(), page.is_in(*old(local)),
        page.is_used_and_primary(*old(local)),
        old(local).page_organization.valid_used_page(page.page_id@, pq as int, list_idx),
        old(local).pages[page.page_id@].inner@.value.unwrap().used == 0,
    ensures
        local.wf(),
        common_preserves(*old(local), *local),
{
    page_get_mut_inner!(page, local, inner => {
        inner.set_has_aligned(false);
    });
    proof { preserves_mem_chunk_good(*old(local), *local); }
    let heap = page.get_heap(Tracked(&*local));

    page_queue_remove(heap, pq, page, Tracked(&mut *local), Ghost(list_idx), Ghost(arbitrary()));

    let tld = heap.get_ref(Tracked(&*local)).tld_ptr;
    crate::segment::segment_page_free(page, force, tld, Tracked(&mut *local));
}
   
fn page_to_full(page: PagePtr, heap: HeapPtr, pq: usize, Tracked(local): Tracked<&mut Local>,
      Ghost(list_idx): Ghost<int>, Ghost(next_id): Ghost<PageId>)
    requires old(local).wf(), page.wf(), page.is_in(*old(local)),
        heap.wf(), heap.is_in(*old(local)),
        page.is_used_and_primary(*old(local)),
        valid_bin_idx(pq as int),
        old(local).page_organization.valid_used_page(page.page_id@, pq as int, list_idx),
    ensures
        local.wf(),
        common_preserves(*old(local), *local),
        old(local).page_organization.valid_used_page(next_id, pq as int, list_idx + 1) ==>
            local.page_organization.valid_used_page(next_id, pq as int, list_idx),
{
    page_queue_enqueue_from(heap, BIN_FULL as usize, pq, page, Tracked(&mut *local),
        Ghost(list_idx), Ghost(next_id));
    crate::alloc_generic::page_free_collect(page, false, Tracked(&mut *local));
}

pub fn page_unfull(page: PagePtr, Tracked(local): Tracked<&mut Local>)
    requires old(local).wf(), page.wf(), page.is_in(*old(local)),
        page.is_used_and_primary(*old(local)),
        old(local).pages[page.page_id@].inner@.value.unwrap().in_full(),
    ensures local.wf(),
        common_preserves(*old(local), *local),
{
    let heap = page.get_heap(Tracked(&*local));
    proof {
        local.page_organization.marked_full_is_in(page.page_id@);
        const_facts();
    }
    let pq = bin(page.get_inner_ref(Tracked(&mut *local)).xblock_size as usize);
    let ghost list_idx = local.page_organization.marked_full_is_in(page.page_id@);
    page_queue_enqueue_from(heap, pq as usize, BIN_FULL as usize, page,
        Tracked(&mut *local), Ghost(list_idx), Ghost(arbitrary()));
}

fn page_queue_enqueue_from(heap: HeapPtr, to: usize, from: usize, page: PagePtr, Tracked(local): Tracked<&mut Local>, Ghost(list_idx): Ghost<int>, Ghost(next_id): Ghost<PageId>)
    requires old(local).wf(), page.wf(), page.is_in(*old(local)),
        heap.wf(), heap.is_in(*old(local)),
        page.is_used_and_primary(*old(local)),
        old(local).page_organization.valid_used_page(page.page_id@, from as int, list_idx),
        (valid_bin_idx(from as int) && to == BIN_FULL)
          || (match old(local).page_organization.pages[page.page_id@].page_header_kind {
            Some(PageHeaderKind::Normal(b, bsize)) =>
              from == BIN_FULL
                && to == b,
                //&& valid_bin_idx(to as int)
                //&& bsize == size_of_bin(to as int),
            None => false,
          })
    ensures
        local.wf(),
        common_preserves(*old(local), *local),
        old(local).page_organization.valid_used_page(next_id, from as int, list_idx + 1) ==>
            local.page_organization.valid_used_page(next_id, from as int, list_idx),
        page.is_used_and_primary(*local),
{
    page_queue_remove(heap, from, page, Tracked(&mut *local), Ghost(list_idx), Ghost(next_id));
    page_queue_push_back(heap, to, page, Tracked(&mut *local), Ghost(next_id), Ghost(from as int), Ghost(list_idx));
}

pub fn page_try_use_delayed_free(page: PagePtr, delay: usize, override_never: bool, Tracked(local): Tracked<&Local>) -> bool
    requires local.wf(), page.wf(), page.is_in(*local),
        page.is_used_and_primary(*local),
        delay == 0, !override_never,
{
    page.get_ref(Tracked(&*local)).xthread_free.try_use_delayed_free(delay, override_never)
}

}
