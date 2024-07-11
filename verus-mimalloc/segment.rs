#![allow(unused_imports)]

use core::intrinsics::{unlikely, likely};

use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::*;
use vstd::modes::*;
use vstd::set_lib::*;
use vstd::pervasive::*;
use vstd::set_lib::*;
use vstd::cell::*;
use vstd::atomic_ghost::*;

use crate::tokens::{Mim, BlockId, DelayState, PageId, PageState, SegmentState, ThreadId};
use crate::types::*;
use crate::layout::*;
use crate::bin_sizes::*;
use crate::config::*;
use crate::page_organization::*;
use crate::linked_list::LL;
use crate::arena::*;
use crate::commit_mask::CommitMask;
use crate::os_mem::MemChunk;
use crate::os_mem_util::*;
use crate::commit_segment::*;
use crate::linked_list::ThreadLLWithDelayBits;
use crate::init::current_thread_count;

verus!{

pub open spec fn good_count_for_block_size(block_size: int, count: int) -> bool {
    count * SLICE_SIZE < block_size * 0x10000
}

pub fn segment_page_alloc(
    heap: HeapPtr,
    block_size: usize,
    page_alignment: usize,
    tld: TldPtr,
    Tracked(local): Tracked<&mut Local>,
) -> (page_ptr: PagePtr)
    requires
        old(local).wf(),
        tld.wf(),
        tld.is_in(*old(local)),
        heap.wf(),
        heap.is_in(*old(local)),
        2 <= block_size,
    ensures
        local.wf_main(),
        common_preserves(*old(local), *local),
        (page_ptr.page_ptr.addr() != 0 ==>
            page_ptr.wf()
            && page_ptr.is_in(*local)
            && local.page_organization.popped == Popped::Ready(page_ptr.page_id@, true)
            && page_init_is_committed(page_ptr.page_id@, *local)
            && good_count_for_block_size(block_size as int,
                    local.page_organization.pages[page_ptr.page_id@].count.unwrap() as int)
        ),
        page_ptr.page_ptr.addr() == 0 ==> local.wf(),
{
    proof { const_facts(); }

    if unlikely(page_alignment > ALIGNMENT_MAX as usize) {
        todo();
    }

    if block_size <= SMALL_OBJ_SIZE_MAX as usize {
        segments_page_alloc(heap, block_size, block_size, tld, Tracked(&mut *local))
    } else if block_size <= MEDIUM_OBJ_SIZE_MAX as usize {
        segments_page_alloc(heap, MEDIUM_PAGE_SIZE as usize, block_size, tld, Tracked(&mut *local))
    } else if block_size <= LARGE_OBJ_SIZE_MAX as usize {
        segments_page_alloc(heap, block_size, block_size, tld, Tracked(&mut *local))
    } else {
        todo(); loop{}
    }
}

fn segments_page_alloc(
    heap: HeapPtr,
    required: usize,
    block_size: usize,
    tld: TldPtr,
    Tracked(local): Tracked<&mut Local>,
) -> (page_ptr: PagePtr)
    requires
        old(local).wf(),
        tld.wf(),
        tld.is_in(*old(local)),
        heap.wf(),
        heap.is_in(*old(local)),
        2 <= block_size <= LARGE_OBJ_SIZE_MAX,
        1 <= required <= LARGE_OBJ_SIZE_MAX,
        (if block_size <= SMALL_OBJ_SIZE_MAX {
            required == block_size
        } else if block_size <= MEDIUM_OBJ_SIZE_MAX {
            required == MEDIUM_PAGE_SIZE
        } else {
            required == block_size
        }),
    ensures
        local.wf_main(),
        common_preserves(*old(local), *local),
        (page_ptr.page_ptr.addr() != 0 ==>
            page_ptr.wf()
            && page_ptr.is_in(*local)
            && local.page_organization.popped == Popped::Ready(page_ptr.page_id@, true)
            && page_init_is_committed(page_ptr.page_id@, *local)
            && good_count_for_block_size(block_size as int,
                    local.page_organization.pages[page_ptr.page_id@].count.unwrap() as int)
        ),
        page_ptr.page_ptr.addr() == 0 ==>
            local.wf(),

{
    proof { const_facts(); }

    let alignment: usize = if required > MEDIUM_PAGE_SIZE as usize
        { MEDIUM_PAGE_SIZE as usize } else { SLICE_SIZE as usize };
    let page_size = align_up(required, alignment);
    let slices_needed = page_size / SLICE_SIZE as usize;

    proof {
        /*let b = (block_size as int) <= (SMALL_OBJ_SIZE_MAX as int);
        if b {
            assert(alignment == SLICE_SIZE);
            assert(page_size == SLICE_SIZE);
            assert(page_size < block_size * 0x10000);
        } else if block_size as int <= MEDIUM_OBJ_SIZE_MAX as int {
            assert(page_size < block_size * 0x10000);
        } else {
            assert(page_size < block_size * 0x10000);
        }*/
        assert(good_count_for_block_size(block_size as int, slices_needed as int));
    }

    proof {
        assert(page_size == slices_needed * SLICE_SIZE as nat) by {
            assert(MEDIUM_PAGE_SIZE as int % SLICE_SIZE as int == 0);
            assert(SLICE_SIZE as int % SLICE_SIZE as int == 0);
            assert(alignment as int % SLICE_SIZE as int == 0);
            assert(page_size as int % alignment as int == 0);
            mod_trans(page_size as int, alignment as int, SLICE_SIZE as int);
            assert(page_size as int % SLICE_SIZE as int == 0);
        }
        assert(1 <= slices_needed <= SLICES_PER_SEGMENT);
    }

    let page_ptr = segments_page_find_and_allocate(slices_needed, tld,
          Tracked(&mut *local), Ghost(block_size as nat));
    if page_ptr.page_ptr.addr() == 0 {
        let roa = segment_reclaim_or_alloc(heap, slices_needed, block_size, tld,
            Tracked(&mut *local));
        if roa.segment_ptr.addr() == 0 {
            return PagePtr::null();
        } else {
            return segments_page_alloc(heap, required, block_size, tld, Tracked(&mut *local));
        }
    } else {
        return page_ptr;
    }
}

fn segment_reclaim_or_alloc(
    heap: HeapPtr,
    needed_slices: usize,
    block_size: usize,
    tld: TldPtr,
    Tracked(local): Tracked<&mut Local>,
) -> (segment_ptr: SegmentPtr)
    requires
        old(local).wf(),
        tld.wf(),
        tld.is_in(*old(local)),
        heap.wf(),
        heap.is_in(*old(local)),
    ensures
        local.wf(),
        common_preserves(*old(local), *local),

{
    // TODO reclaiming

    let arena_id = heap.get_arena_id(Tracked(&*local));
    segment_alloc(0, 0, arena_id, tld, Tracked(&mut *local))
}

#[verifier::spinoff_prover]
fn segments_page_find_and_allocate(
    slice_count0: usize,
    tld_ptr: TldPtr,
    Tracked(local): Tracked<&mut Local>,
    Ghost(block_size): Ghost<nat>,
) -> (page_ptr: PagePtr)
    requires
        old(local).wf(),
        tld_ptr.wf(),
        tld_ptr.is_in(*old(local)),
        1 <= slice_count0 <= SLICES_PER_SEGMENT,
    ensures
        local.wf_main(),
        common_preserves(*old(local), *local),
        (page_ptr.page_ptr.addr() != 0 ==>
            page_ptr.wf()
            && page_ptr.is_in(*local)
            //&& allocated_block_tokens(blocks@, page_ptr.page_id@, block_size, n_blocks, local.instance)
            && local.page_organization.popped == Popped::Ready(page_ptr.page_id@, true)
            && page_init_is_committed(page_ptr.page_id@, *local)
            && (slice_count0 > 0 ==> local.page_organization.pages[page_ptr.page_id@].count == Some(slice_count0 as nat))
        ),
        (page_ptr.page_ptr.addr() == 0 ==> local.wf()),
{
    let mut sbin_idx = slice_bin(slice_count0);
    let slice_count = if slice_count0 == 0 { 1 } else { slice_count0 };

    while sbin_idx <= SEGMENT_BIN_MAX
        invariant
            local.wf(),
            tld_ptr.wf(),
            tld_ptr.is_in(*local),
            slice_count > 0,
            local.heap_id == old(local).heap_id,
            slice_count == (if slice_count0 == 0 { 1 } else { slice_count0 }),
            common_preserves(*old(local), *local),
    {
        let mut slice_ptr = ptr_ref(tld_ptr.tld_ptr, Tracked(&local.tld))
              .segments.span_queue_headers[sbin_idx].first;
        let ghost mut list_idx = 0int;
        let ghost mut slice_page_id: Option<PageId> =
            local.page_organization.unused_dlist_headers[sbin_idx as int].first;
        proof {
            local.page_organization.first_is_in(sbin_idx as int);
        }

        while slice_ptr.addr() != 0
            invariant
                local.wf(),
                tld_ptr.wf(),
                tld_ptr.is_in(*local),
                is_page_ptr_opt(slice_ptr, slice_page_id),
                slice_page_id.is_Some() ==>
                    local.page_organization.valid_unused_page(
                        slice_page_id.get_Some_0(), sbin_idx as int, list_idx),
                slice_count > 0,
                local.heap_id == old(local).heap_id,
                slice_count == (if slice_count0 == 0 { 1 } else { slice_count0 }),
                common_preserves(*old(local), *local),
        {
            let slice = PagePtr {
                page_ptr: slice_ptr,
                page_id: Ghost(slice_page_id.get_Some_0())
            };
            assert(slice.wf());

            let found_slice_count = slice.get_count(Tracked(&*local)) as usize;
            if found_slice_count >= slice_count {
                let segment = SegmentPtr::ptr_segment(slice);

                assert(tld_ptr.is_in(*local));
                span_queue_delete(
                    tld_ptr,
                    sbin_idx,
                    slice,
                    Tracked(&mut *local),
                    Ghost(list_idx),
                    Ghost(found_slice_count as int));

                assert(tld_ptr.is_in(*local));

                if found_slice_count > slice_count {
                    /*proof {
                        let current_slice_count = found_slice_count;
                        let target_slice_count = slice_count;
                        assert((local).wf_main());
                        assert(tld_ptr.wf());
                        assert(tld_ptr.is_in(*local));
                        assert(slice.wf());
                        assert((local).page_organization.popped == Some(Popped { page_id: slice.page_id@ }));
                        assert((local).page_organization.pages[slice.page_id@].countget_Some_0()
                            == current_slice_count);
                        assert(SLICES_PER_SEGMENT >= current_slice_count);
                        assert(current_slice_count > target_slice_count);
                        assert(target_slice_count > 0);
                    }*/

                    segment_slice_split(
                        slice,
                        found_slice_count,
                        slice_count,
                        tld_ptr,
                        Tracked(&mut *local));
                }

                assert(tld_ptr.is_in(*local));

                let suc = segment_span_allocate(
                    segment,
                    slice,
                    slice_count,
                    tld_ptr,
                    Tracked(&mut *local));
                if !suc {
                    todo();
                }

                //assert(local.wf_main());
                //assert(slice.is_in(*local));
                //assert(allocated_block_tokens(block_tokens, slice.page_id@, block_size, n_blocks, local.instance));
                //assert(tld_ptr.is_in(*local));
                return slice;
            }

            slice_ptr = slice.get_next(Tracked(&*local));
            proof {
                local.page_organization.next_is_in(
                    slice_page_id.get_Some_0(), sbin_idx as int, list_idx);

                slice_page_id = local.page_organization.pages[slice_page_id.get_Some_0()]
                    .dlist_entry.get_Some_0().next;
                list_idx = list_idx + 1;
            }
        }

        sbin_idx = sbin_idx + 1;
    }

    PagePtr::null()
}

#[verifier::spinoff_prover]
fn span_queue_delete(
    tld_ptr: TldPtr,
    sbin_idx: usize,

    slice: PagePtr,

    Tracked(local): Tracked<&mut Local>,
    Ghost(list_idx): Ghost<int>,
    Ghost(count): Ghost<int>,
)
    requires
        old(local).wf_main(),
        tld_ptr.wf(),
        tld_ptr.is_in(*old(local)),
        slice.wf(),
        old(local).page_organization.valid_unused_page(slice.page_id@, sbin_idx as int, list_idx),
        count == old(local).page_organization.pages[slice.page_id@].count.get_Some_0(),
        (match old(local).page_organization.popped {
            Popped::No => true,
            Popped::SegmentFreeing(sid, idx) =>
                slice.page_id@.segment_id == sid && slice.page_id@.idx == idx,
            _ => false,
        })
    ensures
        local.wf_main(),
        common_preserves(*old(local), *local),
        local.page_organization.popped == (match old(local).page_organization.popped {
            Popped::No => Popped::VeryUnready(slice.page_id@.segment_id, slice.page_id@.idx as int, count, false),
            Popped::SegmentFreeing(sid, idx) => Popped::SegmentFreeing(sid, idx + count),
            _ => arbitrary(),
        }),

        local.page_organization.pages.dom().contains(slice.page_id@),
        old(local).pages[slice.page_id@]
          == local.pages[slice.page_id@],
        local.page_organization.pages[slice.page_id@].is_used == false,
        //old(local).page_organization.pages[slice.page_id@]
        //    == local.page_organization.pages[slice.page_id@],
{
    let prev = slice.get_prev(Tracked(&*local));
    let next = slice.get_next(Tracked(&*local));

    let ghost mut next_state;
    proof {
        //assert(local.page_organization.pages.dom().contains(slice.page_id@));
        next_state = PageOrg::take_step::take_page_from_unused_queue(
            local.page_organization,
            slice.page_id@,
            sbin_idx as int,
            list_idx);
    }

    if prev.addr() == 0 {
        tld_get_mut!(tld_ptr, local, tld => {
            let cq = tld.segments.span_queue_headers[sbin_idx];
            tld.segments.span_queue_headers.set(
                sbin_idx,
                SpanQueueHeader {
                    first: next,
                    .. cq
                });
        });
    } else {
        //assert(local.page_organization.pages[slice.page_id@].dlist_entry.get_Some_0().prev.is_Some());
        let prev_page_ptr = PagePtr { page_ptr: prev,
            page_id: Ghost(local.page_organization.pages[slice.page_id@].dlist_entry.get_Some_0().prev.get_Some_0()), };
        //assert(prev_page_ptr.wf());

        /*assert(local.page_organization_valid());
        assert(local.page_organization.pages.dom().contains(prev_page_ptr.page_id@));
        assert(page_organization_pages_match_data(
            local.page_organization.pages[prev_page_ptr.page_id@],
            local.pages[prev_page_ptr.page_id@],
            local.psa[prev_page_ptr.page_id@],
            prev_page_ptr.page_id@,
            local.page_organization.popped,
            ));

        assert(!local.page_organization.pages[prev_page_ptr.page_id@].is_used);
        assert(local.psa.dom().contains(prev_page_ptr.page_id@));*/

        unused_page_get_mut_next!(prev_page_ptr, local, n => {
            n = next;
        });
    }

    if next.addr() == 0 {
        tld_get_mut!(tld_ptr, local, tld => {
            let cq = tld.segments.span_queue_headers[sbin_idx];
            tld.segments.span_queue_headers.set(
                sbin_idx,
                SpanQueueHeader {
                    last: prev,
                    .. cq
                });
        });
    } else {
        let next_page_ptr = PagePtr { page_ptr: next,
            page_id: Ghost(local.page_organization.pages[slice.page_id@].dlist_entry.get_Some_0().next.get_Some_0()), };
        //assert(next_page_ptr.wf());

        //assert(local.psa.dom().contains(next_page_ptr.page_id@));

        unused_page_get_mut_prev!(next_page_ptr, local, p => {
            p = prev;
        });
    }

    proof {
        let old_state = local.page_organization;
        local.page_organization = next_state;

        /*if old(local).page_organization.pages[slice.page_id@].dlist_entry.get_Some_0().prev.is_Some() &&
            old(local).page_organization.pages[slice.page_id@].dlist_entry.get_Some_0().next.is_Some()
        {
            let old_p = old(local).page_organization.pages[slice.page_id@].dlist_entry.get_Some_0().prev.get_Some_0();
            let old_n = old(local).page_organization.pages[slice.page_id@].dlist_entry.get_Some_0().next.get_Some_0();

            let p = local.page_organization.pages[slice.page_id@].dlist_entry.get_Some_0().prev.get_Some_0();
            let n = local.page_organization.pages[slice.page_id@].dlist_entry.get_Some_0().next.get_Some_0();

            //assert(old_p == p);
            //assert(old_n == n);

            //assert(page_organization_pages_match_data(old_state.pages[p], old(local).pages[p], old(local).psa[p], p, old_state.popped));
            //assert(old_state.pages[p].offset == local.page_organization.pages[p].offset);

            //assert(page_organization_pages_match_data(local.page_organization.pages[p], local.pages[p], local.psa[p], p, local.page_organization.popped));
            //assert(page_organization_pages_match_data(local.page_organization.pages[n], local.pages[n], local.psa[n], n, local.page_organization.popped));
            //assert(page_organization_pages_match_data(local.page_organization.pages[slice.page_id@], local.pages[slice.page_id@], local.psa[slice.page_id@], slice.page_id@, local.page_organization.popped));

            /*let org_pages = local.page_organization.pages;
            let pages = local.pages;

            let old_org_pages = old(local).page_organization.pages;
            let old_pages = old(local).pages;

            let last_id = PageId { idx: (slice.page_id@.idx + count - 1) as nat, .. slice.page_id@ };

            assert forall |page_id| #[trigger] org_pages.dom().contains(page_id) implies
                page_organization_pages_match_data(org_pages[page_id], pages[page_id], local.psa[page_id], page_id, local.page_organization.popped)
            by {
                if page_id == last_id {
                    assert(page_organization_pages_match_data(org_pages[page_id], pages[page_id], local.psa[page_id], page_id, local.page_organization.popped));
                } else if page_id == p {
                    assert(page_organization_pages_match_data(org_pages[page_id], pages[page_id], local.psa[page_id], page_id, local.page_organization.popped));
                } else if page_id == n {
                    assert(page_organization_pages_match_data(org_pages[page_id], pages[page_id], local.psa[page_id], page_id, local.page_organization.popped));
                } else if page_id == slice.page_id@ {
                    assert(page_organization_pages_match_data(org_pages[page_id], pages[page_id], local.psa[page_id], page_id, local.page_organization.popped));
                } else {
                    //assert(old(local.psa.dom().contains(page_id));
                    //assert(local.psa.dom().contains(page_id));

                    assert(page_organization_pages_match_data(old_org_pages[page_id], old_pages[page_id], local.psa[page_id], page_id, old(local).page_organization.popped));
                    //assert(old_org_pages[page_id] == org_pages[page_id]);
                    //assert(old_pages[page_id] == pages[page_id]);
                    assert(page_organization_pages_match_data(org_pages[page_id], pages[page_id], local.psa[page_id], page_id, local.page_organization.popped));
                }
            }*/
        }*/

        //let org_queues = local.page_organization.unused_dlist_headers;
        //let queues = local.tld@.value.get_Some_0().segments.span_queue_headers;
        /*assert(is_page_ptr_opt(queues@[sbin_idx as int].first, org_queues[sbin_idx as int].first));
        assert(is_page_ptr_opt(queues@[sbin_idx as int].last, org_queues[sbin_idx as int].last));
        assert(page_organization_queues_match(org_queues, queues@));

        assert_sets_equal!(local.page_organization.pages.dom(), local.pages.dom());*/
        preserves_mem_chunk_good(*old(local), *local);

        //assert(local.wf_main());
    }
}

#[verifier::spinoff_prover]
fn segment_slice_split(
    slice: PagePtr,
    current_slice_count: usize,
    target_slice_count: usize,
    tld_ptr: TldPtr,

    Tracked(local): Tracked<&mut Local>,
)
    requires
        old(local).wf_main(),
        tld_ptr.wf(),
        tld_ptr.is_in(*old(local)),
        slice.wf(),
        old(local).page_organization.popped == Popped::VeryUnready(slice.page_id@.segment_id, slice.page_id@.idx as int, current_slice_count as int, false),
        old(local).page_organization.pages.dom().contains(slice.page_id@),
        //old(local).page_organization.pages[slice.page_id@].count.is_some(),
        old(local).page_organization.pages[slice.page_id@].is_used == false,
        SLICES_PER_SEGMENT >= current_slice_count > target_slice_count,
        target_slice_count > 0,
    ensures
        local.wf_main(),
        common_preserves(*old(local), *local),
        slice.wf(),
        local.page_organization.popped == Popped::VeryUnready(slice.page_id@.segment_id, slice.page_id@.idx as int, target_slice_count as int, false),
        local.page_organization.pages.dom().contains(slice.page_id@),
        local.page_organization.pages[slice.page_id@].is_used == false,
{
    proof {
        local.page_organization.get_count_bound_very_unready();
        //assert(local.page_organization.pages[slice.page_id@].count == Some(current_slice_coun
        //assert(slice.page_id@.idx + current_slice_count <= SLICES_PER_SEGMENT + 1);
        //assert(slice.page_id@.idx + target_slice_count <= SLICES_PER_SEGMENT);
    }
    let next_slice = slice.add_offset(target_slice_count);

    //let count_being_returned = target_slice_count - current_slice_count;
    let bin_idx = slice_bin(current_slice_count - target_slice_count);

    let ghost mut next_state;
    proof {
        next_state = PageOrg::take_step::split_page(
            local.page_organization,
            slice.page_id@,
            current_slice_count as int,
            target_slice_count as int,
            bin_idx as int);
    }

    let first_in_queue;

    tld_get_mut!(tld_ptr, local, tld => {
        let mut cq = tld.segments.span_queue_headers[bin_idx];
        first_in_queue = cq.first;

        cq.first = next_slice.page_ptr;
        if first_in_queue.addr() == 0 {
            cq.last = next_slice.page_ptr;
        }

        tld.segments.span_queue_headers.set(bin_idx, cq);
    });

    if first_in_queue.addr() != 0 {
        let first_in_queue_ptr = PagePtr { page_ptr: first_in_queue,
            page_id: Ghost(local.page_organization.unused_dlist_headers[bin_idx as int].first.get_Some_0()) };
        unused_page_get_mut_prev!(first_in_queue_ptr, local, p => {
            p = next_slice.page_ptr;
        });
    }

    unused_page_get_mut_count!(slice, local, c => {
        c = target_slice_count as u32;
    });

    unused_page_get_mut_inner!(next_slice, local, inner => {
        inner.xblock_size = 0;
    });
    unused_page_get_mut_prev!(next_slice, local, p => {
        p = core::ptr::null_mut();
    });
    unused_page_get_mut_next!(next_slice, local, n => {
        n = first_in_queue;
    });
    unused_page_get_mut_count!(next_slice, local, c => {
        c = (current_slice_count - target_slice_count) as u32;
    });
    unused_page_get_mut!(next_slice, local, page => {
        page.offset = 0;
    });

    proof { const_facts(); }

    if current_slice_count > target_slice_count + 1 {
        let last_slice = slice.add_offset(current_slice_count - 1);
        unused_page_get_mut_inner!(last_slice, local, inner => {
            inner.xblock_size = 0;
        });
        unused_page_get_mut_count!(last_slice, local, c => {
            c = (current_slice_count - target_slice_count) as u32;
        });
        unused_page_get_mut!(last_slice, local, page => {
            //assert(0 <= (current_slice_count - target_slice_count) as u32 <= 512);
            //assert(SIZEOF_PAGE_HEADER == 32);
            assert(SIZEOF_PAGE_HEADER as u32 == 80);
            //assert((current_slice_count - target_slice_count) as u32 * (SIZEOF_PAGE_HEADER as u32)
            //    == (current_slice_count - target_slice_count) as u32 * 32);
            page.offset = (current_slice_count - target_slice_count - 1) as u32
                * (SIZEOF_PAGE_HEADER as u32);
        });
    }

    proof {
        local.page_organization = next_state;

        /*let page_id = slice.page_id@;
        let next_id = next_slice.page_id@;
        let last_page_id = PageId { idx: (page_id.idx + current_slice_count - 1) as nat, .. page_id };

        let old_org_pages = old(local).page_organization.pages;
        let old_pages = old(local).pages;
        let old_psa = old(local).psa;

        let org_pages = local.page_organization.pages;
        let pages = local.pages;*/
        local.psa = local.psa.union_prefer_right(local.unused_pages);
        //let psa = local.psa;

        //let old_org_queues = old(local).page_organization.unused_dlist_headers;
        //let old_queues = old(local).tld@.value.get_Some_0().segments.span_queue_headers;

        //assert(page_organization_pages_match_data(org_pages[slice.page_id@], pages[slice.page_id@], psa[slice.page_id@], slice.page_id@, local.page_organization.popped));

        //assert(page_organization_pages_match_data(org_pages[next_slice.page_id@], pages[next_slice.page_id@], psa[next_slice.page_id@], next_slice.page_id@, local.page_organization.popped));

        /*if current_slice_count > target_slice_count + 1 {
            assert(last_page_id != next_id);
            assert(last_page_id != page_id);
            assert(page_organization_pages_match_data(org_pages[last_page_id], pages[last_page_id], psa[last_page_id], last_page_id, local.page_organization.popped));
        } else {
            assert(page_organization_pages_match_data(org_pages[last_page_id], pages[last_page_id], psa[last_page_id], last_page_id, local.page_organization.popped));
        }*/

        /*if first_in_queue.id() != 0 {
            let first_page_id = local.page_organization.unused_dlist_headers[bin_idx as int].first.get_Some_0();
            assert(page_organization_pages_match_data(org_pages[first_page_id], pages[first_page_id], psa[first_page_id]));
        }*/

        //let last_slice = slice.add_offset(current_slice_count - 1);
        //assert(page_organization_pages_match_data(org_pages[last_slice.page_id@], pages[last_slice.page_id@], psa[last_slice.page_id@]));

        /*assert forall |pid| #[trigger] org_pages.dom().contains(pid) implies
            page_organization_pages_match_data(org_pages[pid], pages[pid], psa[pid], pid, local.page_organization.popped)
        by {
            let first_id = old(local).page_organization.unused_dlist_headers[bin_idx as int].first.get_Some_0();
            if pid == page_id { 
                assert(page_organization_pages_match_data(org_pages[pid], pages[pid], psa[pid], pid, local.page_organization.popped));
            } else if pid == next_id {
                assert(page_organization_pages_match_data(org_pages[pid], pages[pid], psa[pid], pid, local.page_organization.popped));
            } else if pid == last_page_id {
                assert(page_organization_pages_match_data(org_pages[pid], pages[pid], psa[pid], pid, local.page_organization.popped));
            } else if pid == first_id {
                if old_org_queues[bin_idx as int].first.is_some() {
                    assert(is_page_ptr_opt(old_queues@[bin_idx as int].first, old_org_queues[bin_idx as int].first));
                    assert(Some(first_id) == old_org_queues[bin_idx as int].first);
                    assert(first_in_queue == old_queues@[bin_idx as int].first);

                    assert(is_page_ptr(first_in_queue.id(), first_id));
                    assert(next_slice.page_id@ == next_id);
                    assert(Some(next_slice.page_id@) == local.page_organization.pages[pid].dlist_entry.unwrap().prev);
                    assert(is_page_ptr(next_slice.page_ptr.id(), next_slice.page_id@));
                    assert(next_slice.page_ptr.id() != 0);
                    assert(is_page_ptr_opt(next_slice.page_ptr, local.page_organization.pages[pid].dlist_entry.unwrap().prev));
                    assert(page_organization_pages_match_data(org_pages[pid], pages[pid], psa[pid], pid, local.page_organization.popped));
                } else {
                    assert(page_organization_pages_match_data(org_pages[pid], pages[pid], psa[pid], pid, local.page_organization.popped));
                }
            } else {
                assert(next_slice.page_id@ == next_id);
                assert(page_organization_pages_match_data(old_org_pages[pid], old_pages[pid], old_psa[pid], pid, old(local).page_organization.popped));
                assert(page_organization_pages_match_data(org_pages[pid], pages[pid], psa[pid], pid, local.page_organization.popped));
            }
        }*/

        /*assert forall |page_id: PageId| (#[trigger] local.page_organization.pages.dom().contains(page_id) &&
            !local.page_organization.pages[page_id].is_used) <==> local.unused_pages.dom().contains(page_id)
        by {
            if (local.page_organization.pages.dom().contains(page_id) && !local.page_organization.pages[page_id].is_used) {
                assert(local.unused_pages.dom().contains(page_id));
            }
            if local.unused_pages.dom().contains(page_id) {
                assert(local.page_organization.pages.dom().contains(page_id) && !local.page_organization.pages[page_id].is_used);
            }
        }*/

        //assert(forall |page_id: PageId| #[trigger] local.unused_pages.dom().contains(page_id) ==>
        //    local.unused_pages[page_id] == local.psa[page_id]);

        //assert(local.page_organization_valid());
        preserves_mem_chunk_good(*old(local), *local);
        //assert(local.wf_main());
    }
}

#[verifier::spinoff_prover]
fn segment_span_allocate(
    segment: SegmentPtr,
    slice: PagePtr,
    slice_count: usize,
    tld_ptr: TldPtr,
    Tracked(local): Tracked<&mut Local>,
) -> (success: bool)
    requires
        old(local).wf_main(),
        slice.wf(),
        segment.wf(),
        segment.segment_id == slice.page_id@.segment_id,
        segment.is_in(*old(local)),

        old(local).page_organization.popped == Popped::VeryUnready(slice.page_id@.segment_id, slice.page_id@.idx as int, slice_count as int, false)
          || (old(local).page_organization.popped == Popped::SegmentCreating(slice.page_id@.segment_id) && slice.page_id@.idx == 0 && slice_count < SLICES_PER_SEGMENT),
        old(local).page_organization.pages.dom().contains(slice.page_id@),
        old(local).page_organization.pages[slice.page_id@].is_used == false,

        SLICES_PER_SEGMENT >= slice_count > 0,
    ensures
        local.wf_main(),
        success ==> old(local).page_organization.popped.is_VeryUnready() ==> local.page_organization.popped == Popped::Ready(slice.page_id@, true),
        success ==> old(local).page_organization.popped.is_SegmentCreating() ==> local.page_organization.popped == Popped::VeryUnready(slice.page_id@.segment_id, slice_count as int, SLICES_PER_SEGMENT - slice_count as int, true),
        success ==> local.page_organization.pages.dom().contains(slice.page_id@),
        success ==> local.page_organization.pages[slice.page_id@].count
            == Some(slice_count as nat),
        success ==> page_init_is_committed(slice.page_id@, *local),
        common_preserves(*old(local), *local),
        segment.is_in(*local),
{
    let ghost mut next_state;
    proof {
        const_facts();
        if local.page_organization.popped.is_VeryUnready() {
            next_state = PageOrg::take_step::allocate_popped(local.page_organization);
        } else {
            next_state = PageOrg::take_step::forget_about_first_page(local.page_organization, slice_count as int);
        }
    }

    let p = segment_page_start_from_slice(segment, slice, 0);

    //assert(slice_count * SLICE_SIZE <= SLICES_PER_SEGMENT * SLICE_SIZE);
    if !segment_ensure_committed(segment, p, slice_count * SLICE_SIZE as usize, Tracked(&mut *local)) {
        return false;
    }

    let ghost old_local = *local;
    let ghost first_page_id = slice.page_id@;

    //assert(local.page_organization.pages.dom().contains(slice.page_id@));

    let ghost range = first_page_id.range_from(0, slice_count as int);

    assert forall |pid| range.contains(pid) implies #[trigger] local.unused_pages.dom().contains(pid)
    by {
        assert(local.pages.dom().contains(pid));
    }

    let tracked mut first_psa = local.unused_pages.tracked_remove(first_page_id);
    let mut page = ptr_mut_read(slice.page_ptr, Tracked(&mut first_psa.points_to));
    page.offset = 0;
    ptr_mut_write(slice.page_ptr, Tracked(&mut first_psa.points_to), page);
    proof {
        local.unused_pages.tracked_insert(first_page_id, first_psa);
    }
    unused_page_get_mut_count!(slice, local, count => {
        // this is usually already set. I think the one case where it actually needs to
        // be set is when initializing the segment.
        count = slice_count as u32;
    });
    unused_page_get_mut_inner!(slice, local, inner => {
        // Not entirely sure what the rationale for setting to bsize to this value is.
        // In normal operation, we're going to set the block_size to something else soon.
        // If we are currently setting up page 0 as part of segment initialization,
        // we do need to set this to some nonzero value.
        let bsize = slice_count * SLICE_SIZE as usize;
        inner.xblock_size = if bsize >= HUGE_BLOCK_SIZE as usize { HUGE_BLOCK_SIZE } else { bsize as u32 };
        //assert(inner.xblock_size != 0);
    });

    // Set up the remaining pages
    let mut i: usize = 1;
    let ghost local_snapshot = *local;
    let extra = slice_count - 1;
    while i <= extra
        invariant 1 <= i <= extra + 1,
          first_page_id.idx + extra < SLICES_PER_SEGMENT,
          local == (Local { unused_pages: local.unused_pages, .. local_snapshot }),
          local.unused_pages.dom() == local_snapshot.unused_pages.dom(),
          slice.wf(),
          slice.page_id == first_page_id,
          forall |page_id|
              #[trigger] first_page_id.range_from(1, extra + 1).contains(page_id) ==>
                  local.unused_pages.dom().contains(page_id)
                  && (local.unused_pages.dom().contains(page_id) ==>
                    local.unused_pages[page_id].points_to.is_init()
                    && is_page_ptr(local.unused_pages[page_id].points_to.ptr() as int, page_id)),
          forall |page_id|
              #[trigger] local.unused_pages.dom().contains(page_id) ==>
              (
                  if first_page_id.range_from(1, i as int).contains(page_id) {
                      psa_differ_only_in_offset(
                          local.unused_pages[page_id],
                          local_snapshot.unused_pages[page_id])
                      && local.unused_pages[page_id].points_to.value().offset ==
                          (page_id.idx - first_page_id.idx) * SIZEOF_PAGE_HEADER
                  } else {
                      local.unused_pages[page_id] == local_snapshot.unused_pages[page_id]
                  }
              ),
    {
        proof { const_facts(); }
        let ghost prelocal = *local;
        let this_slice = slice.add_offset(i);
        let ghost this_page_id = PageId { idx: (first_page_id.idx + i) as nat, .. first_page_id };
        assert(first_page_id.range_from(1, extra + 1).contains(this_page_id));
        //assert(is_page_ptr(local.unused_pages[this_page_id].points_to@.pptr, this_page_id));
        //assert(i * SIZEOF_PAGE_HEADER <= SLICES_PER_SEGMENT * SIZEOF_PAGE_HEADER);

        let tracked mut this_psa = local.unused_pages.tracked_remove(this_page_id);
        let mut page = ptr_mut_read(this_slice.page_ptr, Tracked(&mut this_psa.points_to));
        page.offset = i as u32 * SIZEOF_PAGE_HEADER as u32;
        ptr_mut_write(this_slice.page_ptr, Tracked(&mut this_psa.points_to), page);
        proof {
            local.unused_pages.tracked_insert(this_page_id, this_psa);
            assert_sets_equal!(local.unused_pages.dom() == prelocal.unused_pages.dom());
        }

        i = i + 1;

        /*proof {
            assert forall |page_id|
              #[trigger] local.unused_pages.dom().contains(page_id) implies
              (
                  if first_page_id.range_from(1, i as int).contains(page_id) {
                      psa_differ_only_in_offset(
                          local.unused_pages[page_id],
                          local_snapshot.unused_pages[page_id])
                      && local.unused_pages[page_id].points_to.value().offset ==
                          page_id.idx - first_page_id.idx
                  } else {
                      local.unused_pages[page_id] == local_snapshot.unused_pages[page_id]
                  }
              )
           by {
              if first_page_id.range_from(1, i as int).contains(page_id) {
                      assert(psa_differ_only_in_offset(
                          local.unused_pages[page_id],
                          local_snapshot.unused_pages[page_id]));
                      if page_id.idx - first_page_id.idx == i - 1 {
                          assert(page_id == this_page_id);
                          assert(local.unused_pages[this_page_id].points_to.value().offset == i - 1);
                          assert(local.unused_pages[page_id].points_to.value().offset ==
                              page_id.idx - first_page_id.idx);
                      } else {
                          assert(local.unused_pages[page_id].points_to.value().offset ==
                              page_id.idx - first_page_id.idx);
                      }
                  } else {
                      assert(local.unused_pages[page_id] == local_snapshot.unused_pages[page_id]);
                  }
           }
        }*/
    }

    unused_page_get_mut_inner!(slice, local, inner => {
        inner.set_is_reset(false);
        inner.set_is_committed(false);
    });
    segment_get_mut_main2!(segment, local, main2 => {
        main2.used = main2.used + 1;
    });

    proof {
        let old_po = local.page_organization;
        local.page_organization = next_state;
        local.psa = local.psa.union_prefer_right(local.unused_pages);

        preserves_mem_chunk_good(old_local, *local);

        /*if old_po.popped.is_VeryUnready() {
            assert(local.page_organization.pages[first_page_id].page_header_kind.is_none());
            assert(page_organization_pages_match_data(local.page_organization.pages[first_page_id], local.pages[first_page_id], local.psa[first_page_id], first_page_id, local.page_organization.popped));
            assert(page_organization_pages_match(local.page_organization.pages, local.pages, local.psa, local.page_organization.popped));
            assert(page_organization_segments_match(local.page_organization.segments, local.segments));
            assert(local.page_organization_valid());
        } else {
            let org_pages = local.page_organization.pages;
            let pages = local.pages;
            let psa = local.psa;
            let popped = local.page_organization.popped;
            assert forall |pid| #[trigger] org_pages.dom().contains(pid) implies
              page_organization_pages_match_data(org_pages[pid], pages[pid], psa[pid], pid, popped)
            by {
                if pid == first_page_id {
                    assert(page_organization_pages_match_data(org_pages[pid], pages[pid], psa[pid], pid, popped));
                } else {
                    assert(page_organization_pages_match_data(org_pages[pid], pages[pid], psa[pid], pid, popped));
                }
            }
            assert(local.page_organization.pages[first_page_id].page_header_kind.is_none());
            assert(page_organization_pages_match_data(local.page_organization.pages[first_page_id], local.pages[first_page_id], local.psa[first_page_id], first_page_id, local.page_organization.popped));
            assert(page_organization_pages_match(local.page_organization.pages, local.pages, local.psa, local.page_organization.popped));
            assert(page_organization_segments_match(local.page_organization.segments, local.segments));
            assert(local.page_organization_valid());
        }
        assert(local.wf_main());*/
    }

    return true;
}

// segment_reclaim_or_alloc
//  -> segment_alloc
//  -> segment_os_alloc
//  -> arena_alloc_aligned

// For normal pages, required == 0
// For huge pages, required == ?
#[verifier::spinoff_prover]
fn segment_alloc(
    required: usize,
    page_alignment: usize,
    req_arena_id: ArenaId,
    tld: TldPtr,
    Tracked(local): Tracked<&mut Local>,
    // os_tld,
    // huge_page,
) -> (segment_ptr: SegmentPtr)
    requires
        old(local).wf(),
        tld.wf(),
        tld.is_in(*old(local)),
        required == 0, // only handling non-huge-pages for now
    ensures
        local.wf(),
        common_preserves(*old(local), *local),
{
    proof { const_facts(); }

    let (segment_slices, pre_size, info_slices) = segment_calculate_slices(required);
    let eager_delay = (current_thread_count() > 1 &&
          tld.get_segments_count(Tracked(&*local)) < option_eager_commit_delay() as usize);
    let eager = !eager_delay && option_eager_commit();
    let commit = eager || (required > 0);
    let is_zero = false;

    let mut commit_mask = CommitMask::empty();
    let mut decommit_mask = CommitMask::empty();

    let (pre_segment_ptr, new_psegment_slices, new_ppre_size, new_pinfo_slices, is_zero, pcommit, memid, mem_large, is_pinned, align_offset, Tracked(mem_chunk)) = segment_os_alloc(
        required,
        page_alignment,
        eager_delay,
        req_arena_id,
        segment_slices,
        pre_size,
        info_slices,
        &mut commit_mask,
        &mut decommit_mask,
        commit,
        tld,
        Tracked(&mut *local));

    let ghost local_snap1 = *local;

    if pre_segment_ptr.is_null() {
        return pre_segment_ptr;
    }

    let tracked thread_state_tok = local.take_thread_token();
    let ghost pre_segment_id = pre_segment_ptr.segment_id@;
    let ghost segment_state = SegmentState {
        shared_access: arbitrary(),
        is_enabled: false,
    };
    let tracked (Tracked(thread_state_tok), Ghost(tos), Tracked(thread_of_segment_tok))
        = local.instance.create_segment_mk_tokens(
            local.thread_id,
            pre_segment_id,
            segment_state,
            thread_state_tok);
    let ghost segment_id = Mim::State::mk_fresh_segment_id(tos, pre_segment_id);
    let segment_ptr = SegmentPtr {
        segment_ptr: pre_segment_ptr.segment_ptr,
        segment_id: Ghost(segment_id),
    };
    proof {
        local.thread_token = thread_state_tok;
        const_facts();
        segment_start_eq(segment_id, pre_segment_id);
        //assert(commit_mask.bytes(segment_id) == commit_mask.bytes(pre_segment_id));
    }

    // the C version skips this step if the bytes are all zeroed by the OS
    // We would need a complex transmute operation to do the same thing

    let tracked seg_header_points_to_raw = mem_chunk.take_points_to_range(
        segment_start(segment_id), SIZEOF_SEGMENT_HEADER as int);

    //assert(SIZEOF_SEGMENT_HEADER == vstd::layout::size_of::<SegmentHeader>());
    proof { segment_start_mult8(segment_id); }
    //assert(segment_start(segment_id) % vstd::layout::align_of::<SegmentHeader>() as int == 0);
    vstd::layout::layout_for_type_is_valid::<SegmentHeader>(); // $line_count$Proof$

    let tracked mut seg_header_points_to = seg_header_points_to_raw.into_typed::<SegmentHeader>(segment_start(segment_id) as usize);
    let allow_decommit = option_allow_decommit() && !is_pinned && !mem_large;
    let (pcell_main, Tracked(pointsto_main)) = PCell::new(SegmentHeaderMain {
        memid: memid,
        mem_is_pinned: is_pinned,
        mem_is_large: mem_large,
        mem_is_committed: commit_mask.is_full(),
        mem_alignment: page_alignment,
        mem_align_offset: align_offset,
        allow_decommit: allow_decommit,
        decommit_expire: 0,
        decommit_mask: if allow_decommit { decommit_mask } else { CommitMask::empty() },
        commit_mask: commit_mask,
    });
    let (pcell_main2, Tracked(pointsto_main2)) = PCell::new(SegmentHeaderMain2 {
        next: core::ptr::null_mut(),
        abandoned: 0,
        abandoned_visits: 0,
        used: 0,
        cookie: 0,
        segment_slices: 0,
        segment_info_slices: 0,
        kind: if required == 0 { SegmentKind::Normal } else { SegmentKind::Huge },
        slice_entries: 0,
    });
    let (cur_thread_id, Tracked(is_thread)) = crate::thread::thread_id();
    proof { local.is_thread.agrees(is_thread); }
    ptr_mut_write(segment_ptr.segment_ptr, Tracked(&mut seg_header_points_to), SegmentHeader {
        main: pcell_main,
        abandoned_next: 0,
        main2: pcell_main2,
        thread_id: AtomicU64::new(
            Ghost((Ghost(local.instance), Ghost(segment_id))),
            cur_thread_id.thread_id,
            Tracked(thread_of_segment_tok),
        ),
        instance: Ghost(local.instance),
        segment_id: Ghost(segment_id),
    });

    //assert(segment_ptr.segment_ptr.id() + SEGMENT_SIZE < usize::MAX);
    let mut i: usize = 0;
    let mut cur_page_ptr = segment_ptr.segment_ptr.with_addr(
        segment_ptr.segment_ptr.addr() + SIZEOF_SEGMENT_HEADER
    ) as *mut Page;
    //assert(i * SIZEOF_PAGE_HEADER == 0);
    let ghost old_mem_chunk = mem_chunk;
    let tracked mut psa_map = Map::<PageId, PageSharedAccess>::tracked_empty();
    let tracked mut pla_map = Map::<PageId, PageLocalAccess>::tracked_empty();
    while i <= SLICES_PER_SEGMENT as usize
        invariant mem_chunk.os == old_mem_chunk.os,
            mem_chunk.wf(),
            //mem_chunk.pointsto_has_range(segment_start(segment_id) + SIZEOF_SEGMENT_HEADER + i * SIZEOF_PAGE_HEADER,
            //  COMMIT_SIZE - (SIZEOF_SEGMENT_HEADER + i * SIZEOF_PAGE_HEADER)),
            set_int_range(
                    segment_start(segment_id) + SIZEOF_SEGMENT_HEADER,
                    segment_start(segment_id) + COMMIT_SIZE) <= old_mem_chunk.points_to.dom(),
            mem_chunk.points_to.dom() =~= old_mem_chunk.points_to.dom() - 
                set_int_range(
                    segment_start(segment_id),
                    segment_start(segment_id) + SIZEOF_SEGMENT_HEADER + i * SIZEOF_PAGE_HEADER
                ),

            cur_page_ptr as int == segment_start(segment_id) + SIZEOF_SEGMENT_HEADER + i * SIZEOF_PAGE_HEADER,
            segment_ptr.segment_ptr as int + SEGMENT_SIZE < usize::MAX,
            segment_ptr.wf(),
            segment_ptr.segment_id@ == segment_id,
            i <= SLICES_PER_SEGMENT + 1,
            forall |page_id: PageId|
                #[trigger] psa_map.dom().contains(page_id) ==>
                    page_id.segment_id == segment_id && 0 <= page_id.idx < i,
            forall |page_id: PageId|
                #[trigger] pla_map.dom().contains(page_id) ==>
                    page_id.segment_id == segment_id && 0 <= page_id.idx < i,
            forall |page_id: PageId|
                #![trigger psa_map.dom().contains(page_id)]
                #![trigger psa_map.index(page_id)]
                #![trigger pla_map.dom().contains(page_id)]
                #![trigger pla_map.index(page_id)]
            {
                page_id.segment_id == segment_id && 0 <= page_id.idx < i ==> {
                    &&& psa_map.dom().contains(page_id)
                    &&& pla_map.dom().contains(page_id)
                    &&& pla_map[page_id].inner@.value.is_some()
                    &&& pla_map[page_id].count@.value.is_some()
                    &&& pla_map[page_id].prev@.value.is_some()
                    &&& pla_map[page_id].next@.value.is_some()
                    &&& pla_map[page_id].inner@.value.unwrap().zeroed()
                    &&& pla_map[page_id].count@.value.unwrap() == 0
                    &&& pla_map[page_id].prev@.value.unwrap() as int == 0
                    &&& pla_map[page_id].next@.value.unwrap() as int == 0

                    &&& is_page_ptr(psa_map[page_id].points_to.ptr() as int, page_id)
                    &&& psa_map[page_id].points_to.is_init()
                    &&& psa_map[page_id].points_to.value().count.id() == pla_map[page_id].count@.pcell
                    &&& psa_map[page_id].points_to.value().inner.id() == pla_map[page_id].inner@.pcell
                    &&& psa_map[page_id].points_to.value().prev.id() == pla_map[page_id].prev@.pcell
                    &&& psa_map[page_id].points_to.value().next.id() == pla_map[page_id].next@.pcell
                    &&& psa_map[page_id].points_to.value().offset == 0
                    &&& psa_map[page_id].points_to.value().xthread_free.is_empty()
                    &&& psa_map[page_id].points_to.value().xthread_free.wf()
                    &&& psa_map[page_id].points_to.value().xthread_free.instance
                          == local.instance
                    &&& psa_map[page_id].points_to.value().xheap.is_empty()
                }
            }
    {
        let ghost page_id = PageId { segment_id, idx: i as nat };
        proof {
            const_facts();
            //assert(SIZEOF_PAGE_HEADER as int == vstd::layout::size_of::<Page>());
            segment_start_mult8(segment_id);
            //assert(cur_page_ptr.id() % vstd::layout::align_of::<Page>() as int == 0);
            assert(
                COMMIT_SIZE - (SIZEOF_SEGMENT_HEADER + SLICES_PER_SEGMENT * SIZEOF_PAGE_HEADER)
                <= COMMIT_SIZE - (SIZEOF_SEGMENT_HEADER + i * SIZEOF_PAGE_HEADER))
                by(nonlinear_arith) requires i <= SLICES_PER_SEGMENT;
            //assert(SIZEOF_PAGE_HEADER as int <=
            //    COMMIT_SIZE - (SIZEOF_SEGMENT_HEADER + i * SIZEOF_PAGE_HEADER));
            assert(i * SIZEOF_PAGE_HEADER + SIZEOF_PAGE_HEADER == (i + 1) * SIZEOF_PAGE_HEADER) by(nonlinear_arith);
            //assert(SIZEOF_SEGMENT_HEADER + i * SIZEOF_PAGE_HEADER < SEGMENT_SIZE);
            //assert(is_page_ptr(cur_page_ptr.id(), page_id));
        }

        let ghost phstart = segment_start(segment_id) + SIZEOF_SEGMENT_HEADER + i * SIZEOF_PAGE_HEADER;
        vstd::layout::layout_for_type_is_valid::<Page>(); // $line_count$Proof$
        let tracked page_header_points_to_raw = mem_chunk.take_points_to_range(
            phstart, SIZEOF_PAGE_HEADER as int);
        let tracked mut page_header_points_to = page_header_points_to_raw.into_typed::<Page>(phstart as usize);
        let (pcell_count, Tracked(pointsto_count)) = PCell::new(0);
        let (pcell_inner, Tracked(pointsto_inner)) = PCell::new(PageInner {
            flags0: 0,
            capacity: 0,
            reserved: 0,
            flags1: 0,
            flags2: 0,
            free: LL::empty(),
            used: 0,
            xblock_size: 0,
            local_free: LL::empty(),
        });
        let (pcell_prev, Tracked(pointsto_prev)) = PCell::new(core::ptr::null_mut());
        let (pcell_next, Tracked(pointsto_next)) = PCell::new(core::ptr::null_mut());
        let page = Page {
            count: pcell_count,
            offset: 0,
            inner: pcell_inner,
            xthread_free: ThreadLLWithDelayBits::empty(Tracked(local.instance.clone())),
            xheap: AtomicHeapPtr::empty(),
            prev: pcell_prev,
            next: pcell_next,
            padding: 0,
        };
        let tracked pla = PageLocalAccess {
            count: pointsto_count,
            inner: pointsto_inner,
            prev: pointsto_prev,
            next: pointsto_next,
        };
        ptr_mut_write(cur_page_ptr, Tracked(&mut page_header_points_to), page);
        let tracked psa = PageSharedAccess {
            points_to: page_header_points_to,
        };
        proof {
            psa_map.tracked_insert(page_id, psa);
            pla_map.tracked_insert(page_id, pla);
        }

        //assert(cur_page_ptr.id() + SIZEOF_PAGE_HEADER <= usize::MAX);

        i = i + 1;
        cur_page_ptr = cur_page_ptr.with_addr(cur_page_ptr.addr() + SIZEOF_PAGE_HEADER);

        /*assert(psa_map.dom().contains(page_id));
        assert( pla_map.dom().contains(page_id));
        assert( pla_map[page_id].inner@.value.is_some());
        assert( pla_map[page_id].count@.value.is_some());
        assert( pla_map[page_id].prev@.value.is_some());
        assert( pla_map[page_id].prev@.value.is_some());
        assert( pla_map[page_id].inner@.value.unwrap().zeroed());
        assert( pla_map[page_id].count@.value.unwrap() == 0);
        assert( pla_map[page_id].prev@.value.unwrap().id() == 0);
        assert( pla_map[page_id].next@.value.unwrap().id() == 0);

        assert( is_page_ptr(psa_map[page_id].points_to@.pptr, page_id));
        assert( psa_map[page_id].points_to.is_init());
        assert( psa_map[page_id].points_to.value().count.id() == pla_map[page_id].count@.pcell);
        assert( psa_map[page_id].points_to.value().inner.id() == pla_map[page_id].inner@.pcell);
        assert( psa_map[page_id].points_to.value().prev.id() == pla_map[page_id].prev@.pcell);
        assert( psa_map[page_id].points_to.value().next.id() == pla_map[page_id].next@.pcell);
        assert( psa_map[page_id].points_to.value().offset == 0);
        assert( psa_map[page_id].points_to.value().xthread_free.is_empty());
        assert( psa_map[page_id].points_to.value().xheap.is_empty());*/

    }

    proof {
        local.unused_pages.tracked_union_prefer_right(psa_map);
        local.pages.tracked_union_prefer_right(pla_map);
        local.psa = local.psa.union_prefer_right(psa_map);

        let tracked ssa = SegmentSharedAccess {
            points_to: seg_header_points_to,
        };
        let tracked sla = SegmentLocalAccess {
            mem: mem_chunk,
            main: pointsto_main,
            main2: pointsto_main2,
        };
        local.segments.tracked_insert(segment_id, sla);

        let tracked thread_state_tok = local.take_thread_token();
        let tracked thread_state_tok = local.instance.segment_enable(
                local.thread_id,
                segment_id,
                ssa,
                thread_state_tok,
                ssa);
        local.thread_token = thread_state_tok;

        ////////// Set up pages and stuff

        local.page_organization = PageOrg::take_step::create_segment(local.page_organization, segment_id);

        /*assert forall |page_id|
            #[trigger] local.pages.dom().contains(page_id) &&
              local.unused_pages.dom().contains(page_id) implies
                local.pages.index(page_id).wf_unused(page_id, local.unused_pages[page_id], local.page_organization.popped)
        by {
            if page_id.segment_id == segment_id {
                assert(psa_map[page_id].points_to.value().wf_unused());
                assert(psa_map[page_id].wf_unused(page_id));
                assert(pla_map.dom().contains(page_id));
                assert(local.pages.index(page_id).wf_unused(page_id, local.unused_pages[page_id], local.page_organization.popped));
            } else {
                assert(local.pages.index(page_id).wf_unused(page_id, local.unused_pages[page_id], local.page_organization.popped));
            }
        }*/
        //assert(i == SLICES_PER_SEGMENT + 1);
        //assert(local.segments[segment_id].points_to.value().thread_id.wf(
        //    local.instance, segment_id));
        /*assert(local.segments[segment_id].wf(segment_id,
                local.thread_token@.value.segments.index(segment_id),
                local.instance));*/
        assert(local.thread_token@.value.segments.dom() =~= local.segments.dom());

        /*let org_pages = local.page_organization.pages;
        let pages = local.pages;
        let psa = local.psa;
        assert forall |page_id| #[trigger] org_pages.dom().contains(page_id) implies
            page_organization_pages_match_data(org_pages[page_id], pages[page_id], local.psa[page_id], page_id, local.page_organization.popped)
        by {
            if page_id.segment_id == segment_id {
                assert(page_organization_pages_match_data(org_pages[page_id], pages[page_id], local.psa[page_id], page_id, local.page_organization.popped));
            } else {
                assert(page_organization_pages_match_data(org_pages[page_id], pages[page_id], local.psa[page_id], page_id, local.page_organization.popped));
            }
        }*/

        /*assert(page_organization_pages_match(local.page_organization.pages,
            local.pages, local.psa, local.page_organization.popped));
        assert(local.page_organization_valid());*/
        preserves_mem_chunk_good_except(local_snap1, *local, segment_id);
        assert(mem_chunk_good1(
            local.segments[segment_id].mem,
            segment_id,
            local.commit_mask(segment_id).bytes(segment_id),
            local.decommit_mask(segment_id).bytes(segment_id),
            local.segment_pages_range_total(segment_id),
            local.segment_pages_used_total(segment_id),
        )) by {
            reveal(CommitMask::bytes);
            empty_segment_pages_used_total(*local, segment_id);
        }
        //assert(local.mem_chunk_good(segment_id));
        //assert(local.wf_main());
    }

    let first_slice = PagePtr {
        page_ptr: segment_ptr.segment_ptr.with_addr(
            segment_ptr.segment_ptr.addr() + SIZEOF_SEGMENT_HEADER) as *mut Page,
        page_id: Ghost(PageId { segment_id, idx: 0 }),
    };
    //assert(first_slice.wf());
    let success = segment_span_allocate(segment_ptr, first_slice, 1, tld, Tracked(&mut *local));
    if !success {
        todo(); // TODO actually we don't need this check cause we can't fail
    }
    //assert(local.wf_main());

    /*let all_page_headers_points_to_raw = mem_chunk.take_points_to_range(
        segment_start(segment_id) + SIZEOF_SEGMENT_HEADER,
        (NUM_SLICES + 1) * SIZEOF_PAGE_HEADER,
    );*/

    let ghost local_snap = *local;
    let ghost next_state = PageOrg::take_step::forget_about_first_page2(local.page_organization);
    segment_get_mut_main2!(segment_ptr, local, main2 => {
        main2.used = main2.used - 1;
    });
    proof {
        local.page_organization = next_state;
        local.psa = local.psa.union_prefer_right(local.unused_pages);
        preserves_mem_chunk_good(local_snap, *local);
        //assert(local.wf_main());
    }

    if required == 0 {
        segment_span_free(segment_ptr, 1, SLICES_PER_SEGMENT as usize - 1, false, tld, Tracked(&mut *local));
    } else {
        todo();
    }

    return segment_ptr;
}

#[verifier::spinoff_prover]
fn segment_os_alloc(
    required: usize,
    page_alignment: usize,
    eager_delay: bool,
    req_arena_id: ArenaId,
    psegment_slices: usize,
    pre_size: usize,
    pinfo_slices: usize,
    pcommit_mask: &mut CommitMask,
    pdecommit_mask: &mut CommitMask,
    request_commit: bool,
    tld: TldPtr,
    Tracked(local): Tracked<&mut Local>,
// outparams
// segment_ptr: SegmentPtr,
// new_psegment_slices: usize
// new_ppre_size: usize
// new_pinfo_slices: usize,
// is_zero: bool,
// pcommit: bool,
// memid: MemId,
// mem_large: bool,
// is_pinned: bool,
// align_offset: usize,
) -> (res: (SegmentPtr, usize, usize, usize, bool, bool, MemId, bool, bool, usize, Tracked<MemChunk>))
    requires psegment_slices as int * SLICE_SIZE as int <= usize::MAX,
        pinfo_slices == 1,
        psegment_slices >= 1,
        old(local).wf(),
        tld.wf(),
        tld.is_in(*old(local)),
        psegment_slices == SLICES_PER_SEGMENT,
    ensures
        local.wf(),
        common_preserves(*old(local), *local),
        local.page_organization == old(local).page_organization,
        pdecommit_mask == old(pdecommit_mask), // this is only modified if segment cache is used
    ({
        let (segment_ptr, new_psegment_slices, new_ppre_size, new_pinfo_slices, is_zero, pcommit, mem_id, mem_large, is_pinned, align_offset, mem_chunk) = res; {
        &&& (segment_ptr.segment_ptr.addr() != 0 ==> {
            &&& segment_ptr.wf()
            &&& mem_chunk@.wf()
            &&& mem_chunk@.os_exact_range(segment_ptr.segment_ptr as int, SEGMENT_SIZE as int)
            &&& set_int_range(segment_start(segment_ptr.segment_id@),
                    segment_start(segment_ptr.segment_id@) + COMMIT_SIZE).subset_of( pcommit_mask.bytes(segment_ptr.segment_id@) )
            &&& pcommit_mask.bytes(segment_ptr.segment_id@).subset_of(mem_chunk@.os_rw_bytes())
            &&& mem_chunk@.os_rw_bytes().subset_of(mem_chunk@.points_to.dom())
        })
        }
    })
{
    proof { const_facts(); } 
    
    let mut mem_large = !eager_delay;
    let mut is_pinned = false;
    let mut mem_id: usize = 0;
    let mut align_offset: usize = 0;
    let mut alignment: usize = SEGMENT_ALIGN as usize;
    let mut is_zero = false;
    let mut pcommit = request_commit;
    let mut psegment_slices = psegment_slices;
    let mut pinfo_slices = pinfo_slices;
    let mut pre_size = pre_size;
    let tracked mut mem = MemChunk::empty();

    if page_alignment > 0 {
        /*
        assert(page_alignment >= SEGMENT_ALIGN);
        alignment = page_alignment;
        let info_size = pinfo_sizes * SLICE_SIZE;
        align_offset = align_up(info_size, SEGMENT_ALIGN);
        */
        todo(); 
    }

    let segment_size = psegment_slices * SLICE_SIZE as usize;

    let mut segment = SegmentPtr::null();

    if page_alignment == 0 {
        // TODO get from cache if possible
    }

    if segment.is_null() {
        let (_segment, Tracked(_mem), commit, _large, _is_pinned, _is_zero, _mem_id) = 
          arena_alloc_aligned(
            segment_size, alignment, align_offset, request_commit, mem_large, req_arena_id);
        segment = SegmentPtr {
            segment_ptr: _segment as *mut SegmentHeader,
            segment_id: Ghost(mk_segment_id(_segment as int)),
        };
        mem_id = _mem_id;
        mem_large = _large;
        is_zero = _is_zero;
        is_pinned = _is_pinned;
        pcommit = commit;
        proof {
            mem = _mem;
            //assert(segment.wf());
        }

        if segment.is_null() {
            return (segment,
                psegment_slices, pre_size, pinfo_slices, is_zero, pcommit, mem_id, mem_large, is_pinned, align_offset, Tracked(MemChunk::empty()))
        }
        if pcommit {
            pcommit_mask.create_full();
        } else {
            pcommit_mask.create_empty();
        }
    }

    let commit_needed = pinfo_slices;
    let mut commit_needed_mask = CommitMask::empty();
    commit_needed_mask.create(0, commit_needed);
    if !pcommit_mask.all_set(&commit_needed_mask) {
        //assert(commit_needed as int * COMMIT_SIZE as int <= segment_size);

        let (success, is_zero) = crate::os_commit::os_commit(
            segment.segment_ptr as *mut u8,
            commit_needed * COMMIT_SIZE as usize,
            Tracked(&mut mem));
        if !success {
            return (SegmentPtr::null(), 0, 0, 0, false, false, 0, false, false, 0, Tracked(MemChunk::empty()));
        }
        pcommit_mask.set(&commit_needed_mask);
    }

    // note: segment metadata is set by the caller

    // TODO what does _mi_segment_map_allocated_at do?

    proof {
        /*assert(segment.wf());
        assert(mem.wf());
        assert(mem.os_exact_range(segment.segment_ptr.id(), SEGMENT_SIZE as int));*/
        assert(set_int_range(
            segment_start(segment.segment_id@),
            segment_start(segment.segment_id@) + COMMIT_SIZE
          ).subset_of( pcommit_mask.bytes(segment.segment_id@) ))
        by {
            reveal(CommitMask::bytes);
        }
        assert(pcommit_mask.bytes(segment.segment_id@).subset_of(mem.os_rw_bytes()))
        by {
            reveal(CommitMask::bytes);
        }
        assert(mem.os_rw_bytes().subset_of(mem.points_to.dom()));
    }

    return (segment, psegment_slices, pre_size, pinfo_slices, is_zero, pcommit, mem_id, mem_large, is_pinned, align_offset, Tracked(mem));
}

fn segment_free(segment: SegmentPtr, force: bool, tld: TldPtr, Tracked(local): Tracked<&mut Local>)
    requires
        old(local).wf(),
        tld.wf(),
        tld.is_in(*old(local)),
        segment.wf(),
        segment.is_in(*old(local)),
    ensures
        local.wf(),
        common_preserves(*old(local), *local),
{
    todo();
    /*
    proof {
        let next_state = PageOrg::take_step::segment_freeing_start(local.page_organization, segment.segment_id@);
        local.page_organization = next_state;
        preserves_mem_chunk_good(*old(local), *local);
        assert(local.wf_main());
    }

    let mut slice = segment.get_page_header_ptr(0);
    let end = segment.get_page_after_end();
    let page_count = 0;
    while slice.page_ptr.to_usize() < end.to_usize()
        invariant local.wf_main(),
            segment.wf(),
            segment.is_in(*local),
            tld.is_in(*local),
            tld.wf(),
            slice.page_ptr.id() < end.id() ==> slice.wf(),
            slice.page_ptr.id() >= end.id() ==> slice.page_id@.idx == SLICES_PER_SEGMENT,
            slice.page_id@.segment_id == segment.segment_id@,
            local.page_organization.popped == Popped::SegmentFreeing(slice.page_id@.segment_id, slice.page_id@.idx as int),
            end.id() == page_header_start(
                PageId { segment_id: segment.segment_id@, idx: SLICES_PER_SEGMENT as nat }),
    {
        let ghost list_idx = local.page_organization.segment_freeing_is_in();

        if slice.get_inner_ref(Tracked(&*local)).xblock_size == 0 && !segment.is_kind_huge(Tracked(&*local)) {
            let count = slice.get_count(Tracked(&*local));
            let sbin_idx = slice_bin(count as usize);
            span_queue_delete(tld, sbin_idx, slice, Tracked(&mut *local), Ghost(list_idx), Ghost(count as int));
        } else {
            todo();
        }

        let count = slice.get_count(Tracked(&*local));
        proof { local.page_organization.get_count_bound(slice.page_id@); }
        slice = slice.add_offset(count as usize);
    }

    todo();

    // mi_segment_os_free(segment, tld);
    */
}

fn segment_os_free(segment: SegmentPtr, tld: TldPtr, Tracked(local): Tracked<&mut Local>)
    requires 
        old(local).wf_main(),
        segment.wf(), segment.is_in(*old(local)),
        tld.wf(), tld.is_in(*old(local)),
{
    // TODO segment_map_freed_at(segment);

    //let size = segment_size(segment, Tracked(&*local)) as isize;
    //segments_track_size(-size, tld, Tracked(&mut *local));
    todo();

    /*
    let skip_cache_push = size != SEGMENT_SIZE
        || segment.get_mem_align_offset(Tracked(&*local)) != 0
        || segment.is_kind_huge(Tracked(&*local));

    let mut try_arena_free = skip_cache_push;
    if !skip_cache_push {
        // TODO implement segment cache
        // !_mi_segment_cache_push(segment, size, segment->memid, &segment->commit_mask, &segment->decommit_mask, segment->mem_is_large, segment->mem_is_pinned, tld->os)) 
    }
    */

    
}

// segment_slices = # of slices in the segment
// pre_size = size of the pages that contain the segment metadata
// info_slices = # of slices needed to contain the pages of the segment metadata
fn segment_calculate_slices(required: usize)
  -> (res: (usize, usize, usize))
  requires required == 0,
  ensures ({ let (num_slices, pre_size, info_slices) = res;
      required == 0 ==> num_slices == SLICES_PER_SEGMENT
          && pre_size == crate::os_mem::page_size()
          && info_slices == 1
  })
{
    proof { const_facts(); }

    let page_size = crate::os_mem::get_page_size();
    let i_size = align_up(SIZEOF_SEGMENT_HEADER, page_size);
    let guardsize = 0;

    let pre_size = i_size;
    let j_size = align_up(i_size + guardsize, SLICE_SIZE as usize);
    let info_slices = j_size / SLICE_SIZE as usize;
    let segment_size = if required == 0 {
        SEGMENT_SIZE as usize
    } else {
        align_up(required + j_size + guardsize, SLICE_SIZE as usize)
    };
    let num_slices = segment_size / SLICE_SIZE as usize;

    (num_slices, pre_size, info_slices)
}

#[verifier::spinoff_prover]
fn segment_span_free(
    segment_ptr: SegmentPtr,
    slice_index: usize,
    slice_count: usize,
    allow_decommit: bool,
    tld_ptr: TldPtr,
    Tracked(local): Tracked<&mut Local>,
)
    requires
        old(local).wf_main(),
        tld_ptr.wf(),
        tld_ptr.is_in(*old(local)),
        segment_ptr.wf(),
        segment_ptr.is_in(*old(local)),
        0 <= slice_index,
        slice_index + slice_count <= SLICES_PER_SEGMENT,

        old(local).page_organization.popped == Popped::VeryUnready(segment_ptr.segment_id@, slice_index as int, slice_count as int, old(local).page_organization.popped.get_VeryUnready_3()),
    ensures
        local.wf_main(),
        common_preserves(*old(local), *local),
        segment_ptr.is_in(*local),
        local.page_organization.popped == if old(local).page_organization.popped.get_VeryUnready_3() {
            Popped::ExtraCount(segment_ptr.segment_id@)
        } else {
            Popped::No
        },
        local.pages.dom() =~= old(local).pages.dom(),
{
    let bin_idx = slice_bin(slice_count);

    proof { const_facts(); }
    let ghost mut next_state;
    proof {
        //assert(valid_sbin_idx(bin_idx as int));
        next_state = PageOrg::take_step::free_to_unused_queue(local.page_organization, bin_idx as int);
    }

    let slice = segment_ptr.get_page_header_ptr(slice_index);

    unused_page_get_mut_count!(slice, local, c => {
        c = slice_count as u32;
    });
    unused_page_get_mut!(slice, local, page => {
        page.offset = 0;
    });

    if slice_count > 1 {
        let last = segment_ptr.get_page_header_ptr(slice_index + slice_count - 1);

        unused_page_get_mut!(last, local, page => {
            //assert(SIZEOF_PAGE_HEADER as u32 == 80);
            //assert(slice_count as u32 == slice_count);
            page.offset = (slice_count as u32 - 1) * SIZEOF_PAGE_HEADER as u32;
        });
    }

    proof {
        //assert(SLICE_SIZE as usize == 65536);
        local.psa = local.psa.union_prefer_right(local.unused_pages);
        preserves_mem_chunk_good(*old(local), *local);
        //assert(local.page_organization_valid());
        //assert(local.wf_main());
        very_unready_range_okay_to_decommit(*local);
        //assert(slice_index * SLICE_SIZE + slice_count * SLICE_SIZE
        //    == (slice_index + slice_count) * SLICE_SIZE);
    }
    if allow_decommit {
        segment_perhaps_decommit(segment_ptr, 
            slice.slice_start(),
            slice_count * SLICE_SIZE as usize,
            Tracked(&mut *local));
    }
    //assert(local.wf_main());
    let ghost local_snap = *local;

    let first_in_queue;
    tld_get_mut!(tld_ptr, local, tld => {
        let mut cq = tld.segments.span_queue_headers[bin_idx];
        first_in_queue = cq.first;

        cq.first = slice.page_ptr;
        if first_in_queue.addr() == 0 {
            cq.last = slice.page_ptr;
        }

        tld.segments.span_queue_headers.set(bin_idx, cq);
    });
    if first_in_queue.addr() != 0 {
        let first_in_queue_ptr = PagePtr { page_ptr: first_in_queue,
            page_id: Ghost(local.page_organization.unused_dlist_headers[bin_idx as int].first.get_Some_0()) };
        unused_page_get_mut_prev!(first_in_queue_ptr, local, p => {
            p = slice.page_ptr;
        });
    }
    unused_page_get_mut_prev!(slice, local, p => {
        p = core::ptr::null_mut();
    });
    unused_page_get_mut_next!(slice, local, n => {
        n = first_in_queue;
    });
    unused_page_get_mut_inner!(slice, local, inner => {
        inner.xblock_size = 0;
    });

    proof {
        let old_state = local.page_organization;
        local.page_organization = next_state;
        local.psa = local.psa.union_prefer_right(local.unused_pages);

        assert_sets_equal!(local.page_organization.pages.dom(), local.pages.dom());
        preserves_mem_chunk_good(local_snap, *local);

        /*
        let org_pages = local.page_organization.pages;
        let pages = local.pages;
        let psa = local.psa;
        let isfq = local.page_organization.unused_dlist_headers[bin_idx as int].first.is_some();
        let fqid = local.page_organization.unused_dlist_headers[bin_idx as int].first.get_Some_0();
        let segment_id = slice.page_id@.segment_id;
        assert(slice_index + slice_count >= 1);
        let last_page = PageId { segment_id, idx: (slice_index + slice_count - 1) as nat };
        assert forall |pid| #[trigger] org_pages.dom().contains(pid) implies
            page_organization_pages_match_data(org_pages[pid], pages[pid], psa[pid])
        by {
            if pid == slice.page_id@ {
                assert(page_organization_pages_match_data(org_pages[pid], pages[pid], psa[pid]));
            } else if pid == last_page {
                assert(isfq ==> pid != fqid);
                if slice_count > 1 {
                    assert(org_pages[pid].offset.is_some());
                    assert(org_pages[pid].offset.unwrap() == (slice_count - 1));
                    assert(
                        psa[pid].points_to.value().offset ==
                        (slice_count as u32 - 1) * SIZEOF_PAGE_HEADER as u32);
                    assert(psa[pid].points_to.value().offset ==
                        (slice_count - 1) * SIZEOF_PAGE_HEADER);
                    assert(page_organization_pages_match_data(org_pages[pid], pages[pid], psa[pid]));
                } else {
                    assert(page_organization_pages_match_data(org_pages[pid], pages[pid], psa[pid]));
                }
            } else if first_in_queue.id() != 0 && pid == fqid {
                assert(page_organization_pages_match_data(org_pages[pid], pages[pid], psa[pid]));
            } else {
                assert(page_organization_pages_match_data(org_pages[pid], pages[pid], psa[pid]));
            }
        }
        */

        assert(local.wf_main());
    }
}

pub fn segment_page_free(page: PagePtr, force: bool, tld: TldPtr, Tracked(local): Tracked<&mut Local>)
    requires
        old(local).wf_main(),
        tld.wf(),
        tld.is_in(*old(local)),
        page.wf(),
        page.is_in(*old(local)),
        old(local).page_organization.popped == Popped::Used(page.page_id@, true),
        old(local).pages[page.page_id@].inner@.value.unwrap().used == 0,
    ensures
        local.wf(),
        common_preserves(*old(local), *local),
{
    let segment = SegmentPtr::ptr_segment(page);
    segment_page_clear(page, tld, Tracked(&mut *local));

    let used = segment.get_used(Tracked(&*local));
    if used == 0 {
        segment_free(segment, force, tld, Tracked(&mut *local));
    } else if used == segment.get_abandoned(Tracked(&*local)) {
        todo();
    }
}

#[verifier::spinoff_prover]
fn segment_page_clear(page: PagePtr, tld: TldPtr, Tracked(local): Tracked<&mut Local>)
    requires
        old(local).wf_main(),
        tld.wf(),
        tld.is_in(*old(local)),
        page.wf(),
        page.is_in(*old(local)),
        old(local).page_organization.popped == Popped::Used(page.page_id@, true),
        old(local).pages[page.page_id@].inner@.value.unwrap().used == 0,
    ensures
        local.wf(),
        page.is_in(*local),
        common_preserves(*old(local), *local),
{
    let ghost page_id = page.page_id@;
    let ghost next_state = PageOrg::take_step::set_range_to_not_used(local.page_organization);
    let ghost n_slices = local.page_organization.pages[page_id].count.unwrap();
    //assert(page.is_used_and_primary(*local));
    //assert(local.thread_token@.value.pages.dom().contains(page_id));
    let ghost page_state = local.thread_token@.value.pages[page_id];

    let segment = SegmentPtr::ptr_segment(page);

    let mem_is_pinned = segment.get_mem_is_pinned(Tracked(&*local));
    let is_reset = page.get_inner_ref(Tracked(&*local)).get_is_reset();
    let option_page_reset = option_page_reset();
    if !mem_is_pinned && !is_reset && option_page_reset {
        todo();
    }

    let tracked block_tokens;
    let tracked block_pt;
    page_get_mut_inner!(page, local, inner => {
        inner.set_is_zero_init(false);
        inner.capacity = 0;
        inner.reserved = 0;
        let (Tracked(ll_state1)) = inner.free.make_empty();
        inner.flags1 = 0;
        inner.flags2 = 0;
        inner.used = 0;
        inner.xblock_size = 0;
        let (Tracked(ll_state2)) = inner.local_free.make_empty();

        let tracked (_block_pt, _block_tokens) = LL::reconvene_state(
            local.instance.clone(), &local.thread_token, ll_state1, ll_state2,
            page_state.num_blocks as int);
        proof { block_tokens = _block_tokens; block_pt = _block_pt; }
    });

    let tracked psa_map;
    proof {
        let tracked thread_state_tok = local.take_thread_token();
        let block_state_map = Map::new(
            |block_id: BlockId| block_tokens.dom().contains(block_id),
            |block_id: BlockId| block_tokens[block_id]@.value,
        );
        assert(block_state_map.dom() =~= block_tokens.dom());
        let tracked thread_state_tok = local.instance.page_destroy_block_tokens(
            local.thread_id, page_id, block_state_map,
            thread_state_tok, block_tokens);
        assert forall |pid: PageId| page_id.range_from(0, n_slices as int).contains(pid)
            implies thread_state_tok@.value.pages.dom().contains(pid)
        by {
            assert(pid.segment_id == page_id.segment_id);
            assert(page_id.idx <= pid.idx < page_id.idx + n_slices);
            assert(local.page_organization.pages.dom().contains(pid));
            assert(local.page_organization.pages[pid].is_used);
        }
        local.thread_token = thread_state_tok;
    }
    let tracked checked_tok = local.take_checked_token();
    let tracked perm = &local.instance.thread_local_state_guards_page(
                local.thread_id, page.page_id@, &local.thread_token).points_to;
    let Tracked(checked_tok) = ptr_ref(page.page_ptr, Tracked(perm)).xthread_free.check_is_good(
        Tracked(&local.thread_token),
        Tracked(checked_tok));
    proof {
        let tracked thread_state_tok = local.take_thread_token();

        let tracked (Tracked(thread_state_tok), Tracked(_psa_map)) = local.instance.page_disable(
            local.thread_id, page_id, n_slices,
            thread_state_tok, &checked_tok);
        local.thread_token = thread_state_tok;
        local.checked_token = checked_tok;
        psa_map = _psa_map;

        local.unused_pages.tracked_union_prefer_right(psa_map);
    }

    let tracked delay_token;
    let tracked heap_of_page_token;
    unused_page_get_mut!(page, local, page => {
        let Tracked(_delay_token) = page.xthread_free.disable();
        let Tracked(_heap_of_page_token) = page.xheap.disable();

        proof { delay_token = _delay_token; heap_of_page_token = _heap_of_page_token; }
    });
    /*
    used_page_get_mut_prev!(page, local, p => {
        p = PPtr::from_usize(0);
    });
    used_page_get_mut_next!(page, local, n => {
        n = PPtr::from_usize(0);
    });
    */

    proof {
        /*assert forall |pid: PageId|
            page_id.range_from(0, n_slices as int).contains(pid) &&
              page_id != pid implies local.thread_token@.value.pages[pid].offset != 0
        by {
            //assert(local.page_organization.pages.dom().contains(pid));
            //assert(0 <= pid.idx < SLICES_PER_SEGMENT);
            //assert(local.page_organization.pages[pid].offset.is_some());
            //assert(local.page_organization.pages[pid].offset.unwrap() != 0);
        }*/

        local.psa = local.psa.union_prefer_right(local.unused_pages);

        let segment_id = page_id.segment_id;
        let tracked mut seg = local.segments.tracked_remove(segment_id);
        seg.mem.give_points_to_range(block_pt);
        local.segments.tracked_insert(segment_id, seg);
        local.page_organization = next_state;


        let tracked thread_state_tok = local.take_thread_token();
        //assert(delay_token@.key == page_id);
        //assert(heap_of_page_token@.key == page_id);
        let tracked thread_tok = local.instance.page_destroy_tokens(local.thread_id, page_id, n_slices, thread_state_tok, delay_token, heap_of_page_token);
        local.thread_token = thread_tok;

        preserves_mem_chunk_good_on_transfer_back(*old(local), *local, page_id);
        preserves_mem_chunk_good_except(*old(local), *local, segment_id);

        /*assert forall |pid|
            #[trigger] local.pages.dom().contains(pid) implies
              ((local.unused_pages.dom().contains(pid) <==>
                !local.thread_token@.value.pages.dom().contains(pid)))
        by {
            let s = page_id.range_from(0, n_slices as int);
            if local.unused_pages.dom().contains(pid) {
                if s.contains(pid) {
                    assert(!local.thread_token@.value.pages.dom().contains(pid));
                } else {
                    assert(!psa_map.dom().contains(pid));
                    assert(old(local).unused_pages.dom().contains(pid));
                    assert(!old(local).thread_token@.value.pages.dom().contains(pid));
                    assert(!local.thread_token@.value.pages.dom().contains(pid));
                }
            }
            if !local.unused_pages.dom().contains(pid) {
                assert(local.thread_token@.value.pages.dom().contains(pid));
            }
        }*/

        /*let org_pages = local.page_organization.pages;
        let pages = local.pages;
        let psa = local.psa;

        let old_psa = old(local).psa;
        assert forall |pid| #[trigger] org_pages.dom().contains(pid) implies
            page_organization_pages_match_data(org_pages[pid], pages[pid], psa[pid])
        by {
            let s = page_id.range_from(0, n_slices as int);
            if s.contains(pid) {
                if pid == page_id {
                    assert(org_pages[pid].offset.is_some());
                    let o = org_pages[pid].offset.unwrap();

                    assert(old_psa[pid].points_to@.value.get_Some_0().offset as int == o * SIZEOF_PAGE_HEADER);


                    assert(old(local).thread_token@.value.pages[pid].shared_access
                        .points_to@.value.get_Some_0().offset as int == o * SIZEOF_PAGE_HEADER);

                    assert(psa_map[pid].points_to@.value.get_Some_0().offset as int == o * SIZEOF_PAGE_HEADER);
                    assert(local.unused_pages[pid].points_to@.value.get_Some_0().offset as int == o * SIZEOF_PAGE_HEADER);

                    assert(psa[pid].points_to@.value.get_Some_0().offset as int == o * SIZEOF_PAGE_HEADER);

                    assert(page_organization_pages_match_data(org_pages[pid], pages[pid], psa[pid]));
                } else if pid.idx == page_id.idx + n_slices - 1 {
                    assert(page_organization_pages_match_data(org_pages[pid], pages[pid], psa[pid]));
                } else {
                    assert(page_organization_pages_match_data(org_pages[pid], pages[pid], psa[pid]));
                }
            } else {
                assert(page_organization_pages_match_data(org_pages[pid], pages[pid], psa[pid]));
            }
        }

        assert(page_organization_pages_match(local.page_organization.pages, local.pages, local.psa));
        assert(local.page_organization_valid());*/
        assert(local.wf_main());
    }

    segment_span_free_coalesce(page, tld, Tracked(&mut *local));

    let ghost local_snap = *local;

    let ghost next_state = PageOrg::take_step::clear_ec(local.page_organization);
    segment_get_mut_main2!(segment, local, main2 => {
        main2.used = main2.used - 1;
    });
    proof {
        local.page_organization = next_state;
        local.psa = local.psa.union_prefer_right(local.unused_pages);
        preserves_mem_chunk_good(local_snap, *local);
        //assert(local.wf_main());
    }

    proof {
        preserves_mem_chunk_good(local_snap, *local);
        //assert(local.wf());
    }
}

fn segment_span_free_coalesce(slice: PagePtr, tld: TldPtr, Tracked(local): Tracked<&mut Local>)
    requires
        old(local).wf_main(),
        tld.wf(),
        tld.is_in(*old(local)),
        slice.wf(),
        slice.is_in(*old(local)),
        match old(local).page_organization.popped {
            Popped::VeryUnready(sid, idx, c, _) => slice.page_id@.segment_id == sid
                && slice.page_id@.idx == idx
                && c == old(local).pages[slice.page_id@].count@.value.unwrap(),
            _ => false,
        },
    ensures
        local.wf_main(),
        slice.is_in(*local),
        common_preserves(*old(local), *local),
        local.page_organization.popped == (match old(local).page_organization.popped {
            Popped::VeryUnready(_, _, _, b) => {
                if b {
                    Popped::ExtraCount(slice.page_id@.segment_id)
                } else {
                    Popped::No
                }
            }
            _ => arbitrary(),
        }),
{
    let segment = SegmentPtr::ptr_segment(slice);
    let is_abandoned = segment.is_abandoned(Tracked(&*local));
    if is_abandoned { todo(); }

    let kind = segment.get_segment_kind(Tracked(&*local));
    if matches!(kind, SegmentKind::Huge) {
        todo();
    }

    let mut slice_count = slice.get_count(Tracked(&*local));

    proof {
        local.page_organization.get_count_bound_very_unready();
        //assert(slice_count == local.page_organization.pages[slice.page_id@].count.unwrap());
        const_facts();
    }

    //// Merge with the 'after' page

    let (page, less_than_end) = slice.add_offset_and_check(slice_count as usize, segment);
    proof {
        if less_than_end {
            local.page_organization.valid_page_after(); //slice.page_id@, page.page_id@);
        }
    }
    if less_than_end && page.get_inner_ref(Tracked(&*local)).xblock_size == 0 {
        let ghost page_id = page.page_id@;
        let ghost local_snap = *local;
        let ghost next_state = PageOrg::take_step::merge_with_after(local.page_organization);

        let prev_ptr = page.get_prev(Tracked(&*local));
        let next_ptr = page.get_next(Tracked(&*local));

        let ghost prev_page_id = local.page_organization.pages[page_id].dlist_entry.unwrap().prev.unwrap();
        let prev = PagePtr {
            page_ptr: prev_ptr, page_id: Ghost(prev_page_id),
        };
        let ghost next_page_id = local.page_organization.pages[page_id].dlist_entry.unwrap().next.unwrap();
        let next = PagePtr {
            page_ptr: next_ptr, page_id: Ghost(next_page_id),
        };

        let n_count = page.get_count(Tracked(&*local));
        let sbin_idx = slice_bin(n_count as usize);

        if prev_ptr.addr() != 0 {
            unused_page_get_mut_next!(prev, local, n => {
                n = next_ptr;
            });
        }
        if next_ptr.addr() != 0 {
            unused_page_get_mut_prev!(next, local, p => {
                p = prev_ptr;
            });
        }

        tld_get_mut!(tld, local, tld => {
            let mut cq = tld.segments.span_queue_headers[sbin_idx];

            if prev_ptr.addr() == 0 {
                cq.first = next_ptr;
            }
            if next_ptr.addr() == 0 {
                cq.last = prev_ptr;
            }

            tld.segments.span_queue_headers.set(sbin_idx, cq);
        });

        slice_count += n_count;

        proof {
            //assert(!local.page_organization.pages[page_id].is_used);
            local.page_organization = next_state;

            /*let local1 = local_snap;
            let local2 = *local;
            assert forall |page_id| local1.is_used_primary(page_id) implies
              local2.is_used_primary(page_id)
              && local1.page_capacity(page_id) <= local2.page_capacity(page_id)
              && local1.page_reserved(page_id) <= local2.page_reserved(page_id)
              && local1.block_size(page_id) == local2.block_size(page_id)
            by {
              assert(local2.is_used_primary(page_id));
              assert(local1.page_capacity(page_id) <= local2.page_capacity(page_id));
              assert(local1.page_reserved(page_id) <= local2.page_reserved(page_id));
              assert(local1.block_size(page_id) == local2.block_size(page_id));
            }*/


            preserves_mem_chunk_good(local_snap, *local);
            //assert(page_organization_queues_match(local.page_organization.unused_dlist_headers,
            //      local.tld@.value.get_Some_0().segments.span_queue_headers@));
            //assert(local.page_organization_valid());
            //assert(local.wf_main());
        }
    }

    assert(local.wf_main());

    //// Merge with the 'before' page
    
    // Had to factor this out for timeout-related reasons :\
    let (slice, slice_count) = segment_span_free_coalesce_before(segment, slice, tld, Tracked(&mut *local), slice_count);

    segment_span_free(segment, slice.get_index(), slice_count as usize, true, tld,
        Tracked(&mut *local));
}

#[inline(always)]
#[verifier::spinoff_prover]
fn segment_span_free_coalesce_before(segment: SegmentPtr, slice: PagePtr, tld: TldPtr, Tracked(local): Tracked<&mut Local>, slice_count: u32)
    -> (res: (PagePtr, u32))
    requires
        old(local).wf_main(),
        tld.wf(),
        tld.is_in(*old(local)),
        segment.wf(),
        segment.segment_id@ == slice.page_id@.segment_id,
        slice.wf(),
        slice.is_in(*old(local)),
        old(local).page_organization.popped == Popped::VeryUnready(slice.page_id@.segment_id, slice.page_id@.idx as int, slice_count as int, old(local).page_organization.popped.get_VeryUnready_3())
    ensures
        local.wf_main(),
        common_preserves(*old(local), *local),
        slice.is_in(*local),
        slice.page_id@.segment_id == res.0.page_id@.segment_id,
        ({ let (slice, slice_count) = res;
          slice.wf()
          && local.page_organization.popped == Popped::VeryUnready(slice.page_id@.segment_id, slice.page_id@.idx as int, slice_count as int, old(local).page_organization.popped.get_VeryUnready_3())
          && slice.page_id@.idx + slice_count <= SLICES_PER_SEGMENT
        })
{
    proof { const_facts(); }

    let ghost orig_id = slice.page_id@;

    let mut slice = slice;
    let mut slice_count = slice_count;

    if slice.is_gt_0th_slice(segment) {
        proof {
            /*assert(local.page_organization.popped == Popped::VeryUnready(
                slice.page_id@.segment_id,
                slice.page_id@.idx as int,
                slice_count as int,
                local.page_organization.popped.get_VeryUnready_3()));*/
            local.page_organization.valid_page_before();
        }
        let last = slice.sub_offset(1);
        //assert(local.page_organization.pages.dom().contains(last.page_id@));
        let offset = last.get_ref(Tracked(&*local)).offset; // multiplied by SIZEOF_PAGE_HEADER
        //assert(local.page_organization.pages[last.page_id@].offset.is_some());
        let ghost o = local.page_organization.pages[last.page_id@].offset.unwrap();
        //assert(last.page_id@.idx - o >= 0);
        let ghost page_id = PageId { segment_id: last.page_id@.segment_id,
                idx: (last.page_id@.idx - o) as nat };
        let page_ptr = calculate_page_ptr_subtract_offset(last.page_ptr, offset,
            Ghost(last.page_id@),
            Ghost(page_id));
        let page = PagePtr { page_ptr, page_id: Ghost(page_id) };
        proof { 
            is_page_ptr_nonzero(page_ptr as int, page_id);
            //assert(page.wf());
        }
        if page.get_inner_ref(Tracked(&*local)).xblock_size == 0 {
            let ghost local_snap = *local;
            let ghost next_state = PageOrg::take_step::merge_with_before(local.page_organization);

            let prev_ptr = page.get_prev(Tracked(&*local));
            let next_ptr = page.get_next(Tracked(&*local));

            let ghost prev_page_id = local.page_organization.pages[page_id].dlist_entry.unwrap().prev.unwrap();
            let prev = PagePtr {
                page_ptr: prev_ptr, page_id: Ghost(prev_page_id),
            };
            let ghost next_page_id = local.page_organization.pages[page_id].dlist_entry.unwrap().next.unwrap();
            let next = PagePtr {
                page_ptr: next_ptr, page_id: Ghost(next_page_id),
            };

            let n_count = page.get_count(Tracked(&*local));
            let sbin_idx = slice_bin(n_count as usize);

            if prev_ptr.addr() != 0 {
                unused_page_get_mut_next!(prev, local, n => {
                    n = next_ptr;
                });
            }
            if next_ptr.addr() != 0 {
                unused_page_get_mut_prev!(next, local, p => {
                    p = prev_ptr;
                });
            }

            tld_get_mut!(tld, local, tld => {
                let mut cq = tld.segments.span_queue_headers[sbin_idx];

                if prev_ptr.addr() == 0 {
                    cq.first = next_ptr;
                }
                if next_ptr.addr() == 0 {
                    cq.last = prev_ptr;
                }

                tld.segments.span_queue_headers.set(sbin_idx, cq);
            });

            slice_count += n_count;
            slice = page;

            proof {
                //assert(n_count == local.page_organization.pages[page_id].count.unwrap());
                //assert(!local.page_organization.pages[page_id].is_used);
                local.page_organization = next_state;
                preserves_mem_chunk_good(local_snap, *local);
                //assert(page_organization_queues_match(local.page_organization.unused_dlist_headers,
                //      local.tld@.value.get_Some_0().segments.span_queue_headers));
                //assert(local.page_organization_valid());
                //let slice_page_id = slice.page_id@;
                //assert(
                //  local.pages.index(slice_page_id).wf_unused(slice_page_id, local.unused_pages[slice_page_id], local.page_organization.popped, local.instance)
                //);

                //assert(
                //  old(local).pages.index(orig_id).wf_unused(orig_id, old(local).unused_pages[orig_id], old(local).page_organization.popped, local.instance)
                //);
                //assert(local.pages.index(orig_id).inner@.value.unwrap().zeroed_except_block_size());
                //assert(
                //  local.pages.index(orig_id).wf_unused(orig_id, local.unused_pages[orig_id], local.page_organization.popped, local.instance)
                //);
                //assert(local.wf_main());

                /*assert(slice.wf());
                assert(local.page_organization.popped.is_VeryUnready());
                assert(local.page_organization.popped.get_VeryUnready_1()
                    == slice.page_id@.idx as int);
                assert(local.page_organization.popped.get_VeryUnready_2()
                    == slice_count as int);
                assert(local.page_organization.popped == Popped::VeryUnready(slice.page_id@.segment_id, slice.page_id@.idx as int, slice_count as int));*/
            }
        }
    }

    proof {
        local.page_organization.get_count_bound_very_unready();
        //assert(slice.page_id@.idx + slice_count <= SLICES_PER_SEGMENT);
    }

    (slice, slice_count)
}

}
