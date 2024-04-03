#![allow(unused_imports)]

use core::intrinsics::{unlikely, likely};

use vstd::prelude::*;
use vstd::ptr::*;
use vstd::*;
use vstd::modes::*;
use vstd::set_lib::*;
use vstd::pervasive::*;

use crate::atomic_ghost_modified::*;

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

verus!{

   
#[verifier::spinoff_prover]
pub fn page_queue_remove(heap: HeapPtr, pq: usize, page: PagePtr, Tracked(local): Tracked<&mut Local>, Ghost(list_idx): Ghost<int>, Ghost(next_id): Ghost<PageId>)
    requires old(local).wf(), page.wf(), page.is_in(*old(local)),
        heap.wf(), heap.is_in(*old(local)),
        page.is_used_and_primary(*old(local)),
        //valid_bin_idx(pq as int) || pq == BIN_FULL,
        //old(local).page_organization.pages[page.page_id@].page_header_kind ==
        //    Some(PageHeaderKind::Normal(crate::bin_sizes::size_of_bin(pq as int) as int)),
        old(local).page_organization.valid_used_page(page.page_id@, pq as int, list_idx),
    ensures
        local.wf_main(),
        common_preserves(*old(local), *local),
        page.is_in(*local),
        local.page_organization.popped == Popped::Used(page.page_id@, true),
        local.page_organization.pages[page.page_id@].page_header_kind
            == old(local).page_organization.pages[page.page_id@].page_header_kind,
        local.tld_id == old(local).tld_id,
        old(local).page_organization.valid_used_page(next_id, pq as int, list_idx + 1) ==>
            local.page_organization.valid_used_page(next_id, pq as int, list_idx),
        old(local).pages[page.page_id@].inner@.value.unwrap().used
            == local.pages[page.page_id@].inner@.value.unwrap().used,
{
    let ghost mut next_state;
    let ghost page_id = page.page_id@;
    proof {
        next_state = PageOrg::take_step::out_of_used_list(local.page_organization,
            page_id, pq as int, list_idx);
        holds_on_present_value(*local, pq as int);
        if old(local).page_organization.valid_used_page(next_id, pq as int, list_idx + 1) {
            PageOrg::State::preserved_by_out_of_used_list(
                local.page_organization, next_state, page_id, pq as int, list_idx, next_id);
        }
    }

    let prev = page.get_prev(Tracked(&*local));
    let next = page.get_next(Tracked(&*local));
    let ghost prev_id = local.page_organization.pages[page_id].dlist_entry.unwrap().prev;
    let ghost next_id = local.page_organization.pages[page_id].dlist_entry.unwrap().next;

    if prev.to_usize() != 0 {
        let prev = PagePtr { page_ptr: prev, page_id: Ghost(prev_id.get_Some_0()) };
        //assert(prev.wf());
        //assert(prev.is_in(*local));
        used_page_get_mut_next!(prev, local, n => {
            n = next;
        });
    }

    if next.to_usize() != 0 {
        let next = PagePtr { page_ptr: next, page_id: Ghost(next_id.get_Some_0()) };
        //assert(next.wf());
        //assert(next.is_in(*local));
        used_page_get_mut_prev!(next, local, p => {
            p = prev;
        });
    }

    let ghost mut old_val;
    heap_get_pages!(heap, local, pages => {
        let mut cq = pages[pq];

        proof { old_val = cq.first.id(); }

        if next.to_usize() == 0 {
            cq.last = prev;
        }
        if prev.to_usize() == 0 {
            cq.first = next;
        }

        pages.set(pq, cq);
    });

    proof {
        local.page_organization = next_state;
        preserves_mem_chunk_good(*old(local), *local);
        //assert(local.wf_basic());
    }
    let ghost local_snap = *local;

    if prev.to_usize() == 0 {
        heap_queue_first_update(heap, pq, Tracked(&mut *local), Ghost(old_val));
    }

    let c = heap.get_page_count(Tracked(&*local));
    heap.set_page_count(Tracked(&mut *local), c.wrapping_sub(1));

    // These shouldn't be necessary:
    // page->next = NULL;
    // page->prev = NULL;
    // mi_page_set_in_full(page, false)

    proof {
        let pfd = local.heap.pages_free_direct@.value.unwrap()@;
        let emp = local.page_empty_global@.s.points_to@.pptr;
        let pages = local.heap.pages@.value.unwrap()@;
        if pq != BIN_FULL {
            let opfd = local_snap.heap.pages_free_direct@.value.unwrap()@;
            let pfd = local.heap.pages_free_direct@.value.unwrap()@;
            let pages = local.heap.pages@.value.unwrap()@;
            let emp = local.page_empty_global@.s.points_to@.pptr;
            let i = pfd_lower(pq as int) as int;
            let j = pfd_upper(pq as int) as int + 1;
            assert forall |wsize| 0 <= wsize < pfd.len() implies
                pages_free_direct_match(
                    (#[trigger] pfd[wsize]).id(),
                    pages[smallest_bin_fitting_size(wsize * INTPTR_SIZE)].first.id(),
                    emp)
            by {
                if i <= wsize < j {
                    idx_in_range_has_bin_size(pq as int, wsize);
                    //assert(smallest_bin_fitting_size(wsize * INTPTR_SIZE) == pq);
                    //assert(pages_free_direct_match((pfd[wsize]).id(),
                    //      pages[smallest_bin_fitting_size(wsize * INTPTR_SIZE)].first.id(),
                    //      emp));
                } else {
                    //assert(opfd[wsize] == pfd[wsize]);
                    let sbfs = smallest_bin_fitting_size(wsize * INTPTR_SIZE);
                    bounds_for_smallest_bin_fitting_size(wsize * INTPTR_SIZE);
                    //assert(0 <= sbfs < BIN_FULL);
                    idx_out_of_range_has_different_bin_size(pq as int, wsize);
                    //assert(sbfs != pq);
                    //assert(pages[sbfs].first == local_snap.heap.pages@.value.unwrap()@[sbfs].first);
                    //assert(pages[sbfs].first == old(local).heap.pages@.value.unwrap()@[sbfs].first);
                    /*assert(pages_free_direct_match((#[trigger] pfd[wsize]).id(),
                          pages[smallest_bin_fitting_size(wsize * INTPTR_SIZE)].first.id(),
                          emp));*/
                }
            }
            //assert(pages_free_direct_is_correct(pfd, pages, emp));
        } else {
            //let old_pfd = old(local).heap.pages_free_direct@.value.unwrap()@;
            //let old_pages = old(local).heap.pages@.value.unwrap()@;
            //let old_emp = old(local).page_empty_global@.s.points_to@.pptr;
            //assert(pages_free_direct_is_correct(old_pfd, old_pages, old_emp));

            let pfd = local.heap.pages_free_direct@.value.unwrap()@;
            let pages = local.heap.pages@.value.unwrap()@;
            let emp = local.page_empty_global@.s.points_to@.pptr;

            //assert(pfd == old_pfd);
            //assert(pages == old_pages);
            //assert(emp == old_emp);

            assert forall |wsize| 0 <= wsize < pfd.len() implies
                pages_free_direct_match(
                    (#[trigger] pfd[wsize]).id(),
                    pages[smallest_bin_fitting_size(wsize * INTPTR_SIZE)].first.id(),
                    emp)
            by {
                //let snap_pages = local_snap.heap.pages@.value.unwrap()@;
                //let snap_pages1 = local_snap1.heap.pages@.value.unwrap()@;
                //let snap_pages2 = local_snap2.heap.pages@.value.unwrap()@;
                //let t = smallest_bin_fitting_size(wsize * INTPTR_SIZE);

                bounds_for_smallest_bin_fitting_size(wsize * INTPTR_SIZE);
                //assert(0 <= t < pages.len());
                //assert(t != BIN_FULL);
                //assert(t != pq);

                //assert(old_pages[t] == snap_pages[t]);
                //assert(snap_pages[t] == pages[t]);
                //assert(pages_free_direct_match(
                //    (#[trigger] old_pfd[wsize]).id(),
                //    old_pages[smallest_bin_fitting_size(wsize * INTPTR_SIZE)].first.id(),
                //    old_emp));
            }

            //assert(pages_free_direct_is_correct(pfd, pages, emp));
        }
        preserves_mem_chunk_good(local_snap, *local);

        /*let org_pages = local.page_organization.pages;
        assert forall |pid| #[trigger] org_pages.dom().contains(pid) implies
            page_organization_pages_match_data(org_pages[pid], local.pages[pid], local.psa[pid])
        by {
            if pid == page_id {
                assert(page_organization_pages_match_data(org_pages[pid], local.pages[pid], local.psa[pid]));
            } else if Some(pid) == prev_id {
                assert(page_organization_pages_match_data(org_pages[pid], local.pages[pid], local.psa[pid]));
            } else if Some(pid) == next_id {
                assert(page_organization_pages_match_data(org_pages[pid], local.pages[pid], local.psa[pid]));
            } else {
                assert(page_organization_pages_match_data(org_pages[pid], local.pages[pid], local.psa[pid]));
            }
        }
        assert(page_organization_pages_match(local.page_organization.pages, local.pages, local.psa));*/

        //assert(local.page_organization_valid());
        //assert(local.wf_main());
    }
}

#[verifier::spinoff_prover]
pub fn page_queue_push(heap: HeapPtr, pq: usize, page: PagePtr, Tracked(local): Tracked<&mut Local>)
    requires
        old(local).wf_main(),
        pq == BIN_FULL || valid_bin_idx(pq as int),
        old(local).page_organization.popped == Popped::Used(page.page_id@, true),
        (match old(local).page_organization.pages[page.page_id@].page_header_kind.unwrap() {
              PageHeaderKind::Normal(b, bsize) => {
                  (pq == BIN_FULL || pq as int == b)
                  && valid_bin_idx(b as int)
                  && bsize == crate::bin_sizes::size_of_bin(b)
                  && bsize <= MEDIUM_OBJ_SIZE_MAX
              }
          }),
        heap.wf(),
        heap.is_in(*old(local)),
        page.wf(),
    ensures
        local.wf(),
        common_preserves(*old(local), *local),
        page.wf(),
        page.is_in(*local),
        page.is_used_and_primary(*local),
        local.pages.index(page.page_id@).inner@.value.unwrap().xblock_size ==
            old(local).pages.index(page.page_id@).inner@.value.unwrap().xblock_size,
        local.tld_id == old(local).tld_id,
{
    let ghost mut next_state;
    proof {
        next_state = PageOrg::take_step::into_used_list(local.page_organization, pq as int);
        holds_on_present_value(*local, pq as int);
    }

    page_get_mut_inner!(page, local, inner => {
        inner.set_in_full(pq == BIN_FULL as usize);
    });

    let first_in_queue;

    heap_get_pages!(heap, local, pages => {
        let mut cq = pages[pq];
        first_in_queue = cq.first;

        cq.first = page.page_ptr;
        if first_in_queue.to_usize() == 0 {
            cq.last = page.page_ptr;
        }

        pages.set(pq, cq);
    });

    if first_in_queue.to_usize() != 0 {
        let first_in_queue_ptr = PagePtr { page_ptr: first_in_queue,
            page_id: Ghost(local.page_organization.used_dlist_headers[pq as int].first.get_Some_0()) };
        //assert(first_in_queue_ptr.wf());
        //assert(first_in_queue_ptr.is_in(*old(local)));
        used_page_get_mut_prev!(first_in_queue_ptr, local, p => {
            p = page.page_ptr;
        });
    }

    used_page_get_mut_prev!(page, local, p => {
        p = PPtr::from_usize(0);
    });
    used_page_get_mut_next!(page, local, n => {
        n = first_in_queue;
    });

    proof {
        local.page_organization = next_state;
        preserves_mem_chunk_good(*old(local), *local);
        //crate::os_mem_util::mem_chunk_good_preserved(old(local).page_organization, local.page_organization);
        /*
        let queues = local.heap.pages@.value.unwrap();
        let org_queues = local.page_organization.used_dlist_headers;
        assert forall |i: int| 0 <= i < org_queues.len() implies
            is_page_ptr_opt((#[trigger] queues@[i]).first, org_queues[i].first)
        by {
            if i == pq {
                assert(queues@[i].first == page_ptr.page_ptr);
                assert(org_queues[i].first == Some(page_ptr.page_id@));
                assert(is_page_ptr_opt(queues@[i].first, org_queues[i].first));
            } else {
                assert(is_page_ptr_opt(queues@[i].first, org_queues[i].first));
            }
        }
        */

        //assert(local.wf_basic());
        //assert(local.mem_chunk_good(page.page_id@.segment_id));
    }
    let ghost local_snap = *local;

    heap_queue_first_update(heap, pq, Tracked(&mut *local), Ghost(first_in_queue.id()));

    let c = heap.get_page_count(Tracked(&*local));
    heap.set_page_count(Tracked(&mut *local), c.wrapping_add(1));

    proof {
        if pq != BIN_FULL {
            let opfd = local_snap.heap.pages_free_direct@.value.unwrap()@;
            let pfd = local.heap.pages_free_direct@.value.unwrap()@;
            let pages = local.heap.pages@.value.unwrap()@;
            let emp = local.page_empty_global@.s.points_to@.pptr;
            let i = pfd_lower(pq as int) as int;
            let j = pfd_upper(pq as int) as int + 1;
            assert forall |wsize| 0 <= wsize < pfd.len() implies
                pages_free_direct_match(
                    (#[trigger] pfd[wsize]).id(),
                    pages[smallest_bin_fitting_size(wsize * INTPTR_SIZE)].first.id(),
                    emp)
            by {
                if i <= wsize < j {
                    //assert(pfd[wsize].id() != 0);
                    idx_in_range_has_bin_size(pq as int, wsize);
                    /*assert(smallest_bin_fitting_size(wsize * INTPTR_SIZE) == pq);
                    assert(pages_free_direct_match((#[trigger] pfd[wsize]).id(),
                          pages[smallest_bin_fitting_size(wsize * INTPTR_SIZE)].first.id(),
                          emp));*/
                } else {
                    //assert(opfd[wsize] == pfd[wsize]);
                    let sbfs = smallest_bin_fitting_size(wsize * INTPTR_SIZE);
                    bounds_for_smallest_bin_fitting_size(wsize * INTPTR_SIZE);
                    //assert(0 <= sbfs < BIN_FULL);
                    idx_out_of_range_has_different_bin_size(pq as int, wsize);
                    /*assert(sbfs != pq);
                    assert(pages[sbfs].first == local_snap.heap.pages@.value.unwrap()@[sbfs].first);
                    assert(pages[sbfs].first == old(local).heap.pages@.value.unwrap()@[sbfs].first);
                    assert(pages_free_direct_match((#[trigger] pfd[wsize]).id(),
                          pages[smallest_bin_fitting_size(wsize * INTPTR_SIZE)].first.id(),
                          emp));*/
                }
            }
            //assert(pages_free_direct_is_correct(pfd, pages, emp));
        } else {
            //let old_pfd = old(local).heap.pages_free_direct@.value.unwrap()@;
            //let old_pages = old(local).heap.pages@.value.unwrap()@;
            //let old_emp = old(local).page_empty_global@.s.points_to@.pptr;
            //assert(pages_free_direct_is_correct(old_pfd, old_pages, old_emp));

            let pfd = local.heap.pages_free_direct@.value.unwrap()@;
            let pages = local.heap.pages@.value.unwrap()@;
            let emp = local.page_empty_global@.s.points_to@.pptr;

            //assert(pfd == old_pfd);
            //assert(pages == old_pages);
            //assert(emp == old_emp);

            assert forall |wsize| 0 <= wsize < pfd.len() implies
                pages_free_direct_match(
                    (#[trigger] pfd[wsize]).id(),
                    pages[smallest_bin_fitting_size(wsize * INTPTR_SIZE)].first.id(),
                    emp)
            by {
                //let snap_pages = local_snap.heap.pages@.value.unwrap()@;
                //let snap_pages1 = local_snap1.heap.pages@.value.unwrap()@;
                //let snap_pages2 = local_snap2.heap.pages@.value.unwrap()@;
                //let t = smallest_bin_fitting_size(wsize * INTPTR_SIZE);

                bounds_for_smallest_bin_fitting_size(wsize * INTPTR_SIZE);
                //assert(0 <= t < pages.len());
                //assert(t != BIN_FULL);
                //assert(t != pq);

                //assert(old_pages[t] == snap_pages[t]);
                //assert(snap_pages[t] == pages[t]);
                //assert(pages_free_direct_match(
                //    (#[trigger] old_pfd[wsize]).id(),
                //    old_pages[smallest_bin_fitting_size(wsize * INTPTR_SIZE)].first.id(),
                //    old_emp));
            }

            //assert(pages_free_direct_is_correct(pfd, pages, emp));
        }
        preserves_mem_chunk_good(local_snap, *local);
        //assert(local.wf_main());
        //assert(local.wf());
    }
}

#[verifier::spinoff_prover]
pub fn page_queue_push_back(heap: HeapPtr, pq: usize, page: PagePtr, Tracked(local): Tracked<&mut Local>, Ghost(other_id): Ghost<PageId>, Ghost(other_pq): Ghost<int>, Ghost(other_list_idx): Ghost<int>)
    requires
        old(local).wf_main(),
        pq == BIN_FULL || valid_bin_idx(pq as int),
        old(local).page_organization.popped == Popped::Used(page.page_id@, true),
        (match old(local).page_organization.pages[page.page_id@].page_header_kind.unwrap() {
              PageHeaderKind::Normal(b, bsize) => {
                  (pq == BIN_FULL || b == pq as int)
                  && valid_bin_idx(b as int)
                  && bsize == crate::bin_sizes::size_of_bin(b)
                  && bsize <= MEDIUM_OBJ_SIZE_MAX
              }
          }),
        heap.wf(),
        heap.is_in(*old(local)),
        page.wf(),
    ensures
        local.wf(),
        common_preserves(*old(local), *local),
        page.wf(),
        page.is_in(*local),
        page.is_used_and_primary(*local),
        local.pages.index(page.page_id@).inner@.value.unwrap().xblock_size ==
            old(local).pages.index(page.page_id@).inner@.value.unwrap().xblock_size,
        local.tld_id == old(local).tld_id,

        old(local).page_organization.valid_used_page(other_id, other_pq, other_list_idx) ==>
            local.page_organization.valid_used_page(other_id, other_pq, other_list_idx),
{
    let ghost mut next_state;
    proof {
        next_state = PageOrg::take_step::into_used_list_back(local.page_organization, pq as int);
        holds_on_present_value(*local, pq as int);
        if local.page_organization.valid_used_page(other_id, other_pq, other_list_idx) {
            PageOrg::State::preserved_by_into_used_list_back(
                local.page_organization, next_state, pq as int, other_id, other_pq, other_list_idx);
        }
    }

    page_get_mut_inner!(page, local, inner => {
        inner.set_in_full(pq == BIN_FULL as usize);
    });

    let last_in_queue;

    heap_get_pages!(heap, local, pages => {
        let mut cq = pages[pq];
        last_in_queue = cq.last;

        cq.last = page.page_ptr;
        if last_in_queue.to_usize() == 0 {
            cq.first = page.page_ptr;
        }

        pages.set(pq, cq);
    });

    used_page_get_mut_next!(page, local, n => {
        n = PPtr::from_usize(0);
    });
    used_page_get_mut_prev!(page, local, p => {
        p = last_in_queue;
    });

    if last_in_queue.to_usize() != 0 {
        let last_in_queue_ptr = PagePtr { page_ptr: last_in_queue,
            page_id: Ghost(local.page_organization.used_dlist_headers[pq as int].last.get_Some_0()) };
        //assert(last_in_queue_ptr.wf());
        //assert(last_in_queue_ptr.is_in(*old(local)));
        used_page_get_mut_next!(last_in_queue_ptr, local, n => {
            n = page.page_ptr;
        });
    }

    proof {
        local.page_organization = next_state;
        preserves_mem_chunk_good(*old(local), *local);

        //assert(local.wf_basic());
        //assert(local.mem_chunk_good(page.page_id@.segment_id));
    }
    let ghost local_snap = *local;

    if last_in_queue.to_usize() == 0 {
        heap_queue_first_update(heap, pq, Tracked(&mut *local), Ghost(0));
    }

    let c = heap.get_page_count(Tracked(&*local));
    heap.set_page_count(Tracked(&mut *local), c.wrapping_add(1));

    proof {
        if last_in_queue.id() == 0 {
            if pq != BIN_FULL {
                let opfd = local_snap.heap.pages_free_direct@.value.unwrap()@;
                let pfd = local.heap.pages_free_direct@.value.unwrap()@;
                let pages = local.heap.pages@.value.unwrap()@;
                let emp = local.page_empty_global@.s.points_to@.pptr;
                let i = pfd_lower(pq as int) as int;
                let j = pfd_upper(pq as int) as int + 1;
                assert forall |wsize| 0 <= wsize < pfd.len() implies
                    pages_free_direct_match(
                        (#[trigger] pfd[wsize]).id(),
                        pages[smallest_bin_fitting_size(wsize * INTPTR_SIZE)].first.id(),
                        emp)
                by {
                    if i <= wsize < j {
                        //assert(pfd[wsize].id() != 0);
                        idx_in_range_has_bin_size(pq as int, wsize);
                        /*assert(smallest_bin_fitting_size(wsize * INTPTR_SIZE) == pq);
                        assert(pages_free_direct_match((#[trigger] pfd[wsize]).id(),
                              pages[smallest_bin_fitting_size(wsize * INTPTR_SIZE)].first.id(),
                              emp));*/
                    } else {
                        //assert(opfd[wsize] == pfd[wsize]);
                        let sbfs = smallest_bin_fitting_size(wsize * INTPTR_SIZE);
                        bounds_for_smallest_bin_fitting_size(wsize * INTPTR_SIZE);
                        //assert(0 <= sbfs < BIN_FULL);
                        idx_out_of_range_has_different_bin_size(pq as int, wsize);
                        /*assert(sbfs != pq);
                        assert(pages[sbfs].first == local_snap.heap.pages@.value.unwrap()@[sbfs].first);
                        assert(pages[sbfs].first == old(local).heap.pages@.value.unwrap()@[sbfs].first);
                        assert(pages_free_direct_match((#[trigger] pfd[wsize]).id(),
                              pages[smallest_bin_fitting_size(wsize * INTPTR_SIZE)].first.id(),
                              emp));*/
                    }
                }
                //assert(pages_free_direct_is_correct(pfd, pages, emp));
            } else {
                //let old_pfd = old(local).heap.pages_free_direct@.value.unwrap()@;
                //let old_pages = old(local).heap.pages@.value.unwrap()@;
                //let old_emp = old(local).page_empty_global@.s.points_to@.pptr;
                //assert(pages_free_direct_is_correct(old_pfd, old_pages, old_emp));

                let pfd = local.heap.pages_free_direct@.value.unwrap()@;
                let pages = local.heap.pages@.value.unwrap()@;
                let emp = local.page_empty_global@.s.points_to@.pptr;

                //assert(pfd == old_pfd);
                //assert(pages == old_pages);
                //assert(emp == old_emp);

                assert forall |wsize| 0 <= wsize < pfd.len() implies
                    pages_free_direct_match(
                        (#[trigger] pfd[wsize]).id(),
                        pages[smallest_bin_fitting_size(wsize * INTPTR_SIZE)].first.id(),
                        emp)
                by {
                    //let snap_pages = local_snap.heap.pages@.value.unwrap()@;
                    //let snap_pages1 = local_snap1.heap.pages@.value.unwrap()@;
                    //let snap_pages2 = local_snap2.heap.pages@.value.unwrap()@;
                    //let t = smallest_bin_fitting_size(wsize * INTPTR_SIZE);

                    bounds_for_smallest_bin_fitting_size(wsize * INTPTR_SIZE);
                    //assert(0 <= t < pages.len());
                    //assert(t != BIN_FULL);
                    //assert(t != pq);

                    //assert(old_pages[t] == snap_pages[t]);
                    //assert(snap_pages[t] == pages[t]);
                    //assert(pages_free_direct_match(
                    //    (#[trigger] old_pfd[wsize]).id(),
                    //    old_pages[smallest_bin_fitting_size(wsize * INTPTR_SIZE)].first.id(),
                    //    old_emp));
                }

                //assert(pages_free_direct_is_correct(pfd, pages, emp));
            }
        } else {
            let pfd = local.heap.pages_free_direct@.value.unwrap()@;
            let pages = local.heap.pages@.value.unwrap()@;
            let emp = local.page_empty_global@.s.points_to@.pptr;
            assert forall |wsize| 0 <= wsize < pfd.len() implies
                    pages_free_direct_match(
                        (#[trigger] pfd[wsize]).id(),
                        pages[smallest_bin_fitting_size(wsize * INTPTR_SIZE)].first.id(),
                        emp)
            by {
                bounds_for_smallest_bin_fitting_size(wsize * INTPTR_SIZE);
            }
            //assert(pages_free_direct_is_correct(pfd, pages, emp));
        }
        preserves_mem_chunk_good(local_snap, *local);
        //assert(local.wf_main());
        //assert(local.wf());
    }
}


//spec fn local_direct_no_change_needed(loc1: Local, loc2: Local, pq: int) -> bool {
//}

spec fn local_direct_update(loc1: Local, loc2: Local, i: int, j: int, pq: int) -> bool {
    &&& loc2 == Local { heap: loc2.heap, .. loc1 }
    &&& loc2.heap == HeapLocalAccess { pages_free_direct: loc2.heap.pages_free_direct, .. loc1.heap }
    &&& loc1.heap.pages_free_direct@.pcell == loc2.heap.pages_free_direct@.pcell
    &&& loc1.heap.pages_free_direct@.value.is_some()
    &&& loc2.heap.pages_free_direct@.value.is_some()
    &&& pfd_direct_update(
          loc1.heap.pages_free_direct@.value.unwrap()@,
          loc2.heap.pages_free_direct@.value.unwrap()@, i, j,
            loc1.page_empty_global@.s.points_to@.pptr,
            loc1.heap.pages@.value.unwrap()@[pq].first.id())
}

spec fn pfd_direct_update(pfd1: Seq<PPtr<Page>>, pfd2: Seq<PPtr<Page>>, i: int, j: int, emp: int, p: int) -> bool {
    &&& pfd1.len() == pfd2.len() == PAGES_DIRECT
    &&& (forall |k|
        #![trigger(pfd1.index(k))]
        #![trigger(pfd2.index(k))]
      0 <= k < pfd1.len() && !(i <= k < j) ==> pfd1[k] == pfd2[k])
    &&& (forall |k| #![trigger pfd2.index(k)]
        0 <= k < pfd2.len() && i <= k < j ==>
            pages_free_direct_match(pfd2[k].id(), p, emp))
}

proof fn holds_on_present_value(local: Local, pq: int)
    requires local.wf_main(),
        valid_bin_idx(pq as int) || pq == BIN_FULL,
    ensures
        pq != BIN_FULL ==> (forall |k: int| k < PAGES_DIRECT &&
            pfd_lower(pq as int) <= k <= pfd_upper(pq as int) ==>
                pages_free_direct_match(
                    #[trigger] local.heap.pages_free_direct@.value.unwrap()@[k].id(),
                    local.heap.pages@.value.unwrap()@[pq].first.id(),
                    local.page_empty_global@.s.points_to@.pptr)
        )
{
    if pq != BIN_FULL {
        assert forall |k: int| k < PAGES_DIRECT &&
            pfd_lower(pq as int) <= k <= pfd_upper(pq as int) implies
                pages_free_direct_match(
                    #[trigger] local.heap.pages_free_direct@.value.unwrap()@[k].id(),
                    local.heap.pages@.value.unwrap()@[pq].first.id(),
                    local.page_empty_global@.s.points_to@.pptr)
        by {
            //assert(0 <= k < local.heap.pages_free_direct@.value.unwrap()@.len());
            idx_in_range_has_bin_size(pq as int, k as int);
        }
    }
}

fn heap_queue_first_update(heap: HeapPtr, pq: usize, Tracked(local): Tracked<&mut Local>, Ghost(old_p): Ghost<int>)
    requires
        old(local).wf_basic(),
        heap.wf(),
        heap.is_in(*old(local)),
        valid_bin_idx(pq as int) || pq == BIN_FULL,
        pq != BIN_FULL ==> (forall |k: int| k < PAGES_DIRECT &&
            pfd_lower(pq as int) <= k <= pfd_upper(pq as int) ==>
                pages_free_direct_match(
                    #[trigger] old(local).heap.pages_free_direct@.value.unwrap()@[k].id(),
                    old_p, old(local).page_empty_global@.s.points_to@.pptr)
        ),
    ensures
        pq == BIN_FULL ==> *local == *old(local),
        pq != BIN_FULL ==> local_direct_update(*old(local), *local,
            pfd_lower(pq as int) as int,
            pfd_upper(pq as int) as int + 1,
            pq as int)
{
    proof { const_facts(); }

    let size = heap.get_pages(Tracked(&*local))[pq].block_size;
    if size > SMALL_SIZE_MAX {
        proof {
            if pq != BIN_FULL {
                out_of_small_range(pq as int);
                assert(pfd_lower(pq as int) >= PAGES_DIRECT);
            }
        }
        return;
    }
    assert(pq != BIN_FULL);

    let mut page_ptr = heap.get_pages(Tracked(&*local))[pq].first;
    if page_ptr.to_usize() == 0 {
        let (_page, Tracked(emp)) = heap.get_page_empty(Tracked(&*local));
        page_ptr = _page;
    }

    let idx = size / 8;

    if heap.get_pages_free_direct(Tracked(&*local))[idx].to_usize() == page_ptr.to_usize() {
        /*proof {
            let i = pfd_lower(pq as int) as int;
            let j = pfd_upper(pq as int) as int + 1;
            assert(idx == j - 1);

            let loc1 = *old(local);
            let loc2 = *local;
            let pq = pq as int;
            let pfd1 = loc1.heap.pages_free_direct@.value.unwrap()@;
            let pfd2 = loc2.heap.pages_free_direct@.value.unwrap()@;
            let emp = loc1.page_empty_global@.s.points_to@.pptr;
            let p = loc1.heap.pages@.value.unwrap()@[pq].first.id();
            assert forall |k| #![trigger pfd2.index(k)]
                0 <= k < pfd2.len() && i <= k < j implies
                    pages_free_direct_match(pfd2[k].id(), p, emp)
            by {
                let z = idx as int;
                assert(pages_free_direct_match(pfd2[z].id(), p, emp));
                if p == 0 {
                    assert(pfd2[k].id() == emp);
                } else {
                    assert(pfd2[k].id() == p);
                }
            }
            assert(local_direct_update(loc1, loc2, i, j, pq));
        }*/
        return;
    }

    let start = if idx <= 1 {
        0
    } else {
        let b = bin(size);
        let prev = pq - 1;

        /*
        // for large minimal alignment, need to do something here
        loop
            invariant
                old(local).wf_basic(),
                heap.wf(),
                heap.is_in(*old(local)),
                0 <= prev <= 
        {
            let prev_block_size = heap.get_pages(Tracked(&*local))[prev].block_size;
            if !(b == bin(prev_block_size) && prev > 0) {
                break;
            }
            prev = prev - 1;
        }*/

        let prev_block_size = heap.get_pages(Tracked(&*local))[prev].block_size;
        proof {
            const_facts();
            if prev != 0 {
                size_of_bin_bounds_not_huge(prev as int);
                assert(valid_bin_idx(prev as int));
                assert(prev_block_size == size_of_bin(prev as int));
            }
        }
        let s = 1 + prev_block_size / 8;
        s
        //let t = if s > idx { idx } else { s };
        //t
    };

    proof {
        if idx <= 1 {
            size_le_8_implies_idx_eq_1(pq as int);
            assert(pq == 1);
            assert(start == pfd_lower(pq as int));
        } else {
            size_gt_8_implies_idx_gt_1(pq as int);
            assert(pq > 1);
            assert(start == pfd_lower(pq as int));
        }
        assert(idx == pfd_upper(pq as int));
        pfd_lower_le_upper(pq as int);
        assert(start <= idx);
    }

    let mut sz = start;
    while sz <= idx
        invariant
            local.wf_basic(),
            heap.wf(),
            heap.is_in(*local),
            start <= sz <= idx + 1,
            idx < PAGES_DIRECT,
            local_direct_update(*old(local), *local, start as int, sz as int, pq as int),
            page_ptr.id() != 0,
            pages_free_direct_match(page_ptr.id(), 
                old(local).heap.pages@.value.unwrap()@[pq as int].first.id(),
                local.page_empty_global@.s.points_to@.pptr),
    {
        let ghost prev_local = *local;
        heap_get_pages_free_direct!(heap, local, pages_free_direct => {
            pages_free_direct.set(sz, page_ptr);
        });
        
        sz += 1;
    }
}

}
