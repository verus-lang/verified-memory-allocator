#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::*;
use vstd::modes::*;

use core::intrinsics::{likely, unlikely};

use crate::tokens::{Mim, BlockId, DelayState};
use crate::types::*;
use crate::layout::*;
use crate::linked_list::*;
use crate::dealloc_token::*;

verus!{

// The algorithm for `free` is this:
//
//  1. Given the ptr, compute the segment and page it is on.
//
//  2. Check the 'thread_id' on the page. If it matches the thread we're on, then
//      this is a 'local' transition (the common case).
//      Otherwise, it's a 'thread' transition.
//
// If it's a LOCAL transition:
//
//   Update the local_free list.
//
// If it's a THREAD transition:
//
//   Attempt to update the thread_free list by first reading the atomic, then performing
//   a CAS (repeating if necessary). The thread_free contains both the linked_list pointer
//   and a 'delay' state.
//
//   If the 'delay' state is NOT in 'UseDelayedFree' (the usual case):
//
//     Update the thread_free atomically by inserting the new block to the front of the list.
//
//   If the 'delay' state is in 'UseDelayedFree' (the unusual case):
//
//     Set 'delay' to Freeing
//     Follow the heap pointer to access the Heap
//     Atomically add to the delayed free list.
//     Set 'delay' to NoDelaying
//
//     (The purpose of setting the 'Freeing' state is to ensure that the Heap remains
//     valid while we perform this operation.)
//
//     (Also note that setting the 'Freeing' state does not prevent the next thread that
//     comes along from adding to the thread_free list.)

pub fn free(ptr: *mut u8, Tracked(user_perm): Tracked<PointsToRaw>, Tracked(user_dealloc): Tracked<Option<MimDealloc>>, Tracked(local): Tracked<&mut Local>)
    // According to the Linux man pages, `ptr` is allowed to be NULL,
    // in which case no operation is performed.
    requires
        old(local).wf(),
        ptr.addr() != 0 ==> user_dealloc.is_some(),
        ptr.addr() != 0 ==> user_perm.is_range(ptr as int, user_dealloc.unwrap().size()),
        ptr.addr() != 0 ==> user_perm.provenance() == ptr@.provenance,
        ptr.addr() != 0 ==> ptr == user_dealloc.unwrap().ptr(),
        ptr.addr() != 0 ==> old(local).inst() == user_dealloc.unwrap().inst()
    ensures
        local.wf(),
        local.inst() == old(local).inst(),
        forall |heap: HeapPtr| heap.is_in(*old(local)) ==> heap.is_in(*local),
{
    if ptr.addr() == 0 {
        return;
    }

    let tracked user_dealloc = user_dealloc.tracked_unwrap();

    let tracked dealloc;
    let tracked perm;
    proof {
        let tracked (x, y) = user_dealloc.into_internal(user_perm);
        dealloc = x;
        perm = y;
    }

    // Calculate the pointer to the segment this block is in.

    let segment_ptr = calculate_segment_ptr_from_block(ptr, Ghost(dealloc.block_id()));

    let tracked segment_shared_access: &SegmentSharedAccess =
        dealloc.mim_instance.alloc_guards_segment_shared_access(
            dealloc.block_id(),
            &dealloc.mim_block,
        );

    let segment: &SegmentHeader = ptr_ref(segment_ptr,
        Tracked(&segment_shared_access.points_to));

    // Determine if this operation is thread local or not

    let segment_thread_id_u64 = atomic_with_ghost!(
        &segment.thread_id => load();
        returning thread_id_u64;
        ghost g => {
            if g.value() == local.thread_id {
                local.instance.block_on_the_local_thread(
                    local.thread_token.key(),
                    dealloc.mim_block.key(),
                    &local.thread_token,
                    &dealloc.mim_block,
                    &g,
                    );
            }
        }
    );

    let (thread_id, Tracked(is_thread)) = crate::thread::thread_id();
    proof { local.is_thread.agrees(is_thread); }
    let is_local = thread_id.thread_id == segment_thread_id_u64;

    // Calculate the pointer to the PageHeader for the *slice* that this block is in.
    // Remember this might not be the "main" PageHeader for this Page.

    let slice_page_ptr = calculate_slice_page_ptr_from_block(ptr, segment_ptr, Ghost(dealloc.block_id()));

    let tracked page_slice_shared_access: &PageSharedAccess =
        dealloc.mim_instance.alloc_guards_page_slice_shared_access(
            dealloc.block_id(),
            &dealloc.mim_block,
        );

    let slice_page: &Page = ptr_ref(slice_page_ptr,
        Tracked(&page_slice_shared_access.points_to));

    // Use the 'offset' to calculate a pointer to the main PageHeader for this page.

    let offset = slice_page.offset;

    let page_ptr = calculate_page_ptr_subtract_offset(
        slice_page_ptr,
        offset,
        Ghost(dealloc.block_id().page_id_for_slice()),
        Ghost(dealloc.block_id().page_id),
    );

    //assert(is_page_ptr(page_ptr, dealloc.block_id().page_id));

    /*
    let tracked page_shared_access: &PageSharedAccess;
    proof {
        page_shared_access = dealloc.mim_instance.alloc_guards_page_shared_access(
            dealloc.block_id(), &dealloc.mim_block);
    }
    let page: &Page = page_ptr.borrow(Tracked(&page_shared_access.points_to));
    */

    let ghost page_id = dealloc.block_id().page_id;
    let page = PagePtr {
        page_ptr,
        page_id: Ghost(page_id),
    };
    assert(page_ptr.addr() != 0) by { is_page_ptr_nonzero(page_ptr, page_id); }

    // Case based on whether this is thread local or not

    if likely(is_local) {
        //assert(local.pages.dom().contains(page_id));
        //assert(page.is_in(*local));
        //assert(page.wf());
        //assert(local.is_used_primary(page_id));

        if likely(page.get_inner_ref(Tracked(&*local)).not_full_nor_aligned()) {
            let used;
            page_get_mut_inner!(page, local, page_inner => {
                let tracked mim_block = dealloc.mim_block;

                //proof {
                    //assert(mim_block.key().page_id == page_inner.free.page_id());
                    //assert(mim_block.key().block_size == page_inner.free.block_size());
                //}

                page_inner.free.insert_block(ptr, Tracked(perm), Tracked(mim_block));

                bound_on_2_lists(Tracked(local.instance.clone()), Tracked(&local.thread_token), &mut page_inner.free, &mut page_inner.local_free);
                //assert(page_inner.used >= 1);

                used = page_inner.used - 1;
                page_inner.used = used;
            });

            proof {
                crate::os_mem_util::preserves_mem_chunk_good(*old(local), *local);
                //assert(local.wf());
            }

            if unlikely(used == 0) {
                crate::page::page_retire(page, Tracked(&mut *local));
            }
        } else {
            free_generic(segment_ptr, page, true, ptr,
                Tracked(perm), Tracked(dealloc), Tracked(&mut *local));
        }
    } else {
        free_generic(segment_ptr, page, false, ptr,
            Tracked(perm), Tracked(dealloc), Tracked(&mut *local));
    }
}

fn free_generic(segment: *mut SegmentHeader, page: PagePtr, is_local: bool, p: *mut u8, Tracked(perm): Tracked<PointsToRaw>, Tracked(dealloc): Tracked<MimDeallocInner>, Tracked(local): Tracked<&mut Local>)
    requires
        old(local).wf(),
        dealloc.wf(),
        perm.is_range(p as int, dealloc.block_id().block_size as int),
        perm.provenance() == p@.provenance,
        p == dealloc.ptr,
        old(local).instance == dealloc.mim_instance,
        page.wf(),
        is_local ==> page.is_in(*old(local)),
        is_local ==> old(local).is_used_primary(page.page_id@),
        is_local ==> old(local).thread_token.value().pages[page.page_id@].block_size == dealloc.block_id().block_size,
        page.page_id@ == dealloc.block_id().page_id,
    ensures
        local.wf(),
        common_preserves(*old(local), *local),
{
    // this has_aligned check could be a data race??
    //if page.get_inner_ref(Tracked(&*local)).get_has_aligned() {
    //    todo();
    //}

    free_block(page, is_local, p, Tracked(perm), Tracked(dealloc), Tracked(&mut *local));
}

fn free_block(page: PagePtr, is_local: bool, ptr: *mut u8, Tracked(perm): Tracked<PointsToRaw>, Tracked(dealloc): Tracked<MimDeallocInner>, Tracked(local): Tracked<&mut Local>)
    requires
        old(local).wf(),
        dealloc.wf(),
        perm.is_range(ptr as int, dealloc.block_id().block_size as int),
        perm.provenance() == ptr@.provenance,
        ptr == dealloc.ptr,
        old(local).instance == dealloc.mim_instance,
        page.wf(),
        is_local ==> page.is_in(*old(local)),
        is_local ==> old(local).is_used_primary(page.page_id@),
        is_local ==> old(local).thread_token.value().pages[page.page_id@].block_size == dealloc.block_id().block_size,
        page.page_id@ == dealloc.block_id().page_id,
    ensures
        local.wf(),
        common_preserves(*old(local), *local),
{
    if likely(is_local) {
        let used;
        page_get_mut_inner!(page, local, page_inner => {
            let tracked mim_block = dealloc.mim_block;

            //proof {
            //    assert(mim_block.key().page_id == page_inner.free.page_id());
            //    assert(mim_block.key().block_size == page_inner.free.block_size());
            //}

            page_inner.free.insert_block(ptr, Tracked(perm), Tracked(mim_block));

            bound_on_2_lists(Tracked(local.instance.clone()), Tracked(&local.thread_token), &mut page_inner.free, &mut page_inner.local_free);
            //assert(page_inner.used >= 1);

            used = page_inner.used - 1;
            page_inner.used = used;
        });

        proof {
            crate::os_mem_util::preserves_mem_chunk_good(*old(local), *local);
            //assert(local.wf());
        }

        if unlikely(used == 0) {
            crate::page::page_retire(page, Tracked(&mut *local));
        } else if unlikely(page.get_inner_ref(Tracked(&*local)).get_in_full()) {
            crate::page::page_unfull(page, Tracked(&mut *local));
        }
    } else {
        free_block_mt(page, ptr, Tracked(perm), Tracked(dealloc), Tracked(&mut *local));
    }
}

fn free_block_mt(page: PagePtr, ptr: *mut u8, Tracked(perm): Tracked<PointsToRaw>, Tracked(dealloc): Tracked<MimDeallocInner>, Tracked(local): Tracked<&mut Local>)
    requires
        old(local).wf(),
        dealloc.wf(),
        perm.is_range(ptr as int, dealloc.block_id().block_size as int),
        perm.provenance() == ptr@.provenance,
        ptr == dealloc.ptr,
        old(local).instance == dealloc.mim_instance,
        page.page_id@ == dealloc.block_id().page_id,
        page.wf(),
    ensures
        local.wf(),
        common_preserves(*old(local), *local),
{
    // Based on _mi_free_block_mt

    // TODO check the segment kind

    let tracked mut perm = perm;
    let tracked mut delay_actor_token_opt: Option<Mim::delay_actor> = None;
    let tracked MimDeallocInner { mim_block, mim_instance, .. } = dealloc;
    let tracked mut mim_block_opt = Some(mim_block);
    let ptr = ptr as *mut Node;
    let mut use_delayed;

    loop
        invariant
            dealloc.wf(),
            mim_block_opt == Some(dealloc.mim_block),
            mim_instance == dealloc.mim_instance,
            mim_instance == local.instance,
            perm.is_range(ptr as int, dealloc.block_id().block_size as int),
            perm.provenance() == ptr@.provenance,
            ptr as *mut u8 == dealloc.ptr,
            is_page_ptr(page.page_ptr, dealloc.block_id().page_id),
            local.wf(),
            common_preserves(*old(local), *local),

            //*page == 
            //    dealloc.mim_block.value().page_shared_access.points_to@.value.get_Some_0(),
        //ensures
        //    use_delayed ==> (match delay_actor_token_opt {
        //        None => false,
        //        Some(tok) => tok@.instance == dealloc.mim_instance
        //            && tok@.key == dealloc.block_id().page_id
        //    }),
    {
        let tracked page_shared_access: &PageSharedAccess =
            mim_instance.alloc_guards_page_shared_access(
                dealloc.block_id(), mim_block_opt.tracked_borrow());
        let pag: &Page = ptr_ref(page.page_ptr, Tracked(&page_shared_access.points_to));


        let ghost mut next_ptr;
        let ghost mut delay;
        let mask = atomic_with_ghost!(&pag.xthread_free.atomic => load(); ghost g => {
            pag.xthread_free.emp_inst.borrow().agree(pag.xthread_free.emp.borrow(), &g.0);
            next_ptr = g.1.unwrap().1.ptr();
            delay = g.1.unwrap().0.value(); // TODO fix macro syntax in atomic_with_ghost
        });

        use_delayed = masked_ptr_delay_get_is_use_delayed(mask, Ghost(delay), Ghost(next_ptr));
        let mask1;
        
        let tracked mut ptr_mem = None;
        let tracked mut raw_mem = None;
        let tracked mut exposed = None;

        if unlikely(use_delayed) {
            mask1 = masked_ptr_delay_set_freeing(mask, Ghost(delay), Ghost(next_ptr));
        } else {
            proof {
                block_size_ge_word();
                block_ptr_aligned_to_word();
                is_block_ptr_mult4(ptr as *mut u8, dealloc.block_id());
            }

            // *ptr = mask.next_ptr
            let (ptr_mem0, raw_mem0) = LL::block_write_ptr(
                ptr,
                Tracked(perm),
                masked_ptr_delay_get_ptr(mask, Ghost(delay), Ghost(next_ptr)));
            //assert(ptr_mem0@.ptr() == ptr);

            let Tracked(exposed0) = expose_provenance(ptr);

            proof {
                perm = PointsToRaw::empty(ptr@.provenance);
                ptr_mem = Some(ptr_mem0.get());
                raw_mem = Some(raw_mem0.get());
                exposed = Some(exposed0);
            }

            //assert(ptr_mem.unwrap().ptr() == ptr);

            // mask1 = mask (set next_ptr to ptr)
            mask1 = masked_ptr_delay_set_ptr(mask, ptr, Ghost(delay), Ghost(next_ptr));
        }

        //assert(pag.xthread_free.instance == mim_instance);

        let cas_result = atomic_with_ghost!(
            &pag.xthread_free.atomic => compare_exchange_weak(mask, mask1);
            update v_old -> v_new;
            returning cas_result;
            ghost g =>
        {
            pag.xthread_free.emp_inst.borrow().agree(pag.xthread_free.emp.borrow(), &g.0);
            let tracked (emp_token, pair_opt) = g;
            let tracked pair = pair_opt.tracked_unwrap();
            let tracked (mut delay_token, mut ghost_ll) = pair;

            let ghost ok = cas_result.is_Ok();
            if use_delayed {
                if ok {
                    let tracked (Tracked(delay_token0), Tracked(delay_actor_token)) =
                        mim_instance.delay_enter_freeing(
                            dealloc.block_id().page_id,
                            dealloc.block_id(),
                            mim_block_opt.tracked_borrow(),
                            delay_token);
                    delay_token = delay_token0;
                    delay_actor_token_opt = Some(delay_actor_token);
                } else {
                    // do nothing
                }
            } else {
                if ok {
                    let tracked mim_block = mim_block_opt.tracked_unwrap();
                    //assert(ptr_mem.unwrap().ptr() == ptr);
                    ghost_ll.ghost_insert_block(ptr, ptr_mem.tracked_unwrap(),
                        raw_mem.tracked_unwrap(), mim_block, exposed.tracked_unwrap());

                    mim_block_opt = None;

                    is_block_ptr_mult4(ptr as *mut u8, dealloc.block_id());
                } else {
                    // do nothing

                    // okay, actually do 1 thing: reset the 'perm' variable
                    // for the next loop.
                    let tracked mut ptr_mem = ptr_mem.tracked_unwrap();
                    let tracked raw_mem = raw_mem.tracked_unwrap();
                    ptr_mem.leak_contents();
                    perm = ptr_mem.into_raw().join(raw_mem);
                }
            }

            g = (emp_token, Some((delay_token, ghost_ll)));

            //assert(ghost_ll.wf());
            //assert(ghost_ll.block_size() == pag.xthread_free.block_size());
            //assert(ghost_ll.instance() == pag.xthread_free.instance@);
            //assert(ghost_ll.page_id() == pag.xthread_free.page_id());
            //assert(ghost_ll.fixed_page());
            //assert(delay_token@.instance == pag.xthread_free.instance@);
            //assert(delay_token@.key == pag.xthread_free.page_id());
            //assert(v_new as int == ghost_ll.ptr() as int + delay_token@.value.to_int());
            //assert(ghost_ll.ptr() as int % 4 == 0);
        });

        match cas_result {
            Result::Err(_) => { }
            Result::Ok(_) => {
                if unlikely(use_delayed) {
                    // Lookup the heap ptr

                    let tracked mut delay_actor_token;
                    let ghost mut heap_id;

                    let tracked page_shared_access: &PageSharedAccess =
                        mim_instance.alloc_guards_page_shared_access(
                            dealloc.block_id(), mim_block_opt.tracked_borrow());
                    let pag: &Page = ptr_ref(page.page_ptr, Tracked(&page_shared_access.points_to));

                    let heap_ptr = atomic_with_ghost!(
                        &pag.xheap.atomic => load();
                        ghost g =>
                    {
                        delay_actor_token = delay_actor_token_opt.tracked_unwrap();
                        //assert(!pag.xheap.is_empty());
                        //assert(pag.xheap.wf(pag.xheap.instance@, pag.xheap.page_id@));
                        pag.xheap.emp_inst.borrow().agree(pag.xheap.emp.borrow(), &g.0);
                        //assert(g.0@.value == false);
                        let tracked (Tracked(tok), _) = mim_instance.delay_lookup_heap(
                            dealloc.block_id(),
                            &local.my_inst,
                            mim_block_opt.tracked_borrow(),
                            g.1.tracked_borrow(),
                            delay_actor_token);
                        delay_actor_token = tok;
                        heap_id = g.1.unwrap().value();
                    });

                    let tracked heap_shared_access: &HeapSharedAccess;
                    proof {
                        heap_shared_access = mim_instance.delay_guards_heap_shared_access(
                            dealloc.block_id().page_id,
                            &delay_actor_token,
                        );
                        //assert(heap_shared_access.wf2(heap_id, mim_instance));
                    }
                    let heap: &Heap = ptr_ref(heap_ptr,
                        Tracked(&heap_shared_access.points_to));

                    let tracked mim_block = mim_block_opt.tracked_unwrap();
                    let tracked mim_block = local.instance.block_set_heap_id(mim_block.key(),
                        mim_block, &delay_actor_token);
                    heap.thread_delayed_free.atomic_insert_block(ptr, Tracked(perm), Tracked(mim_block));

                    let tracked page_shared_access: &PageSharedAccess =
                        mim_instance.delay_guards_page_shared_access(
                            dealloc.block_id().page_id, &delay_actor_token);
                    let pag: &Page = ptr_ref(page.page_ptr, Tracked(&page_shared_access.points_to));

                    //pag.xthread_free.exit_delaying_state(Tracked(delay_actor_token));

                    // have to inline this bc of lifetimes
                    atomic_with_ghost!(
                        &pag.xthread_free.atomic => fetch_xor(3);
                        update v_old -> v_new;
                        ghost g => {
                            pag.xthread_free.emp_inst.borrow().agree(pag.xthread_free.emp.borrow(), &g.0);
                            let tracked (emp_token, pair_opt) = g;
                            let tracked pair = pair_opt.tracked_unwrap();
                            let tracked (mut delay_token, mut ll) = pair;

                            delay_token = mim_instance.delay_leave_freeing(dealloc.block_id().page_id,
                                delay_token, delay_actor_token);

                            // TODO right now this only works for fixed-width architecture
                            //verus_proof_expr!{ { // TODO fix atomic_with_ghost
                            //    assert(v_old % 4 == 1usize ==> (v_old ^ 3) == add(v_old, 1)) by (bit_vector);
                            //} }

                            g = (emp_token, Some((delay_token, ll)));

                            let v_old = v_old as usize;

                            assert(v_old % 4 == 1usize ==> (v_old ^ 3) == add(v_old, 1))
                              by (bit_vector);
                        }
                    );
                }
                return;
            }
        }
    }
}

pub fn free_delayed_block(ptr: *mut u8,
    Tracked(perm): Tracked<PointsToRaw>,
    Tracked(dealloc): Tracked<MimDeallocInner>,
    Tracked(local): Tracked<&mut Local>,
) -> (res: (bool, Tracked<Option<PointsToRaw>>, Tracked<Option<MimDeallocInner>>))
    requires old(local).wf(),
        dealloc.wf(),
        perm.is_range(ptr as int, dealloc.block_id().block_size as int),
        perm.provenance() == ptr@.provenance,
        ptr == dealloc.ptr,
        old(local).instance == dealloc.mim_instance,
        dealloc.mim_block.value().heap_id == Some(old(local).thread_token.value().heap_id),
    ensures
        local.wf(),
        common_preserves(*old(local), *local),
        !res.0 ==> res.1@ == Some(perm),
        !res.0 ==> res.2@ == Some(dealloc),
{
    let ghost block_id = dealloc.mim_block.key();
    let segment = crate::layout::calculate_segment_ptr_from_block(ptr, Ghost(block_id));

    let slice_page_ptr = crate::layout::calculate_slice_page_ptr_from_block(ptr, segment, Ghost(block_id));
    let tracked page_slice_shared_access: &PageSharedAccess =
        local.instance.alloc_guards_page_slice_shared_access(
            block_id,
            &dealloc.mim_block,
        );
    let slice_page: &Page = ptr_ref(slice_page_ptr,
        Tracked(&page_slice_shared_access.points_to));
    let offset = slice_page.offset;
    let page_ptr = crate::layout::calculate_page_ptr_subtract_offset(
        slice_page_ptr,
        offset,
        Ghost(block_id.page_id_for_slice()),
        Ghost(block_id.page_id),
    );
    //assert(crate::layout::is_page_ptr(page_ptr, block_id.page_id));
    let ghost page_id = dealloc.block_id().page_id;
    assert(page_ptr as int != 0) by { is_page_ptr_nonzero(page_ptr, page_id); }

    let page = PagePtr { page_ptr: page_ptr, page_id: Ghost(block_id.page_id) };
    proof {
        local.instance.block_in_heap_has_valid_page(
            local.thread_token.key(),
            dealloc.mim_block.key(),
            &local.thread_token,
            &dealloc.mim_block);
    }
    //assert(page.is_in(*local));
    //assert(page.is_used_and_primary(*local));
    //assert(local.thread_token.value().pages[page.page_id@].block_size == dealloc.block_id().block_size);

    if !crate::page::page_try_use_delayed_free(page, 0, false, Tracked(&*local)) {
        return (false, Tracked(Some(perm)), Tracked(Some(dealloc)));
    }

    crate::alloc_generic::page_free_collect(page, false, Tracked(&mut *local));

    //assert(local.thread_token.value().pages[page.page_id@].block_size == dealloc.block_id().block_size);

    crate::free::free_block(page, true, ptr,
        Tracked(perm), Tracked(dealloc), Tracked(&mut *local));

    return (true, Tracked(None), Tracked(None));
}

}
