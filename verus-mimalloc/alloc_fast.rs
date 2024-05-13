#![allow(unused_imports)]

use core::intrinsics::{unlikely, likely};

use vstd::prelude::*;
use vstd::ptr::*;
use vstd::*;
use vstd::modes::*;
use vstd::set_lib::*;

use crate::tokens::{Mim, BlockId, DelayState};
use crate::types::*;
use crate::layout::*;
use crate::linked_list::*;
use crate::dealloc_token::*;
use crate::alloc_generic::*;
use crate::os_mem_util::*;
use crate::config::*;
use crate::bin_sizes::*;

verus!{

// Implements the "fast path"

// malloc -> heap_malloc -> heap_malloc_zero -> heap_malloc_zero_ex
//  -> heap_malloc_small_zero
//  -> heap_get_free_small_page & page_malloc

#[inline]
pub fn heap_malloc(heap: HeapPtr, size: usize, Tracked(local): Tracked<&mut Local>)  // $line_count$Trusted$
    -> (t: (PPtr<u8>, Tracked<PointsToRaw>, Tracked<MimDealloc>)) // $line_count$Trusted$
    requires // $line_count$Trusted$
        old(local).wf(), // $line_count$Trusted$
        heap.wf(), // $line_count$Trusted$
        heap.is_in(*old(local)), // $line_count$Trusted$
    ensures // $line_count$Trusted$
        local.wf(), // $line_count$Trusted$
        local.instance == old(local).instance, // $line_count$Trusted$
        forall |heap: HeapPtr| heap.is_in(*old(local)) ==> heap.is_in(*local), // $line_count$Trusted$
        ({ // $line_count$Trusted$
            let (ptr, points_to_raw, dealloc) = t; // $line_count$Trusted$

            dealloc@.wf() // $line_count$Trusted$
              && points_to_raw@.is_range(ptr.id(), size as int)  // $line_count$Trusted$
              && ptr.id() == dealloc@.ptr()  // $line_count$Trusted$
              && dealloc@.instance() == local.instance  // $line_count$Trusted$
              && dealloc@.size == size  // $line_count$Trusted$
        })  // $line_count$Trusted$
{
    heap_malloc_zero(heap, size, false, Tracked(&mut *local))
}

#[inline]
pub fn heap_malloc_zero(heap: HeapPtr, size: usize, zero: bool, Tracked(local): Tracked<&mut Local>)
    -> (t: (PPtr<u8>, Tracked<PointsToRaw>, Tracked<MimDealloc>))
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
    heap_malloc_zero_ex(heap, size, zero, 0, Tracked(&mut *local))
}

#[inline]
pub fn heap_malloc_zero_ex(heap: HeapPtr, size: usize, zero: bool, huge_alignment: usize, Tracked(local): Tracked<&mut Local>)
    -> (t: (PPtr<u8>, Tracked<PointsToRaw>, Tracked<MimDealloc>))
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
    if likely(size <= SMALL_SIZE_MAX) {
        heap_malloc_small_zero(heap, size, zero, Tracked(&mut *local))
    } else {
        malloc_generic(heap, size, zero, huge_alignment, Tracked(&mut *local))
    }
}

#[inline]
pub fn heap_get_free_small_page(heap: HeapPtr, size: usize, Tracked(local): Tracked<&Local>) -> (page: PagePtr)
    requires 0 <= size <= SMALL_SIZE_MAX,
        local.wf_main(), heap.is_in(*local), heap.wf(),
    ensures
        !page.is_empty_global(*local) ==> ({
          &&& page.wf()
          &&& Some(page.page_id@) == 
            local.page_organization.used_dlist_headers[smallest_bin_fitting_size((size + 7) / 8 * 8)].first
        })
{
    let idx = (size + 7) / 8;
    let ptr = heap.get_pages_free_direct(Tracked(local))[idx];

    let ghost bin_idx = smallest_bin_fitting_size((size + 7) / 8 * 8);
    let ghost page_id = 
        local.page_organization.used_dlist_headers[bin_idx].first.unwrap();
    let page_ptr = PagePtr { page_ptr: ptr, page_id: Ghost(page_id) };
    proof {
        bounds_for_smallest_bin_fitting_size((size + 7) / 8 * 8);
        if page_ptr.page_ptr.id() != local.page_empty_global@.s.points_to@.pptr {
            //assert(local.heap.pages_free_direct@.value.unwrap()@[idx as int].id()
            //    == local.heap.pages@.value.unwrap()@[bin_idx].first.id());
            //assert(local.heap.pages@.value.unwrap()@[bin_idx].first.id() != 0);
        }
    }
    return page_ptr;
}

#[inline]
pub fn heap_malloc_small_zero(
    heap: HeapPtr,
    size: usize,
    zero: bool,
    Tracked(local): Tracked<&mut Local>,
) -> (t: (PPtr<u8>, Tracked<PointsToRaw>, Tracked<MimDealloc>))
    requires
        old(local).wf(),
        heap.wf(),
        heap.is_in(*old(local)),
        size <= SMALL_SIZE_MAX,
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
    /*let mut size = size;
    if PADDING {
        if size == 0 {
            size = INTPTR_SIZE;
        }
    }*/

    let page = heap_get_free_small_page(heap, size, Tracked(&*local));

    proof {
        let bin_idx = smallest_bin_fitting_size((size + 7) / 8 * 8);
        bounds_for_smallest_bin_fitting_size((size + 7) / 8 * 8);
        local.page_organization.used_first_is_in(bin_idx);

        //assert(local.page_organization.used_dlist_headers[bin_idx].first == Some(page.page_id@));
        //assert(local.page_organization.pages.dom().contains(page.page_id@));
        //assert(local.pages.dom().contains(page.page_id@));
    }

    let (p, Tracked(points_to_raw), Tracked(mim_dealloc)) = page_malloc(heap, page, size, zero, Tracked(&mut *local));

    (p, Tracked(points_to_raw), Tracked(mim_dealloc))
}

pub fn page_malloc(
    heap: HeapPtr,
    page_ptr: PagePtr,
    size: usize,
    zero: bool,

    Tracked(local): Tracked<&mut Local>,
) -> (t: (PPtr<u8>, Tracked<PointsToRaw>, Tracked<MimDealloc>))
    requires
        old(local).wf(),
        heap.wf(),
        heap.is_in(*old(local)),
        page_ptr.is_empty_global(*old(local)) || ({
            &&& page_ptr.wf()
            &&& page_ptr.is_used_and_primary(*old(local))
            &&& size <= old(local).page_state(page_ptr.page_id@).block_size
        })
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
    if unlikely(page_ptr.get_inner_ref_maybe_empty(Tracked(&*local)).free.is_empty()) {
        return malloc_generic(heap, size, zero, 0, Tracked(&mut *local));
    }
    //assert(!page_ptr.is_empty_global(*local));

    let popped;

    page_get_mut_inner!(page_ptr, local, page_inner => {
        popped = page_inner.free.pop_block();

        //assert(page_inner.used < 1000000);
        page_inner.used = page_inner.used + 1;
    });

    let ptr = popped.0;

    let tracked dealloc;
    let tracked points_to_raw;
    proof {
        let tracked points_to_r = popped.1.get();
        let tracked block = popped.2.get();

        //const_facts(); 
        //reveal(is_block_ptr);
        local.instance.get_block_properties(
            local.thread_token@.key,
            block@.key,
            &local.thread_token,
            &block);
        /*assert(block@.key.slice_idx >= block@.key.page_id.idx);
        assert(block@.value.page_shared_access == local.thread_token@.value.pages[block@.key.page_id].shared_access);
        assert(local.thread_token@.value.pages.dom().contains(block@.key.page_id_for_slice()));
        assert(block@.value.page_slice_shared_access == local.thread_token@.value.pages[block@.key.page_id_for_slice()].shared_access);
        assert(block@.value.segment_shared_access == local.thread_token@.value.segments[block@.key.page_id.segment_id].shared_access);

        assert(block@.value.page_shared_access.wf(block@.key.page_id,
            block@.key.block_size, local.instance));
        assert(valid_block_token(block, local.instance));*/
        //assert(!block@.value.allocated);

        // Mark the block as 'allocated' in the token system
        // let tracked thread_token = local.take_thread_token();
        //assert(thread_token@.instance == local.instance);
        //assert(block@.instance == local.instance);
        //assert(block@.key.page_id == page_ptr.page_id);
        //#[spec] let ot = thread_token;
        // let tracked (Tracked(thread_token), Tracked(block)) = local.instance.alloc_block(
        //    block@.key, local.thread_id,
        //    thread_token, block);
        //local.thread_token = thread_token;

        //assert(thread_token@.value.pages.index(page_ptr.page_id).len + 1 ==
        //       ot@.value.pages.index(page_ptr.page_id).len);

        let tracked dealloc_inner = MimDeallocInner {
            mim_instance: local.instance.clone(),
            mim_block: block,
            ptr: ptr.id(),
        };
        let tracked (dealloc0, points_to_raw0) = dealloc_inner.into_user(points_to_r, size as int);

        dealloc = dealloc0;
        points_to_raw = points_to_raw0;

        // Mark the block as 'allocated' in the token system
        //let Local { thread_id, instance, thread_token, heap_id, heap, pages, segments }
        //    = local;

        /*assert(local.pages.index(page_ptr.page_id@).wf(
                    page_ptr.page_id@,
                    local.thread_token@.value.pages.index(page_ptr.page_id@),
                    local.instance,
                  ));*/
        preserves_mem_chunk_good(*old(local), *local);
        //assert(local.wf());
    }

    (ptr, Tracked(points_to_raw), Tracked(dealloc))
}


}
