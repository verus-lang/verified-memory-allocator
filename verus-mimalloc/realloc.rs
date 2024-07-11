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

/*
#[inline(always)]
fn usable_size(p: PPtr<u8>,
    Tracked(user_perm): Tracked<&ptr::PointsToRaw>,
    Tracked(user_dealloc): Tracked<&MimDealloc>,
    Tracked(local): Tracked<&Local>,
)
    requires
        old(local).wf(),
        user_dealloc.wf(),
        ptr.id() == user_perm@.pptr,
        ptr.id() == user_dealloc.ptr(),
        user_perm@.size == user_dealloc.size,
        old(local).instance == user_dealloc.instance()
    ensures
        local.wf(),
        local.instance == old(local).instance,
{
    let segment_ptr = calculate_segment_ptr_from_block(ptr, Ghost(dealloc.block_id()));

    let tracked segment_shared_access: &SegmentSharedAccess =
        dealloc.mim_instance.alloc_guards_segment_shared_access(
            dealloc.block_id(),
            &dealloc.mim_block,
        );

    let segment: &SegmentHeader = segment_ptr.borrow(
        Tracked(&segment_shared_access.points_to));

    let slice_page_ptr = calculate_slice_page_ptr_from_block(ptr, segment_ptr, Ghost(dealloc.block_id()));

    let tracked page_slice_shared_access: &PageSharedAccess =
        dealloc.mim_instance.alloc_guards_page_slice_shared_access(
            dealloc.block_id(),
            &dealloc.mim_block,
        );

    let slice_page: &Page = slice_page_ptr.borrow(
        Tracked(&page_slice_shared_access.points_to));

    // Use the 'offset' to calculate a pointer to the main PageHeader for this page.

    let offset = slice_page.offset;

    let page_ptr = calculate_page_ptr_subtract_offset(
        slice_page_ptr,
        offset,
        Ghost(dealloc.block_id().page_id_for_slice()),
        Ghost(dealloc.block_id().page_id),
    );

    assert(is_page_ptr(page_ptr.id(), dealloc.block_id().page_id));

    let ghost page_id = dealloc.block_id().page_id;
    let page = PagePtr {
        page_ptr,
        page_id: Ghost(page_id),
    };
    assert(page_ptr.id() != 0) by { is_page_ptr_nonzero(page_ptr.id(), page_id); }

    // TODO check aligned
}
*/


}
