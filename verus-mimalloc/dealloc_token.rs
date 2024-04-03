#![allow(unused_imports)]
use vstd::ptr::*;
use crate::tokens::{Mim, BlockId, DelayState};
use crate::types::*;
use crate::layout::*;
use vstd::prelude::*;
use vstd::set_lib::*;

verus!{

pub tracked struct MimDealloc {
    pub tracked padding: PointsToRaw,

    // Size of the allocation from the user perspective, <= the block size
    pub ghost size: int,

    // Memory to make up the difference between user size and block size
    pub tracked inner: MimDeallocInner,
}

pub tracked struct MimDeallocInner {
    pub tracked mim_instance: Mim::Instance,
    pub tracked mim_block: Mim::block,

    pub ghost ptr: int,
}

pub open spec fn valid_block_token(block: Mim::block, instance: Mim::Instance) -> bool {
    &&& block@.key.wf()
    &&& block@.instance == instance

    // TODO factor this stuff into wf predicates

    // Valid segment

    &&& is_segment_ptr(
        block@.value.segment_shared_access.points_to@.pptr,
        block@.key.page_id.segment_id)
    &&& block@.value.segment_shared_access.points_to@.value.is_some()
    &&& block@.value.segment_shared_access.points_to@.value.get_Some_0()
        .wf(instance, block@.key.page_id.segment_id)

    // Valid slice page

    &&& is_page_ptr(
        block@.value.page_slice_shared_access.points_to@.pptr,
        block@.key.page_id_for_slice())
    &&& block@.value.page_slice_shared_access.points_to@.value.is_some()
    &&& block@.value.page_slice_shared_access.points_to@.value.get_Some_0().offset as int
          == (block@.key.slice_idx - block@.key.page_id.idx) * crate::config::SIZEOF_PAGE_HEADER

    // Valid main page

    &&& block@.value.page_shared_access.wf(
        block@.key.page_id,
        block@.key.block_size,
        instance)
}

impl MimDeallocInner {
    #[verifier(inline)]
    pub open spec fn block_id(&self) -> BlockId {
        self.mim_block@.key
    }

    pub open spec fn wf(&self) -> bool {
        &&& valid_block_token(self.mim_block, self.mim_instance)
        &&& is_block_ptr(self.ptr, self.block_id())
    }

    pub proof fn into_user(tracked self, tracked points_to_raw: PointsToRaw, sz: int)
        -> (tracked res: (MimDealloc, PointsToRaw))

        requires
            self.wf(),
            points_to_raw.is_range(self.ptr, self.block_id().block_size as int),
            0 <= sz <= self.block_id().block_size,
        ensures ({
            let (md, points_to_raw) = res;
            md.wf()
            && points_to_raw.is_range(self.ptr, sz)
            && md.size == sz
            && md.block_id() == self.block_id()
            && md.ptr() == self.ptr
            && md.instance() == self.mim_instance
        })
    {
        let tracked (x, y) = points_to_raw.split(set_int_range(self.ptr, self.ptr + sz));
        let tracked md = MimDealloc { padding: y, size: sz, inner: self };
        (md, x)
    }
}

impl MimDealloc {
    #[verifier(inline)]
    pub open spec fn block_id(&self) -> BlockId {
        self.inner.block_id()
    }

    pub open spec fn ptr(&self) -> int {
        self.inner.ptr
    }

    pub open spec fn instance(&self) -> Mim::Instance {
        self.inner.mim_instance
    }

    pub open spec fn wf(&self) -> bool {
        self.inner.wf()
          // PAPER CUT: is_range should probably have this condition in it
          && self.block_id().block_size - self.size >= 0
          && self.size >= 0
          && self.padding.is_range(self.inner.ptr + self.size,
              self.block_id().block_size - self.size)
    }

    pub proof fn into_internal(tracked self, tracked points_to_raw: PointsToRaw)
        -> (tracked res: (MimDeallocInner, PointsToRaw))

        requires
            self.wf(),
            points_to_raw.is_range(self.ptr(), self.size)
        ensures ({
            let (md, points_to_raw_full) = res;
            md.wf()
            && points_to_raw_full.is_range(self.ptr(), self.block_id().block_size as int)
            && self.ptr() == md.ptr
            && self.block_id().block_size == md.mim_block@.key.block_size
            && md.mim_instance == self.instance()
        })
    {
        let tracked MimDealloc { padding, size, inner } = self;
        let tracked p = points_to_raw.join(padding);
        (inner, p)
    }
}


}
