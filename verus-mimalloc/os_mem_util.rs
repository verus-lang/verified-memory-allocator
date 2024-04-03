use vstd::prelude::*;
use vstd::set_lib::*;
use vstd::ptr::*;
use vstd::modes::*;

use crate::os_mem::*;
use crate::layout::*;
use crate::tokens::*;
use crate::config::*;
use crate::page_organization::*;
use crate::types::*;

verus!{

impl MemChunk {
    pub proof fn empty() -> (tracked mc: MemChunk)
    {
       MemChunk { os: Map::tracked_empty(), points_to: PointsToRaw::empty() }
    }

    #[verifier::inline]
    pub open spec fn pointsto_has_range(&self, start: int, len: int) -> bool {
        set_int_range(start, start + len) <= self.range_points_to()
    }

    pub open spec fn os_rw_bytes(&self) -> Set<int> {
        self.range_os_rw()
    }

    pub open spec fn committed_pointsto_has_range(&self, start: int, len: int) -> bool {
        self.pointsto_has_range(start, len) && self.os_has_range_read_write(start, len)
    }

    pub proof fn split(
        tracked &mut self,
        start: int,
        len: int
    ) -> (tracked t: Self)
        ensures
            t.points_to@ == old(self).points_to@.restrict(set_int_range(start, start + len)),
            t.os == old(self).os.restrict(set_int_range(start, start + len)),
            self.points_to@ == old(self).points_to@.remove_keys(set_int_range(start, start + len)),
            self.os == old(self).os.remove_keys(set_int_range(start, start + len)),
    {
        let tracked split_os = self.os.tracked_remove_keys(
            set_int_range(start, start + len).intersect(self.os.dom())
        );

        let tracked mut pt = PointsToRaw::empty();
        tracked_swap(&mut pt, &mut self.points_to);
        let tracked (rt, pt) = pt.split(set_int_range(start, start + len).intersect(pt@.dom()));
        self.points_to = pt;

        let tracked t = MemChunk { os: split_os, points_to: rt };

        assert(self.points_to@ =~= old(self).points_to@.remove_keys(set_int_range(start, start + len)));
        assert(self.os =~= old(self).os.remove_keys(set_int_range(start, start + len)));
        assert(t.points_to@ =~= old(self).points_to@.restrict(set_int_range(start, start + len)));
        assert(t.os =~= old(self).os.restrict(set_int_range(start, start + len)));

        t
    }

    pub proof fn join(
        tracked &mut self,
        tracked t: Self,
    )
        ensures
            self.points_to@ == old(self).points_to@.union_prefer_right(t.points_to@),
            self.os == old(self).os.union_prefer_right(t.os),
    {
        let tracked MemChunk { os, points_to } = t;
        self.os.tracked_union_prefer_right(os);

        let tracked mut pt = PointsToRaw::empty();
        tracked_swap(&mut pt, &mut self.points_to);
        let tracked pt = pt.join(points_to);
        self.points_to = pt;
    }

    pub proof fn os_restrict(
        tracked &mut self,
        start: int,
        len: int
    )
        requires old(self).os_has_range(start, len),
        ensures self.points_to == old(self).points_to,
            self.os == old(self).os.restrict(set_int_range(start, start + len))
    {
        self.os.tracked_remove_keys(self.os.dom() - set_int_range(start, start + len));
        assert(self.os =~= old(self).os.restrict(set_int_range(start, start + len)));
    }

    pub proof fn take_points_to_set(
        tracked &mut self,
        s: Set<int>,
    ) -> (tracked points_to: PointsToRaw)
        requires 
            s <= old(self).points_to@.dom()
        ensures
            self.os == old(self).os,
            self.points_to@ == old(self).points_to@.remove_keys(s),
            points_to@.dom() == s,
    {
        let tracked mut pt = PointsToRaw::empty();
        tracked_swap(&mut pt, &mut self.points_to);
        let tracked (rt, pt) = pt.split(s);
        self.points_to = pt;
        assert(rt@.dom() =~= s);
        rt
    }

    pub proof fn take_points_to_range(
        tracked &mut self,
        start: int,
        len: int
    ) -> (tracked points_to: PointsToRaw)
        requires 
            len >= 0,
            old(self).pointsto_has_range(start, len),
        ensures
            self.os == old(self).os,
            self.points_to@ == old(self).points_to@.remove_keys(set_int_range(start, start+len)),
            points_to.is_range(start, len)
    {
        let tracked mut pt = PointsToRaw::empty();
        tracked_swap(&mut pt, &mut self.points_to);
        let tracked (rt, pt) = pt.split(set_int_range(start, start + len));
        self.points_to = pt;
        rt
    }

    pub proof fn give_points_to_range(
        tracked &mut self,
        tracked points_to: PointsToRaw,
    )
        requires 
            old(self).wf(),
        ensures
            self.wf(),
            self.os == old(self).os,
            self.points_to@.dom() == old(self).points_to@.dom() + points_to@.dom(),
    {
        let tracked mut pt = PointsToRaw::empty();
        tracked_swap(&mut pt, &mut self.points_to);
        let tracked pt = pt.join(points_to);
        self.points_to = pt;
        assert(self.points_to@.dom() =~= old(self).points_to@.dom() + points_to@.dom());
    }
}

pub open spec fn segment_info_range(segment_id: SegmentId) -> Set<int> {
    set_int_range(segment_start(segment_id),
        segment_start(segment_id) + SIZEOF_SEGMENT_HEADER + SIZEOF_PAGE_HEADER * (SLICES_PER_SEGMENT + 1)
    )
}

pub open spec fn mem_chunk_good1(
    mem: MemChunk,
    segment_id: SegmentId,
    commit_bytes: Set<int>,
    decommit_bytes: Set<int>,
    pages_range_total: Set<int>,
    pages_used_total: Set<int>,
) -> bool {
    &&& mem.wf()
    &&& mem.os_exact_range(segment_start(segment_id), SEGMENT_SIZE as int)

    &&& commit_bytes.subset_of(mem.os_rw_bytes())

    &&& decommit_bytes <= commit_bytes
    &&& segment_info_range(segment_id) <= commit_bytes - decommit_bytes
    &&& pages_used_total <= commit_bytes - decommit_bytes

    &&& mem.os_rw_bytes() <=
          mem.points_to@.dom()
            + segment_info_range(segment_id)
            + pages_range_total
}

impl Local {
    spec fn segment_page_range(&self, segment_id: SegmentId, page_id: PageId) -> Set<int> {
        if page_id.segment_id == segment_id && self.is_used_primary(page_id) {
            set_int_range(
                page_start(page_id) + start_offset(self.block_size(page_id)),
                page_start(page_id) + start_offset(self.block_size(page_id))
                    + self.page_capacity(page_id) * self.block_size(page_id)
            )
        } else {
            Set::empty()
        }
    }

    pub closed spec fn segment_pages_range_total(&self, segment_id: SegmentId) -> Set<int> {
        Set::<int>::new(|addr| exists |page_id|
            self.segment_page_range(segment_id, page_id).contains(addr)
        )
    }

    spec fn segment_page_used(&self, segment_id: SegmentId, page_id: PageId) -> Set<int> {
        if page_id.segment_id == segment_id && self.is_used_primary(page_id) {
            set_int_range(
                page_start(page_id),
                page_start(page_id) + self.page_count(page_id) * SLICE_SIZE
            )
        } else {
            Set::empty()
        }
    }

    pub closed spec fn segment_pages_used_total(&self, segment_id: SegmentId) -> Set<int> {
        Set::<int>::new(|addr| exists |page_id|
            self.segment_page_used(segment_id, page_id).contains(addr)
        )
    }

    /*spec fn segment_page_range_reserved(&self, segment_id: SegmentId, page_id: PageId) -> Set<int> {
        if page_id.segment_id == segment_id && self.is_used_primary(page_id) {
            set_int_range(
                page_start(page_id) + start_offset(self.block_size(page_id)),
                page_start(page_id) + start_offset(self.block_size(page_id))
                    + self.page_reserved(page_id) * self.block_size(page_id)
            )
        } else {
            Set::empty()
        }
    }

    spec fn segment_pages_range_reserved_total(&self, segment_id: SegmentId) -> Set<int> {
        Set::<int>::new(|addr| exists |page_id|
            self.segment_page_range_reserved(segment_id, page_id).contains(addr)
        )
    }*/

    pub open spec fn mem_chunk_good(&self, segment_id: SegmentId) -> bool {
        self.segments.dom().contains(segment_id)
        && mem_chunk_good1(
            self.segments[segment_id].mem,
            segment_id,
            self.commit_mask(segment_id).bytes(segment_id),
            self.decommit_mask(segment_id).bytes(segment_id),
            self.segment_pages_range_total(segment_id),
            self.segment_pages_used_total(segment_id),
        )
    }
}

pub proof fn range_total_le_used_total(local: Local, sid: SegmentId)
    requires
        local.wf_main(),
        local.segments.dom().contains(sid),
    ensures
        local.segment_pages_range_total(sid)
            <= local.segment_pages_used_total(sid)
{
    assert forall |addr| local.segment_pages_range_total(sid).contains(addr)
        implies local.segment_pages_used_total(sid).contains(addr)
    by {
        let pid = choose |pid: PageId|
            local.segment_page_range(sid, pid).contains(addr);
        let p_blocksize = local.block_size(pid);
        let p_capacity = local.page_capacity(pid);
        let p_reserved = local.page_reserved(pid);
        start_offset_le_slice_size(p_blocksize);
        assert(p_capacity * p_blocksize <= p_reserved * p_blocksize) by(nonlinear_arith)
            requires p_capacity <= p_reserved, p_blocksize >= 0;
        assert(local.segment_page_used(sid, pid).contains(addr));
    }
}

pub proof fn decommit_subset_of_pointsto(local: Local, sid: SegmentId)
    requires
        local.wf_main(),
        local.segments.dom().contains(sid),
        local.mem_chunk_good(sid),
    ensures
        local.decommit_mask(sid).bytes(sid) <= 
            local.segments[sid].mem.points_to@.dom()
{
    range_total_le_used_total(local, sid);
}

pub proof fn very_unready_range_okay_to_decommit(local: Local)
    requires
        local.wf_main(),
        local.page_organization.popped.is_VeryUnready(),
    ensures
        (match local.page_organization.popped {
            Popped::VeryUnready(segment_id, idx, count, _) => {
                set_int_range(
                    segment_start(segment_id) + idx * SLICE_SIZE,
                    segment_start(segment_id) + idx * SLICE_SIZE + count * SLICE_SIZE,
                ).disjoint(
                    segment_info_range(segment_id)
                        + local.segment_pages_used_total(segment_id)
                )
            }
            _ => false,
        }),
{
    match local.page_organization.popped {
        Popped::VeryUnready(segment_id, idx, count, _) => {
            const_facts();
            local.page_organization.get_count_bound_very_unready();
            assert(idx > 0);
            assert forall |addr| 
                local.segment_pages_used_total(segment_id).contains(addr)
                  && set_int_range(
                    segment_start(segment_id) + idx * SLICE_SIZE,
                    segment_start(segment_id) + idx * SLICE_SIZE + count * SLICE_SIZE,
                ).contains(addr)
                implies false
            by {
                let page_id = choose |page_id| 
                  local.segment_page_used(segment_id, page_id).contains(addr);
                local.page_organization.lemma_range_disjoint_very_unready(page_id);
                let p_count = local.page_count(page_id);
                assert(page_id.idx + p_count <= idx || idx + count <= page_id.idx);
            }
        }
        _ => { }
    }
}

pub proof fn preserves_mem_chunk_good(local1: Local, local2: Local)
    requires 
        //local2.page_organization == local1.page_organization,
        //local2.pages == local1.pages,
        //local2.commit_mask(sid).bytes(sid) == local1.commit_mask(sid).bytes(sid),
        //local2.segments[sid].mem.has_new_pointsto(&local1.segments[sid].mem),
        local1.segments.dom() == local2.segments.dom(),
        forall |sid| local1.segments.dom().contains(sid) ==>
            local2.commit_mask(sid).bytes(sid) == local1.commit_mask(sid).bytes(sid),
        forall |sid| local1.segments.dom().contains(sid) ==>
            local2.decommit_mask(sid).bytes(sid) == local1.decommit_mask(sid).bytes(sid),
        forall |sid| local1.segments.dom().contains(sid) ==>
            local2.segments[sid].mem == local1.segments[sid].mem,
        forall |page_id| local1.is_used_primary(page_id) ==>
              local2.is_used_primary(page_id)
              && local1.page_capacity(page_id) <= local2.page_capacity(page_id)
              && local1.page_reserved(page_id) <= local2.page_reserved(page_id)
              && local1.page_count(page_id) == local2.page_count(page_id)
              && local1.block_size(page_id) == local2.block_size(page_id),
        forall |page_id: PageId| #[trigger] local2.is_used_primary(page_id) ==>
              local1.is_used_primary(page_id),

    ensures forall |sid| #[trigger] local1.segments.dom().contains(sid) ==>
        local1.mem_chunk_good(sid) ==> local2.mem_chunk_good(sid),
{
    let sid1 = SegmentId { id: 0, uniq: 0 };
    let sid2 = SegmentId { id: 1, uniq: 0 };
    preserves_mem_chunk_good_except(local1, local2, sid1);
    preserves_mem_chunk_good_except(local1, local2, sid2);
}

pub proof fn preserves_mem_chunk_good_except(local1: Local, local2: Local, esegment_id: SegmentId)
    requires 
        //local2.page_organization == local1.page_organization,
        //local2.pages == local1.pages,
        //local2.commit_mask(sid).bytes(sid) == local1.commit_mask(sid).bytes(sid),
        //local2.segments[sid].mem.has_new_pointsto(&local1.segments[sid].mem),
        local1.segments.dom().subset_of(local2.segments.dom()),
        forall |sid| sid != esegment_id ==> #[trigger] local1.segments.dom().contains(sid) ==> local2.commit_mask(sid).bytes(sid) == local1.commit_mask(sid).bytes(sid),
        forall |sid| sid != esegment_id ==> #[trigger] local1.segments.dom().contains(sid) ==> local2.decommit_mask(sid).bytes(sid) == local1.decommit_mask(sid).bytes(sid),
        forall |sid| sid != esegment_id ==> #[trigger] local1.segments.dom().contains(sid) ==> local2.segments[sid].mem == local1.segments[sid].mem,
        forall |page_id: PageId| page_id.segment_id != esegment_id && #[trigger] local1.is_used_primary(page_id) ==>
              local2.is_used_primary(page_id)
              && local1.page_capacity(page_id) <= local2.page_capacity(page_id)
              && local1.page_reserved(page_id) <= local2.page_reserved(page_id)
              && local1.page_count(page_id) == local2.page_count(page_id)
              && local1.block_size(page_id) == local2.block_size(page_id),

        forall |page_id: PageId| page_id.segment_id != esegment_id && #[trigger] local2.is_used_primary(page_id) ==>
              local1.is_used_primary(page_id),

    ensures forall |sid| sid != esegment_id ==> #[trigger] local1.segments.dom().contains(sid) ==>
        local1.mem_chunk_good(sid) ==> local2.mem_chunk_good(sid),
{
    assert forall |sid| sid != esegment_id && #[trigger] local1.segments.dom().contains(sid) &&
        local1.mem_chunk_good(sid) implies local2.mem_chunk_good(sid)
    by {
        let mem = local2.segments[sid].mem;
        let commit_bytes = local2.commit_mask(sid).bytes(sid);
        let decommit_bytes = local2.decommit_mask(sid).bytes(sid);
        let pages_range_total1 = local1.segment_pages_range_total(sid);
        let pages_range_total2 = local2.segment_pages_range_total(sid);

        //let pages_range_reserved_total1 = local1.segment_pages_range_reserved_total(sid);
        //let pages_range_reserved_total2 = local2.segment_pages_range_reserved_total(sid);
        assert(mem.wf());
        assert(mem.os_exact_range(segment_start(sid), SEGMENT_SIZE as int));
        assert(commit_bytes.subset_of(mem.os_rw_bytes()));
        assert forall |addr| pages_range_total1.contains(addr) implies pages_range_total2.contains(addr)
        by {
            let page_id = choose |page_id|
                local1.segment_page_range(sid, page_id).contains(addr);
            assert(page_id.segment_id == sid);
            assert(local1.is_used_primary(page_id));
            assert(local2.is_used_primary(page_id));
            assert(
                local1.page_capacity(page_id) * local1.block_size(page_id)
                <= local2.page_capacity(page_id) * local2.block_size(page_id))
              by(nonlinear_arith)
              requires local1.page_capacity(page_id) <= local2.page_capacity(page_id),
                  local1.block_size(page_id) == local2.block_size(page_id);
            assert(local2.segment_page_range(sid, page_id).contains(addr));
        }
        assert(pages_range_total1.subset_of(pages_range_total2));
        assert(mem.os_rw_bytes().subset_of(
              mem.points_to@.dom()
                + segment_info_range(sid)
                + pages_range_total2
        ));
        //assert(pages_range_reserved_total2.subset_of(commit_bytes - decommit_bytes));

        preserves_segment_pages_used_total(local1, local2, sid);

        assert(mem_chunk_good1(
            local2.segments[sid].mem,
            sid,
            local2.commit_mask(sid).bytes(sid),
            local2.decommit_mask(sid).bytes(sid),
            local2.segment_pages_range_total(sid),
            local2.segment_pages_used_total(sid),
        ));
    }
}

pub proof fn empty_segment_pages_used_total(local1: Local, sid: SegmentId)
    requires
        forall |pid: PageId| pid.segment_id == sid ==> !local1.is_used_primary(pid),
    ensures
        local1.segment_pages_used_total(sid) =~= Set::empty(),
{
}

pub proof fn preserves_segment_pages_used_total(local1: Local, local2: Local, sid: SegmentId)
    requires 
        forall |page_id: PageId| page_id.segment_id == sid && #[trigger] local2.is_used_primary(page_id) ==>
              local1.is_used_primary(page_id)
              && local1.page_count(page_id) == local2.page_count(page_id),
    ensures local2.segment_pages_used_total(sid) <=
        local1.segment_pages_used_total(sid),
{
    assert forall |addr| local2.segment_pages_used_total(sid).contains(addr)
        implies local1.segment_pages_used_total(sid).contains(addr)
    by {
        let pid = choose |pid| local2.segment_page_used(sid, pid).contains(addr);
        assert(local1.segment_page_used(sid, pid).contains(addr));
    }
}

pub proof fn preserve_totals(local1: Local, local2: Local, sid: SegmentId)
    requires 
        forall |page_id: PageId| page_id.segment_id == sid && #[trigger] local2.is_used_primary(page_id) ==>
              local1.is_used_primary(page_id)
              && local1.page_count(page_id) == local2.page_count(page_id)
              && local1.page_capacity(page_id) == local2.page_capacity(page_id)
              && local1.block_size(page_id) == local2.block_size(page_id),
        forall |page_id: PageId| page_id.segment_id == sid && #[trigger] local1.is_used_primary(page_id) ==>
              local2.is_used_primary(page_id)
    ensures
        local2.segment_pages_used_total(sid) =~= local1.segment_pages_used_total(sid),
        local2.segment_pages_range_total(sid) =~= local1.segment_pages_range_total(sid),
{
    assert forall |addr| local2.segment_pages_used_total(sid).contains(addr)
        implies local1.segment_pages_used_total(sid).contains(addr)
    by {
        let pid = choose |pid| local2.segment_page_used(sid, pid).contains(addr);
        assert(local1.segment_page_used(sid, pid).contains(addr));
    }
    assert forall |addr| local1.segment_pages_used_total(sid).contains(addr)
        implies local2.segment_pages_used_total(sid).contains(addr)
    by {
        let pid = choose |pid| local1.segment_page_used(sid, pid).contains(addr);
        assert(local2.segment_page_used(sid, pid).contains(addr));
    }
    assert forall |addr| local2.segment_pages_range_total(sid).contains(addr)
        implies local1.segment_pages_range_total(sid).contains(addr)
    by {
        let pid = choose |pid| local2.segment_page_range(sid, pid).contains(addr);
        assert(local1.segment_page_range(sid, pid).contains(addr));
    }
    assert forall |addr| local1.segment_pages_range_total(sid).contains(addr)
        implies local2.segment_pages_range_total(sid).contains(addr)
    by {
        let pid = choose |pid| local1.segment_page_range(sid, pid).contains(addr);
        assert(local2.segment_page_range(sid, pid).contains(addr));
    }
}

pub proof fn preserves_mem_chunk_good_on_commit(local1: Local, local2: Local, sid: SegmentId)
    requires
        local1.segments.dom().contains(sid),
        local2.segments.dom().contains(sid),
        local1.mem_chunk_good(sid),
        local2.page_organization == local1.page_organization,
        local2.pages == local1.pages,
        local2.commit_mask(sid).bytes(sid) == local1.commit_mask(sid).bytes(sid),
        local2.decommit_mask(sid).bytes(sid) == local1.decommit_mask(sid).bytes(sid),
        local2.segments[sid].mem.wf(),
        local2.segments[sid].mem.has_new_pointsto(&local1.segments[sid].mem),
    ensures local2.mem_chunk_good(sid),
{
    preserves_mem_chunk_good_on_commit_with_mask_set(local1, local2, sid);
}

pub proof fn preserves_mem_chunk_good_on_decommit(local1: Local, local2: Local, sid: SegmentId)
    requires
        local1.segments.dom().contains(sid),
        local2.segments.dom().contains(sid),
        local1.mem_chunk_good(sid),
        local2.page_organization == local1.page_organization,
        local2.pages == local1.pages,
        local2.segments[sid].mem.wf(),

        local2.decommit_mask(sid).bytes(sid) <= local1.decommit_mask(sid).bytes(sid),
        local2.commit_mask(sid).bytes(sid) =~=
            local1.commit_mask(sid).bytes(sid) -
              (local1.decommit_mask(sid).bytes(sid) - local2.decommit_mask(sid).bytes(sid)),

        local2.segments[sid].mem.os_rw_bytes() <= local1.segments[sid].mem.os_rw_bytes(),
        local2.segments[sid].mem.points_to@.dom() =~=
            local1.segments[sid].mem.points_to@.dom() -
              (local1.segments[sid].mem.os_rw_bytes() - local2.segments[sid].mem.os_rw_bytes()),

        (local1.segments[sid].mem.os_rw_bytes() - local2.segments[sid].mem.os_rw_bytes())
          <= (local1.decommit_mask(sid).bytes(sid) - local2.decommit_mask(sid).bytes(sid)),

              //(local1.decommit_mask(sid).bytes(sid) - local2.decommit_mask(sid).bytes(sid)),

        local2.segments[sid].mem.os.dom() =~= local1.segments[sid].mem.os.dom(),
    ensures local2.mem_chunk_good(sid),
{
    preserve_totals(local1, local2, sid);
    assert(mem_chunk_good1(
            local2.segments[sid].mem,
            sid,
            local2.commit_mask(sid).bytes(sid),
            local2.decommit_mask(sid).bytes(sid),
            local2.segment_pages_range_total(sid),
            local2.segment_pages_used_total(sid),
        ));
}

pub proof fn preserves_mem_chunk_good_on_commit_with_mask_set(local1: Local, local2: Local, sid: SegmentId)
    requires
        local1.segments.dom().contains(sid),
        local2.segments.dom().contains(sid),
        local1.mem_chunk_good(sid),
        local2.page_organization == local1.page_organization,
        local2.pages == local1.pages,
        local2.segments[sid].mem.wf(),
        local2.segments[sid].mem.has_new_pointsto(&local1.segments[sid].mem),

        local2.decommit_mask(sid).bytes(sid).subset_of( local1.decommit_mask(sid).bytes(sid) ),
        local1.commit_mask(sid).bytes(sid).subset_of( local2.commit_mask(sid).bytes(sid) ),

        local2.decommit_mask(sid).bytes(sid).disjoint(
            local2.commit_mask(sid).bytes(sid) - local1.commit_mask(sid).bytes(sid)),

        (local1.segments[sid].mem.os_rw_bytes() + (
            local2.commit_mask(sid).bytes(sid) - local1.commit_mask(sid).bytes(sid)))
          .subset_of(local2.segments[sid].mem.os_rw_bytes())
    ensures local2.mem_chunk_good(sid),
{
    let old_mem = local1.segments[sid].mem;
    let mem = local2.segments[sid].mem;
    let commit_bytes = local2.commit_mask(sid).bytes(sid);
    let decommit_bytes = local2.decommit_mask(sid).bytes(sid);
    let pages_range_total1 = local1.segment_pages_range_total(sid);
    let pages_range_total2 = local2.segment_pages_range_total(sid);
    assert(mem.wf());
    assert(mem.os_exact_range(segment_start(sid), SEGMENT_SIZE as int));
    assert(commit_bytes.subset_of(mem.os_rw_bytes()));
    assert forall |addr| pages_range_total1.contains(addr) implies pages_range_total2.contains(addr)
    by {
        let page_id = choose |page_id|
            local1.segment_page_range(sid, page_id).contains(addr);
        assert(page_id.segment_id == sid);
        assert(local1.is_used_primary(page_id));
        assert(local2.is_used_primary(page_id));
        assert(local2.segment_page_range(sid, page_id).contains(addr));
    }
    assert(pages_range_total1.subset_of(pages_range_total2));
    assert((mem.os_rw_bytes() - old_mem.os_rw_bytes()).subset_of(mem.points_to@.dom()));
    assert(mem.os_rw_bytes().subset_of(
          mem.points_to@.dom()
            + segment_info_range(sid)
            + pages_range_total2
    ));
    assert(decommit_bytes.subset_of(commit_bytes));
    preserves_segment_pages_used_total(local1, local2, sid);
}

pub proof fn preserves_mem_chunk_good_on_transfer_to_capacity(local1: Local, local2: Local, page_id: PageId)
    requires
        local1.segments.dom().contains(page_id.segment_id),
        local2.segments.dom().contains(page_id.segment_id),
        local1.mem_chunk_good(page_id.segment_id),
        local2.page_organization == local1.page_organization,
        local1.pages.dom().contains(page_id),
        local2.pages.dom().contains(page_id),
        local2.commit_mask(page_id.segment_id).bytes(page_id.segment_id) == local1.commit_mask(page_id.segment_id).bytes(page_id.segment_id),
        local2.decommit_mask(page_id.segment_id).bytes(page_id.segment_id) == local1.decommit_mask(page_id.segment_id).bytes(page_id.segment_id),
        local2.segments[page_id.segment_id].mem.wf(),

        local1.is_used_primary(page_id),
        forall |page_id| #[trigger] local1.is_used_primary(page_id) ==>
              local2.is_used_primary(page_id)
              && local1.page_capacity(page_id) <= local2.page_capacity(page_id)
              && local1.block_size(page_id) == local2.block_size(page_id)
              && local1.page_count(page_id) == local2.page_count(page_id),

        forall |page_id| local2.is_used_primary(page_id) ==>
              local1.is_used_primary(page_id),

        local2.segments[page_id.segment_id].mem.os
          == local1.segments[page_id.segment_id].mem.os,
        ({ let sr = set_int_range(
                page_start(page_id)
                    + start_offset(local1.block_size(page_id))
                    + local1.page_capacity(page_id) * local1.block_size(page_id),
                page_start(page_id)
                    + start_offset(local1.block_size(page_id))
                    + local2.page_capacity(page_id) * local1.block_size(page_id),
            );
          local2.segments[page_id.segment_id].mem.points_to@.dom() =~=
              local1.segments[page_id.segment_id].mem.points_to@.dom() - sr
          //&& local2.decommit_mask(page_id.segment_id).bytes(page_id.segment_id).disjoint(sr)
        }),
    ensures local2.mem_chunk_good(page_id.segment_id),
{
    let sid = page_id.segment_id;
    let rng = set_int_range(
                page_start(page_id)
                    + start_offset(local1.block_size(page_id))
                    + local1.page_capacity(page_id) * local1.block_size(page_id),
                page_start(page_id)
                    + start_offset(local1.block_size(page_id))
                    + local2.page_capacity(page_id) * local1.block_size(page_id),
            );

    let r1 = local1.page_capacity(page_id);
    let r2 = local2.page_capacity(page_id);
    let bs = local1.block_size(page_id);
    assert(r1 * bs <= r2 * bs) by(nonlinear_arith)
        requires r1 <= r2 && bs >= 0;

    let old_mem = local1.segments[sid].mem;
    let mem = local2.segments[sid].mem;
    let commit_bytes = local2.commit_mask(sid).bytes(sid);
    let old_decommit_bytes = local1.decommit_mask(sid).bytes(sid);
    let decommit_bytes = local2.decommit_mask(sid).bytes(sid);
    let pages_range_total1 = local1.segment_pages_range_total(sid);
    let pages_range_total2 = local2.segment_pages_range_total(sid);
    assert(mem.wf());
    assert(mem.os_exact_range(segment_start(sid), SEGMENT_SIZE as int));
    assert(commit_bytes.subset_of(mem.os_rw_bytes()));

    assert forall |addr| pages_range_total1.contains(addr) || rng.contains(addr) implies pages_range_total2.contains(addr)
    by {
        if pages_range_total1.contains(addr) {
            let page_id = choose |page_id|
                local1.segment_page_range(sid, page_id).contains(addr);
            assert(page_id.segment_id == sid);
            assert(local1.is_used_primary(page_id));
            assert(local2.is_used_primary(page_id));
            assert(
                local1.page_capacity(page_id) * local1.block_size(page_id)
                <= local2.page_capacity(page_id) * local2.block_size(page_id))
              by(nonlinear_arith)
              requires local1.page_capacity(page_id) <= local2.page_capacity(page_id),
                  local1.block_size(page_id) == local2.block_size(page_id);
            assert(local2.segment_page_range(sid, page_id).contains(addr));
        } else {
            assert(r1 * bs >= 0) by(nonlinear_arith) requires r1 >= 0, bs >= 0;
            assert(local2.segment_page_range(sid, page_id).contains(addr));
        }
    }

    //assert(pages_range_total1.subset_of(pages_range_total2));
    //assert((mem.os_rw_bytes() - old_mem.os_rw_bytes()).subset_of(mem.points_to@.dom()));

    preserves_segment_pages_used_total(local1, local2, page_id.segment_id);

    assert(mem.os_rw_bytes().subset_of(
          mem.points_to@.dom()
            + segment_info_range(sid)
            + pages_range_total2
    ));

    //assert(old_decommit_bytes.subset_of(old_mem.points_to@.dom()));
    //assert(decommit_bytes.subset_of(old_mem.points_to@.dom()));
    //assert(decommit_bytes.subset_of(mem.points_to@.dom()));
    //assert(decommit_bytes.subset_of(commit_bytes));

}

pub proof fn preserves_mem_chunk_good_on_transfer_back(local1: Local, local2: Local, page_id: PageId)
    requires
        local1.segments.dom().contains(page_id.segment_id),
        local2.segments.dom().contains(page_id.segment_id),
        local1.mem_chunk_good(page_id.segment_id),

        local1.pages.dom().contains(page_id),
        local2.pages.dom().contains(page_id),
        local2.commit_mask(page_id.segment_id).bytes(page_id.segment_id) == local1.commit_mask(page_id.segment_id).bytes(page_id.segment_id),
        local2.decommit_mask(page_id.segment_id).bytes(page_id.segment_id) == local1.decommit_mask(page_id.segment_id).bytes(page_id.segment_id),
        local2.segments[page_id.segment_id].mem.wf(),

        local1.is_used_primary(page_id),
        forall |pid| #[trigger] local1.is_used_primary(pid) && pid != page_id ==>
              local2.is_used_primary(pid)
              && local1.page_capacity(pid) <= local2.page_capacity(pid)
              && local1.block_size(pid) == local2.block_size(pid)
              && local1.page_count(pid) == local2.page_count(pid),

        forall |pid| #[trigger] local2.is_used_primary(pid) ==>
              local1.is_used_primary(pid),
        !local2.is_used_primary(page_id),

        local2.segments[page_id.segment_id].mem.os
          == local1.segments[page_id.segment_id].mem.os,
        local2.segments[page_id.segment_id].mem.points_to@.dom() =~=
            local1.segments[page_id.segment_id].mem.points_to@.dom() +
            set_int_range(
                page_start(page_id)
                    + start_offset(local1.block_size(page_id)),
                page_start(page_id)
                    + start_offset(local1.block_size(page_id))
                    + local1.page_capacity(page_id) * local1.block_size(page_id),
            )
    ensures local2.mem_chunk_good(page_id.segment_id),
{
    let sid = page_id.segment_id;
    let rng = set_int_range(
                page_start(page_id)
                    + start_offset(local1.block_size(page_id)),
                page_start(page_id)
                    + start_offset(local1.block_size(page_id))
                    + local1.page_capacity(page_id) * local1.block_size(page_id),
            );

    let old_mem = local1.segments[sid].mem;
    let mem = local2.segments[sid].mem;
    let commit_bytes = local2.commit_mask(sid).bytes(sid);
    let pages_range_total1 = local1.segment_pages_range_total(sid);
    let pages_range_total2 = local2.segment_pages_range_total(sid);
    assert(mem.wf());
    assert(mem.os_exact_range(segment_start(sid), SEGMENT_SIZE as int));
    assert(commit_bytes.subset_of(mem.os_rw_bytes()));

    assert forall |addr| pages_range_total1.contains(addr)
        && !pages_range_total2.contains(addr)
        implies #[trigger] rng.contains(addr)
    by {
        let pid = choose |pid| local1.segment_page_range(sid, pid).contains(addr);
        if pid == page_id {
            assert(mem.points_to@.dom().contains(addr));
        } else {
            assert(pid.segment_id == sid);
            assert(local1.is_used_primary(pid));
            assert(local2.is_used_primary(pid));
            assert(
                local1.page_capacity(pid) * local1.block_size(pid)
                <= local2.page_capacity(pid) * local2.block_size(pid))
              by(nonlinear_arith)
              requires local1.page_capacity(pid) <= local2.page_capacity(pid),
                  local1.block_size(pid) == local2.block_size(pid);
            assert(local2.segment_page_range(sid, pid).contains(addr));

            assert(false);
        }
    }

    assert((pages_range_total1 - pages_range_total2).subset_of(rng));
    assert((pages_range_total1 - pages_range_total2).subset_of(mem.points_to@.dom()));

    assert(mem.os_rw_bytes().subset_of(
          mem.points_to@.dom()
            + segment_info_range(sid)
            + pages_range_total2
    ));

    preserves_segment_pages_used_total(local1, local2, page_id.segment_id);
}

pub proof fn preserves_mem_chunk_on_set_used(local1: Local, local2: Local, page_id: PageId)
    requires 
        local1.mem_chunk_good(page_id.segment_id),
        //local2.page_organization == local1.page_organization,
        //local2.pages == local1.pages,
        //local2.commit_mask(sid).bytes(sid) == local1.commit_mask(sid).bytes(sid),
        //local2.segments[sid].mem.has_new_pointsto(&local1.segments[sid].mem),
        local1.segments.dom() == local2.segments.dom(),
        forall |sid| local1.segments.dom().contains(sid) ==>
            local2.commit_mask(sid).bytes(sid) == local1.commit_mask(sid).bytes(sid),
        forall |sid| local1.segments.dom().contains(sid) ==>
            local2.decommit_mask(sid).bytes(sid) == local1.decommit_mask(sid).bytes(sid),
        forall |sid| local1.segments.dom().contains(sid) ==>
            local2.segments[sid].mem == local1.segments[sid].mem,
        forall |pid| local1.is_used_primary(pid) ==>
              local2.is_used_primary(pid)
              && local1.page_capacity(pid) <= local2.page_capacity(pid)
              && local1.page_reserved(pid) <= local2.page_reserved(pid)
              && local1.page_count(pid) == local2.page_count(pid)
              && local1.block_size(pid) == local2.block_size(pid),
        forall |pid: PageId| #[trigger] local2.is_used_primary(pid) && page_id != pid ==>
              local1.is_used_primary(pid),
        page_init_is_committed(page_id, local2),
    ensures local2.mem_chunk_good(page_id.segment_id),
{
    let sid = page_id.segment_id;

    let mem = local2.segments[sid].mem;
    let commit_bytes = local2.commit_mask(sid).bytes(sid);
    let decommit_bytes = local2.decommit_mask(sid).bytes(sid);
    let pages_range_total1 = local1.segment_pages_range_total(sid);
    let pages_range_total2 = local2.segment_pages_range_total(sid);

    //let pages_range_reserved_total1 = local1.segment_pages_range_reserved_total(sid);
    //let pages_range_reserved_total2 = local2.segment_pages_range_reserved_total(sid);
    assert(mem.wf());
    assert(mem.os_exact_range(segment_start(sid), SEGMENT_SIZE as int));
    assert(commit_bytes.subset_of(mem.os_rw_bytes()));
    assert forall |addr| pages_range_total1.contains(addr) implies pages_range_total2.contains(addr)
    by {
        let page_id = choose |page_id|
            local1.segment_page_range(sid, page_id).contains(addr);
        assert(page_id.segment_id == sid);
        assert(local1.is_used_primary(page_id));
        assert(local2.is_used_primary(page_id));
        assert(
            local1.page_capacity(page_id) * local1.block_size(page_id)
            <= local2.page_capacity(page_id) * local2.block_size(page_id))
          by(nonlinear_arith)
          requires local1.page_capacity(page_id) <= local2.page_capacity(page_id),
              local1.block_size(page_id) == local2.block_size(page_id);
        assert(local2.segment_page_range(sid, page_id).contains(addr));
    }
    assert(pages_range_total1.subset_of(pages_range_total2));
    assert(mem.os_rw_bytes().subset_of(
          mem.points_to@.dom()
            + segment_info_range(sid)
            + pages_range_total2
    ));
    //assert(pages_range_reserved_total2.subset_of(commit_bytes - decommit_bytes));

    assert forall |addr| local2.segment_pages_used_total(sid).contains(addr)
        implies commit_bytes.contains(addr) && !decommit_bytes.contains(addr)
    by {
        const_facts();
        let pid = choose |pid| local2.segment_page_used(sid, pid).contains(addr);
        assert(local2.segment_page_used(sid, pid).contains(addr));
        if pid == page_id {
            /*if page_id.segment_id == sid && local2.is_used_primary(page_id) {
                let start = page_start(page_id);
                let len = page_start(page_id) + local2.page_count(page_id) * SLICE_SIZE;
                assert(set_int_range(start, start + len).contains(addr));
                assert(commit_bytes.contains(addr) && !decommit_bytes.contains(addr));
            } else {
                assert(false);
            }*/
        } else {
            assert(local1.segment_page_used(sid, pid).contains(addr));
            assert(local1.segment_pages_used_total(sid).contains(addr));
            assert(commit_bytes.contains(addr) && !decommit_bytes.contains(addr));
        }
    }

    assert(mem_chunk_good1(
        local2.segments[sid].mem,
        sid,
        local2.commit_mask(sid).bytes(sid),
        local2.decommit_mask(sid).bytes(sid),
        local2.segment_pages_range_total(sid),
        local2.segment_pages_used_total(sid),
    ));
}

pub proof fn segment_mem_has_reserved_range(local: Local, page_id: PageId, new_cap: int)
    requires
        local.wf_main(),
        local.is_used_primary(page_id),
        local.page_capacity(page_id) <= new_cap <= local.page_reserved(page_id),
    ensures ({ let blocksize = local.block_size(page_id);
        local.segments[page_id.segment_id].mem.pointsto_has_range(
            block_start_at(page_id, blocksize, local.page_capacity(page_id)),
            (new_cap - local.page_capacity(page_id)) * blocksize)
    })
{
    let blocksize = local.block_size(page_id);
    let capacity = local.page_capacity(page_id);
    let reserved = local.page_reserved(page_id);
    let r1 = block_start_at(page_id, blocksize, local.page_capacity(page_id));
    let size = (new_cap - local.page_capacity(page_id)) * blocksize;
    let range = set_int_range(r1, r1 + size);
    let segment_id = page_id.segment_id;
    let mem = local.segments[segment_id].mem;
    let commit_bytes = local.commit_mask(segment_id).bytes(segment_id);

    block_start_at_diff(page_id, blocksize as nat, capacity as nat, new_cap as nat);

    let res_range = set_int_range(
        block_start_at(page_id, blocksize, 0),
        block_start_at(page_id, blocksize, reserved));

    assert(capacity * blocksize >= 0);
    start_offset_le_slice_size(blocksize);

    const_facts();
    local.page_organization.used_offset0_has_count(page_id);
    local.page_organization.get_count_bound(page_id);
    assert(page_id.idx != 0);
    assert(new_cap * blocksize <= reserved * blocksize) by(nonlinear_arith)
        requires new_cap <= reserved, blocksize >= 0;

    assert(range <= res_range);
    let pages_used_total = local.segment_pages_used_total(segment_id);
    assert forall |addr| res_range.contains(addr) implies commit_bytes.contains(addr)
    by {
        start_offset_le_slice_size(blocksize);
        assert(local.segment_page_used(segment_id, page_id).contains(addr));
        assert(pages_used_total.contains(addr));
    } 
    assert(res_range <= commit_bytes);

    assert(range.subset_of(mem.os_rw_bytes()));
    assert(range.disjoint(segment_info_range(segment_id) ));

    assert forall |addr, pid| 
        local.segment_page_range(segment_id, pid).contains(addr)
          implies !range.contains(addr)
    by {
        if pid == page_id {
            assert(!range.contains(addr));
        } else if pid.segment_id == page_id.segment_id && local.is_used_primary(page_id) {
            let p_blocksize = local.block_size(pid);
            let p_capacity = local.page_capacity(pid);
            let p_reserved = local.page_reserved(pid);
            start_offset_le_slice_size(p_blocksize);
            assert(p_capacity * p_blocksize <= p_reserved * p_blocksize) by(nonlinear_arith)
                requires p_capacity <= p_reserved, p_blocksize >= 0;

            let my_count = local.pages[page_id].count@.value.unwrap() as int;
            let p_count = local.pages[pid].count@.value.unwrap() as int;

            local.page_organization.lemma_range_disjoint_used2(page_id, pid);
            assert(page_id.idx + my_count <= pid.idx
              || pid.idx + p_count <= page_id.idx);

            assert(!range.contains(addr));
        } else {
            assert(!range.contains(addr));
        }
    }
    assert(range.disjoint(local.segment_pages_range_total(segment_id)));

    assert(range.subset_of(mem.points_to@.dom()));
}

///////

pub open spec fn page_init_is_committed(page_id: PageId, local: Local) -> bool {
    let count = local.page_organization.pages[page_id].count.unwrap() as int;
    let start = page_start(page_id);
    let len = count * SLICE_SIZE;
    let cm = local.segments[page_id.segment_id].main@.value.unwrap().commit_mask@;

    set_int_range(start, start + len) <=
        local.commit_mask(page_id.segment_id).bytes(page_id.segment_id)
        - local.decommit_mask(page_id.segment_id).bytes(page_id.segment_id)
    && count == local.page_count(page_id)
}

}
