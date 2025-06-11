#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::*;
use state_machines_macros::*;

use crate::tokens::{PageId, SegmentId, TldId};
use crate::config::*;
use crate::bin_sizes::{valid_sbin_idx, smallest_sbin_fitting_size, smallest_bin_fitting_size, valid_bin_idx, size_of_bin};

verus!{

pub ghost struct DlistHeader {
    pub first: Option<PageId>,
    pub last: Option<PageId>,
}

pub ghost struct DlistEntry {
    pub prev: Option<PageId>,
    pub next: Option<PageId>,
}

#[is_variant]
pub ghost enum PageHeaderKind {
    Normal(int, int),
}

pub ghost struct PageData {
    // Option means unspecified (i.e., does not constrain the physical value)
    pub dlist_entry: Option<DlistEntry>,
    pub count: Option<nat>,
    pub offset: Option<nat>,

    pub is_used: bool,
    pub full: Option<bool>,
    pub page_header_kind: Option<PageHeaderKind>,
}

pub ghost struct SegmentData {
    pub used: int,
}

#[is_variant]
pub ghost enum Popped {
    No,
    Ready(PageId, bool),            // set up the offsets   (all pages have offsets set)
    Used(PageId, bool),             // everything is set to 'used'

    SegmentCreating(SegmentId),     // just created
    VeryUnready(SegmentId, int, int, bool),      // no pages are set, not even first or last

    SegmentFreeing(SegmentId, int),

    ExtraCount(SegmentId),
}

pub open spec fn pages_with_segment(segment_id: SegmentId, lo: int, hi: int, data_fn: spec_fn(PageId) -> PageData) -> Map<PageId, PageData>
{
    Map::new(
        Set::int_range(lo, hi)
            .map(|idx: int| PageId{ segment_id, idx: idx as nat }),
        data_fn)
}

pub broadcast proof fn pages_with_segment_ensures(segment_id: SegmentId, lo: int, hi: int, data_fn: spec_fn(PageId) -> PageData)
requires 0<=lo<=hi,
ensures (#[trigger] pages_with_segment(segment_id, lo, hi, data_fn)) .congruent(
    IMap::new(
        |page_id: PageId| page_id.segment_id == segment_id
            && lo <= page_id.idx < hi, data_fn)),
{
    let ir = Set::int_range(lo, hi);
    let im = IMap::new(|page_id: PageId| page_id.segment_id == segment_id && lo <= page_id.idx < hi, data_fn);
    assert forall |k| #![auto] im.dom().contains(k)
        implies pages_with_segment(segment_id, lo, hi, data_fn).dom().contains(k) by {
        assert( ir.contains(k.idx as int) );    // witness to map exists
    }
}

pub open spec fn keys_with_segment(segment_id: SegmentId, lo: int, hi: int) -> Set<PageId>
{
    Set::int_range(lo, hi)
        .map(|idx: int| PageId{ segment_id, idx: idx as nat })
}

broadcast proof fn keys_with_segment_ensures(segment_id: SegmentId, lo: int, hi: int)
requires 0<=lo<=hi,
ensures (#[trigger] keys_with_segment(segment_id, lo, hi)).congruent(
    ISet::new(|page_id: PageId| page_id.segment_id == segment_id && lo <= page_id.idx < hi)),
{
    let ir = Set::int_range(lo, hi);
    let iset = ISet::new(|page_id: PageId| page_id.segment_id == segment_id && lo <= page_id.idx < hi);
    let fset = keys_with_segment(segment_id, lo, hi);
    assert forall |k| #![auto] iset.contains(k) implies fset.contains(k) by {
        assert( ir.contains(k.idx as int) );    // witness to map exists
    }
}

state_machine!{ PageOrg {
    fields {
        // Roughly corresponds to physical state
        pub unused_dlist_headers: Seq<DlistHeader>,     // indices are sbin
        pub used_dlist_headers: Seq<DlistHeader>,       // indices are bin
        pub pages: Map<PageId, PageData>,
        pub segments: Map<SegmentId, SegmentData>,

        // Actor state
        pub popped: Popped,

        // Internals
        pub unused_lists: Seq<Seq<PageId>>,
        pub used_lists: Seq<Seq<PageId>>,
    }

    #[invariant]
    pub open spec fn public_invariant(&self) -> bool {
        &&& self.unused_dlist_headers.len() == SEGMENT_BIN_MAX + 1
        &&& self.used_dlist_headers.len() == BIN_FULL + 1
        &&& (forall |page_id| #[trigger] self.pages.dom().contains(page_id) ==>
              self.segments.dom().contains(page_id.segment_id))
    }

    #[invariant]
    pub closed spec fn ll_basics(&self) -> bool {
        &&& self.unused_lists.len() == SEGMENT_BIN_MAX + 1
        &&& self.used_lists.len() == BIN_FULL + 1
    }

    #[invariant]
    pub closed spec fn page_id_domain(&self) -> bool {
        forall |pid| #[trigger] self.pages.dom().contains(pid) <==> (
            self.segments.dom().contains(pid.segment_id)
              && 0 <= pid.idx <= SLICES_PER_SEGMENT
        )
    }

    #[invariant]
    pub closed spec fn count_off0(&self) -> bool {
        forall |pid: PageId|
            #[trigger] self.pages.dom().contains(pid) ==>
            (self.pages[pid].count.is_some() <==> self.pages[pid].offset == Some(0nat))
    }

    #[invariant]
    pub closed spec fn end_is_unused(&self) -> bool {
        forall |pid: PageId| #![auto]
            self.pages.dom().contains(pid) && pid.idx == SLICES_PER_SEGMENT ==>
              !self.pages[pid].is_used
              && self.pages[pid].offset.is_none()
    }

    #[invariant]
    pub closed spec fn count_is_right(&self) -> bool {
        forall |sid| #[trigger] self.segments.dom().contains(sid) ==>
            self.segments[sid].used == self.ucount(sid) + self.popped_ec(sid)
    }

    #[invariant]
    pub closed spec fn popped_basics(&self) -> bool {
        match self.popped {
            Popped::No => true,
            Popped::Ready(page_id, _) => {
                self.pages.dom().contains(page_id)
                  && self.pages[page_id].is_used == false
                  && is_unused_header(self.pages[page_id])
                  && page_id.idx != 0
                  && self.pages[page_id].count.is_some()
                  && page_id.idx + self.pages[page_id].count.unwrap() <= SLICES_PER_SEGMENT
                  && !is_in_lls(page_id, self.unused_lists)
            }
            Popped::Used(page_id, _) => {
                self.pages.dom().contains(page_id)
                  && self.pages[page_id].is_used == true
                  && is_used_header(self.pages[page_id])
                  && page_id.idx != 0
                  && self.pages[page_id].count.is_some()
                  && page_id.idx + self.pages[page_id].count.unwrap() <= SLICES_PER_SEGMENT
            }
            Popped::SegmentCreating(segment_id) => {
                self.segments.dom().contains(segment_id)
            }
            Popped::SegmentFreeing(segment_id, idx) => {
                self.segments.dom().contains(segment_id)
                    && 0 < idx <= SLICES_PER_SEGMENT
                    && self.seg_free_prefix(segment_id, idx)
                    && self.segments[segment_id].used == 0
                    && (forall |page_id: PageId| page_id.segment_id == segment_id &&
                        0 <= page_id.idx < idx &&
                        #[trigger] self.pages.dom().contains(page_id) ==>
                            self.pages[page_id].is_used == false)
            }
            Popped::VeryUnready(segment_id, start, count, _) => {
                let page_id = PageId { segment_id, idx: start as nat };
                self.pages.dom().contains(page_id)
                  && self.pages[page_id].is_used == false
                  && self.good_range_very_unready(PageId { segment_id, idx: start as nat })

                  && self.segments.dom().contains(segment_id)
                  && 1 <= start < start + count <= SLICES_PER_SEGMENT
            }
            Popped::ExtraCount(segment_id) => {
                self.segments.dom().contains(segment_id)
            }
        }
    }

    #[invariant]
    pub closed spec fn data_for_used_header(&self) -> bool {
        forall |page_id: PageId| #[trigger] self.pages.dom().contains(page_id)
            ==> is_used_header(self.pages[page_id])
            ==> self.pages[page_id].count.is_some()
                && self.pages[page_id].count.unwrap() > 0
                && self.pages[page_id].offset == Some(0nat)
    }

    #[invariant]
    pub closed spec fn inv_segment_creating(&self) -> bool {
        match self.popped {
            Popped::SegmentCreating(segment_id) => {
                forall |pid: PageId|
                  pid.segment_id == segment_id
                    && self.pages.dom().contains(pid) ==>
                        !(#[trigger] self.pages[pid]).is_used
                        && self.pages[pid].offset.is_none()
                        && self.pages[pid].count.is_none()
                        && self.pages[pid].page_header_kind.is_none()
                        && self.pages[pid].dlist_entry.is_none()
                        && self.pages[pid].full.is_none()
            }
            _ => true,
        }
    }

    #[invariant]
    pub closed spec fn inv_very_unready(&self) -> bool {
        match self.popped {
            Popped::VeryUnready(segment_id, start, count, _) => {
                forall |pid: PageId|
                  pid.segment_id == segment_id
                    && start <= pid.idx < start + count ==>
                        !(#[trigger] self.pages[pid]).is_used
                        && self.pages[pid].offset.is_none()
                        && self.pages[pid].count.is_none()
                        && self.pages[pid].page_header_kind.is_none()
                        && self.pages[pid].dlist_entry.is_none()
                        && self.pages[pid].full.is_none()
            }
            _ => true,
        }
    }

    #[invariant]
    pub closed spec fn inv_ready(&self) -> bool {
        match self.popped {
            Popped::Ready(page_id, _) => {
                forall |pid: PageId|
                    pid.segment_id == page_id.segment_id
                      && page_id.idx <= pid.idx < page_id.idx + self.pages[page_id].count.unwrap()
                    ==>
                        self.pages.dom().contains(pid) ==>
                        !(#[trigger] self.pages[pid]).is_used
                        && self.pages[pid].offset == Some((pid.idx - page_id.idx) as nat)
                        && (self.pages[pid].count.is_some() <==> pid == page_id)
                        && self.pages[pid].page_header_kind.is_none()
                        && self.pages[pid].dlist_entry.is_none()
                        && self.pages[pid].full.is_none()
            }
            _ => true,
        }
    }

    #[invariant]
    pub closed spec fn inv_used(&self) -> bool {
        match self.popped {
            Popped::Used(page_id, _) => {
                forall |pid: PageId|
                    #![trigger self.pages.index(pid)]
                    #![trigger self.pages.dom().contains(pid)]
                    pid.segment_id == page_id.segment_id
                      && page_id.idx <= pid.idx < page_id.idx + self.pages[page_id].count.unwrap()
                    ==>
                        self.pages.dom().contains(pid)
                        && self.pages[pid].is_used
                        && self.pages[pid].offset == Some((pid.idx - page_id.idx) as nat)
                        && (self.pages[pid].count.is_some() <==> pid == page_id)
                        && (self.pages[pid].page_header_kind.is_some() <==> pid == page_id)
                        && self.pages[pid].dlist_entry.is_none()
                        && self.pages[pid].full.is_none()
            }
            _ => true,
        }
    }

    #[invariant]
    pub closed spec fn data_for_unused_header(&self) -> bool {
        forall |page_id: PageId| #[trigger] self.pages.dom().contains(page_id)
            ==> is_unused_header(self.pages[page_id])
            ==> self.pages[page_id].count.is_some()
                && self.pages[page_id].count.unwrap() > 0
                && self.pages[page_id].offset == Some(0nat)
    }

    #[invariant]
    pub closed spec fn ll_inv_valid_unused(&self) -> bool {
        forall |i| #![auto] 0 <= i < self.unused_lists.len() ==> valid_ll(self.pages, self.unused_dlist_headers[i], self.unused_lists[i])
        /*
          0 <= i < self.unused_lists.len() ==>
            forall |j| #![triggers self.unused_lists.index(i).index(j)]
              0 <= j < self.unused_lists[i].len() ==>
                self.pages.dom().contains(self.unused_lists[i][j])
                  && is_unused_header(self.pages[self.unused_lists[i][j]])
                  && self.pages[self.unused_lists[i][j]].dlist_entry.is_some()
                  && self.pages[self.unused_lists[i][j]].dlist_entry.unwrap().prev
                        == get_prev(self.unused_lists[i], j)
                  && self.pages[self.unused_lists[i][j]].dlist_entry.unwrap().next
                        == get_next(self.unused_lists[i], j)*/
    }


    #[invariant]
    pub closed spec fn ll_inv_valid_used(&self) -> bool {
        forall |i| #![auto] 0 <= i < self.used_lists.len() ==> valid_ll(self.pages, self.used_dlist_headers[i], self.used_lists[i])
        /*
        forall |i| #![triggers self.used_lists.index(i)]
          0 <= i < self.used_lists.len() ==>
            forall |j| #![triggers self.used_lists.index(i).index(j)]
              0 <= j < self.used_lists[i].len() ==>
                self.pages.dom().contains(self.used_lists[i][j])
                  && is_used_header(self.pages[self.used_lists[i][j]])
                  && self.pages[self.used_lists[i][j]].dlist_entry.is_some()
                  && self.pages[self.used_lists[i][j]].dlist_entry.unwrap().prev
                        == get_prev(self.used_lists[i], j)
                  && self.pages[self.used_lists[i][j]].dlist_entry.unwrap().next
                        == get_next(self.used_lists[i], j)*/
    }

    #[invariant]
    pub closed spec fn ll_inv_valid_unused2(&self) -> bool {
        forall |i| #![trigger self.unused_lists.index(i)] 0 <= i < self.unused_lists.len() ==>
          forall |j| #![trigger self.unused_lists.index(i).index(j)] 0 <= j < self.unused_lists[i].len() ==>
              self.pages.dom().contains(#[trigger] self.unused_lists[i][j])
              && is_unused_header(self.pages[self.unused_lists[i][j]])
              && self.unused_lists[i][j].idx != 0
              && self.pages[self.unused_lists[i][j]].count.is_some()
              && i == smallest_sbin_fitting_size(
                  self.pages[self.unused_lists[i][j]].count.unwrap() as int)
    }

    #[invariant]
    pub closed spec fn ll_inv_valid_used2(&self) -> bool {
        forall |i| #![trigger self.used_lists.index(i)] 0 <= i < self.used_lists.len() ==>
          forall |j| #![trigger self.used_lists.index(i).index(j)] 0 <= j < self.used_lists[i].len() ==>
              self.pages.dom().contains(#[trigger] self.used_lists[i][j])
              && is_used_header(self.pages[self.used_lists[i][j]])
              && self.used_lists[i][j].idx != 0
              && self.pages[self.used_lists[i][j]].full.is_some()
              && (self.pages[self.used_lists[i][j]].full.unwrap() <==> i == BIN_FULL)
              && (match self.pages[self.used_lists[i][j]].page_header_kind {
                  None => false,
                  Some(PageHeaderKind::Normal(bin, bsize)) =>
                      valid_bin_idx(bin)
                        && bsize == crate::bin_sizes::size_of_bin(bin)
                        && (i != BIN_FULL ==> i == bin)
                        && bsize <= MEDIUM_OBJ_SIZE_MAX,
              })
    }

    #[invariant]
    #[verifier::opaque]
    pub closed spec fn ll_inv_exists_in_some_list(&self) -> bool {
        forall |page_id: PageId| #[trigger] self.pages.dom().contains(page_id)
            && self.pages[page_id].offset == Some(0nat)
            && page_id.idx != 0
            && !self.expect_out_of_lists(page_id)
                ==> is_in_lls(page_id, self.used_lists) || is_in_lls(page_id, self.unused_lists)
    }

    ///////

    #[invariant]
    pub closed spec fn attached_ranges(&self) -> bool {
        forall |segment_id| #[trigger] self.segments.dom().contains(segment_id) ==>
            self.attached_ranges_segment(segment_id)
    }

    pub closed spec fn attached_ranges_segment(&self, segment_id: SegmentId) -> bool {
        match self.popped {
            Popped::SegmentCreating(sid) if sid == segment_id => true,
            Popped::SegmentFreeing(sid, idx) if sid == segment_id && idx > 0 => self.attached_rec(segment_id, idx, false),
            _ => self.attached_rec0(segment_id, self.popped_for_seg(segment_id))
        }
    }

    pub closed spec fn seg_free_prefix(&self, segment_id: SegmentId, idx: int) -> bool {
        forall |pid: PageId|
            #![trigger self.pages.dom().contains(pid)]
            #![trigger self.pages.index(pid)]
            pid.segment_id == segment_id && 0 <= pid.idx < idx ==>
            self.pages.dom().contains(pid)
            && self.pages[pid].dlist_entry.is_none()
            && self.pages[pid].count.is_none()
            && self.pages[pid].offset.is_none()
            && self.pages[pid].is_used == false
            && self.pages[pid].full.is_none()
            && self.pages[pid].page_header_kind.is_none()
    }

    pub closed spec fn attached_rec0(&self, segment_id: SegmentId, sp: bool) -> bool {
        self.good_range0(segment_id)
          && self.attached_rec(segment_id, self.pages[PageId { segment_id, idx: 0 }].count.unwrap() as int, sp)
    }

    #[verifier::opaque]
    pub closed spec fn attached_rec(&self, segment_id: SegmentId, idx: int, sp: bool) -> bool
        decreases SLICES_PER_SEGMENT - idx
    {
        if idx == SLICES_PER_SEGMENT {
          !sp
        } else if idx > SLICES_PER_SEGMENT {
          false
        } else if Self::is_the_popped(segment_id, idx, self.popped) {
          sp
            && self.popped_len() > 0
            && idx + self.popped_len() <= SLICES_PER_SEGMENT
            && self.attached_rec(segment_id, idx + self.popped_len(), false)
        } else {
          let page_id = PageId { segment_id, idx: idx as nat };
               (self.pages[page_id].is_used ==> self.good_range_used(page_id))
            && (!self.pages[page_id].is_used ==> self.good_range_unused(page_id))
            && self.pages[page_id].count.unwrap() > 0
            && idx + self.pages[page_id].count.unwrap() <= SLICES_PER_SEGMENT
            && self.attached_rec(segment_id, idx + self.pages[page_id].count.unwrap(), sp)
        }
    }

    pub closed spec fn popped_ranges_match(pre: Self, post: Self) -> bool {
        Self::is_any_the_popped(pre.popped) == Self::is_any_the_popped(post.popped)
          && (Self::is_any_the_popped(pre.popped) ==>
              pre.popped_len() == post.popped_len()
                && Self::page_id_of_popped(pre.popped) == Self::page_id_of_popped(post.popped)
          )
    }

    pub closed spec fn popped_ranges_match_for_sid(pre: Self, post: Self, sid: SegmentId) -> bool {
        pre.popped_for_seg(sid) == post.popped_for_seg(sid)
          && (pre.popped_for_seg(sid) ==>
              pre.popped_len() == post.popped_len()
                && Self::page_id_of_popped(pre.popped) == Self::page_id_of_popped(post.popped)
          )
    }


    pub closed spec fn popped_for_seg(&self, segment_id: SegmentId) -> bool {
        match self.popped {
            Popped::No => false,
            Popped::Ready(page_id, _)
                | Popped::Used(page_id, _)
                => page_id.segment_id == segment_id,
            Popped::SegmentCreating(_) => false,
            Popped::SegmentFreeing(_, _) => false,
            Popped::VeryUnready(sid, _, _, _) => sid == segment_id,
            Popped::ExtraCount(_) => false,
        }
    }

    pub closed spec fn is_any_the_popped(popped: Popped) -> bool {
        match popped {
            Popped::No => false,
            Popped::Ready(page_id, _)
                | Popped::Used(page_id, _)
                => true,
            Popped::SegmentCreating(_) => false,
            Popped::SegmentFreeing(_, _) => false,
            Popped::VeryUnready(sid, i, _, _) => true,
            Popped::ExtraCount(_) => false,
        }
    }

    pub closed spec fn is_the_popped(segment_id: SegmentId, idx: int, popped: Popped) -> bool {
        match popped {
            Popped::No => false,
            Popped::Ready(page_id, _)
                | Popped::Used(page_id, _)
                => page_id.segment_id == segment_id && page_id.idx == idx,
            Popped::SegmentCreating(_) => false,
            Popped::SegmentFreeing(_, _) => false,
            Popped::VeryUnready(sid, i, _, _) => sid == segment_id && i == idx,
            Popped::ExtraCount(_) => false,
        }
    }

    pub closed spec fn popped_len(&self) -> int {
        match self.popped {
            Popped::No => arbitrary(),
            Popped::Ready(page_id, _)
                | Popped::Used(page_id, _)
                => self.pages[page_id].count.unwrap() as int,
            Popped::SegmentCreating(_) => arbitrary(),
            Popped::SegmentFreeing(_, _) => arbitrary(),
            Popped::VeryUnready(sid, i, count, _) => count,
            Popped::ExtraCount(_) => arbitrary(),
        }
    }

    ///////

    pub open spec fn valid_unused_page(&self, page_id: PageId, sbin_idx: int, list_idx: int) -> bool {
        self.pages.dom().contains(page_id)
          && self.pages[page_id].is_used == false
          && (match self.pages[page_id].count {
              Some(count) => 0 <= count <= SLICES_PER_SEGMENT,
              None => false,
          })
          && self.pages[page_id].dlist_entry.is_Some()
          && 0 <= sbin_idx <= SEGMENT_BIN_MAX
          && 0 <= list_idx < self.unused_lists[sbin_idx].len()
          && self.unused_lists[sbin_idx][list_idx] == page_id
    }

    pub proof fn first_is_in(&self, sbin_idx: int)
        requires self.invariant(), self.popped.is_No(),
            0 <= sbin_idx <= SEGMENT_BIN_MAX,
        ensures
            match self.unused_dlist_headers[sbin_idx].first {
                Some(page_id) => self.valid_unused_page(page_id, sbin_idx, 0),
                None => true,
            }
    {
        match self.unused_dlist_headers[sbin_idx].first {
            Some(page_id) => {
                self.first_last_ll_stuff_unused(sbin_idx);
                self.lemma_range_not_used(page_id);
            }
            None => { }
        }
    }

    pub proof fn next_is_in(&self, page_id: PageId, sbin_idx: int, list_idx: int)
        requires self.invariant(), self.popped.is_No(),
            self.valid_unused_page(page_id, sbin_idx, list_idx)
        ensures
            match self.pages[page_id].dlist_entry.get_Some_0().next {
                Some(page_id) => self.valid_unused_page(page_id, sbin_idx, list_idx + 1),
                None => true,
            }
    {
        match self.pages[page_id].dlist_entry.get_Some_0().next {
            Some(next_id) => {
                self.unused_ll_stuff(sbin_idx, list_idx);
                assert(valid_ll_i(self.pages, self.unused_lists[sbin_idx], list_idx));
                self.lemma_range_not_used(next_id);
            }
            None => { }
        }
    }

    pub proof fn segment_freeing_is_in(&self) -> (list_idx: int)
        requires self.invariant(),
            self.popped.is_SegmentFreeing(),
            self.popped.get_SegmentFreeing_1() < SLICES_PER_SEGMENT,
        ensures (match self.popped {
            Popped::SegmentFreeing(segment_id, idx) => { idx >= 0 && {
                let page_id = PageId { segment_id, idx: idx as nat };
                let count = self.pages[page_id].count.unwrap();
                let sbin_idx = smallest_sbin_fitting_size(count as int);
                self.valid_unused_page(page_id, sbin_idx, list_idx)
            }}
            _ => false,
        }),
    {
        match self.popped {
            Popped::SegmentFreeing(segment_id, idx) => {
                reveal(State::attached_rec);
                let page_id = PageId { segment_id, idx: idx as nat };
                self.ucount_eq0_inverse(page_id);
                self.unused_is_in_sbin(page_id);
                return Self::get_list_idx(self.unused_lists, page_id).1;
            }
            _ => { return 0; }
        }
    }

    pub proof fn marked_full_is_in(&self, page_id: PageId) -> (list_idx: int)
        requires self.invariant(),
            self.pages.dom().contains(page_id),
            self.popped.is_No(),
            self.pages[page_id].offset == Some(0nat),
            self.pages[page_id].full != Some(false),
            self.pages[page_id].is_used,
        ensures
            self.valid_used_page(page_id, BIN_FULL as int, list_idx),
            (match self.pages[page_id].page_header_kind {
                Some(PageHeaderKind::Normal(bin, size)) =>
                  size == size_of_bin(bin)
                  && bin == smallest_bin_fitting_size(size)
                  && size <= MEDIUM_OBJ_SIZE_MAX,
                None => false,
            }),

    {
        assert(is_in_lls(page_id, self.used_lists) || is_in_lls(page_id, self.unused_lists)) by { reveal(State::ll_inv_exists_in_some_list); };
        assert(is_in_lls(page_id, self.used_lists));
        let list_idx = choose |list_idx: int| 0 <= list_idx < self.used_lists[BIN_FULL as int].len() && self.used_lists[BIN_FULL as int][list_idx] == page_id;
        assert(self.used_lists[BIN_FULL as int][list_idx] == page_id);

        let bin_idx = BIN_FULL as int;
        assert(valid_ll_i(self.pages, self.used_lists[bin_idx], list_idx));

        match self.pages[page_id].page_header_kind {
            Some(PageHeaderKind::Normal(bin_idx, size)) => {
                crate::bin_sizes::smallest_bin_fitting_size_size_of_bin(bin_idx);
            }
            _ => { }
        }

        return list_idx;
    }

    pub proof fn marked_unfull_is_in(&self, page_id: PageId) -> (list_idx: int)
        requires self.invariant(),
            self.pages.dom().contains(page_id),
            self.popped.is_No(),
            self.pages[page_id].offset == Some(0nat),
            self.pages[page_id].full != Some(true),
            self.pages[page_id].is_used,
        ensures
            (match self.pages[page_id].page_header_kind {
                Some(PageHeaderKind::Normal(bin, size)) =>
                  size == size_of_bin(bin)
                  && self.valid_used_page(page_id, bin, list_idx)
                  && bin == smallest_bin_fitting_size(size)
                  && size <= MEDIUM_OBJ_SIZE_MAX,
                None => false,
            }),
    {
        assert(is_in_lls(page_id, self.used_lists) || is_in_lls(page_id, self.unused_lists)) by { reveal(State::ll_inv_exists_in_some_list); };
        match self.pages[page_id].page_header_kind {
            Some(PageHeaderKind::Normal(_, size)) => {
                assert(is_in_lls(page_id, self.used_lists));
                //let bin_idx = smallest_bin_fitting_size(size);
                //crate::bin_sizes::bounds_for_smallest_bin_fitting_size(size);
                let (bin_idx, list_idx) = choose |bin_idx: int, list_idx: int| 0 <= bin_idx < self.used_lists.len() && 0 <= list_idx < self.used_lists[bin_idx].len() && self.used_lists[bin_idx][list_idx] == page_id;
                assert(self.used_lists[bin_idx][list_idx] == page_id);
                assert(valid_ll_i(self.pages, self.used_lists[bin_idx], list_idx));
                assert(bin_idx != BIN_FULL);
                crate::bin_sizes::smallest_bin_fitting_size_size_of_bin(bin_idx);
                return list_idx;
            }
            None => {
                assert(false);
                return 0;
            }
        }
    }

    #[verifier::opaque]
    pub closed spec fn get_list_idx(lists: Seq<Seq<PageId>>, pid: PageId) -> (int, int) {
        let (i, j): (int, int) = choose |i: int, j: int|
            0 <= i < lists.len()
            && 0 <= j < lists[i].len()
            && lists[i][j] == pid;
        (i, j)
    }

    proof fn unused_is_in_sbin(&self, page_id: PageId)
        requires self.invariant(),
            self.pages.dom().contains(page_id),
            self.popped.is_VeryUnready() || self.popped.is_SegmentFreeing(),
            self.pages[page_id].offset == Some(0nat),
            !self.pages[page_id].is_used,
            page_id.idx != 0,
        ensures ({
            let sbin_idx = smallest_sbin_fitting_size(self.pages[page_id].count.unwrap() as int);
            let list_idx = Self::get_list_idx(self.unused_lists, page_id).1;
            self.valid_unused_page(page_id, sbin_idx, list_idx)
        })
    {
        let sbin_idx = smallest_sbin_fitting_size(self.pages[page_id].count.unwrap() as int);
        let (i, list_idx) = Self::get_list_idx(self.unused_lists, page_id);
        assert(
            0 <= i < self.unused_lists.len()
            && 0 <= list_idx < self.unused_lists[i].len()
            && self.unused_lists[i][list_idx] == page_id
        ) by {
            reveal(State::ll_inv_exists_in_some_list);
            reveal(State::get_list_idx);
        }

        assert(i == sbin_idx);

        assert(valid_ll(self.pages, self.unused_dlist_headers[sbin_idx], self.unused_lists[sbin_idx]));
        assert(valid_ll_i(self.pages, self.unused_lists[sbin_idx], list_idx));
        self.lemma_range_not_used(page_id);
    }

    pub proof fn get_count_bound_very_unready(&self)
        requires self.invariant(), self.popped.is_VeryUnready(),
        ensures
            0 < self.popped.get_VeryUnready_1(),
            self.popped.get_VeryUnready_1() + 
                self.popped.get_VeryUnready_2() <= SLICES_PER_SEGMENT,
    {
    }

    pub proof fn lemma_range_disjoint_very_unready(&self, page_id: PageId)
        requires self.invariant(), self.popped.is_VeryUnready(),
            self.pages.dom().contains(page_id),
            self.pages[page_id].offset == Some(0nat),
            self.pages[page_id].is_used,
            page_id.segment_id == self.popped.get_VeryUnready_0(),
        ensures
            match self.popped {
                Popped::VeryUnready(_, idx, p_count, _) => {
                    match self.pages[page_id].count {
                        Some(count) => page_id.idx + count <= idx || idx + p_count <= page_id.idx,
                        None => false,
                    }
                }
                _ => false,
            }
    {
        self.lemma_range_used(page_id);
        self.good_range_disjoint_very_unready(page_id);
    }

    pub proof fn lemma_range_disjoint_used2(&self, page_id1: PageId, page_id2: PageId)
        requires self.invariant(),
            self.pages.dom().contains(page_id1),
            self.pages[page_id1].offset == Some(0nat),
            self.pages[page_id1].is_used,
            self.pages.dom().contains(page_id2),
            self.pages[page_id2].offset == Some(0nat),
            self.pages[page_id2].is_used,
            page_id1 != page_id2,
            page_id1.segment_id == page_id2.segment_id,
        ensures
            match (self.pages[page_id1].count, self.pages[page_id2].count) {
                (Some(count1), Some(count2)) => {
                    page_id1.idx + count1 <= page_id2.idx
                      || page_id2.idx + count2 <= page_id1.idx
                }
                _ => false,
            }
    {
        if self.popped.is_Used() && self.popped.get_Used_0() == page_id1 {
            self.lemma_range_used(page_id2);
        } else if self.popped.is_Used() && self.popped.get_Used_0() == page_id2 {
            self.lemma_range_used(page_id1);
        } else {
            self.lemma_range_used(page_id1);
            self.lemma_range_used(page_id2);
        }
    }

    pub proof fn used_offset0_has_count(&self, page_id: PageId)
        requires self.invariant(), self.pages.dom().contains(page_id),
            self.pages[page_id].is_used,
            self.pages[page_id].offset == Some(0nat),
            page_id.idx != 0,
        ensures
            self.pages[page_id].count.is_some()
    {
    }

    pub proof fn get_offset_for_something_in_used_range(&self, page_id: PageId, slice_id: PageId)
        requires self.invariant(),
            self.pages.dom().contains(page_id),
            self.pages[page_id].is_used,
            self.pages[page_id].offset == Some(0nat),
            slice_id.segment_id == page_id.segment_id,
            page_id.idx <= slice_id.idx < page_id.idx + self.pages[page_id].count.unwrap(),
        ensures
            self.pages.dom().contains(slice_id),
            self.pages[slice_id].is_used,
            self.pages[slice_id].offset == Some((slice_id.idx - page_id.idx) as nat)
    {
        if self.popped.is_Used() && self.popped.get_Used_0() == page_id {
        } else {
            self.lemma_range_used(page_id);
        }
    }

    pub proof fn get_count_bound(&self, page_id: PageId)
        requires self.invariant(), self.pages.dom().contains(page_id),
        ensures
            (match self.pages[page_id].count {
                None => true,
                Some(count) => page_id.idx + count <= SLICES_PER_SEGMENT
            }),
    {
        if self.popped.is_Ready() && self.popped.get_Ready_0() == page_id {
            return;
        }
        match self.pages[page_id].count {
            None => { }
            Some(count) => {
                if page_id.idx == 0 {
                    assert(page_id.idx + count <= SLICES_PER_SEGMENT);
                } else if is_unused_header(self.pages[page_id]) {
                    self.lemma_range_not_used(page_id);
                } else {
                    assert(is_used_header(self.pages[page_id]));
                    match self.popped {
                        Popped::Used(pid, _) if pid == page_id => {
                        }
                        _ => {
                            self.lemma_range_used(page_id);
                        }
                   }
                }
            }
        }
    }

    pub open spec fn valid_used_page(&self, page_id: PageId, bin_idx: int, list_idx: int) -> bool {
        self.pages.dom().contains(page_id)
          && self.pages[page_id].is_used == true
          //&& (match self.pages[page_id].count {
          //    Some(count) => 0 <= count <= SLICES_PER_SEGMENT,
          //    None => false,
          //})
          && self.pages[page_id].dlist_entry.is_Some()
          && self.pages[page_id].offset == Some(0nat)
          && (crate::bin_sizes::valid_bin_idx(bin_idx) || bin_idx == BIN_FULL)
          && 0 <= list_idx < self.used_lists[bin_idx].len()
          && self.used_lists[bin_idx][list_idx] == page_id
          && (match self.pages[page_id].page_header_kind {
              None => false,
              Some(PageHeaderKind::Normal(bin, bsize)) =>
                  valid_bin_idx(bin)
                  && size_of_bin(bin) == bsize
                  && (bin_idx != BIN_FULL ==> bin_idx == bin)
          })
    }

    pub proof fn used_first_is_in(&self, bin_idx: int)
        requires self.invariant(), !self.popped.is_Ready(),
            0 <= bin_idx <= BIN_HUGE,
        ensures
            match self.used_dlist_headers[bin_idx].first {
                Some(page_id) => self.valid_used_page(page_id, bin_idx, 0),
                None => true,
            }
    {
        match self.used_dlist_headers[bin_idx].first {
            Some(page_id) => {
                self.first_last_ll_stuff_used(bin_idx);
                self.lemma_range_used(page_id);
                assert(self.pages[page_id].dlist_entry.is_some());
            }
            None => { }
        }
    }

    pub proof fn used_next_is_in(&self, page_id: PageId, bin_idx: int, list_idx: int)
        requires self.invariant(),
            self.valid_used_page(page_id, bin_idx, list_idx)
        ensures
            match self.pages[page_id].dlist_entry.get_Some_0().next {
                Some(page_id) => self.valid_used_page(page_id, bin_idx, list_idx + 1),
                None => true,
            }
    {
        match self.pages[page_id].dlist_entry.get_Some_0().next {
            Some(next_id) => {
                self.used_ll_stuff(bin_idx, list_idx);
                assert(valid_ll_i(self.pages, self.used_lists[bin_idx], list_idx));
                self.lemma_range_used(next_id);
            }
            None => { }
        }
    }

    pub proof fn rec_valid_page_after(&self, idx: int, sp: bool)
        requires self.invariant(),
            match self.popped {
                Popped::VeryUnready(sid, start, len, _) => {
                    start + len < SLICES_PER_SEGMENT
                }
                _ => false,
            },
            self.attached_rec(self.popped.get_VeryUnready_0(), idx, sp),
            !sp ==>
                idx >= Self::page_id_of_popped(self.popped).idx + self.popped_len(),
            idx >= 0,
        ensures
            sp ==> match self.popped {
                Popped::VeryUnready(sid, start, len, _) => {
                    let page_id = PageId { segment_id: sid, idx: (start + len) as nat };
                    self.pages.dom().contains(page_id)
                      && self.pages[page_id].offset == Some(0nat)
                }
                _ => false,
            },
            sp ==>
                idx <= Self::page_id_of_popped(self.popped).idx,
        decreases SLICES_PER_SEGMENT - idx
    {
        reveal(State::attached_rec);
        let segment_id = self.popped.get_VeryUnready_0();
        if idx == SLICES_PER_SEGMENT {
            assert(!sp);
        } else if idx > SLICES_PER_SEGMENT {
            assert(false);
        } else if Self::is_the_popped(segment_id, idx, self.popped) {
            assert(self.attached_rec(segment_id, idx + self.popped_len(), false));
        } else {
            let page_id = PageId { segment_id, idx: idx as nat };
            self.rec_valid_page_after(idx + self.pages[page_id].count.unwrap(), sp);
        }
    }

    pub proof fn valid_page_after(&self)
        requires self.invariant(),
            match self.popped {
                Popped::VeryUnready(sid, start, len, _) => {
                    start + len < SLICES_PER_SEGMENT
                }
                _ => false,
            }
        ensures
            match self.popped {
                Popped::VeryUnready(sid, start, len, _) => {
                    let page_id = PageId { segment_id: sid, idx: (start + len) as nat };
                    self.pages.dom().contains(page_id)
                      && self.pages[page_id].offset == Some(0nat)
                }
                _ => false,
            }
    {
        let segment_id = self.popped.get_VeryUnready_0();
        self.rec_valid_page_after(
            self.pages[PageId { segment_id, idx: 0 }].count.unwrap() as int, true);
    }

    pub proof fn rec_valid_page_before(&self, idx: int, sp: bool)
        requires self.invariant(),
            match self.popped {
                Popped::VeryUnready(sid, start, len, _) => {
                    start > 0
                }
                _ => false,
            },
            self.attached_rec(self.popped.get_VeryUnready_0(), idx, sp),
            !sp ==>
                idx >= Self::page_id_of_popped(self.popped).idx + self.popped_len(),
            idx >= 0,
        ensures
            idx < Self::page_id_of_popped(self.popped).idx ==> (
                match self.popped {
                    Popped::VeryUnready(sid, start, len, _) => {
                        let last_id = PageId { segment_id: sid, idx: (start - 1) as nat };
                        let offset = self.pages[last_id].offset.unwrap();
                        let page_id = PageId { segment_id: sid, idx: (last_id.idx - offset) as nat };
                        self.pages.dom().contains(last_id)
                        && last_id.idx - offset >= 0
                        && self.pages[last_id].offset.is_some()
                        && self.pages.dom().contains(page_id)
                        && self.pages[page_id].offset == Some(0nat)
                        && self.pages[page_id].count == Some(offset + 1)
                    }
                    _ => false,
                }),
            sp ==>
                idx <= Self::page_id_of_popped(self.popped).idx,
        decreases SLICES_PER_SEGMENT - idx
    {
        reveal(State::attached_rec);
        let segment_id = self.popped.get_VeryUnready_0();
        if idx == SLICES_PER_SEGMENT {
            assert(!sp);
        } else if idx > SLICES_PER_SEGMENT {
            assert(false);
        } else if Self::is_the_popped(segment_id, idx, self.popped) {
            assert(self.attached_rec(segment_id, idx + self.popped_len(), false));
        } else {
            let page_id = PageId { segment_id, idx: idx as nat };
            self.rec_valid_page_before(idx + self.pages[page_id].count.unwrap(), sp);
        }
    }

    pub proof fn valid_page_before(&self)
        requires self.invariant(),
            match self.popped {
                Popped::VeryUnready(sid, start, len, _) => {
                    start > 0
                }
                _ => false,
            }
        ensures
            match self.popped {
                Popped::VeryUnready(sid, start, len, _) => {
                    let last_id = PageId { segment_id: sid, idx: (start - 1) as nat };
                    let offset = self.pages[last_id].offset.unwrap();
                    let page_id = PageId { segment_id: sid, idx: (last_id.idx - offset) as nat };
                    self.pages.dom().contains(last_id)
                    && last_id.idx - offset >= 0
                    && self.pages[last_id].offset.is_some()
                    && self.pages.dom().contains(page_id)
                    && self.pages[page_id].offset == Some(0nat)
                    && self.pages[page_id].count == Some(offset + 1)
                }
                _ => false,
            }
    {
        let segment_id = self.popped.get_VeryUnready_0();
        self.rec_valid_page_before(
            self.pages[PageId { segment_id, idx: 0 }].count.unwrap() as int, true);
    }

    init!{
        initialize() {
            init unused_dlist_headers = Seq::new((SEGMENT_BIN_MAX + 1) as nat,
                |i| DlistHeader { first: None, last: None });
            init used_dlist_headers = Seq::new((BIN_FULL + 1) as nat,
                |i| DlistHeader { first: None, last: None });
            init pages = Map::empty();
            init segments = Map::empty();
            init popped = Popped::No;

            // TODO internals
            init unused_lists = Seq::new((SEGMENT_BIN_MAX + 1) as nat, |i| Seq::empty());
            init used_lists = Seq::new((BIN_FULL + 1) as nat, |i| Seq::empty());
        }
    }

    transition!{
        take_page_from_unused_queue(page_id: PageId, sbin_idx: int, list_idx: int) {
            require pre.valid_unused_page(page_id, sbin_idx, list_idx);
            require pre.popped == Popped::No
                || pre.popped == Popped::SegmentFreeing(page_id.segment_id, page_id.idx as int);

            assert let Some(dlist_entry) = pre.pages[page_id].dlist_entry;
            assert pre.pages[page_id].is_used == false;

            update pages[page_id] = PageData {
                dlist_entry: None,
                count: None,
                offset: None,
                .. pre.pages[page_id]
            };

            // Update prev to point to next
            match dlist_entry.prev {
                Some(prev_page_id) => {
                    assert prev_page_id != page_id
                      && pre.pages.dom().contains(prev_page_id)
                      && pre.pages[prev_page_id].dlist_entry.is_some()
                      && pre.pages[prev_page_id].is_used == false

                      by { pre.unused_ll_stuff(sbin_idx, list_idx); };

                    update pages[prev_page_id] = PageData {
                        dlist_entry: Some(DlistEntry {
                            next: dlist_entry.next,
                            .. pre.pages[prev_page_id].dlist_entry.unwrap()
                        }),
                        .. pre.pages[prev_page_id]
                    };
                }
                Option::None => { }
            }

            // Update next to point to prev
            match dlist_entry.next {
                Some(next_page_id) => {
                    assert next_page_id != page_id
                      && pre.pages.dom().contains(next_page_id)
                      && pre.pages[next_page_id].dlist_entry.is_some()
                      && pre.pages[next_page_id].is_used == false

                      by { pre.unused_ll_stuff(sbin_idx, list_idx); };

                    update pages[next_page_id] = PageData {
                        dlist_entry: Some(DlistEntry {
                            prev: dlist_entry.prev,
                            .. pre.pages[next_page_id].dlist_entry.unwrap()
                        }),
                        .. pre.pages[next_page_id]
                    };
                }
                Option::None => { }
            }
            
            // Workaround for not begin able to do `update unused_dlist_headers[sbin_idx].first = ...`
            if dlist_entry.prev.is_none() && dlist_entry.next.is_none() {
                update unused_dlist_headers[sbin_idx] = DlistHeader {
                    first: dlist_entry.next,
                    last: dlist_entry.prev,
                };
            } else if dlist_entry.prev.is_none() {
                update unused_dlist_headers[sbin_idx] = DlistHeader {
                    first: dlist_entry.next,
                    .. pre.unused_dlist_headers[sbin_idx]
                };
            } else if dlist_entry.next.is_none() {
                update unused_dlist_headers[sbin_idx] = DlistHeader {
                    last: dlist_entry.prev,
                    .. pre.unused_dlist_headers[sbin_idx]
                };
            }

            assert dlist_entry.prev.is_some() && dlist_entry.next.is_some() ==>
                dlist_entry.prev.unwrap() != dlist_entry.next.unwrap()

                by { pre.unused_ll_stuff(sbin_idx, list_idx); };

            assert let Some(count) = pre.pages[page_id].count;

            assert count >= 1;
            let last_id = PageId { idx: (page_id.idx + count - 1) as nat, ..page_id };
            if last_id != page_id {
                update pages[last_id] = PageData {
                    offset: None,
                    .. pre.pages[last_id]
                };
                assert(pre.pages.dom().contains(last_id))
                    by { pre.get_count_bound(page_id); };

                assert(pre.pages[last_id].is_used == false
                      && pre.pages[last_id].page_header_kind.is_none())

                    by { pre.lemma_range_not_used(page_id);
                        assert(pre.pages.dom().contains(last_id));
                    };
            }
            assert dlist_entry.prev != Some(last_id)
                && dlist_entry.next != Some(last_id)
              by { pre.unused_ll_stuff(sbin_idx, list_idx); pre.lemma_range_not_used(page_id); };

            match pre.popped {
                Popped::No => {
                    update popped = Popped::VeryUnready(page_id.segment_id, page_id.idx as int, count as int, false);
                }
                Popped::SegmentFreeing(sid, i) => {
                    update popped = Popped::SegmentFreeing(sid, i + count);
                }
                _ => { }
            }

            update unused_lists[sbin_idx] = pre.unused_lists[sbin_idx].remove(list_idx);
        }
    }

    transition!{
        split_page(page_id: PageId, current_count: int, target_count: int, sbin_idx: int) {
            // Require that `page_id` is currently popped
            // and that it has has count equal to `current_count`
            require pre.popped == Popped::VeryUnready(page_id.segment_id, page_id.idx as int, current_count, false);
            assert pre.pages.dom().contains(page_id);
            assert pre.pages[page_id].count.is_none();
            require !pre.pages[page_id].is_used;

            require 1 <= target_count < current_count;
            require 0 <= sbin_idx <= SEGMENT_BIN_MAX;
            require sbin_idx == smallest_sbin_fitting_size(current_count - target_count);

            //  |------------current_count---------------|
            //  
            //  |--------------|-------------------------|
            //    target_count
            //
            //                   ^                      ^
            //                   |                      |
            //    ^           next_page_id          last_page_id
            //    |
            //  page_id

            let next_page_id = PageId { idx: (page_id.idx + target_count) as nat, .. page_id };
            let last_page_id = PageId { idx: (page_id.idx + current_count - 1) as nat, .. page_id };
            assert pre.pages.dom().contains(next_page_id)
                && pre.pages.dom().contains(last_page_id)
                && pre.pages[next_page_id].is_used == false
                && pre.pages[last_page_id].is_used == false;

            update pages[next_page_id] = PageData {
                count: Some((current_count - target_count) as nat),
                offset: Some(0),
                dlist_entry: Some(DlistEntry {
                    prev: None,
                    next: pre.unused_dlist_headers[sbin_idx].first,
                }),
                .. pre.pages[next_page_id]
            };

            // If the 'last page' is distinct from the 'next page'
            // we have to update it too
            if current_count - target_count > 1 {
                update pages[last_page_id] = PageData {
                    count: None, //Some((current_count - target_count) as nat),
                    offset: Some((current_count - target_count - 1) as nat),
                    .. pre.pages[last_page_id]
                };
            }

            // Insert into the queue
            update unused_dlist_headers[sbin_idx] = DlistHeader {
                first: Some(next_page_id),
                last:
                    if pre.unused_dlist_headers[sbin_idx].first.is_some() {
                        pre.unused_dlist_headers[sbin_idx].last
                    } else {
                        Some(next_page_id)
                    },
            };
            if pre.unused_dlist_headers[sbin_idx].first.is_some() {
                let first_id = pre.unused_dlist_headers[sbin_idx].first.unwrap();
                assert pre.pages.dom().contains(first_id)          by { pre.first_last_ll_stuff_unused(sbin_idx); };
                assert !pre.pages[first_id].is_used                by { pre.first_last_ll_stuff_unused(sbin_idx); };
                assert pre.pages[first_id].dlist_entry.is_some()   by { pre.first_last_ll_stuff_unused(sbin_idx); };
                assert first_id != page_id                         by { pre.first_last_ll_stuff_unused(sbin_idx); };
                assert first_id != next_page_id                    by { pre.first_last_ll_stuff_unused(sbin_idx); /*pre.lemma_range_not_header(page_id, next_page_id);*/ };
                assert first_id != last_page_id                    by { pre.first_last_ll_stuff_unused(sbin_idx); /*pre.lemma_range_not_header(page_id, last_page_id);*/ };
                update pages[first_id] = PageData {
                    dlist_entry: Some(DlistEntry {
                        prev: Some(next_page_id),
                        .. pre.pages[first_id].dlist_entry.unwrap()
                    }),
                    .. pre.pages[first_id]
                };
            }

            update popped = Popped::VeryUnready(page_id.segment_id, page_id.idx as int, target_count, false);
            update unused_lists = Self::insert_front(pre.unused_lists, sbin_idx, next_page_id);
        }
    }

    transition!{
        create_segment(segment_id: SegmentId) {
            require pre.popped == Popped::No;
            require !pre.segments.dom().contains(segment_id);

            let new_pages = pages_with_segment(segment_id, 0, SLICES_PER_SEGMENT+1,
                |page_id: PageId| PageData {
                    dlist_entry: None,
                    count: None,
                    offset: None,
                    is_used: false,
                    page_header_kind: None,
                    full: None,
                });

//             let i_new_pages = IMap::new(
//                 |page_id: PageId| page_id.segment_id == segment_id
//                     && 0 <= page_id.idx <= SLICES_PER_SEGMENT,
//                 |page_id: PageId| PageData {
//                     dlist_entry: None,
//                     count: None,
//                     offset: None,
//                     is_used: false,
//                     page_header_kind: None,
//                     full: None,
//                 });
//             assert( Set::congruent(new_pages.dom(), i_new_pages.dom()) ) by {
//                 pages_with_segment_ensures(segment_id, 0,SLICES_PER_SEGMENT+1,
//                     |page_id: PageId| PageData {
//                         dlist_entry: None,
//                         count: None,
//                         offset: None,
//                         is_used: false,
//                         page_header_kind: None,
//                         full: None,
//                     });
//             };

            update segments = pre.segments.insert(segment_id, SegmentData { used: 0 });
            update pages = pre.pages.union_prefer_right(new_pages);
            update popped = Popped::SegmentCreating(segment_id);
        }
    }

    transition!{
        allocate_popped() {
            require let Popped::VeryUnready(segment_id, idx, count, fals) = pre.popped;
            require fals == false;
            assert idx >= 0;
            let page_id = PageId { segment_id, idx: idx as nat };
            assert pre.pages.dom().contains(page_id);
            assert count > 0;
            assert count + page_id.idx <= SLICES_PER_SEGMENT;

            assert (forall |pid: PageId| pid.segment_id == page_id.segment_id &&
                    page_id.idx <= pid.idx < page_id.idx + count
                    ==> pre.pages.dom().contains(pid)
                );
            assert (forall |pid: PageId| pid.segment_id == page_id.segment_id &&
                    page_id.idx <= pid.idx < page_id.idx + count
                    ==> !pre.pages[pid].is_used
                );

            let changed_pages  = pages_with_segment(segment_id, page_id.idx as int, page_id.idx + count as int,
                |pid: PageId| PageData {
                    count: if pid == page_id { Some(count as nat) } else { pre.pages[pid].count },
                    offset: Some((pid.idx - page_id.idx) as nat), // set offset
                    dlist_entry: pre.pages[pid].dlist_entry,
                    // keep is_used=false for now
                    // instead, we mark that this operation is done by setting popped=Ready
                    is_used: false,
                    page_header_kind: None,
                    full: None,
                }
            );

//             let i_changed_pages = IMap::new(
//                 |pid: PageId| pid.segment_id == page_id.segment_id &&
//                     page_id.idx <= pid.idx < page_id.idx + count,
//                 |pid: PageId| PageData {
//                     count: if pid == page_id { Some(count as nat) } else { pre.pages[pid].count },
//                     offset: Some((pid.idx - page_id.idx) as nat), // set offset
//                     dlist_entry: pre.pages[pid].dlist_entry,
//                     // keep is_used=false for now
//                     // instead, we mark that this operation is done by setting popped=Ready
//                     is_used: false,
//                     page_header_kind: None,
//                     full: None,
//                 }
//             );
//             assert( Set::congruent(changed_pages.dom(), i_changed_pages.dom()) );

            let new_pages = pre.pages.union_prefer_right(changed_pages);
            assert pre.pages.dom() =~= new_pages.dom();

            assert pre.segments[page_id.segment_id].used <= SLICES_PER_SEGMENT + 1
                by { pre.lemma_used_bound(page_id.segment_id); };
            update segments[page_id.segment_id] = SegmentData {
                used: pre.segments[page_id.segment_id].used + 1,
            };

            update pages = new_pages;
            update popped = Popped::Ready(page_id, true);
        }
    }

    transition!{
        forget_about_first_page(count: int) {
            require 1 <= count < SLICES_PER_SEGMENT;
            require let Popped::SegmentCreating(segment_id) = pre.popped;
            assert pre.segments.dom().contains(segment_id);

            assert (forall |pid: PageId| pid.segment_id == segment_id &&
                    0 <= pid.idx < count
                    ==> pre.pages.dom().contains(pid)
                );
            assert (forall |pid: PageId| pid.segment_id == segment_id &&
                    0 <= pid.idx < count
                    ==> !pre.pages[pid].is_used
                );

            let page_id = PageId { segment_id, idx: 0 };
            assert pre.pages.dom().contains(page_id);
            assert count + page_id.idx <= SLICES_PER_SEGMENT;

            let changed_pages = pages_with_segment(segment_id, 0, count, 
                |pid: PageId| PageData {
                    count: if pid == page_id { Some(count as nat) } else { pre.pages[pid].count },
                    offset: Some((pid.idx - page_id.idx) as nat), // set offset
                    dlist_entry: pre.pages[pid].dlist_entry,
                    is_used: false,
                    page_header_kind: None,
                    full: None,
                }
            );

//             let i_changed_pages = IMap::new(
//                 |pid: PageId| pid.segment_id == segment_id &&
//                     0 <= pid.idx < count,
//                 |pid: PageId| PageData {
//                     count: if pid == page_id { Some(count as nat) } else { pre.pages[pid].count },
//                     offset: Some((pid.idx - page_id.idx) as nat), // set offset
//                     dlist_entry: pre.pages[pid].dlist_entry,
//                     is_used: false,
//                     page_header_kind: None,
//                     full: None,
//                 }
//             );
//             assert( Set::congruent(changed_pages.dom(), i_changed_pages.dom()) );

            let new_pages = pre.pages.union_prefer_right(changed_pages);
            assert pre.pages.dom() =~= new_pages.dom();
            update pages = new_pages;

            assert pre.segments[page_id.segment_id].used <= SLICES_PER_SEGMENT + 1
                by { pre.lemma_used_bound(page_id.segment_id); };
            update segments[page_id.segment_id] = SegmentData {
                used: pre.segments[page_id.segment_id].used + 1,
            };

            update popped = Popped::VeryUnready(segment_id, count, SLICES_PER_SEGMENT - count, true);
        }
    }

    transition!{
        forget_about_first_page2() {
            require let Popped::VeryUnready(segment_id, start, count, tru) = pre.popped;
            require tru == true;

            assert pre.segments[segment_id].used >= 1;
            update segments[segment_id] = SegmentData {
                used: pre.segments[segment_id].used - 1,
            };

            update popped = Popped::VeryUnready(segment_id, start, count, false);
        }
    }

    transition!{
        clear_ec() {
            require let Popped::ExtraCount(segment_id) = pre.popped;

            assert pre.segments[segment_id].used >= 1;
            update segments[segment_id] = SegmentData {
                used: pre.segments[segment_id].used - 1,
            };

            update popped = Popped::No;
        }
    }


    transition!{
        free_to_unused_queue(sbin_idx: int) {
            require valid_sbin_idx(sbin_idx);
            require let Popped::VeryUnready(segment_id, start, count, ec) = pre.popped;
            assert pre.segments.dom().contains(segment_id);
            assert 1 <= start < start + count <= SLICES_PER_SEGMENT;

            require sbin_idx == smallest_sbin_fitting_size(count);

            let first_page = PageId { segment_id, idx: start as nat };
            let last_page = PageId { segment_id, idx: (first_page.idx + count - 1) as nat };

            assert pre.pages.dom().contains(first_page);
            assert !pre.pages[first_page].is_used;
            assert pre.pages.dom().contains(last_page);
            assert !pre.pages[last_page].is_used;

            assert pre.pages[first_page].count.is_none();
            assert pre.pages[first_page].offset.is_none();
            assert pre.pages[last_page].offset.is_none();

            update pages[first_page] = PageData {
                dlist_entry: Some(DlistEntry {
                    prev: None,
                    next: pre.unused_dlist_headers[sbin_idx].first,
                }),
                count: Some(count as nat),
                offset: Some(0),
                is_used: false,
                page_header_kind: None,
                full: None,
            };

            if count > 1 {
                assert last_page != first_page;
                update pages[last_page] = PageData {
                    offset: Some((count - 1) as nat),
                    .. pre.pages[last_page]
                };
            }

            update unused_dlist_headers[sbin_idx] = DlistHeader {
                first: Some(first_page),
                last: if pre.unused_dlist_headers[sbin_idx].first.is_some() {
                    pre.unused_dlist_headers[sbin_idx].last
                } else {
                    Some(first_page)
                },
            };

            if pre.unused_dlist_headers[sbin_idx].first.is_some() {
                let queue_first_page_id = pre.unused_dlist_headers[sbin_idx].first.unwrap();
                assert queue_first_page_id != first_page;
                assert queue_first_page_id != last_page;
                assert pre.pages.dom().contains(queue_first_page_id);
                assert !pre.pages[queue_first_page_id].is_used;
                assert pre.pages[queue_first_page_id].dlist_entry.is_some()
                    by { pre.first_last_ll_stuff_unused(sbin_idx); };

                update pages[queue_first_page_id] = PageData {
                    dlist_entry: Some(DlistEntry {
                        prev: Some(first_page),
                        .. pre.pages[queue_first_page_id].dlist_entry.unwrap()
                    }),
                    .. pre.pages[queue_first_page_id]
                };
            }

            update popped = if ec { Popped::ExtraCount(segment_id) } else { Popped::No };
            update unused_lists = Self::insert_front(pre.unused_lists, sbin_idx, first_page);
        }
    }

    /*transition!{
        original_free_in_segment_creation() {
            require let Popped::SegmentCreatingSkipped(segment_id, skip_count) = pre.popped;
        }
    }*/

    transition!{
        set_range_to_used(page_header_kind: PageHeaderKind) {
            require let Popped::Ready(page_id, b) = pre.popped;
            assert pre.pages.dom().contains(page_id);
            assert pre.pages[page_id].count.is_some();
            let count = pre.pages[page_id].count.unwrap();
            assert count > 0;
            assert pre.pages[page_id].offset == Some(0nat);
            assert page_id.idx != 0;

            assert (forall |pid: PageId| pid.segment_id == page_id.segment_id &&
                    page_id.idx <= pid.idx < page_id.idx + count
                    ==> pre.pages.dom().contains(pid)
                );
            assert (forall |pid: PageId| pid.segment_id == page_id.segment_id &&
                    page_id.idx <= pid.idx < page_id.idx + count
                    ==> !pre.pages[pid].is_used
                );
            assert (forall |pid: PageId| pid.segment_id == page_id.segment_id &&
                    page_id.idx <= pid.idx < page_id.idx + count
                    ==> pre.pages[pid].offset.is_some()
                        && pre.pages[pid].offset.unwrap() == pid.idx - page_id.idx
                );

            let changed_pages = pages_with_segment(page_id.segment_id, page_id.idx as int, page_id.idx+count as int,
                |pid: PageId| PageData {
                    is_used: true,
                    page_header_kind: if pid == page_id { Some(page_header_kind) } else { None },
                    .. pre.pages[pid]
                }
            );

//             let i_changed_pages = IMap::new(
//                 |pid: PageId| pid.segment_id == page_id.segment_id &&
//                     page_id.idx <= pid.idx < page_id.idx + count,
//                 |pid: PageId| PageData {
//                     is_used: true,
//                     page_header_kind: if pid == page_id { Some(page_header_kind) } else { None },
//                     .. pre.pages[pid]
//                 }
//             );
// 
//             assert( Set::congruent(changed_pages.dom(), i_changed_pages.dom()) );

            let new_pages = pre.pages.union_prefer_right(changed_pages);
            assert pre.pages.dom() =~= new_pages.dom();

            update pages = new_pages;
            update popped = Popped::Used(page_id, b);
        }
    }

    transition!{
        set_range_to_not_used() {
            require let Popped::Used(page_id, b) = pre.popped;
            assert pre.pages.dom().contains(page_id);
            assert pre.pages[page_id].count.is_some();
            let count = pre.pages[page_id].count.unwrap();
            assert count > 0;
            assert pre.pages[page_id].offset == Some(0nat);
            assert pre.pages[page_id].full.is_none();

            assert (forall |pid: PageId| pid.segment_id == page_id.segment_id &&
                    page_id.idx <= pid.idx < page_id.idx + count
                    ==> pre.pages.dom().contains(pid)
                );
            assert (forall |pid: PageId| pid.segment_id == page_id.segment_id &&
                    page_id.idx <= pid.idx < page_id.idx + count
                    ==> pre.pages[pid].is_used
                );
            assert (forall |pid: PageId| pid.segment_id == page_id.segment_id &&
                    page_id.idx <= pid.idx < page_id.idx + count
                    ==> pre.pages[pid].offset.is_some()
                        && pre.pages[pid].offset.unwrap() == pid.idx - page_id.idx
                );

            let changed_pages = pages_with_segment(page_id.segment_id, page_id.idx as int, page_id.idx + count as int, 
                |pid: PageId| PageData {
                    is_used: false,
                    page_header_kind: None,
                    offset: None,
                    count: None,
                    .. pre.pages[pid]
                }
            );

//             let i_changed_pages = IMap::new(
//                 |pid: PageId| pid.segment_id == page_id.segment_id &&
//                     page_id.idx <= pid.idx < page_id.idx + count,
//                 |pid: PageId| PageData {
//                     is_used: false,
//                     page_header_kind: None,
//                     offset: None,
//                     count: None,
//                     .. pre.pages[pid]
//                 }
//             );
//             assert( Set::congruent(changed_pages.dom(), i_changed_pages.dom()) );

            let new_pages = pre.pages.union_prefer_right(changed_pages);
            assert pre.pages.dom() =~= new_pages.dom();

            update pages = new_pages;
            update popped = Popped::VeryUnready(page_id.segment_id, page_id.idx as int, count as int, b);
        }
    }

    transition!{
        into_used_list(bin_idx: int) {
            require valid_bin_idx(bin_idx) || bin_idx == BIN_FULL;
            require let Popped::Used(page_id, tru) = pre.popped;
            require tru == true;

            assert pre.pages.dom().contains(page_id);
            assert pre.pages[page_id].page_header_kind.is_some();
            match pre.pages[page_id].page_header_kind.unwrap() {
                PageHeaderKind::Normal(i, bsize) => {
                    require((bin_idx != BIN_FULL ==> bin_idx == i)
                        && valid_bin_idx(i)
                        && bsize == crate::bin_sizes::size_of_bin(i)
                        && bsize <= MEDIUM_OBJ_SIZE_MAX);
                }
            }

            update used_dlist_headers[bin_idx] = DlistHeader {
                first: Some(page_id),
                last:
                    if pre.used_dlist_headers[bin_idx].first.is_some() {
                        pre.used_dlist_headers[bin_idx].last
                    } else {
                        Some(page_id)
                    },
            };
            if pre.used_dlist_headers[bin_idx].first.is_some() {
                let first_id = pre.used_dlist_headers[bin_idx].first.unwrap();
                assert pre.pages.dom().contains(first_id);
                assert pre.pages[first_id].is_used;
                assert pre.pages[first_id].dlist_entry.is_some()
                    by { pre.first_last_ll_stuff_used(bin_idx); };
                assert first_id != page_id;
                update pages[first_id] = PageData {
                    dlist_entry: Some(DlistEntry {
                        prev: Some(page_id),
                        .. pre.pages[first_id].dlist_entry.unwrap()
                    }),
                    .. pre.pages[first_id]
                };
            }

            assert pre.pages.dom().contains(page_id);
            assert pre.pages[page_id].is_used;
            assert pre.pages[page_id].offset == Some(0nat);
            assert pre.pages[page_id].dlist_entry.is_none();

            update pages[page_id] = PageData {
                dlist_entry: Some(DlistEntry {
                    prev: None,
                    next: pre.used_dlist_headers[bin_idx].first,
                }),
                full: Some(bin_idx == BIN_FULL),
                .. pre.pages[page_id]
            };

            update popped = Popped::No;
            update used_lists = Self::insert_front(pre.used_lists, bin_idx, page_id);
        }
    }

    transition!{
        into_used_list_back(bin_idx: int) {
            require valid_bin_idx(bin_idx) || bin_idx == BIN_FULL;
            require let Popped::Used(page_id, tru) = pre.popped;
            require tru == true;

            assert pre.pages.dom().contains(page_id);
            assert pre.pages[page_id].page_header_kind.is_some();
            match pre.pages[page_id].page_header_kind.unwrap() {
                PageHeaderKind::Normal(i, bsize) => {
                    require((bin_idx != BIN_FULL ==> bin_idx == i)
                        && valid_bin_idx(i)
                        && bsize == crate::bin_sizes::size_of_bin(i)
                        && bsize <= MEDIUM_OBJ_SIZE_MAX);
                }
            }

            assert pre.used_dlist_headers[bin_idx].last.is_some()
                <==> pre.used_dlist_headers[bin_idx].first.is_some()

                by { pre.first_last_ll_stuff_used(bin_idx); };

            update used_dlist_headers[bin_idx] = DlistHeader {
                first:
                    if pre.used_dlist_headers[bin_idx].last.is_some() {
                        pre.used_dlist_headers[bin_idx].first
                    } else {
                        Some(page_id)
                    },
                last: Some(page_id),
            };
            if pre.used_dlist_headers[bin_idx].last.is_some() {
                let last_id = pre.used_dlist_headers[bin_idx].last.unwrap();
                assert pre.pages.dom().contains(last_id)
                    && pre.pages[last_id].is_used
                    && pre.pages[last_id].dlist_entry.is_some()
                    && last_id != page_id

                    by { pre.first_last_ll_stuff_used(bin_idx); };

                update pages[last_id] = PageData {
                    dlist_entry: Some(DlistEntry {
                        next: Some(page_id),
                        .. pre.pages[last_id].dlist_entry.unwrap()
                    }),
                    .. pre.pages[last_id]
                };
            }

            assert pre.pages.dom().contains(page_id);
            assert pre.pages[page_id].is_used;
            assert pre.pages[page_id].offset == Some(0nat);
            assert pre.pages[page_id].dlist_entry.is_none();

            update pages[page_id] = PageData {
                dlist_entry: Some(DlistEntry {
                    prev: pre.used_dlist_headers[bin_idx].last,
                    next: None,
                }),
                full: Some(bin_idx == BIN_FULL),
                .. pre.pages[page_id]
            };

            update popped = Popped::No;
            update used_lists = Self::insert_back(pre.used_lists, bin_idx, page_id);
        }
    }

    transition!{
        out_of_used_list(page_id: PageId, bin_idx: int, list_idx: int) {
            require pre.popped == Popped::No;
            require pre.valid_used_page(page_id, bin_idx, list_idx);

            assert pre.pages[page_id].dlist_entry.is_some();
            let prev_page_id_opt = pre.pages[page_id].dlist_entry.unwrap().prev;
            let next_page_id_opt = pre.pages[page_id].dlist_entry.unwrap().next;

            assert prev_page_id_opt != Some(page_id)
                && next_page_id_opt != Some(page_id)
                && prev_page_id_opt.is_some() ==> prev_page_id_opt != next_page_id_opt

                by { pre.used_ll_stuff(bin_idx, list_idx); };

            match prev_page_id_opt {
                Option::Some(prev_page_id) => {
                    assert pre.pages.dom().contains(prev_page_id)
                        && pre.pages[prev_page_id].dlist_entry.is_some()
                        && pre.pages[prev_page_id].is_used

                      by { pre.used_ll_stuff(bin_idx, list_idx); };

                    update pages[prev_page_id] = PageData {
                        dlist_entry: Some(DlistEntry {
                            next: next_page_id_opt,
                            .. pre.pages[prev_page_id].dlist_entry.unwrap()
                        }),
                        .. pre.pages[prev_page_id]
                    };
                }
                Option::None => { }
            }

            match next_page_id_opt {
                Option::Some(next_page_id) => {
                    assert pre.pages.dom().contains(next_page_id)
                        && pre.pages[next_page_id].dlist_entry.is_some()
                        && pre.pages[next_page_id].is_used

                      by { pre.used_ll_stuff(bin_idx, list_idx); };

                    update pages[next_page_id] = PageData {
                        dlist_entry: Some(DlistEntry {
                            prev: prev_page_id_opt,
                            .. pre.pages[next_page_id].dlist_entry.unwrap()
                        }),
                        .. pre.pages[next_page_id]
                    };
                }
                Option::None => { }
            }

            update used_dlist_headers[bin_idx] = DlistHeader {
                first: if prev_page_id_opt.is_some() {
                    pre.used_dlist_headers[bin_idx].first // no change
                } else {
                    next_page_id_opt
                },
                last: if next_page_id_opt.is_some() {
                    pre.used_dlist_headers[bin_idx].last // no change
                } else {
                    prev_page_id_opt
                }
            };

            update pages[page_id] = PageData {
                full: None,
                dlist_entry: None,
                .. pre.pages[page_id]
            };

            update popped = Popped::Used(page_id, true);
            update used_lists[bin_idx] = pre.used_lists[bin_idx].remove(list_idx);
        }
    }

    transition!{
        segment_freeing_start(segment_id: SegmentId) {
            require let Popped::No = pre.popped;
            require pre.segments.dom().contains(segment_id);
            require pre.segments[segment_id].used == 0;

            let page_id = PageId { segment_id, idx: 0 };
            assert pre.pages.dom().contains(page_id);
            assert pre.pages[page_id].count.is_some();
            let count = pre.pages[page_id].count.unwrap();
            assert 1 <= count <= SLICES_PER_SEGMENT;

            let last_id = PageId { segment_id, idx: (count - 1) as nat };

            let new_page_map = pages_with_segment(page_id.segment_id, 0, count as int,
                |page_id: PageId| PageData {
                    dlist_entry: None,
                    count: None,
                    offset: None,
                    is_used: false,
                    full: None,
                    page_header_kind: None,
                }
            );

            update pages = pre.pages.union_prefer_right(new_page_map);

            update popped = Popped::SegmentFreeing(segment_id, count as int);
        }
    }

    transition!{
        segment_freeing_finish() {
            require let Popped::SegmentFreeing(segment_id, idx) = pre.popped;
            require idx == SLICES_PER_SEGMENT;
            assert pre.segments.dom().contains(segment_id);
            update segments = pre.segments.remove(segment_id);
            update popped = Popped::No;

            let keys = keys_with_segment(segment_id, 0, SLICES_PER_SEGMENT+1);
//             let keys = Set::int_range(0, SLICES_PER_SEGMENT+1)
//                 .map(|idx: int| PageId{ segment_id, idx: idx as nat });
//             let i_keys = ISet::<PageId>::new(
//                 |page_id: PageId| page_id.segment_id == segment_id && 0 <= page_id.idx <= SLICES_PER_SEGMENT);
//             assert( Set::congruent(keys, i_keys) );

            update pages = pre.pages.remove_keys(keys);
        }
    }


    transition!{
        merge_with_after() {
            require let Popped::VeryUnready(segment_id, cur_start, cur_count, b) = pre.popped;

            require cur_start + cur_count < SLICES_PER_SEGMENT;
            let page_id = PageId { segment_id, idx: (cur_start + cur_count) as nat };
            assert pre.pages.dom().contains(page_id);
            require !pre.pages[page_id].is_used;
            assert pre.pages[page_id].count.is_some()
                by { pre.get_stuff_after(); };
            let n_count = pre.pages[page_id].count.unwrap();
            assert cur_count + n_count <= SLICES_PER_SEGMENT
                by { pre.get_stuff_after(); };


            assert pre.pages[page_id].dlist_entry.is_some()
                by { pre.get_stuff_after(); };

            assert let Some(dlist_entry) = pre.pages[page_id].dlist_entry;

            update pages[page_id] = PageData {
              offset: None,
              count: None,
              dlist_entry: None,
              .. pre.pages[page_id]
            };
            let final_id = PageId { segment_id, idx: (cur_start + cur_count + n_count - 1) as nat };
            assert pre.pages.dom().contains(final_id)      by { pre.get_stuff_after(); };
            update pages[final_id] = PageData {
              offset: None,
              count: None,
              dlist_entry: None,
              .. pre.pages[final_id]
            };
            assert !pre.pages[final_id].is_used

                    by { pre.lemma_range_not_used(page_id);
                        assert(pre.pages.dom().contains(final_id)); };

            match dlist_entry.prev {
                Some(prev_page_id) => {
                    assert prev_page_id != page_id
                        && pre.pages.dom().contains(prev_page_id)
                        && pre.pages[prev_page_id].dlist_entry.is_some()
                        && pre.pages[prev_page_id].is_used == false

                    by { let (i, j) = pre.get_stuff_after(); pre.unused_ll_stuff(i, j); };

                    update pages[prev_page_id] = PageData {
                        dlist_entry: Some(DlistEntry {
                            next: dlist_entry.next,
                            .. pre.pages[prev_page_id].dlist_entry.unwrap()
                        }),
                        .. pre.pages[prev_page_id]
                    };
                }
                Option::None => { }
            }

            match dlist_entry.next {
                Some(next_page_id) => {
                    assert next_page_id != page_id
                        && pre.pages.dom().contains(next_page_id)
                        && pre.pages[next_page_id].dlist_entry.is_some()
                        && pre.pages[next_page_id].is_used == false

                    by { let (i, j) = pre.get_stuff_after(); pre.unused_ll_stuff(i, j); };

                    update pages[next_page_id] = PageData {
                        dlist_entry: Some(DlistEntry {
                            prev: dlist_entry.prev,
                            .. pre.pages[next_page_id].dlist_entry.unwrap()
                        }),
                        .. pre.pages[next_page_id]
                    };
                }
                Option::None => { }
            }

            let sbin_idx = smallest_sbin_fitting_size(n_count as int);
            assert 0 <= sbin_idx <= SEGMENT_BIN_MAX
                by { crate::bin_sizes::valid_sbin_idx_smallest_sbin_fitting_size(n_count as int); };

            update unused_dlist_headers[sbin_idx] = DlistHeader {
                first: if dlist_entry.prev.is_none() {
                    dlist_entry.next
                } else {
                    pre.unused_dlist_headers[sbin_idx].first
                },
                last: if dlist_entry.next.is_none() {
                    dlist_entry.prev
                } else {
                    pre.unused_dlist_headers[sbin_idx].last
                }
            };

            assert dlist_entry.prev.is_some() && dlist_entry.next.is_some() ==>
                dlist_entry.prev.unwrap() != dlist_entry.next.unwrap()

                by { let (i, j) = pre.get_stuff_after(); pre.unused_ll_stuff(i, j); };

            update popped = Popped::VeryUnready(segment_id, cur_start, (cur_count + n_count) as int, b);

            let list_idx = Self::get_list_idx(pre.unused_lists, page_id).1;
            update unused_lists[sbin_idx] = pre.unused_lists[sbin_idx].remove(list_idx);
        }
    }

    transition!{
        merge_with_before() {
            require let Popped::VeryUnready(segment_id, cur_start, cur_count, b) = pre.popped;

            require cur_start > 1;
            let last_id = PageId { segment_id, idx: (cur_start - 1) as nat };
            assert pre.pages[last_id].offset.is_some()    by { pre.get_stuff_before(); };
            let offset = pre.pages[last_id].offset.unwrap();
            require last_id.idx - offset > 0; // exclude very first page
            let page_id = PageId { segment_id, idx: (last_id.idx - offset) as nat };
            require !pre.pages[page_id].is_used;
            assert !pre.pages[last_id].is_used            by { pre.get_stuff_before(); };

            assert pre.pages[page_id].count.is_some()     by { pre.get_stuff_before(); };
            let p_count = pre.pages[page_id].count.unwrap();
            assert cur_count + p_count <= SLICES_PER_SEGMENT
                by { pre.get_stuff_before(); };

            assert pre.pages.dom().contains(PageId { segment_id, idx: cur_start as nat });
            assert pre.pages[PageId { segment_id, idx: cur_start as nat }].offset.is_none();
            assert pre.pages[PageId { segment_id, idx: cur_start as nat }].is_used == false;

            assert pre.pages[page_id].dlist_entry.is_some()
                by { pre.get_stuff_before(); };

            assert let Some(dlist_entry) = pre.pages[page_id].dlist_entry;

            update pages[page_id] = PageData {
              offset: None,
              count: None,
              dlist_entry: None,
              .. pre.pages[page_id]
            };
            assert pre.pages.dom().contains(last_id)      by { pre.get_stuff_after(); };
            update pages[last_id] = PageData {
              offset: None,
              count: None,
              dlist_entry: None,
              .. pre.pages[last_id]
            };

            match dlist_entry.prev {
                Some(prev_page_id) => {
                    assert prev_page_id != page_id
                        && pre.pages.dom().contains(prev_page_id)
                        && pre.pages[prev_page_id].dlist_entry.is_some()
                        && pre.pages[prev_page_id].is_used == false
                        && prev_page_id != last_id
                        by { let (i, j) = pre.get_stuff_before(); pre.unused_ll_stuff(i, j); };

                    update pages[prev_page_id] = PageData {
                        dlist_entry: Some(DlistEntry {
                            next: dlist_entry.next,
                            .. pre.pages[prev_page_id].dlist_entry.unwrap()
                        }),
                        .. pre.pages[prev_page_id]
                    };
                }
                Option::None => { }
            }

            match dlist_entry.next {
                Some(next_page_id) => {
                    assert next_page_id != page_id
                        && pre.pages.dom().contains(next_page_id)
                        && pre.pages[next_page_id].dlist_entry.is_some()
                        && pre.pages[next_page_id].is_used == false
                        && next_page_id != last_id
                        by { let (i, j) = pre.get_stuff_before(); pre.unused_ll_stuff(i, j); };

                    update pages[next_page_id] = PageData {
                        dlist_entry: Some(DlistEntry {
                            prev: dlist_entry.prev,
                            .. pre.pages[next_page_id].dlist_entry.unwrap()
                        }),
                        .. pre.pages[next_page_id]
                    };
                }
                Option::None => { }
            }

            let sbin_idx = smallest_sbin_fitting_size(p_count as int);

            assert 0 <= sbin_idx <= SEGMENT_BIN_MAX
                by { crate::bin_sizes::valid_sbin_idx_smallest_sbin_fitting_size(p_count as int); };

            update unused_dlist_headers[sbin_idx] = DlistHeader {
                first: if dlist_entry.prev.is_none() {
                    dlist_entry.next
                } else {
                    pre.unused_dlist_headers[sbin_idx].first
                },
                last: if dlist_entry.next.is_none() {
                    dlist_entry.prev
                } else {
                    pre.unused_dlist_headers[sbin_idx].last
                }
            };

            assert dlist_entry.prev.is_some() && dlist_entry.next.is_some() ==>
                dlist_entry.prev.unwrap() != dlist_entry.next.unwrap()

                by { let (i, j) = pre.get_stuff_before(); pre.unused_ll_stuff(i, j); };

            update popped = Popped::VeryUnready(segment_id,
                  page_id.idx as int, (cur_count + p_count) as int, b);

            let list_idx = Self::get_list_idx(pre.unused_lists, page_id).1;
            update unused_lists[sbin_idx] = pre.unused_lists[sbin_idx].remove(list_idx);
        }
    }

    #[inductive(take_page_from_unused_queue)]
    #[verifier::spinoff_prover]
    fn take_page_from_unused_queue_inductive(pre: Self, post: Self, page_id: PageId, sbin_idx: int, list_idx: int) {
        pre.unused_ll_stuff(sbin_idx, list_idx);
        pre.lemma_range_not_used(page_id);

        assert(post.popped_basics());

        //Self::ucount_preserve_except(pre, post, page_id.segment_id);
        Self::ucount_preserve_all(pre, post);
        assert(post.count_is_right());
        Self::unchanged_used_ll(pre, post);

        let dlist_entry = pre.pages[page_id].dlist_entry.unwrap();

        
        Self::take_page_from_unused_queue_ll_inv_valid_unused(pre, post, page_id, sbin_idx, list_idx);
        Self::take_page_from_unused_queue_inductive_attached_ranges(pre, post, page_id, sbin_idx, list_idx);
        Self::take_page_from_unused_queue_inductive_unusedinv2(pre, post, page_id, sbin_idx, list_idx);
        Self::ll_inv_exists_take_page_from_unused_queue(pre, post, page_id, sbin_idx, list_idx);
    }

    #[verifier::spinoff_prover]
    pub proof fn take_page_from_unused_queue_ll_inv_valid_unused(pre: Self, post: Self, page_id: PageId, sbin_idx: int, list_idx: int)
        requires pre.invariant(),
            State::take_page_from_unused_queue_strong(pre, post, page_id, sbin_idx, list_idx),
        ensures
            post.ll_inv_valid_unused()
    {
        pre.unused_ll_stuff(sbin_idx, list_idx);

        let dlist_entry = pre.pages[page_id].dlist_entry.unwrap();
        assert forall |i| 0 <= i < post.unused_lists.len() implies valid_ll(post.pages, post.unused_dlist_headers[i], post.unused_lists[i])
        by {
            assert(valid_ll(pre.pages, pre.unused_dlist_headers[i], pre.unused_lists[i]));
            assert(valid_ll_i(pre.pages, pre.unused_lists[sbin_idx], list_idx));
            let pre_ll = pre.unused_lists[i];
            let ll = post.unused_lists[i];
            if i == sbin_idx {
                assert(list_idx < pre_ll.len());
                assert forall |j| 0 <= j < ll.len() implies valid_ll_i(post.pages, ll, j)
                by {
                    if j < list_idx {
                        pre.ll_unused_distinct(i, j, i, list_idx);
                        assert(ll[j] != page_id);
                        match dlist_entry.prev {
                            Some(pid) => {
                                if j < list_idx - 1 {
                                    pre.ll_unused_distinct(i, j, i, list_idx - 1);
                                    assert(ll[j] != pid);
                                }
                            }
                            None => { }
                        }
                        match dlist_entry.next {
                            Some(pid) => {
                                pre.ll_unused_distinct(i, j, i, list_idx + 1);
                                assert(ll[j] != pid);
                            }
                            None => { }
                        }
                        assert(valid_ll_i(pre.pages, pre_ll, j));
                        if j < list_idx - 1 {
                            assert(valid_ll_i(post.pages, ll, j));
                        } else {
                            assert(j == list_idx - 1);
                            if list_idx == pre_ll.len() - 1 {
                                assert(valid_ll_i(post.pages, ll, j));
                            } else {
                                assert(post.pages[ll[j]].dlist_entry.unwrap().next == get_next(ll, j));
                                assert(valid_ll_i(post.pages, ll, j));
                            }
                        }
                    } else {
                        pre.ll_unused_distinct(i, j+1, i, list_idx);
                        assert(ll[j] != page_id);
                        match dlist_entry.prev {
                            Some(pid) => {
                                pre.ll_unused_distinct(i, j+1, sbin_idx, list_idx - 1);
                                assert(ll[j] != pid);
                            }
                            None => { }
                        }
                        match dlist_entry.next {
                            Some(pid) => {
                                if j > list_idx {
                                    pre.ll_unused_distinct(i, j+1, sbin_idx, list_idx + 1);
                                    assert(ll[j] != pid);
                                }
                            }
                            None => { }
                        }
                        assert(valid_ll_i(pre.pages, pre_ll, j + 1));
                        if j > list_idx {
                            assert(valid_ll_i(post.pages, ll, j));
                        } else {
                            assert(valid_ll_i(post.pages, ll, j));
                        }
                    }
                }
                assert(valid_ll(post.pages, post.unused_dlist_headers[i], post.unused_lists[i]));
            } else {
                assert forall |j| 0 <= j < ll.len() implies valid_ll_i(post.pages, ll, j)
                by {
                    pre.ll_unused_distinct(i, j, sbin_idx, list_idx);
                    match dlist_entry.prev {
                        Some(pid) => {
                            pre.ll_unused_distinct(i, j, sbin_idx, list_idx - 1);
                            assert(ll[j] != pid);
                        }
                        None => { }
                    }
                    match dlist_entry.next {
                        Some(pid) => {
                            pre.ll_unused_distinct(i, j, sbin_idx, list_idx + 1);
                            assert(ll[j] != pid);
                        }
                        None => { }
                    }
                    assert(valid_ll_i(pre.pages, ll, j));
                }
                assert(valid_ll(post.pages, post.unused_dlist_headers[i], post.unused_lists[i]));
            }
        }
    }

    #[verifier::spinoff_prover]
    pub proof fn take_page_from_unused_queue_inductive_attached_ranges(
        pre: Self, post: Self, page_id: PageId, sbin_idx: int, list_idx: int
    )
        requires pre.invariant(),
          State::take_page_from_unused_queue_strong(pre, post, page_id, sbin_idx, list_idx),
        ensures post.attached_ranges()
    {
        pre.unused_ll_stuff(sbin_idx, list_idx);
        pre.lemma_range_not_used(page_id);

        let segment_id = page_id.segment_id;
        Self::attached_ranges_except(pre, post, segment_id);
        if pre.popped.is_No() {
            assert(post.good_range0(segment_id));
            Self::rec_take_page_from_unused_queue(pre, post, page_id, sbin_idx, list_idx,
                pre.pages[PageId { segment_id, idx: 0 }].count.unwrap() as int);
            //assert(post.attached_ranges());
        } else {
            reveal(State::attached_rec);
            assert(pre.attached_rec(segment_id,
                page_id.idx + pre.pages[page_id].count.unwrap() as int,
                false));
            /*assert forall |pid: PageId|
                //(pre.pages.dom().contains(pid) <==> post.pages.dom().contains(pid))
                pre.pages.dom().contains(pid) &&
                    !pre.in_popped_range(pid) implies ({
                    &&& post.pages.dom().contains(pid)
                    &&& pre.pages[pid].count == post.pages[pid].count
                    &&& pre.pages[pid].dlist_entry.is_some() <==> post.pages[pid].dlist_entry.is_some()
                    &&& pre.pages[pid].offset == post.pages[pid].offset
                    &&& pre.pages[pid].is_used == post.pages[pid].is_used
                    &&& pre.pages[pid].full == post.pages[pid].full
                    &&& pre.pages[pid].page_header_kind == post.pages[pid].page_header_kind
                  })
            by {
            }*/
            Self::attached_rec_same(pre, post, segment_id,
                page_id.idx + pre.pages[page_id].count.unwrap() as int,
                false);
            assert(post.attached_rec(segment_id,
                page_id.idx + pre.pages[page_id].count.unwrap() as int,
                false));
            /*assert(post.popped.get_SegmentFreeing_0() == segment_id);
            assert(post.popped.get_SegmentFreeing_1() == 
                page_id.idx + pre.pages[page_id].count.unwrap() as int);
            assert(post.popped.get_SegmentFreeing_1() > 0);
            assert(post.attached_ranges());*/
        }
    }

    #[verifier::spinoff_prover]
    pub proof fn take_page_from_unused_queue_inductive_unusedinv2(
        pre: Self, post: Self, page_id: PageId, sbin_idx: int, list_idx: int
    )
        requires pre.invariant(),
          State::take_page_from_unused_queue_strong(pre, post, page_id, sbin_idx, list_idx),
        ensures post.ll_inv_valid_unused2()
    {
        pre.lemma_range_not_used(page_id);
        assert forall |i, j| 0 <= i < post.unused_lists.len() &&
          0 <= j < post.unused_lists[i].len() implies
              post.pages.dom().contains(post.unused_lists[i][j])
              && is_unused_header(post.pages[post.unused_lists[i][j]])
              && post.unused_lists[i][j].idx != 0
        by {
            if i == sbin_idx && j >= list_idx {
                pre.ll_unused_distinct(i, j+1, sbin_idx, list_idx);
                assert(post.unused_lists[i][j] != page_id);
            } else {
                pre.ll_unused_distinct(i, j, sbin_idx, list_idx);
                assert(post.unused_lists[i][j] != page_id);
            }
        }
    }

    pub proof fn ll_inv_exists_take_page_from_unused_queue(pre: Self, post: Self, page_id: PageId, sbin_idx: int, list_idx: int)
      requires
          0 <= sbin_idx < pre.unused_lists.len(),
          0 <= list_idx < pre.unused_lists[sbin_idx].len(),
          pre.ll_inv_exists_in_some_list(),
          //post.expect_out_of_lists(page_id),
          State::take_page_from_unused_queue_strong(pre, post, page_id, sbin_idx, list_idx),
      ensures
          post.ll_inv_exists_in_some_list(),
    {
        Self::ll_remove(pre.unused_lists, post.unused_lists, sbin_idx, list_idx);
        reveal(State::ll_inv_exists_in_some_list);
        //assert(forall |pid| pid != page_id && is_in_lls(pid, pre.unused_lists) ==> is_in_lls(pid, post.unused_lists));
    }

    #[verifier::spinoff_prover]
    pub proof fn rec_take_page_from_unused_queue(pre: Self, post: Self, pid: PageId, sbin_idx: int, list_idx: int, idx: int)
      requires pre.invariant(),
          State::take_page_from_unused_queue_strong(pre, post, pid, sbin_idx, list_idx),
          pre.attached_rec(pid.segment_id, idx, false),
          pre.popped.is_No(),
          idx >= 0,
          pid.idx < SLICES_PER_SEGMENT,
      ensures
          post.attached_rec(pid.segment_id, idx, idx <= pid.idx)
      decreases SLICES_PER_SEGMENT - idx
    {
        reveal(State::attached_rec);
        let segment_id = pid.segment_id;
        let page_id = PageId { segment_id, idx: idx as nat };
        assert(pid.idx < SLICES_PER_SEGMENT);
        if idx == SLICES_PER_SEGMENT {
            assert(post.attached_rec(pid.segment_id, idx, idx <= pid.idx));
        } else if idx > SLICES_PER_SEGMENT {
            assert(false);
        } else if Self::is_the_popped(segment_id, idx, post.popped) {
            Self::rec_take_page_from_unused_queue(pre, post, pid, sbin_idx, list_idx, idx + post.popped_len());
            assert(post.attached_rec(pid.segment_id, idx, idx <= pid.idx));
        } else {
            Self::rec_take_page_from_unused_queue(pre, post, pid, sbin_idx, list_idx, idx + pre.pages[page_id].count.unwrap());
            pre.lemma_range_not_used(pid);
            //assert(post.popped.is_Popped());
            //assert(post.popped.get_Popped_0() == pid);
            //assert(!(post.popped.get_Popped_0().segment_id == pid.segment_id && post.popped.get_Popped_0().idx == idx));
            //assert(!(post.popped.get_Popped_0().segment_id == page_id.segment_id && post.popped.get_Popped_0().idx == page_id.idx));
            //assert(post.popped.get_Popped_0() != page_id);
            //pre.good_range_disjoint_two(page_id, pid);
            //assert(pre.good_range_unused(page_id));
            //assert(post.good_range_unused(page_id));
            //assert(post.attached_rec(pid.segment_id, idx, idx <= pid.idx));
            /*assert(pre.good_range_unused(page_id));
            pre.good_range_disjoint_very_unready(page_id);
            assert(post.good_range_unused(page_id));
            assert(post.attached_rec(pre.popped.get_VeryUnready_0(), idx, false));*/
        }
    }

    #[verifier::spinoff_prover]
    #[inductive(split_page)]
    fn split_page_inductive(pre: Self, post: Self, page_id: PageId, current_count: int, target_count: int, sbin_idx: int) {
        Self::ucount_preserve_all(pre, post);
        Self::unchanged_used_ll(pre, post);

        pre.first_last_ll_stuff_unused(sbin_idx);

        let next_page_id = PageId { idx: (page_id.idx + target_count) as nat, .. page_id };
        let last_page_id = PageId { idx: (page_id.idx + current_count - 1) as nat, .. page_id };
        assert(page_id != next_page_id);
        assert(page_id != last_page_id);

        if pre.unused_dlist_headers[sbin_idx].first.is_some() {
            assert(pre.unused_dlist_headers[sbin_idx].first.unwrap()
                != next_page_id);
            assert(pre.unused_dlist_headers[sbin_idx].first.unwrap()
                != last_page_id);
            assert(pre.unused_dlist_headers[sbin_idx].first.unwrap()
                != page_id);
        }

        //assert(post.pages[page_id].offset == Some(0nat));
        //assert(post.pages[page_id].count.is_some());
        //assert(post.pages[next_page_id].offset.is_some());
        //assert(post.pages[next_page_id].count.is_some());
        //assert(post.pages[last_page_id].offset.is_some());
        //assert(post.pages[last_page_id].count.is_none());

        if last_page_id != next_page_id {
            assert(pre.pages[last_page_id].count.is_none());
            assert(post.pages[last_page_id].count.is_none());
        }

        /*assert forall |pid: PageId|
            #[trigger] post.pages.dom().contains(pid) implies
            (post.pages[pid].count.is_some() <==> post.pages[pid].offset == Some(0nat))
        by {
            if post.pages[pid].count.is_some() {
                if pid == page_id {
                    assert(pre.pages[pid].count.is_none());
                    assert(post.pages[pid].offset == Some(0nat));
                } else if pid == next_page_id {
                    assert(post.pages[pid].offset == Some(0nat));
                } else if pid == last_page_id {
                    if last_page_id == next_page_id {
                        assert(post.pages[pid].offset == Some(0nat));
                    } else {
                        assert(post.pages[pid].offset == Some(0nat));
                    }
                } else if Some(pid) == pre.unused_dlist_headers[sbin_idx].first {
                    assert(post.pages[pid].offset == Some(0nat));
                } else {
                    assert(post.pages[pid].offset == Some(0nat));
                }
            }
            if post.pages[pid].offset == Some(0nat) {
                assert(post.pages[pid].count.is_some());
            }
        }*/

        let queue_first_page_id = pre.unused_dlist_headers[sbin_idx].first;

        assert forall |i| 0 <= i < post.unused_lists.len() implies valid_ll(post.pages, post.unused_dlist_headers[i], post.unused_lists[i])
        by {
            assert(valid_ll(pre.pages, pre.unused_dlist_headers[i], pre.unused_lists[i]));
            let pre_ll = pre.unused_lists[i];
            let ll = post.unused_lists[i];
            if i == sbin_idx {
                assert forall |j| 0 <= j < ll.len() implies valid_ll_i(post.pages, ll, j)
                by {
                    if j == 0 {
                        assert(valid_ll_i(post.pages, ll, j));
                    } else {
                        if j > 1 {
                            assert(ll[j-1] != next_page_id);
                        }
                        assert(valid_ll_i(pre.pages, pre_ll, j-1));
                        if j == 1 {
                            assert(valid_ll_i(post.pages, ll, j));
                        } else {
                            pre.ll_unused_distinct(i, j-1, i, 0);
                            assert(ll[j] != ll[1]);
                            assert(valid_ll_i(post.pages, ll, j));
                        }
                    }
                }
                assert(valid_ll(post.pages, post.unused_dlist_headers[i], post.unused_lists[i]));
            } else {
                assert forall |j| 0 <= j < ll.len() implies valid_ll_i(post.pages, ll, j)
                by {
                    assert(ll[j] != next_page_id);
                    match queue_first_page_id {
                        Some(pid) => {
                            pre.ll_unused_distinct(i, j, sbin_idx, 0);
                            assert(ll[j] != pid);
                        }
                        None => { }
                    }
                    assert(valid_ll_i(pre.pages, ll, j));
                }
                assert(valid_ll(post.pages, post.unused_dlist_headers[i], post.unused_lists[i]));
            }
        }

        assert(post.ll_inv_exists_in_some_list()) by {
            reveal(State::ll_inv_exists_in_some_list);
            assert(post.unused_lists[sbin_idx][0] == next_page_id);
            Self::ll_mono(pre.unused_lists, sbin_idx, next_page_id);
        }

        assert(post.attached_ranges()) by {
            let segment_id = pre.popped.get_VeryUnready_0();
            Self::attached_ranges_except(pre, post, segment_id);
            assert(post.good_range0(segment_id));
            Self::rec_split_page(pre, post, page_id, current_count, target_count, sbin_idx, 
                pre.pages[PageId { segment_id, idx: 0 }].count.unwrap() as int, true);
        }
    }

    pub proof fn rec_split_page(pre: Self, post: Self, pid: PageId, current_count: int, target_count: int, sbin_idx: int, idx: int, sp: bool)
      requires pre.invariant(),
          State::split_page_strong(pre, post, pid, current_count, target_count, sbin_idx),
          pre.attached_rec(pre.popped.get_VeryUnready_0(), idx, sp)
      ensures
          post.attached_rec(pre.popped.get_VeryUnready_0(), idx, sp)
      decreases SLICES_PER_SEGMENT - idx
    {
        reveal(State::attached_rec);
        let segment_id = pre.popped.get_VeryUnready_0();
        let page_id = PageId { segment_id, idx: idx as nat };
        if idx == SLICES_PER_SEGMENT {
            assert(post.attached_rec(pre.popped.get_VeryUnready_0(), idx, sp));
        } else if idx > SLICES_PER_SEGMENT {
            assert(false);
        } else if Self::is_the_popped(segment_id, idx, pre.popped) {
            Self::rec_split_page(pre, post, pid, current_count, target_count, sbin_idx, idx + pre.popped_len(), false);
            assert(post.attached_rec(pre.popped.get_VeryUnready_0(), idx + post.popped_len(), false));
            assert(post.attached_rec(pre.popped.get_VeryUnready_0(), idx, sp));
        } else {
            Self::rec_split_page(pre, post, pid, current_count, target_count, sbin_idx, idx + pre.pages[page_id].count.unwrap(), sp);
            pre.good_range_disjoint_very_unready(page_id);
            assert(post.attached_rec(pre.popped.get_VeryUnready_0(), idx, sp));
        }
    }

   
    #[inductive(allocate_popped)]
    fn allocate_popped_inductive(pre: Self, post: Self) {
        broadcast use pages_with_segment_ensures;
        Self::ucount_preserve_all(pre, post);
        Self::unchanged_used_ll(pre, post);
        Self::unchanged_unused_ll(pre, post);
        //let page_id = pre.popped.get_Popped_0();
        /*assert forall |pid: PageId|
                    pid.segment_id == page_id.segment_id
                      && page_id.idx <= pid.idx < page_id.idx + post.pages[page_id].count.unwrap()
                    &&
                        post.pages.dom().contains(pid) implies
                        !(#[trigger] post.pages[pid]).is_used
                        && post.pages[pid].offset == Some((pid.idx - page_id.idx) as nat)
                        && (post.pages[pid].count.is_some() <==> pid == page_id)
                        && post.pages[pid].page_header_kind.is_none()
                        && post.pages[pid].dlist_entry.is_none()
                        && post.pages[pid].full.is_none()
        by { }*/
        assert(post.inv_ready());

        assert(post.ll_inv_exists_in_some_list()) by {
            reveal(State::ll_inv_exists_in_some_list);
        }

        Self::attached_ranges_all(pre, post);
    }
  
    #[inductive(set_range_to_used)]
    fn set_range_to_used_inductive(pre: Self, post: Self, page_header_kind: PageHeaderKind) {
        broadcast use pages_with_segment_ensures;
        let page_id = post.popped.get_Used_0();
        let segment_id = page_id.segment_id;
        Self::unchanged_used_ll(pre, post);
        Self::unchanged_unused_ll(pre, post);
        Self::ucount_inc1(pre, post, page_id);
        Self::ucount_preserve_except(pre, post, segment_id);

        assert(post.ll_inv_exists_in_some_list()) by {
            reveal(State::ll_inv_exists_in_some_list);
        }
        Self::attached_ranges_all(pre, post);

        assert forall |i: int, j: int| 0 <= i < post.unused_lists.len()
            && 0 <= j < post.unused_lists[i].len() implies post.unused_lists[i][j] != page_id
        by {
            assert(valid_ll(pre.pages, pre.unused_dlist_headers[i], pre.unused_lists[i]));
            assert(valid_ll_i(pre.pages, pre.unused_lists[i], j));
        }
    }

    #[inductive(set_range_to_not_used)]
    fn set_range_to_not_used_inductive(pre: Self, post: Self) {
        broadcast use pages_with_segment_ensures;
        let page_id = pre.popped.get_Used_0();
        let segment_id = page_id.segment_id;

        Self::unchanged_used_ll(pre, post);
        Self::unchanged_unused_ll(pre, post);
        Self::ucount_dec1(pre, post, page_id);
        Self::ucount_preserve_except(pre, post, segment_id);

        assert(post.ll_inv_exists_in_some_list()) by {
            reveal(State::ll_inv_exists_in_some_list);
        }
        Self::attached_ranges_all(pre, post);

        assert forall |i: int, j: int| 0 <= i < post.unused_lists.len()
            && 0 <= j < post.unused_lists[i].len() implies post.unused_lists[i][j] != page_id
        by {
            assert(valid_ll(pre.pages, pre.unused_dlist_headers[i], pre.unused_lists[i]));
            assert(valid_ll_i(pre.pages, pre.unused_lists[i], j));
        }
    }

    #[verifier::spinoff_prover]
    #[inductive(into_used_list)]
    fn into_used_list_inductive(pre: Self, post: Self, bin_idx: int) {
        Self::ucount_preserve_all(pre, post);
        Self::unchanged_unused_ll(pre, post);

        let page_id = pre.popped.get_Used_0();
        let segment_id = page_id.segment_id;
        let queue_first_page_id = pre.used_dlist_headers[bin_idx].first;

        assert forall |i| 0 <= i < post.used_lists.len() implies valid_ll(post.pages, post.used_dlist_headers[i], post.used_lists[i])
        by {
            assert(valid_ll(pre.pages, pre.used_dlist_headers[i], pre.used_lists[i]));
            let pre_ll = pre.used_lists[i];
            let ll = post.used_lists[i];
            if i == bin_idx {
                assert forall |j| 0 <= j < ll.len() implies valid_ll_i(post.pages, ll, j)
                by {
                    if j == 0 {
                        assert(valid_ll_i(post.pages, ll, j));
                    } else {
                        if j > 1 {
                            assert(ll[j-1] != page_id);
                        }
                        assert(valid_ll_i(pre.pages, pre_ll, j-1));
                        if j == 1 {
                            assert(valid_ll_i(post.pages, ll, j));
                        } else {
                            pre.ll_used_distinct(i, j-1, i, 0);
                            assert(ll[j] != ll[1]);
                            assert(valid_ll_i(post.pages, ll, j));
                        }
                    }
                }
                assert(valid_ll(post.pages, post.used_dlist_headers[i], post.used_lists[i]));
            } else {
                assert forall |j| 0 <= j < ll.len() implies valid_ll_i(post.pages, ll, j)
                by {
                    assert(ll[j] != page_id);
                    match queue_first_page_id {
                        Some(pid) => {
                            pre.ll_used_distinct(i, j, bin_idx, 0);
                            assert(ll[j] != pid);
                        }
                        None => { }
                    }
                    assert(valid_ll_i(pre.pages, ll, j));
                }
                assert(valid_ll(post.pages, post.used_dlist_headers[i], post.used_lists[i]));
            }
        }

        assert(valid_bin_idx(bin_idx) || bin_idx == BIN_FULL);

        /*assert forall |i, j| 0 <= i < post.used_lists.len()
            && 0 <= j < post.used_lists[i].len() implies
              post.pages.dom().contains(#[trigger] post.used_lists[i][j])
              && is_used_header(post.pages[post.used_lists[i][j]])
              && post.used_lists[i][j].idx != 0
              && post.pages[post.used_lists[i][j]].full.is_some()
              && (post.pages[post.used_lists[i][j]].full.unwrap() <==> i == BIN_FULL)
              && (match post.pages[post.used_lists[i][j]].page_header_kind {
                  None => false,
                  Some(PageHeaderKind::Normal(bsize)) => i != BIN_FULL ==>
                      valid_bin_idx(i) &&
                      bsize == crate::bin_sizes::size_of_bin(i)
              })
        by {
        }*/

        assert(post.attached_ranges()) by {
            Self::attached_ranges_except(pre, post, segment_id);
            Self::rec_into_used_list(pre, post, bin_idx, 
                pre.pages[PageId { segment_id, idx: 0 }].count.unwrap() as int, true);
        }

        assert(post.ll_inv_exists_in_some_list()) by {
            reveal(State::ll_inv_exists_in_some_list);
            assert(post.used_lists[bin_idx][0] == page_id);
            Self::ll_mono(pre.used_lists, bin_idx, page_id);
        }
    }

    pub proof fn rec_into_used_list(pre: Self, post: Self, bin_idx: int, idx: int, sp: bool)
      requires pre.invariant(),
          State::into_used_list_strong(pre, post, bin_idx)
            || State::into_used_list_back_strong(pre, post, bin_idx),
          pre.attached_rec(pre.popped.get_Used_0().segment_id, idx, sp)
      ensures
          post.attached_rec(pre.popped.get_Used_0().segment_id, idx, false)
      decreases SLICES_PER_SEGMENT - idx
    {
        reveal(State::attached_rec);
        let segment_id = pre.popped.get_Used_0().segment_id;
        let page_id = PageId { segment_id, idx: idx as nat };
        if idx == SLICES_PER_SEGMENT {
            assert(post.attached_rec(segment_id, idx, false));
        } else if idx > SLICES_PER_SEGMENT {
            assert(false);
        } else if Self::is_the_popped(segment_id, idx, pre.popped) {
            Self::rec_into_used_list(pre, post, bin_idx, idx + pre.popped_len(), false);
            assert(post.attached_rec(segment_id, idx, false));
        } else {
            Self::rec_into_used_list(pre, post, bin_idx, idx + pre.pages[page_id].count.unwrap(), sp);
            //pre.good_range_disjoint_very_unready(page_id);
            assert(post.attached_rec(segment_id, idx, false));
        }
    }


    #[inductive(create_segment)]
    fn create_segment_inductive(pre: Self, post: Self, segment_id: SegmentId) {
        Self::ucount_preserve_all(pre, post);
        post.ucount_eq0(segment_id);

        Self::unchanged_used_ll(pre, post);
        Self::unchanged_unused_ll(pre, post);

        assert(post.attached_ranges()) by {
            reveal_with_fuel(State::attached_rec);
            assert(post.attached_ranges_segment(segment_id));
            Self::attached_ranges_except(pre, post, segment_id);
        }

        reveal(State::ll_inv_exists_in_some_list);

        broadcast use pages_with_segment_ensures;
//         pages_with_segment_ensures(segment_id, 0, SLICES_PER_SEGMENT+1,
//                 |page_id: PageId| PageData {
//                     dlist_entry: None,
//                     count: None,
//                     offset: None,
//                     is_used: false,
//                     page_header_kind: None,
//                     full: None,
//                 });
    }
   
    #[inductive(forget_about_first_page)]
    fn forget_about_first_page_inductive(pre: Self, post: Self, count: int) {
        broadcast use pages_with_segment_ensures;
        let segment_id = pre.popped.get_SegmentCreating_0();
        let page_id = PageId { segment_id, idx: count as nat };
        assert(post.good_range_very_unready(page_id));
        assert(post.popped_basics());
        Self::ucount_preserve_all(pre, post);
        assert(post.count_is_right());
        Self::unchanged_used_ll(pre, post);
        Self::unchanged_unused_ll(pre, post);
        assert(post.attached_ranges()) by {
            reveal_with_fuel(State::attached_rec);
            let page_id = PageId { segment_id, idx: 0 };
            /*assert forall |pid: PageId|
              pid.segment_id == page_id.segment_id
              && page_id.idx <= pid.idx < page_id.idx + count implies
                post.pages.dom().contains(pid)
                && post.pages[pid].is_used == false
                && post.pages[pid].full.is_none()
                && post.pages[pid].page_header_kind.is_none()
                && (post.pages[pid].count.is_some() <==> pid == page_id)
                && post.pages[pid].dlist_entry.is_none()
                && post.pages[pid].offset == 
                            Some((pid.idx - page_id.idx) as nat)
            by {
            }*/
            assert(post.good_range0(segment_id));
            assert(post.popped_for_seg(segment_id));

            assert(count + post.popped_len() == SLICES_PER_SEGMENT);

            assert(post.attached_rec(segment_id, SLICES_PER_SEGMENT as int, false));
            assert(post.attached_rec(segment_id, count, true));
            assert(post.attached_rec0(segment_id, true));
            assert(post.attached_ranges_segment(segment_id));

            Self::attached_ranges_except(pre, post, segment_id);
        }

        reveal(State::ll_inv_exists_in_some_list);
    }

    #[verifier::spinoff_prover]
    #[inductive(free_to_unused_queue)]
    fn free_to_unused_queue_inductive(pre: Self, post: Self, sbin_idx: int) {
        let segment_id = pre.popped.get_VeryUnready_0();
        let start = pre.popped.get_VeryUnready_1();
        let count = pre.popped.get_VeryUnready_2();
        let first_page = PageId { segment_id, idx: start as nat };
        let last_page = PageId { segment_id, idx: (first_page.idx + count - 1) as nat };
        let queue_first_page_id = pre.unused_dlist_headers[sbin_idx].first;

        Self::ucount_preserve_all(pre, post);
        Self::unchanged_used_ll(pre, post);
        assert forall |i| 0 <= i < post.unused_lists.len() implies valid_ll(post.pages, post.unused_dlist_headers[i], post.unused_lists[i])
        by {
            assert(valid_ll(pre.pages, pre.unused_dlist_headers[i], pre.unused_lists[i]));
            let pre_ll = pre.unused_lists[i];
            let ll = post.unused_lists[i];
            if i == sbin_idx {
                assert forall |j| 0 <= j < ll.len() implies valid_ll_i(post.pages, ll, j)
                by {
                    if j == 0 {
                        assert(valid_ll_i(post.pages, ll, j));
                    } else {
                        if j > 1 {
                            assert(ll[j-1] != first_page);
                        }
                        assert(valid_ll_i(pre.pages, pre_ll, j-1));
                        if j == 1 {
                            assert(valid_ll_i(post.pages, ll, j));
                        } else {
                            pre.ll_unused_distinct(i, j-1, i, 0);
                            assert(ll[j] != ll[1]);
                            assert(valid_ll_i(post.pages, ll, j));
                        }
                    }
                }
                assert(valid_ll(post.pages, post.unused_dlist_headers[i], post.unused_lists[i]));
            } else {
                assert forall |j| 0 <= j < ll.len() implies valid_ll_i(post.pages, ll, j)
                by {
                    assert(ll[j] != first_page);
                    match queue_first_page_id {
                        Some(pid) => {
                            pre.ll_unused_distinct(i, j, sbin_idx, 0);
                            assert(ll[j] != pid);
                        }
                        None => { }
                    }
                    assert(valid_ll_i(pre.pages, ll, j));
                }
                assert(valid_ll(post.pages, post.unused_dlist_headers[i], post.unused_lists[i]));
            }
        }

        assert(post.ll_inv_exists_in_some_list()) by {
            reveal(State::ll_inv_exists_in_some_list);
            assert(post.unused_lists[sbin_idx][0] == first_page);
            Self::ll_mono(pre.unused_lists, sbin_idx, first_page);
        }

        assert(post.attached_ranges()) by {
            Self::attached_ranges_except(pre, post, segment_id);
            assert(post.good_range0(segment_id));
            Self::rec_free_to_unused_queue(pre, post, sbin_idx, 
                pre.pages[PageId { segment_id, idx: 0 }].count.unwrap() as int, true);
        }
    }

    #[verifier::spinoff_prover]
    pub proof fn rec_free_to_unused_queue(pre: Self, post: Self, sbin_idx: int, idx: int, sp: bool)
      requires pre.invariant(),
          State::free_to_unused_queue_strong(pre, post, sbin_idx),
          pre.attached_rec(pre.popped.get_VeryUnready_0(), idx, sp)
      ensures
          post.attached_rec(pre.popped.get_VeryUnready_0(), idx, false)
      decreases SLICES_PER_SEGMENT - idx
    {
        reveal(State::attached_rec);
        let segment_id = pre.popped.get_VeryUnready_0();
        let page_id = PageId { segment_id, idx: idx as nat };
        if idx == SLICES_PER_SEGMENT {
            assert(post.attached_rec(pre.popped.get_VeryUnready_0(), idx, false));
        } else if idx > SLICES_PER_SEGMENT {
            assert(false);
        } else if Self::is_the_popped(segment_id, idx, pre.popped) {
            Self::rec_free_to_unused_queue(pre, post, sbin_idx, idx + pre.popped_len(), false);
            /*assert(pre.good_range_very_unready(page_id));
            let count = post.pages[page_id].count.unwrap();
            assert forall |pid: PageId|
              pid.segment_id == page_id.segment_id
              && page_id.idx <= pid.idx < page_id.idx + count implies
                post.pages.dom().contains(pid)
                && post.pages[pid].is_used == false
                && post.pages[pid].full.is_none()
                && post.pages[pid].page_header_kind.is_none()
                && (post.pages[pid].count.is_some() <==> pid == page_id)
                && (post.pages[pid].dlist_entry.is_some() <==> pid == page_id)
                && post.pages[pid].offset == (if pid == page_id || pid == (PageId { segment_id: page_id.segment_id, idx: (page_id.idx + post.pages[page_id].count.unwrap() - 1) as nat }) {
                            Some((pid.idx - page_id.idx) as nat)
                        } else {
                            None
                        })
            by {
                if pid == page_id {
                    assert(post.pages[pid].offset == Some(0nat));
                } else if pid == (PageId { segment_id: page_id.segment_id, idx: (page_id.idx + post.pages[page_id].count.unwrap() - 1) as nat }) {
                    //assert(post.pages[pid].offset ==
                    //        Some((pid.idx - page_id.idx) as nat));
                } else {
                    assert(post.pages[pid].offset.is_none());
                }
            }
            assert(post.good_range_unused(page_id));*/
            assert(post.attached_rec(pre.popped.get_VeryUnready_0(), idx, false));
        } else {
            Self::rec_free_to_unused_queue(pre, post, sbin_idx, idx + pre.pages[page_id].count.unwrap(), sp);
            pre.good_range_disjoint_very_unready(page_id);
            assert(post.attached_rec(pre.popped.get_VeryUnready_0(), idx, false));
        }
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self) {
        reveal(State::ll_inv_exists_in_some_list);
    }

    #[verifier::spinoff_prover]
    #[inductive(out_of_used_list)]
    fn out_of_used_list_inductive(pre: Self, post: Self, page_id: PageId, bin_idx: int, list_idx: int) {
        pre.used_ll_stuff(bin_idx, list_idx);
        pre.lemma_range_used(page_id);
        Self::ucount_preserve_all(pre, post);
        Self::unchanged_unused_ll(pre, post);

        let dlist_entry = pre.pages[page_id].dlist_entry.unwrap();

        assert forall |i| 0 <= i < post.used_lists.len() implies valid_ll(post.pages, post.used_dlist_headers[i], post.used_lists[i])
        by {
            assert(valid_ll(pre.pages, pre.used_dlist_headers[i], pre.used_lists[i]));
            assert(valid_ll_i(pre.pages, pre.used_lists[bin_idx], list_idx));
            let pre_ll = pre.used_lists[i];
            let ll = post.used_lists[i];
            if i == bin_idx {
                assert(list_idx < pre_ll.len());
                assert forall |j| 0 <= j < ll.len() implies valid_ll_i(post.pages, ll, j)
                by {
                    if j < list_idx {
                        pre.ll_used_distinct(i, j, i, list_idx);
                        assert(ll[j] != page_id);
                        match dlist_entry.prev {
                            Some(pid) => {
                                if j < list_idx - 1 {
                                    pre.ll_used_distinct(i, j, i, list_idx - 1);
                                    assert(ll[j] != pid);
                                }
                            }
                            None => { }
                        }
                        match dlist_entry.next {
                            Some(pid) => {
                                pre.ll_used_distinct(i, j, i, list_idx + 1);
                                assert(ll[j] != pid);
                            }
                            None => { }
                        }
                        assert(valid_ll_i(pre.pages, pre_ll, j));
                        if j < list_idx - 1 {
                            assert(valid_ll_i(post.pages, ll, j));
                        } else {
                            assert(j == list_idx - 1);
                            if list_idx == pre_ll.len() - 1 {
                                assert(valid_ll_i(post.pages, ll, j));
                            } else {
                                assert(post.pages[ll[j]].dlist_entry.unwrap().next == get_next(ll, j));
                                assert(valid_ll_i(post.pages, ll, j));
                            }
                        }
                    } else {
                        pre.ll_used_distinct(i, j+1, i, list_idx);
                        assert(ll[j] != page_id);
                        match dlist_entry.prev {
                            Some(pid) => {
                                pre.ll_used_distinct(i, j+1, bin_idx, list_idx - 1);
                                assert(ll[j] != pid);
                            }
                            None => { }
                        }
                        match dlist_entry.next {
                            Some(pid) => {
                                if j > list_idx {
                                    pre.ll_used_distinct(i, j+1, bin_idx, list_idx + 1);
                                    assert(ll[j] != pid);
                                }
                            }
                            None => { }
                        }
                        assert(valid_ll_i(pre.pages, pre_ll, j + 1));
                        if j > list_idx {
                            assert(valid_ll_i(post.pages, ll, j));
                        } else {
                            assert(valid_ll_i(post.pages, ll, j));
                        }
                    }
                }
                assert(valid_ll(post.pages, post.used_dlist_headers[i], post.used_lists[i]));
            } else {
                assert forall |j| 0 <= j < ll.len() implies valid_ll_i(post.pages, ll, j)
                by {
                    pre.ll_used_distinct(i, j, bin_idx, list_idx);
                    match dlist_entry.prev {
                        Some(pid) => {
                            pre.ll_used_distinct(i, j, bin_idx, list_idx - 1);
                            assert(ll[j] != pid);
                        }
                        None => { }
                    }
                    match dlist_entry.next {
                        Some(pid) => {
                            pre.ll_used_distinct(i, j, bin_idx, list_idx + 1);
                            assert(ll[j] != pid);
                        }
                        None => { }
                    }
                    assert(valid_ll_i(pre.pages, ll, j));
                }
                assert(valid_ll(post.pages, post.used_dlist_headers[i], post.used_lists[i]));
            }
        }

        State::out_of_used_list_inductive_ll_inv_valid_used2(pre, post, page_id, bin_idx, list_idx);
        State::out_of_used_list_inductive_ll_inv_exists_in_some_list(pre, post, page_id, bin_idx, list_idx);
        State::out_of_used_list_inductive_attached_ranges(pre, post, page_id, bin_idx, list_idx);
    }

    proof fn out_of_used_list_inductive_ll_inv_valid_used2(pre: Self, post: Self, page_id: PageId, bin_idx: int, list_idx: int)
        requires pre.invariant(),
          State::out_of_used_list_strong(pre, post, page_id, bin_idx, list_idx)
        ensures
          post.ll_inv_valid_used2(),
    {
        pre.lemma_range_used(page_id);
        assert forall |i, j| 0 <= i < post.used_lists.len() &&
          0 <= j < post.used_lists[i].len() implies
              post.pages.dom().contains(post.used_lists[i][j])
              && is_used_header(post.pages[post.used_lists[i][j]])
              && post.used_lists[i][j].idx != 0
              && post.pages[post.used_lists[i][j]].full.is_some()
        by {
            if i == bin_idx && j >= list_idx {
                pre.ll_used_distinct(i, j+1, bin_idx, list_idx);
                assert(post.used_lists[i][j] != page_id);
            } else {
                pre.ll_used_distinct(i, j, bin_idx, list_idx);
                assert(post.used_lists[i][j] != page_id);
            }
        }
    }

    proof fn out_of_used_list_inductive_ll_inv_exists_in_some_list(pre: Self, post: Self, page_id: PageId, bin_idx: int, list_idx: int)
        requires pre.invariant(),
          State::out_of_used_list_strong(pre, post, page_id, bin_idx, list_idx)
        ensures
          post.ll_inv_exists_in_some_list(),
    {
        Self::ll_remove(pre.used_lists, post.used_lists, bin_idx, list_idx);
        reveal(State::ll_inv_exists_in_some_list);
    }

    proof fn out_of_used_list_inductive_attached_ranges(pre: Self, post: Self, page_id: PageId, bin_idx: int, list_idx: int)
        requires pre.invariant(),
          State::out_of_used_list_strong(pre, post, page_id, bin_idx, list_idx)
        ensures
          post.attached_ranges(),
    {
        pre.used_ll_stuff(bin_idx, list_idx);
        pre.lemma_range_used(page_id);
        let segment_id = page_id.segment_id;
        Self::attached_ranges_except(pre, post, segment_id);
          Self::rec_out_of_used_list(pre, post, page_id, bin_idx, list_idx,
              pre.pages[PageId { segment_id, idx: 0 }].count.unwrap() as int);
    }

    pub proof fn rec_out_of_used_list(pre: Self, post: Self, pid: PageId, bin_idx: int, list_idx: int, idx: int)
      requires pre.invariant(),
          State::out_of_used_list_strong(pre, post, pid, bin_idx, list_idx),
          pre.attached_rec(pid.segment_id, idx, false),
          idx >= 0,
          pid.idx < SLICES_PER_SEGMENT,
      ensures
          post.attached_rec(pid.segment_id, idx, idx <= pid.idx)
      decreases SLICES_PER_SEGMENT - idx
    {
        reveal(State::attached_rec);
        let segment_id = pid.segment_id;
        let page_id = PageId { segment_id, idx: idx as nat };
        assert(pid.idx < SLICES_PER_SEGMENT);
        if idx == SLICES_PER_SEGMENT {
            assert(post.attached_rec(pid.segment_id, idx, idx <= pid.idx));
        } else if idx > SLICES_PER_SEGMENT {
            assert(false);
        } else if Self::is_the_popped(segment_id, idx, post.popped) {
            Self::rec_out_of_used_list(pre, post, pid, bin_idx, list_idx, idx + post.popped_len());
            assert(post.attached_rec(pid.segment_id, idx, idx <= pid.idx));
        } else {
            Self::rec_out_of_used_list(pre, post, pid, bin_idx, list_idx, idx + pre.pages[page_id].count.unwrap());
            pre.lemma_range_used(pid);
        }
    }

    #[inductive(merge_with_after)]
    #[verifier::spinoff_prover]
    fn merge_with_after_inductive(pre: Self, post: Self) {
        let segment_id = pre.popped.get_VeryUnready_0();
        let cur_start = pre.popped.get_VeryUnready_1();
        let cur_count = pre.popped.get_VeryUnready_2();
        let cur_id = PageId { segment_id, idx: cur_start as nat };
        let page_id = PageId { segment_id, idx: (cur_start + cur_count) as nat };
        pre.lemma_range_not_used(page_id);

        Self::ucount_preserve_all(pre, post);
        Self::unchanged_used_ll(pre, post);

        let count = post.popped.get_VeryUnready_2();
        /*assert(count == cur_count + pre.pages[page_id].count.unwrap());
        assert forall |pid: PageId|
              pid.segment_id == cur_id.segment_id
              && cur_id.idx <= pid.idx < cur_id.idx + count implies
                post.pages.dom().contains(pid)
                && post.pages[pid].is_used == false
                && post.pages[pid].full.is_none()
                && post.pages[pid].page_header_kind.is_none()
                && post.pages[pid].count.is_none()
                && post.pages[pid].dlist_entry.is_none()
                && post.pages[pid].offset.is_none()
        by {
            if page_id.idx <= pid.idx {
                assert(page_id.idx <= pid.idx < page_id.idx + pre.pages[page_id].count.unwrap());
                if page_id.idx == pid.idx {
                    assert(post.pages[pid].dlist_entry.is_none());
                } else {
                    assert(post.pages[pid].dlist_entry.is_none());
                }
            } else {
                assert(cur_id.idx <= pid.idx < cur_id.idx + cur_count);
                assert(post.pages[pid].dlist_entry.is_none());
            }
        }*/

        assert(post.good_range_very_unready(cur_id));
        assert(post.popped_basics());

        let n_count = pre.pages[page_id].count.unwrap();
        let sbin_idx = smallest_sbin_fitting_size(n_count as int);
        let list_idx = Self::get_list_idx(pre.unused_lists, page_id).1;
        pre.unused_is_in_sbin(page_id);
        //assert(0 <= sbin_idx < pre.unused_lists.len());
        //assert(0 <= list_idx < pre.unused_lists[sbin_idx].len());
        let dlist_entry = pre.pages[page_id].dlist_entry.unwrap();
        //let final_id = PageId { segment_id, idx: (cur_start + cur_count + n_count - 1) as nat };

        assert(post.attached_ranges()) by {
            Self::attached_ranges_except(pre, post, segment_id);
            assert(post.good_range0(segment_id));
            Self::rec_merge_with_after(pre, post,
                pre.pages[PageId { segment_id, idx: 0 }].count.unwrap() as int, true);
        }

        Self::ll_inv_exists_merge_with_after(pre, post, page_id, sbin_idx, list_idx);
        Self::merge_with_after_ll_inv_valid_unused(pre, post);

        assert forall |i, j| 0 <= i < post.unused_lists.len()
            && 0 <= j < post.unused_lists[i].len() implies
              post.pages.dom().contains(#[trigger] post.unused_lists[i][j])
              && is_unused_header(post.pages[post.unused_lists[i][j]])
              && post.unused_lists[i][j].idx != 0
        by {
            if i == sbin_idx && j >= list_idx {
                pre.ll_unused_distinct(i, j+1, sbin_idx, list_idx);
                assert(post.unused_lists[i][j] != page_id);
            } else {
                pre.ll_unused_distinct(i, j, sbin_idx, list_idx);
                assert(post.unused_lists[i][j] != page_id);
            }
            assert(is_unused_header(pre.pages[post.unused_lists[i][j]]));
        }
        assert(post.ll_inv_valid_unused2());
    }

    pub proof fn merge_with_after_ll_inv_valid_unused(pre: Self, post: Self)
        requires pre.invariant(),
            State::merge_with_after_strong(pre, post),
        ensures
            post.ll_inv_valid_unused()
    {
        let segment_id = pre.popped.get_VeryUnready_0();
        let cur_start = pre.popped.get_VeryUnready_1();
        let cur_count = pre.popped.get_VeryUnready_2();
        let page_id = PageId { segment_id, idx: (cur_start + cur_count) as nat };
        pre.lemma_range_not_used(page_id);
        let n_count = pre.pages[page_id].count.unwrap();
        let sbin_idx = smallest_sbin_fitting_size(n_count as int);
        let list_idx = Self::get_list_idx(pre.unused_lists, page_id).1;
        pre.unused_is_in_sbin(page_id);
        let dlist_entry = pre.pages[page_id].dlist_entry.unwrap();

        assert forall |i| 0 <= i < post.unused_lists.len() implies valid_ll(post.pages, post.unused_dlist_headers[i], post.unused_lists[i])
        by {
            assert(valid_ll(pre.pages, pre.unused_dlist_headers[i], pre.unused_lists[i]));
            assert(valid_ll_i(pre.pages, pre.unused_lists[sbin_idx], list_idx));
            let pre_ll = pre.unused_lists[i];
            let ll = post.unused_lists[i];
            if i == sbin_idx {
                assert(list_idx < pre_ll.len());
                assert forall |j| 0 <= j < ll.len() implies valid_ll_i(post.pages, ll, j)
                by {
                    if j < list_idx {
                        pre.ll_unused_distinct(i, j, i, list_idx);
                        assert(ll[j] != page_id);
                        match dlist_entry.prev {
                            Some(pid) => {
                                if j < list_idx - 1 {
                                    pre.ll_unused_distinct(i, j, i, list_idx - 1);
                                    assert(ll[j] != pid);
                                }
                            }
                            None => { }
                        }
                        match dlist_entry.next {
                            Some(pid) => {
                                pre.ll_unused_distinct(i, j, i, list_idx + 1);
                                assert(ll[j] != pid);
                            }
                            None => { }
                        }
                        assert(valid_ll_i(pre.pages, pre_ll, j));
                        if j < list_idx - 1 {
                            assert(valid_ll_i(post.pages, ll, j));
                        } else {
                            assert(j == list_idx - 1);
                            if list_idx == pre_ll.len() - 1 {
                                assert(valid_ll_i(post.pages, ll, j));
                            } else {
                                assert(post.pages[ll[j]].dlist_entry.unwrap().next == get_next(ll, j));
                                assert(valid_ll_i(post.pages, ll, j));
                            }
                        }
                    } else {
                        pre.ll_unused_distinct(i, j+1, i, list_idx);
                        assert(ll[j] != page_id);
                        match dlist_entry.prev {
                            Some(pid) => {
                                pre.ll_unused_distinct(i, j+1, sbin_idx, list_idx - 1);
                                assert(ll[j] != pid);
                            }
                            None => { }
                        }
                        match dlist_entry.next {
                            Some(pid) => {
                                if j > list_idx {
                                    pre.ll_unused_distinct(i, j+1, sbin_idx, list_idx + 1);
                                    assert(ll[j] != pid);
                                }
                            }
                            None => { }
                        }
                        assert(valid_ll_i(pre.pages, pre_ll, j + 1));
                        if j > list_idx {
                            assert(valid_ll_i(post.pages, ll, j));
                        } else {
                            assert(valid_ll_i(post.pages, ll, j));
                        }
                    }
                }
                assert(valid_ll(post.pages, post.unused_dlist_headers[i], post.unused_lists[i]));
            } else {
                assert forall |j| 0 <= j < ll.len() implies valid_ll_i(post.pages, ll, j)
                by {
                    pre.ll_unused_distinct(i, j, sbin_idx, list_idx);
                    match dlist_entry.prev {
                        Some(pid) => {
                            pre.ll_unused_distinct(i, j, sbin_idx, list_idx - 1);
                            assert(ll[j] != pid);
                        }
                        None => { }
                    }
                    match dlist_entry.next {
                        Some(pid) => {
                            pre.ll_unused_distinct(i, j, sbin_idx, list_idx + 1);
                            assert(ll[j] != pid);
                        }
                        None => { }
                    }
                    assert(valid_ll_i(pre.pages, ll, j));
                }
                assert(valid_ll(post.pages, post.unused_dlist_headers[i], post.unused_lists[i]));
            }
        }
    }

    pub proof fn sp_true_implies_le(&self, idx: int)
      requires self.invariant(),
          self.popped.is_VeryUnready(),
          self.attached_rec(self.popped.get_VeryUnready_0(), idx, true),
          idx >= 0,
      ensures
          idx <= self.popped.get_VeryUnready_1()
      decreases SLICES_PER_SEGMENT - idx
    {
        reveal(State::attached_rec);
        let segment_id = self.popped.get_VeryUnready_0();
        if idx == SLICES_PER_SEGMENT {
        } else if idx > SLICES_PER_SEGMENT {
        } else if Self::is_the_popped(segment_id, idx, self.popped) {
        } else {
            if idx > self.popped.get_VeryUnready_1() {
                let page_id = PageId { segment_id, idx: idx as nat };
                /*assert(self.pages[page_id].count.unwrap() > 0);
                assert(idx + self.pages[page_id].count.unwrap()
                    <= SLICES_PER_SEGMENT);*/
                self.sp_true_implies_le(idx + 
                    self.pages[page_id].count.unwrap());
            }
        }
    }

    #[verifier::spinoff_prover]
    pub proof fn rec_merge_with_after(pre: Self, post: Self, idx: int, sp: bool)
      requires pre.invariant(),
          State::merge_with_after_strong(pre, post),
          pre.attached_rec(pre.popped.get_VeryUnready_0(), idx, sp),
          idx >= 0,
          //sp ==> idx <= pre.popped.get_VeryUnready_1(),
          !sp ==> idx >= pre.popped.get_VeryUnready_1() + post.popped_len(),
      ensures
          post.attached_rec(pre.popped.get_VeryUnready_0(), idx, sp)
      decreases SLICES_PER_SEGMENT - idx
    {
        reveal(State::attached_rec);
        let segment_id = pre.popped.get_VeryUnready_0();
        let page_id = PageId { segment_id, idx: idx as nat };
        let pidx = pre.popped.get_VeryUnready_1() + pre.popped.get_VeryUnready_2();
        if idx == SLICES_PER_SEGMENT {
            assert(post.attached_rec(segment_id, idx, sp));
        } else if idx > SLICES_PER_SEGMENT {
            assert(false);
        } else if Self::is_the_popped(segment_id, idx, post.popped) {
            assert(pre.attached_rec(segment_id, idx + pre.popped_len(), false));
            Self::rec_merge_with_after(pre, post, idx + post.popped_len(), false);
            assert(post.attached_rec(pre.popped.get_VeryUnready_0(), idx, sp));
        } else {
            if sp {
                pre.sp_true_implies_le(idx);
            }
            assert(pidx >= 0);
            let pid = PageId { segment_id, idx: pidx as nat };
            let c = pre.pages[pid].count.unwrap();
            assert(pid.idx + c <= idx || idx + pre.pages[page_id].count.unwrap() <= pid.idx);
            pre.lemma_range_not_used(pid);
            Self::rec_merge_with_after(pre, post, idx + pre.pages[page_id].count.unwrap(), sp);
            assert(post.attached_rec(pre.popped.get_VeryUnready_0(), idx, sp));
        }
    }

    #[verifier::spinoff_prover]
    pub proof fn rec_merge_with_before(pre: Self, post: Self, idx: int, sp: bool)
      requires pre.invariant(),
          State::merge_with_before_strong(pre, post),
          pre.attached_rec(pre.popped.get_VeryUnready_0(), idx, sp),
          idx >= 0,
          //sp ==> idx <= pre.popped.get_VeryUnready_1(),
          idx != pre.popped.get_VeryUnready_1(),
          !sp ==> idx >= pre.popped.get_VeryUnready_1() + pre.popped_len(),
      ensures
          post.attached_rec(pre.popped.get_VeryUnready_0(), idx, sp)
      decreases SLICES_PER_SEGMENT - idx
    {
        let segment_id = pre.popped.get_VeryUnready_0();
        let cur_start = pre.popped.get_VeryUnready_1();
        let cur_count = pre.popped.get_VeryUnready_2();
        let last_id = PageId { segment_id, idx: (cur_start - 1) as nat };
        let offset = pre.pages[last_id].offset.unwrap();
        let first_id = PageId { segment_id, idx: (last_id.idx - offset) as nat };
        let p_count = pre.pages[first_id].count.unwrap();
        pre.get_stuff_before();

        reveal(State::attached_rec);
        let segment_id = pre.popped.get_VeryUnready_0();
        let page_id = PageId { segment_id, idx: idx as nat };
        let pidx = pre.popped.get_VeryUnready_1() + pre.popped.get_VeryUnready_2();
        if idx == SLICES_PER_SEGMENT {
            assert(post.attached_rec(segment_id, idx, sp));
        } else if idx > SLICES_PER_SEGMENT {
            assert(false);
        } else if Self::is_the_popped(segment_id, idx, pre.popped) {
            assert(false);
        } else {
            if idx + pre.pages[page_id].count.unwrap() == pre.popped.get_VeryUnready_1() {
                assert(pre.attached_rec(segment_id, idx + pre.pages[page_id].count.unwrap(), sp));
                Self::rec_merge_with_before(pre, post, pre.popped.get_VeryUnready_1() + pre.popped_len(), false);
                assert(post.attached_rec(segment_id, idx, sp));
            } else {
                Self::rec_merge_with_before(pre, post, idx + pre.pages[page_id].count.unwrap(), sp);
                //assert(pid.idx + c <= idx || idx + pre.pages[page_id].count.unwrap() <= pid.idx);
                if sp {
                    pre.sp_true_implies_le(idx);
                }
                assert(first_id.idx + p_count <= page_id.idx || page_id.idx + pre.pages[page_id].count.unwrap() <= first_id.idx);
                assert(post.attached_rec(segment_id, idx, sp));
            }
            /*
            if sp {
                pre.sp_true_implies_le(idx);
            }
            assert(pidx >= 0);
            let pid = PageId { segment_id, idx: pidx as nat };
            let c = pre.pages[pid].count.unwrap();
            assert(pid.idx + c <= idx || idx + pre.pages[page_id].count.unwrap() <= pid.idx);
            pre.lemma_range_not_used(pid);
            Self::rec_merge_with_after(pre, post, idx + pre.pages[page_id].count.unwrap(), sp);
            assert(post.attached_rec(pre.popped.get_VeryUnready_0(), idx, sp));
            */
        }
    }


    pub proof fn ll_inv_exists_merge_with_after(pre: Self, post: Self, page_id: PageId, sbin_idx: int, list_idx: int)
      requires
          0 <= sbin_idx < pre.unused_lists.len(),
          0 <= list_idx < pre.unused_lists[sbin_idx].len(),
          pre.ll_inv_exists_in_some_list(),
          post.pages[page_id].offset.is_none(),
          State::merge_with_after_strong(pre, post),
          ({
              let segment_id = pre.popped.get_VeryUnready_0();
              let cur_start = pre.popped.get_VeryUnready_1();
              let cur_count = pre.popped.get_VeryUnready_2();
              let cur_id = PageId { segment_id, idx: cur_start as nat };
              let n_count = pre.pages[page_id].count.unwrap();
              page_id == PageId { segment_id, idx: (cur_start + cur_count) as nat }
               && sbin_idx == smallest_sbin_fitting_size(n_count as int)
               && list_idx == Self::get_list_idx(pre.unused_lists, page_id).1
          }),
          page_id == pre.unused_lists[sbin_idx][list_idx],
      ensures
          post.ll_inv_exists_in_some_list(),
    {
        Self::ll_remove(pre.unused_lists, post.unused_lists, sbin_idx, list_idx);
        //assert(post.unused_lists ==
        //    pre.unused_lists.update(sbin_idx, pre.unused_lists[sbin_idx].remove(list_idx)));
        //assert(forall |pid| pid != page_id && is_in_lls(pid, pre.unused_lists) ==> is_in_lls(pid, post.unused_lists));
        reveal(State::ll_inv_exists_in_some_list);
        assert forall |pid: PageId| #[trigger] post.pages.dom().contains(pid)
            && post.pages[pid].offset == Some(0nat)
            && pid.idx != 0
            && !post.expect_out_of_lists(pid)
              implies is_in_lls(pid, post.used_lists) || is_in_lls(pid, post.unused_lists)
        by {
            if pid == page_id {
                assert(is_in_lls(pid, post.used_lists) || is_in_lls(pid, post.unused_lists));
            } else {
                assert(is_in_lls(pid, pre.used_lists) || is_in_lls(pid, pre.unused_lists));
                if is_in_lls(pid, pre.used_lists) {
                    assert(is_in_lls(pid, post.used_lists));
                } else {
                    assert(is_in_lls(pid, pre.unused_lists));
                    assert(is_in_lls(pid, post.unused_lists));
                }
            }
        }
    }

    pub proof fn ll_inv_exists_merge_with_before(pre: Self, post: Self, page_id: PageId, sbin_idx: int, list_idx: int)
      requires
          0 <= sbin_idx < pre.unused_lists.len(),
          0 <= list_idx < pre.unused_lists[sbin_idx].len(),
          pre.ll_inv_exists_in_some_list(),
          post.pages[page_id].offset.is_none(),
          State::merge_with_before_strong(pre, post),
          ({
              let segment_id = pre.popped.get_VeryUnready_0();
              let cur_start = pre.popped.get_VeryUnready_1();
              let cur_count = pre.popped.get_VeryUnready_2();
              let last_id = PageId { segment_id, idx: (cur_start - 1) as nat };
              let offset = pre.pages[last_id].offset.unwrap();
              let p_count = pre.pages[page_id].count.unwrap();
              page_id == PageId { segment_id, idx: (last_id.idx - offset) as nat }
               && sbin_idx == smallest_sbin_fitting_size(p_count as int)
               && list_idx == Self::get_list_idx(pre.unused_lists, page_id).1
          }),
          page_id == pre.unused_lists[sbin_idx][list_idx],
      ensures
          post.ll_inv_exists_in_some_list(),
    {
        Self::ll_remove(pre.unused_lists, post.unused_lists, sbin_idx, list_idx);
        //assert(post.unused_lists ==
        //    pre.unused_lists.update(sbin_idx, pre.unused_lists[sbin_idx].remove(list_idx)));
        //assert(forall |pid| pid != page_id && is_in_lls(pid, pre.unused_lists) ==> is_in_lls(pid, post.unused_lists));
        reveal(State::ll_inv_exists_in_some_list);
        assert forall |pid: PageId| #[trigger] post.pages.dom().contains(pid)
            && post.pages[pid].offset == Some(0nat)
            && pid.idx != 0
            && !post.expect_out_of_lists(pid)
              implies is_in_lls(pid, post.used_lists) || is_in_lls(pid, post.unused_lists)
        by {
            if pid == page_id {
                assert(is_in_lls(pid, post.used_lists) || is_in_lls(pid, post.unused_lists));
            } else {
                assert(is_in_lls(pid, pre.used_lists) || is_in_lls(pid, pre.unused_lists));
                if is_in_lls(pid, pre.used_lists) {
                    assert(is_in_lls(pid, post.used_lists));
                } else {
                    assert(is_in_lls(pid, pre.unused_lists));
                    assert(is_in_lls(pid, post.unused_lists));
                }
            }
        }
    }



    #[inductive(merge_with_before)]
    #[verifier::spinoff_prover]
    fn merge_with_before_inductive(pre: Self, post: Self) {
        let segment_id = pre.popped.get_VeryUnready_0();
        let cur_start = pre.popped.get_VeryUnready_1();
        let cur_count = pre.popped.get_VeryUnready_2();
        let last_id = PageId { segment_id, idx: (cur_start - 1) as nat };
        let offset = pre.pages[last_id].offset.unwrap();
        let page_id = PageId { segment_id, idx: (last_id.idx - offset) as nat };
        let p_count = pre.pages[page_id].count.unwrap();

        Self::ucount_preserve_all(pre, post);
        Self::unchanged_used_ll(pre, post);
        pre.get_stuff_before();
        pre.lemma_range_not_used(page_id);

        assert(post.popped_basics());
        let sbin_idx = smallest_sbin_fitting_size(p_count as int);
        let list_idx = Self::get_list_idx(pre.unused_lists, page_id).1;
        pre.unused_is_in_sbin(page_id);
        let dlist_entry = pre.pages[page_id].dlist_entry.unwrap();

        assert forall |i, j| 0 <= i < post.unused_lists.len()
            && 0 <= j < post.unused_lists[i].len() implies
              post.pages.dom().contains(#[trigger] post.unused_lists[i][j])
              && is_unused_header(post.pages[post.unused_lists[i][j]])
              && post.unused_lists[i][j].idx != 0
        by {
            if i == sbin_idx && j >= list_idx {
                pre.ll_unused_distinct(i, j+1, sbin_idx, list_idx);
                assert(post.unused_lists[i][j] != page_id);
            } else {
                pre.ll_unused_distinct(i, j, sbin_idx, list_idx);
                assert(post.unused_lists[i][j] != page_id);
            }
            assert(is_unused_header(pre.pages[post.unused_lists[i][j]]));
        }
        assert(post.ll_inv_valid_unused2());

        Self::merge_with_before_ll_inv_valid_unused(pre, post);
        Self::merge_with_before_inductive_attached_ranges(pre, post);
        Self::ll_inv_exists_merge_with_before(pre, post, page_id, sbin_idx, list_idx);
    }

    #[verifier::spinoff_prover]
    pub proof fn merge_with_before_ll_inv_valid_unused(pre: Self, post: Self)
        requires pre.invariant(),
            State::merge_with_before_strong(pre, post),
        ensures
            post.ll_inv_valid_unused()
    {
        let segment_id = pre.popped.get_VeryUnready_0();
        let cur_start = pre.popped.get_VeryUnready_1();
        let last_id = PageId { segment_id, idx: (cur_start - 1) as nat };
        let offset = pre.pages[last_id].offset.unwrap();
        let page_id = PageId { segment_id, idx: (last_id.idx - offset) as nat };
        let p_count = pre.pages[page_id].count.unwrap();
        let sbin_idx = smallest_sbin_fitting_size(p_count as int);
        let list_idx = Self::get_list_idx(pre.unused_lists, page_id).1;
        pre.unused_is_in_sbin(page_id);
        let dlist_entry = pre.pages[page_id].dlist_entry.unwrap();

        assert forall |i| 0 <= i < post.unused_lists.len() implies valid_ll(post.pages, post.unused_dlist_headers[i], post.unused_lists[i])
        by {
            assert(valid_ll(pre.pages, pre.unused_dlist_headers[i], pre.unused_lists[i]));
            assert(valid_ll_i(pre.pages, pre.unused_lists[sbin_idx], list_idx));
            let pre_ll = pre.unused_lists[i];
            let ll = post.unused_lists[i];
            if i == sbin_idx {
                assert(list_idx < pre_ll.len());
                assert forall |j| 0 <= j < ll.len() implies valid_ll_i(post.pages, ll, j)
                by {
                    if j < list_idx {
                        pre.ll_unused_distinct(i, j, i, list_idx);
                        assert(ll[j] != page_id);
                        match dlist_entry.prev {
                            Some(pid) => {
                                if j < list_idx - 1 {
                                    pre.ll_unused_distinct(i, j, i, list_idx - 1);
                                    assert(ll[j] != pid);
                                }
                            }
                            None => { }
                        }
                        match dlist_entry.next {
                            Some(pid) => {
                                pre.ll_unused_distinct(i, j, i, list_idx + 1);
                                assert(ll[j] != pid);
                            }
                            None => { }
                        }
                        assert(valid_ll_i(pre.pages, pre_ll, j));
                        if j < list_idx - 1 {
                            assert(valid_ll_i(post.pages, ll, j));
                        } else {
                            assert(j == list_idx - 1);
                            if list_idx == pre_ll.len() - 1 {
                                assert(valid_ll_i(post.pages, ll, j));
                            } else {
                                assert(post.pages[ll[j]].dlist_entry.unwrap().next == get_next(ll, j));
                                assert(valid_ll_i(post.pages, ll, j));
                            }
                        }
                    } else {
                        pre.ll_unused_distinct(i, j+1, i, list_idx);
                        assert(ll[j] != page_id);
                        match dlist_entry.prev {
                            Some(pid) => {
                                pre.ll_unused_distinct(i, j+1, sbin_idx, list_idx - 1);
                                assert(ll[j] != pid);
                            }
                            None => { }
                        }
                        match dlist_entry.next {
                            Some(pid) => {
                                if j > list_idx {
                                    pre.ll_unused_distinct(i, j+1, sbin_idx, list_idx + 1);
                                    assert(ll[j] != pid);
                                }
                            }
                            None => { }
                        }
                        assert(valid_ll_i(pre.pages, pre_ll, j + 1));
                        if j > list_idx {
                            assert(valid_ll_i(post.pages, ll, j));
                        } else {
                            assert(valid_ll_i(post.pages, ll, j));
                        }
                    }
                }
                assert(valid_ll(post.pages, post.unused_dlist_headers[i], post.unused_lists[i]));
            } else {
                assert forall |j| 0 <= j < ll.len() implies valid_ll_i(post.pages, ll, j)
                by {
                    pre.ll_unused_distinct(i, j, sbin_idx, list_idx);
                    match dlist_entry.prev {
                        Some(pid) => {
                            pre.ll_unused_distinct(i, j, sbin_idx, list_idx - 1);
                            assert(ll[j] != pid);
                        }
                        None => { }
                    }
                    match dlist_entry.next {
                        Some(pid) => {
                            pre.ll_unused_distinct(i, j, sbin_idx, list_idx + 1);
                            assert(ll[j] != pid);
                        }
                        None => { }
                    }
                    assert(valid_ll_i(pre.pages, ll, j));
                }
                assert(valid_ll(post.pages, post.unused_dlist_headers[i], post.unused_lists[i]));
            }
        }
    }

    pub proof fn merge_with_before_inductive_attached_ranges(
        pre: Self, post: Self,
    )
        requires pre.invariant(),
          State::merge_with_before_strong(pre, post),
        ensures post.attached_ranges()
    {
        let segment_id = pre.popped.get_VeryUnready_0();
        let cur_start = pre.popped.get_VeryUnready_1();
        let cur_count = pre.popped.get_VeryUnready_2();
        let last_id = PageId { segment_id, idx: (cur_start - 1) as nat };
        let offset = pre.pages[last_id].offset.unwrap();
        let page_id = PageId { segment_id, idx: (last_id.idx - offset) as nat };
        let p_count = pre.pages[page_id].count.unwrap();

        pre.get_stuff_before();
        pre.lemma_range_not_used(page_id);

        Self::attached_ranges_except(pre, post, segment_id);
        assert(post.good_range0(segment_id));
        Self::rec_merge_with_before(pre, post,
            pre.pages[PageId { segment_id, idx: 0 }].count.unwrap() as int, true);
    }

    #[inductive(segment_freeing_start)]
    fn segment_freeing_start_inductive(pre: Self, post: Self, segment_id: SegmentId) {
        broadcast use pages_with_segment_ensures;
        Self::ucount_preserve_all(pre, post);
        assert(post.popped_basics());
        Self::unchanged_unused_ll(pre, post);
        Self::unchanged_used_ll(pre, post);

        assert(post.ll_inv_exists_in_some_list()) by {
            reveal(State::ll_inv_exists_in_some_list);
        }

        assert(post.attached_ranges()) by {
            Self::attached_ranges_except(pre, post, segment_id);
            reveal(State::attached_rec);
            let page_id = PageId { segment_id, idx: 0 };
            Self::attached_rec_same(pre, post, segment_id,
                pre.pages[page_id].count.unwrap() as int,
                false);
        }
    }

    #[inductive(segment_freeing_finish)]
    fn segment_freeing_finish_inductive(pre: Self, post: Self) {
        broadcast use keys_with_segment_ensures;
        Self::ucount_preserve_all(pre, post);
        Self::unchanged_used_ll(pre, post);
        let segment_id = pre.popped.get_SegmentFreeing_0();
        Self::attached_ranges_except(pre, post, segment_id);
        assert(post.ll_inv_exists_in_some_list()) by {
            reveal(State::ll_inv_exists_in_some_list);
        }

        assert forall |i| 0 <= i < post.unused_lists.len()
            implies valid_ll(post.pages, post.unused_dlist_headers[i], post.unused_lists[i])
        by {
            let ll = post.unused_lists[i];
            assert forall |j| 0 <= j < ll.len() implies valid_ll_i(post.pages, ll, j)
            by {
                assert(valid_ll_i(pre.pages, pre.unused_lists[i], j));
            }
        }
    }

    #[verifier::spinoff_prover]
    #[inductive(into_used_list_back)]
    fn into_used_list_back_inductive(pre: Self, post: Self, bin_idx: int) {
        Self::ucount_preserve_all(pre, post);
        Self::unchanged_unused_ll(pre, post);

        let page_id = pre.popped.get_Used_0();
        let segment_id = page_id.segment_id;
        let queue_last_page_id = pre.used_dlist_headers[bin_idx].last;

        assert forall |i| 0 <= i < post.used_lists.len() implies valid_ll(post.pages, post.used_dlist_headers[i], post.used_lists[i])
        by {
            assert(valid_ll(pre.pages, pre.used_dlist_headers[i], pre.used_lists[i]));
            let pre_ll = pre.used_lists[i];
            let ll = post.used_lists[i];
            if i == bin_idx {
                assert forall |j| 0 <= j < ll.len() implies valid_ll_i(post.pages, ll, j)
                by {
                    if j == ll.len() - 1 {
                        assert(valid_ll_i(post.pages, ll, j));
                    } else {
                        if j < ll.len() - 2 {
                            assert(ll[j+1] != page_id);
                        }
                        assert(valid_ll_i(pre.pages, pre_ll, j));
                        if j == ll.len() - 2 {
                            assert(valid_ll_i(post.pages, ll, j));
                        } else {
                            pre.ll_used_distinct(i, j, i, pre_ll.len() - 1);
                            assert(ll[j] != ll[ll.len() - 2]);
                            assert(valid_ll_i(post.pages, ll, j));
                        }
                    }
                }
                assert(valid_ll(post.pages, post.used_dlist_headers[i], post.used_lists[i]));
            } else {
                assert forall |j| 0 <= j < ll.len() implies valid_ll_i(post.pages, ll, j)
                by {
                    assert(ll[j] != page_id);
                    match queue_last_page_id {
                        Some(pid) => {
                            pre.ll_used_distinct(i, j, bin_idx, pre.used_lists[bin_idx].len() - 1);
                            assert(ll[j] != pid);
                        }
                        None => { }
                    }
                    assert(valid_ll_i(pre.pages, ll, j));
                }
                assert(valid_ll(post.pages, post.used_dlist_headers[i], post.used_lists[i]));
            }
        }

        assert(valid_bin_idx(bin_idx) || bin_idx == BIN_FULL);

        assert(post.attached_ranges()) by {
            Self::attached_ranges_except(pre, post, segment_id);
            Self::rec_into_used_list(pre, post, bin_idx, 
                pre.pages[PageId { segment_id, idx: 0 }].count.unwrap() as int, true);
        }

        assert(post.ll_inv_exists_in_some_list()) by {
            reveal(State::ll_inv_exists_in_some_list);
            assert(post.used_lists[bin_idx][post.used_lists[bin_idx].len() - 1] == page_id);
            Self::ll_mono_back(pre.used_lists, bin_idx, page_id);
        }

        /*assert forall |i, j| 0 <= i < post.used_lists.len() ==>
          0 <= j < post.used_lists[i].len()
          implies
              post.pages.dom().contains(#[trigger] post.used_lists[i][j])
              && is_used_header(post.pages[post.used_lists[i][j]])
              && post.used_lists[i][j].idx != 0
              && post.pages[post.used_lists[i][j]].full.is_some()
              && (post.pages[post.used_lists[i][j]].full.unwrap() <==> i == BIN_FULL)
              && (match post.pages[post.used_lists[i][j]].page_header_kind {
                  None => false,
                  Some(PageHeaderKind::Normal(bin, bsize)) =>
                      valid_bin_idx(bin)
                        && bsize == crate::bin_sizes::size_of_bin(bin)
                        && (i != BIN_FULL ==> i == bin)
              })
        by {
        }*/
    }

    pub proof fn preserved_by_into_used_list_back(pre: Self, post: Self,
        bin_idx: int, other_page_id: PageId, other_bin_idx: int, other_list_idx: int)
        requires Self::into_used_list_back(pre, post, bin_idx),
            pre.invariant(),
            pre.valid_used_page(other_page_id, other_bin_idx, other_list_idx)
        ensures
            post.valid_used_page(other_page_id, other_bin_idx, other_list_idx)
    {
        pre.first_last_ll_stuff_used(bin_idx);
    }

    pub proof fn preserved_by_out_of_used_list(pre: Self, post: Self,
        page_id: PageId, bin_idx: int, list_idx: int,
        next_page_id: PageId)
        requires Self::out_of_used_list(pre, post, page_id, bin_idx, list_idx),
            pre.invariant(),
            pre.valid_used_page(next_page_id, bin_idx, list_idx + 1)
        ensures
            post.valid_used_page(next_page_id, bin_idx, list_idx)
    {
        pre.used_ll_stuff(bin_idx, list_idx);
        assert(valid_ll_i(pre.pages, pre.used_lists[bin_idx], list_idx));
        pre.ll_used_distinct(bin_idx, list_idx, bin_idx, list_idx + 1);
        assert(next_page_id != page_id);
        assert(post.pages[next_page_id].dlist_entry.is_Some());
    }

    #[inductive(forget_about_first_page2)]
    fn forget_about_first_page2_inductive(pre: Self, post: Self) {
        Self::ucount_preserve_all(pre, post);
        Self::attached_ranges_all(pre, post);
        assert(post.ll_inv_exists_in_some_list()) by {
            reveal(State::ll_inv_exists_in_some_list);
        }
    }

    #[inductive(clear_ec)]
    fn clear_ec_inductive(pre: Self, post: Self) {
        Self::ucount_preserve_all(pre, post);
        Self::attached_ranges_all(pre, post);
        assert(post.ll_inv_exists_in_some_list()) by {
            reveal(State::ll_inv_exists_in_some_list);
        }
    }

    pub proof fn used_ll_stuff(&self, i: int, j: int)
        requires self.invariant(),
            0 <= i < self.used_lists.len(),
            0 <= j < self.used_lists[i].len(),
        ensures
            self.pages.dom().contains(self.used_lists[i][j]),
            self.pages[self.used_lists[i][j]].is_used == true,
            self.pages[self.used_lists[i][j]].count.is_some(),
            self.pages[self.used_lists[i][j]].dlist_entry.is_some(),
            self.pages[self.used_lists[i][j]].dlist_entry.unwrap().prev != Some(self.used_lists[i][j]),
            self.pages[self.used_lists[i][j]].dlist_entry.unwrap().next != Some(self.used_lists[i][j]),
            self.pages[self.used_lists[i][j]].dlist_entry.unwrap().prev.is_some() ==>
                self.pages[self.used_lists[i][j]].dlist_entry.unwrap().prev != self.pages[self.used_lists[i][j]].dlist_entry.unwrap().next,

            self.pages[self.used_lists[i][j]].dlist_entry.unwrap().prev.is_some() ==>
                self.pages.dom().contains(self.pages[self.used_lists[i][j]].dlist_entry.unwrap().prev.unwrap())
                && self.pages[self.pages[self.used_lists[i][j]].dlist_entry.unwrap().prev.unwrap()].dlist_entry.is_some()
                && self.pages[self.pages[self.used_lists[i][j]].dlist_entry.unwrap().prev.unwrap()].is_used == true,
            self.pages[self.used_lists[i][j]].dlist_entry.unwrap().next.is_some() ==>
                self.pages.dom().contains(self.pages[self.used_lists[i][j]].dlist_entry.unwrap().next.unwrap())
                && self.pages[self.pages[self.used_lists[i][j]].dlist_entry.unwrap().next.unwrap()].dlist_entry.is_some()
                && self.pages[self.pages[self.used_lists[i][j]].dlist_entry.unwrap().next.unwrap()].is_used == true,

    {
        assert(valid_ll(self.pages, self.used_dlist_headers[i], self.used_lists[i]));
        assert(valid_ll_i(self.pages, self.used_lists[i], j));
        self.lemma_range_used(self.used_lists[i][j]);
        if self.pages[self.used_lists[i][j]].dlist_entry.unwrap().prev.is_some() {
            self.lemma_range_used(
              self.pages[self.used_lists[i][j]].dlist_entry.unwrap().prev.unwrap());
            assert(self.pages.dom().contains(self.pages[self.used_lists[i][j]].dlist_entry.unwrap().prev.unwrap()));
            assert(valid_ll_i(self.pages, self.used_lists[i], j - 1));
            assert(self.pages[self.pages[self.used_lists[i][j]].dlist_entry.unwrap().prev.unwrap()].dlist_entry.is_some());
            assert(self.pages[self.pages[self.used_lists[i][j]].dlist_entry.unwrap().prev.unwrap()].is_used == true);
            self.ll_used_distinct(i, j, i, j-1);
        }
        if self.pages[self.used_lists[i][j]].dlist_entry.unwrap().next.is_some() {
            assert(self.pages.dom().contains(self.pages[self.used_lists[i][j]].dlist_entry.unwrap().next.unwrap()));
            self.lemma_range_used(
              self.pages[self.used_lists[i][j]].dlist_entry.unwrap().next.unwrap());
            assert(valid_ll_i(self.pages, self.used_lists[i], j + 1));
            assert(self.pages[self.pages[self.used_lists[i][j]].dlist_entry.unwrap().next.unwrap()].dlist_entry.is_some());
            assert(self.pages[self.pages[self.used_lists[i][j]].dlist_entry.unwrap().next.unwrap()].is_used == true);
            self.ll_used_distinct(i, j, i, j+1);

            if self.pages[self.used_lists[i][j]].dlist_entry.unwrap().prev.is_some() {
                self.ll_used_distinct(i, j-1, i, j+1);
            }
        }
    }

    pub proof fn unused_ll_stuff(&self, i: int, j: int)
        requires self.invariant(),
            0 <= i < self.unused_lists.len(),
            0 <= j < self.unused_lists[i].len(),
        ensures
            self.pages.dom().contains(self.unused_lists[i][j]),
            self.pages[self.unused_lists[i][j]].is_used == false,
            self.pages[self.unused_lists[i][j]].count.is_some(),
            self.pages[self.unused_lists[i][j]].dlist_entry.is_some(),
            self.pages[self.unused_lists[i][j]].dlist_entry.unwrap().prev != Some(self.unused_lists[i][j]),
            self.pages[self.unused_lists[i][j]].dlist_entry.unwrap().next != Some(self.unused_lists[i][j]),
            self.pages[self.unused_lists[i][j]].dlist_entry.unwrap().prev.is_some() ==>
                self.pages[self.unused_lists[i][j]].dlist_entry.unwrap().prev != self.pages[self.unused_lists[i][j]].dlist_entry.unwrap().next,

            self.pages[self.unused_lists[i][j]].dlist_entry.unwrap().prev.is_some() ==>
                self.pages.dom().contains(self.pages[self.unused_lists[i][j]].dlist_entry.unwrap().prev.unwrap())
                && self.pages[self.pages[self.unused_lists[i][j]].dlist_entry.unwrap().prev.unwrap()].dlist_entry.is_some()
                && self.pages[self.pages[self.unused_lists[i][j]].dlist_entry.unwrap().prev.unwrap()].is_used == false,
            self.pages[self.unused_lists[i][j]].dlist_entry.unwrap().next.is_some() ==>
                self.pages.dom().contains(self.pages[self.unused_lists[i][j]].dlist_entry.unwrap().next.unwrap())
                && self.pages[self.pages[self.unused_lists[i][j]].dlist_entry.unwrap().next.unwrap()].dlist_entry.is_some()
                && self.pages[self.pages[self.unused_lists[i][j]].dlist_entry.unwrap().next.unwrap()].is_used == false,
    {
        assert(valid_ll(self.pages, self.unused_dlist_headers[i], self.unused_lists[i]));
        assert(valid_ll_i(self.pages, self.unused_lists[i], j));
        if j > 0 {
            self.ll_unused_distinct(i, j, i, j-1);
        }
        if j < self.unused_lists[i].len() - 1 {
            self.ll_unused_distinct(i, j, i, j+1);
            if j > 0 {
                self.ll_unused_distinct(i, j+1, i, j-1);
            }
        }

        self.lemma_range_not_used(self.unused_lists[i][j]);

        if self.pages[self.unused_lists[i][j]].dlist_entry.unwrap().prev.is_some() {
            self.lemma_range_not_used(
              self.pages[self.unused_lists[i][j]].dlist_entry.unwrap().prev.unwrap());
        }
        if self.pages[self.unused_lists[i][j]].dlist_entry.unwrap().next.is_some() {
            self.lemma_range_not_used(
              self.pages[self.unused_lists[i][j]].dlist_entry.unwrap().next.unwrap());
        }
    }

    pub closed spec fn page_id_of_popped(p: Popped) -> PageId {
        match p {
            Popped::Ready(page_id, _) => page_id,
            Popped::Used(page_id, _) => page_id,
            Popped::VeryUnready(segment_id, idx, _, _) => PageId { segment_id, idx: idx as nat },
            _ => arbitrary(),
        }
    }

    pub closed spec fn popped_page_id(&self) -> PageId {
        Self::page_id_of_popped(self.popped)
    }

    pub closed spec fn expect_out_of_lists(&self, pid: PageId) -> bool {
        match self.popped {
            Popped::No => false,
            Popped::ExtraCount(_) => false,
            Popped::Ready(page_id, _) => pid == page_id,
            Popped::Used(page_id, _) => pid == page_id,
            Popped::SegmentCreating(segment_id) => false,
            Popped::SegmentFreeing(segment_id, idx) => pid.segment_id == segment_id && pid.idx < idx,
            Popped::VeryUnready(segment_id, start, _, _) => false,
        }
    }

    pub closed spec fn ec_of_popped(p: Popped, segment_id: SegmentId) -> int {
        match p {
            Popped::No => 0,
            Popped::Ready(p, b) => if p.segment_id == segment_id && b { 1 } else { 0 },
            Popped::Used(p, b) => if p.segment_id == segment_id {
                if b { 0 } else { -1 }
              } else { 0 }
            Popped::SegmentCreating(_) => 0,
            Popped::VeryUnready(sid, _, _, b) => if segment_id == sid && b { 1 } else { 0 },
            Popped::SegmentFreeing(_, _) => 0,
            Popped::ExtraCount(sid) => if segment_id == sid { 1 } else { 0 },
        }
    }

    pub closed spec fn popped_ec(&self, segment_id: SegmentId) -> int {
        Self::ec_of_popped(self.popped, segment_id)
    }

    #[verifier::opaque]
    pub closed spec fn ucount(&self, segment_id: SegmentId) -> nat {
        self.ucount_sum(segment_id, SLICES_PER_SEGMENT as int)
    }

    pub closed spec fn ucount_sum(&self, segment_id: SegmentId, idx: int) -> nat
        decreases idx
    {
        if idx <= 0 {
            0
        } else {
            self.ucount_sum(segment_id, idx - 1)
              + self.one_count(PageId { segment_id, idx: (idx - 1) as nat })
        }
    }

    pub proof fn first_last_ll_stuff_unused(&self, i: int)
        requires self.invariant(),
            0 <= i < self.unused_lists.len(),
        ensures
            (self.popped.is_Ready())
              ==>
                self.unused_dlist_headers[i].first != Some(self.popped_page_id())
                && self.unused_dlist_headers[i].last != Some(self.popped_page_id()),
            (match self.unused_dlist_headers[i].first {
                Some(first_id) => self.pages.dom().contains(first_id)
                  && is_unused_header(self.pages[first_id])
                  && self.pages[first_id].dlist_entry.is_some(),
                None => true,
            }),
            (match self.unused_dlist_headers[i].last {
                Some(last_id) => self.pages.dom().contains(last_id)
                  && is_unused_header(self.pages[last_id])
                  && self.pages[last_id].dlist_entry.is_some(),
                None => true,
            }),
    {
        assert(valid_ll(self.pages, self.unused_dlist_headers[i], self.unused_lists[i]));
        if self.popped.is_Ready() {
            assert(self.unused_dlist_headers[i].first != Some(self.popped_page_id()));
            assert(self.unused_dlist_headers[i].last != Some(self.popped_page_id()));
        }
        match self.unused_dlist_headers[i].last {
            Some(last_id) => {
              assert(valid_ll_i(self.pages, self.unused_lists[i], self.unused_lists[i].len() - 1));
              assert(self.pages.dom().contains(last_id));
              assert(is_unused_header(self.pages[last_id]));
              assert(self.pages[last_id].dlist_entry.is_some());
            }
            None => { }
        }
        match self.unused_dlist_headers[i].first {
            Some(first_id) => {
                assert(valid_ll_i(self.pages, self.unused_lists[i], 0));
                assert(self.pages.dom().contains(first_id));
                assert(is_unused_header(self.pages[first_id]));
                assert(self.pages[first_id].dlist_entry.is_some());
            }
            None => { }
        }
    }

    pub proof fn first_last_ll_stuff_used(&self, i: int)
        requires self.invariant(),
            0 <= i < self.used_lists.len(),
        ensures
            (self.popped.is_Ready())
              ==>
                self.used_dlist_headers[i].first != Some(self.popped_page_id())
                && self.used_dlist_headers[i].last != Some(self.popped_page_id()),
            self.used_dlist_headers[i].first.is_some() <==>
                self.used_dlist_headers[i].last.is_some(),
            (match self.used_dlist_headers[i].first {
                Some(first_id) => self.pages.dom().contains(first_id)
                  && is_used_header(self.pages[first_id])
                  && self.pages[first_id].dlist_entry.is_some(),
                None => true,
            }),
            (match self.used_dlist_headers[i].last {
                Some(last_id) => self.pages.dom().contains(last_id)
                  && is_used_header(self.pages[last_id])
                  && self.pages[last_id].dlist_entry.is_some(),
                None => true,
            }),
    {
        assert(valid_ll(self.pages, self.used_dlist_headers[i], self.used_lists[i]));
        if self.used_lists[i].len() > 0 {
            assert(valid_ll_i(self.pages, self.used_lists[i], 0));
            assert(valid_ll_i(self.pages, self.used_lists[i], self.used_lists[i].len() - 1));
        }
    }

    /*pub proof fn lemma_range_not_header(&self, page_id: PageId, next_id: PageId)
        requires
            self.invariant(),
            self.popped.is_VeryUnready(),
            page_id.segment_id == next_id.segment_id,
            self.pages.dom().contains(page_id),
            page_id.idx == self.popped.get_VeryUnready_1(),
            next_id.segment_id == page_id.segment_id,
            page_id.idx < next_id.idx < page_id.idx + self.popped.get_VeryUnready_2(),
        ensures
            self.pages[next_id].offset != Some(0nat)
    {
        if page_id.segment_id == self.popped.get_VeryUnready_0()
            && page_id.idx == self.popped.get_VeryUnready_1()
        {
            assert(self.pages[next_id].offset != Some(0nat));
        } else if page_id.idx == 0 {
            assert(self.pages[next_id].offset != Some(0nat));
        } else {
            assert(self.pages[next_id].offset != Some(0nat));
            /*if self.pages[page_id].is_used {
                self.lemma_range_used(page_id);
                assert(self.pages[next_id].offset != Some(0nat));
            } else {
                self.lemma_range_not_used(page_id);
                assert(self.pages[next_id].offset != Some(0nat));
            }*/
        }
    }*/

    pub proof fn lemma_range_not_used(&self, page_id: PageId)
        requires self.invariant(), self.pages.dom().contains(page_id),
            is_unused_header(self.pages[page_id]),
            page_id.idx != 0,
            match self.popped {
                //Popped::SegmentFreeing(sid, idx) =>
                //    page_id.segment_id == sid ==> idx <= page_id.idx,
                Popped::Ready(pid, _) => pid != page_id,
                _ => true,
            }
        ensures
            self.pages[page_id].count.is_some(),
            self.good_range_unused(page_id),
    {
        assert(self.attached_ranges_segment(page_id.segment_id));
        match self.popped {
            Popped::SegmentCreating(sid) if sid == page_id.segment_id => {
            }
            Popped::SegmentFreeing(sid, idx) if sid == page_id.segment_id && idx > 0 => {
                //assert(idx >= 0);
                //assert(self.pages.dom().contains(page_id));
                self.rec_lemma_range_not_used(page_id, idx, false);
            }
            _ => {
                self.rec_lemma_range_not_used(page_id, 
                    self.pages[PageId { segment_id: page_id.segment_id, idx: 0 }].count.unwrap() as int,
                    self.popped_for_seg(page_id.segment_id));
            }
        }
    }

    pub proof fn lemma_range_used(&self, page_id: PageId)
        requires self.invariant(), self.pages.dom().contains(page_id),
            is_used_header(self.pages[page_id]),
            match self.popped {
                Popped::Used(pid, _) => pid != page_id,
                _ => true,
            },
        ensures
            self.pages[page_id].count.is_some(),
            self.good_range_used(page_id),
    {
        assert(self.attached_ranges_segment(page_id.segment_id));
        match self.popped {
            Popped::SegmentCreating(sid) if sid == page_id.segment_id => {
            }
            Popped::SegmentFreeing(sid, idx) if sid == page_id.segment_id && idx > 0 => {
                //assert(idx >= 0);
                //assert(self.pages.dom().contains(page_id));
                self.rec_lemma_range_used(page_id, idx, false);
            }
            _ => {
                self.rec_lemma_range_used(page_id, 
                    self.pages[PageId { segment_id: page_id.segment_id, idx: 0 }].count.unwrap() as int,
                    self.popped_for_seg(page_id.segment_id));
            }
        }
    }

    pub proof fn rec_lemma_range_used(&self, page_id: PageId, idx: int, sp: bool)
        requires self.invariant(), self.pages.dom().contains(page_id),
            is_used_header(self.pages[page_id]),
            page_id.idx != SLICES_PER_SEGMENT,
            0 <= idx <= page_id.idx,
            match self.popped {
                Popped::Used(pid, _) => pid != page_id,
                _ => true,
            },
            self.attached_rec(page_id.segment_id, idx, sp),
        ensures 
            self.pages[page_id].count.is_some(),
            self.good_range_used(page_id),
        decreases SLICES_PER_SEGMENT - idx
    {
        reveal(State::attached_rec);
        let segment_id = page_id.segment_id;
        if idx == SLICES_PER_SEGMENT {
            assert(self.pages[page_id].count.is_some());
            assert(self.good_range_used(page_id));
        } else if idx > SLICES_PER_SEGMENT {
        } else if Self::is_the_popped(segment_id, idx, self.popped) {
            let c = self.popped_len();
            let idx2 = idx + c;
            if idx == page_id.idx {
                assert(self.pages[page_id].count.is_some());
                assert(self.good_range_used(page_id));
            } else {
                /*match self.popped {
                    Popped::No => { assert(idx2 <= page_id.idx); }
                    Popped::Ready(pid, _) => { assert(idx2 <= page_id.idx); }
                    Popped::Used(pid, _) => { assert(idx2 <= page_id.idx); }
                    Popped::SegmentCreating(_) => { assert(idx2 <= page_id.idx); }
                    Popped::SegmentFreeing(..) => { assert(idx2 <= page_id.idx); }
                    Popped::VeryUnready(_, _, _, _) => { assert(idx2 <= page_id.idx); }
                    Popped::ExtraCount(_) => { assert(idx2 <= page_id.idx); }
                }*/
                self.rec_lemma_range_used(page_id, idx + self.popped_len(), false);
                assert(self.pages[page_id].count.is_some());
                assert(self.good_range_used(page_id));
            }
        } else {
            if idx == page_id.idx {
                assert(self.pages[page_id].count.is_some());
                assert(self.good_range_used(page_id));
            } else {
                let pid = PageId { segment_id: page_id.segment_id, idx: idx as nat };
                if self.pages[page_id].is_used {
                    self.rec_lemma_range_used(page_id, idx + self.pages[pid].count.unwrap(), sp);
                } else {
                    self.rec_lemma_range_used(page_id, idx + self.pages[pid].count.unwrap(), sp);
                }
                assert(self.pages[page_id].count.is_some());
                assert(self.good_range_used(page_id));
            }
        }
    }

    pub proof fn rec_lemma_range_not_used(&self, page_id: PageId, idx: int, sp: bool)
        requires self.invariant(), self.pages.dom().contains(page_id),
            is_unused_header(self.pages[page_id]),
            0 <= idx <= page_id.idx,
            page_id.idx != SLICES_PER_SEGMENT,
            match self.popped {
                //Popped::SegmentFreeing(sid, idx) =>
                //    page_id.segment_id == sid ==> idx <= page_id.idx,
                Popped::Ready(pid, _) => pid != page_id,
                _ => true,
            },
            self.attached_rec(page_id.segment_id, idx, sp)
        ensures 
            self.pages[page_id].count.is_some(),
            self.good_range_unused(page_id),
        decreases SLICES_PER_SEGMENT - idx
    {
        reveal(State::attached_rec);
        let segment_id = page_id.segment_id;
        if idx == SLICES_PER_SEGMENT {
            assert(self.pages[page_id].count.is_some());
            assert(self.good_range_unused(page_id));
        } else if idx > SLICES_PER_SEGMENT {
        } else if Self::is_the_popped(segment_id, idx, self.popped) {
            let c = self.popped_len();
            let idx2 = idx + c;
            if idx == page_id.idx {
                assert(self.pages[page_id].count.is_some());
                assert(self.good_range_unused(page_id));
            } else {
                self.rec_lemma_range_not_used(page_id, idx + self.popped_len(), false);
                assert(self.pages[page_id].count.is_some());
                assert(self.good_range_unused(page_id));
            }
        } else {
            if idx == page_id.idx {
                assert(self.pages[page_id].count.is_some());
                assert(self.good_range_unused(page_id));
            } else {
                let pid = PageId { segment_id: page_id.segment_id, idx: idx as nat };
                if self.pages[page_id].is_used {
                    self.rec_lemma_range_not_used(page_id, idx + self.pages[pid].count.unwrap(), sp);
                } else {
                    self.rec_lemma_range_not_used(page_id, idx + self.pages[pid].count.unwrap(), sp);
                }
                assert(self.pages[page_id].count.is_some());
                assert(self.good_range_unused(page_id));
            }
        }
    }

    pub proof fn get_stuff_after(&self) -> (r: (int, int))
        requires self.invariant(),
        ensures
          match self.popped {
              Popped::VeryUnready(segment_id, cur_start, cur_count, _) => {
                  let page_id = PageId { segment_id, idx: (cur_start + cur_count) as nat };
                  page_id.idx < SLICES_PER_SEGMENT ==> (
                      self.pages.dom().contains(page_id)
                      && (!self.pages[page_id].is_used ==> self.good_range_unused(page_id)
                          && self.pages[page_id].dlist_entry.is_some()
                          && 0 <= r.0 < self.unused_lists.len()
                          && 0 <= r.1 < self.unused_lists[r.0].len()
                          && self.unused_lists[r.0][r.1] == page_id
                      )
                  )
              }
              _ => true,
          },
    {
        match self.popped {
            Popped::VeryUnready(segment_id, cur_start, cur_count, _) => {
                let page_id = PageId { segment_id, idx: (cur_start + cur_count) as nat };
                if cur_start + cur_count < SLICES_PER_SEGMENT {
                    self.valid_page_after();
                    if self.pages[page_id].is_used == false {
                        self.lemma_range_not_used(page_id);
                    }
                }
                let (i, j) = Self::get_list_idx(self.unused_lists, page_id);
                reveal(State::get_list_idx);
                reveal(State::ll_inv_exists_in_some_list);
                (i, j)
            }
            _ => { (0, 0) }
        }
    }

    pub proof fn get_stuff_before(&self) -> (r: (int, int))
        requires self.invariant(),
        ensures
          match self.popped {
              Popped::VeryUnready(segment_id, cur_start, cur_count, _) => {
                  cur_start >= 1 && ({
                    let last_id = PageId { segment_id, idx: (cur_start - 1) as nat };
                      self.pages.dom().contains(last_id)
                      && self.pages[last_id].offset.is_some()
                      && cur_start - 1 - self.pages[last_id].offset.unwrap() >= 0
                      && ({
                        let page_id = PageId { segment_id, idx: (cur_start - 1 - self.pages[last_id].offset.unwrap()) as nat };
                        self.pages.dom().contains(page_id)
                          && (!self.pages[page_id].is_used && page_id.idx != 0 ==> self.good_range_unused(page_id)
                              && self.pages[page_id].dlist_entry.is_some()
                              && 0 <= r.0 < self.unused_lists.len()
                              && 0 <= r.1 < self.unused_lists[r.0].len()
                              && self.unused_lists[r.0][r.1] == page_id
                              && self.pages[page_id].count.unwrap()
                                  == self.pages[last_id].offset.unwrap() + 1
                          )
                      })
                  })
              }
              _ => true,
          },
    {
        match self.popped {
            Popped::VeryUnready(segment_id, cur_start, cur_count, _) => {
                if cur_start >= 1 {
                    let last_id = PageId { segment_id, idx: (cur_start - 1) as nat };
                    self.valid_page_before();
                    let page_id = PageId { segment_id, idx: (cur_start - 1 - self.pages[last_id].offset.unwrap()) as nat };
                    if self.pages[page_id].is_used == false && page_id.idx != 0 {
                        self.lemma_range_not_used(page_id);
                    }

                    let (i, j) = Self::get_list_idx(self.unused_lists, page_id);
                    reveal(State::get_list_idx);
                    reveal(State::ll_inv_exists_in_some_list);
                    return (i, j);
                }
            }
            _ => { }
        }
        (0, 0)
    }

    /*
    pub proof fn lemma_range_not_used_very_unready(&self)
        requires self.invariant(), self.popped.is_VeryUnready(),
        ensures match self.popped {
            Popped::VeryUnready(segment_id, start, count, _) => {
                (forall |pid| #![trigger self.pages.dom().contains(pid)]
                    #![trigger self.pages.index(pid)]
                  pid.segment_id == segment_id
                  && start <= pid.idx < start + count ==> 
                    self.pages.dom().contains(pid)
                    && self.pages[pid].is_used == false)
            }
            _ => false,
        }
    {
    }
    */

    pub closed spec fn good_range_very_unready(&self, page_id: PageId) -> bool
    {
        &&& self.pages.dom().contains(page_id)
        &&& self.pages[page_id].offset.is_none()
        &&& self.pages[page_id].count.is_none()
        &&& ({ let count = self.popped.get_VeryUnready_2();
            page_id.idx + count <= SLICES_PER_SEGMENT
            && (forall |pid| #![trigger self.pages.dom().contains(pid)]
                #![trigger self.pages.index(pid)]
              pid.segment_id == page_id.segment_id
              && page_id.idx <= pid.idx < page_id.idx + count ==> 
                self.pages.dom().contains(pid)
                && self.pages[pid].is_used == false
                && self.pages[pid].full.is_none()
                && self.pages[pid].page_header_kind.is_none()
                && self.pages[pid].count.is_none()
                && self.pages[pid].dlist_entry.is_none()
                && self.pages[pid].offset.is_none()
           )
        })
    }

    pub closed spec fn good_range0(&self, segment_id: SegmentId) -> bool
    {
        let page_id = PageId { segment_id, idx: 0 }; {
        &&& self.pages.dom().contains(page_id)
        &&& self.pages[page_id].offset == Some(0nat)
        &&& self.pages[page_id].count.is_some()
        &&& ({ let count = self.pages[page_id].count.unwrap();
            page_id.idx + count <= SLICES_PER_SEGMENT
            && (forall |pid| #![trigger self.pages.dom().contains(pid)]
                #![trigger self.pages.index(pid)]
              pid.segment_id == page_id.segment_id
              && page_id.idx <= pid.idx < page_id.idx + count ==> 
                self.pages.dom().contains(pid)
                && self.pages[pid].is_used == false
                && self.pages[pid].full.is_none()
                && self.pages[pid].page_header_kind.is_none()
                && (self.pages[pid].count.is_some() <==> pid == page_id)
                && self.pages[pid].dlist_entry.is_none()
                && self.pages[pid].offset == Some((pid.idx - page_id.idx) as nat)
            )
        })
        }
    }

    pub closed spec fn good_range_unused(&self, page_id: PageId) -> bool
    {
        &&& self.pages.dom().contains(page_id)
        &&& self.pages[page_id].offset == Some(0nat)
        &&& self.pages[page_id].count.is_some()
        &&& ({ let count = self.pages[page_id].count.unwrap();
            page_id.idx + count <= SLICES_PER_SEGMENT
            && (forall |pid| #![trigger self.pages.dom().contains(pid)]
                #![trigger self.pages.index(pid)]
              pid.segment_id == page_id.segment_id
              && page_id.idx <= pid.idx < page_id.idx + count ==> 
                self.pages.dom().contains(pid)
                && self.pages[pid].is_used == false
                && self.pages[pid].full.is_none()
                && self.pages[pid].page_header_kind.is_none()
                && (self.pages[pid].count.is_some() <==> pid == page_id)
                && (self.pages[pid].dlist_entry.is_some() <==> pid == page_id)
                && self.pages[pid].offset == (if pid == page_id || pid == (PageId { segment_id: page_id.segment_id, idx: (page_id.idx + self.pages[page_id].count.unwrap() - 1) as nat }) {
                            Some((pid.idx - page_id.idx) as nat)
                        } else {
                            None
                        })
            )
        })
    }

    pub closed spec fn good_range_used(&self, page_id: PageId) -> bool
    {
        &&& self.pages.dom().contains(page_id)
        &&& self.pages[page_id].offset == Some(0nat)
        &&& self.pages[page_id].count.is_some()
        &&& ({ let count = self.pages[page_id].count.unwrap();
            page_id.idx + count <= SLICES_PER_SEGMENT
            && (forall |pid| #![trigger self.pages.dom().contains(pid)]
                #![trigger self.pages.index(pid)]
              pid.segment_id == page_id.segment_id
              && page_id.idx <= pid.idx < page_id.idx + count ==> 
                self.pages.dom().contains(pid)
                && self.pages[pid].is_used == true
                && self.pages[pid].offset == Some((pid.idx - page_id.idx) as nat)
                //&& (self.pages[pid].count.is_some() <==> pid == page_id)
                && (self.pages[pid].page_header_kind.is_some() <==> pid == page_id)
                && (self.pages[pid].dlist_entry.is_some() <==> pid == page_id)
                && (self.pages[pid].full.is_some() <==> pid == page_id)
            )
        })
    }

    pub proof fn lemma_used_bound(&self, segment_id: SegmentId)
        requires self.segments.dom().contains(segment_id),
            self.invariant(),
        ensures self.segments[segment_id].used <= SLICES_PER_SEGMENT + 1,
    {
        reveal(State::ucount);
        self.ucount_sum_le(segment_id, SLICES_PER_SEGMENT as int);
    }

    pub proof fn ucount_sum_le(&self, segment_id: SegmentId, idx: int)
        requires idx >= 0,
        ensures self.ucount_sum(segment_id, idx) <= idx
        decreases idx,
    {
        if idx > 0 {
            self.ucount_sum_le(segment_id, idx - 1);
            assert(self.ucount_sum(segment_id, idx) <= idx);
        } else {
            assert(self.ucount_sum(segment_id, idx) <= idx);
        }
    }

    pub proof fn ucount_preserve_except(pre: Self, post: Self, esid: SegmentId)
        requires
          forall |pid: PageId| #![all_triggers] pid.segment_id != esid ==>
            (pre.pages.dom().contains(pid) <==> post.pages.dom().contains(pid))
            && (pre.pages.dom().contains(pid) ==> pre.pages[pid] == post.pages[pid]),
          //pre.if_popped_then_for(esid),
          //post.if_popped_then_for(esid),
        ensures
          forall |sid: SegmentId| sid != esid ==> pre.ucount(sid) == post.ucount(sid)
    {
        assert forall |sid: SegmentId| sid != esid implies pre.ucount(sid) == post.ucount(sid)
        by {
            Self::ucount_sum_preserve(pre, post, sid, SLICES_PER_SEGMENT as int);
            reveal(State::ucount);
        }
    }

    pub proof fn ucount_preserve_all(pre: Self, post: Self)
        requires
          forall |pid: PageId|
            pre.does_count(pid) <==> post.does_count(pid),
        ensures
          forall |sid: SegmentId| pre.ucount(sid) == post.ucount(sid)
    {
        assert forall |sid: SegmentId| pre.ucount(sid) == post.ucount(sid)
        by {
            Self::ucount_sum_preserve(pre, post, sid, SLICES_PER_SEGMENT as int);
            reveal(State::ucount);
        }
    }

    pub proof fn ucount_sum_preserve(pre: Self, post: Self, segment_id: SegmentId, idx: int)
        requires
            idx >= 0,
            (forall |pid: PageId| #![all_triggers] pid.segment_id == segment_id ==>
              (pre.pages.dom().contains(pid) <==> post.pages.dom().contains(pid))
              && (pre.pages.dom().contains(pid) ==> pre.pages[pid] == post.pages[pid])
            ) || (
              forall |pid: PageId|
                pre.does_count(pid) <==> post.does_count(pid)
            ),
        ensures
            pre.ucount_sum(segment_id, idx) == post.ucount_sum(segment_id, idx)
        decreases idx,
    {
        if idx > 0 {
            Self::ucount_sum_preserve(pre, post, segment_id, idx - 1);
        }
    }

    pub closed spec fn one_count(&self, page_id: PageId) -> nat {
        if self.does_count(page_id) { 1 } else { 0 }
    }

    pub closed spec fn does_count(&self, page_id: PageId) -> bool {
        self.pages.dom().contains(page_id)
          && page_id.idx != 0
          && self.pages[page_id].is_used
          && self.pages[page_id].offset == Some(0nat)
    }

    pub proof fn ucount_inc1(pre: Self, post: Self, page_id: PageId)
        requires
            0 <= page_id.idx < SLICES_PER_SEGMENT,
            forall |pid: PageId| pid != page_id ==>
              (pre.does_count(pid) <==> post.does_count(pid)),
            !pre.does_count(page_id),
            post.does_count(page_id),
        ensures
            post.ucount(page_id.segment_id) == pre.ucount(page_id.segment_id) + 1
    {
        Self::ucount_sum_inc1(pre, post, page_id, SLICES_PER_SEGMENT as int);
        reveal(State::ucount);
    }

    pub proof fn ucount_sum_inc1(pre: Self, post: Self, page_id: PageId, idx: int)
        requires
            idx >= 0,
            forall |pid: PageId| pid != page_id ==>
                (pre.does_count(pid) <==> post.does_count(pid)),
            !pre.does_count(page_id),
            post.does_count(page_id),
        ensures
            pre.ucount_sum(page_id.segment_id, idx) + (if page_id.idx < idx { 1int } else { 0 }) == post.ucount_sum(page_id.segment_id, idx)
        decreases idx,
    {
        if idx > 0 {
            Self::ucount_sum_inc1(pre, post, page_id, idx - 1);
        }
    }

    pub proof fn ucount_dec1(pre: Self, post: Self, page_id: PageId)
        requires
            0 <= page_id.idx < SLICES_PER_SEGMENT,
            forall |pid: PageId| pid != page_id ==>
              (pre.does_count(pid) <==> post.does_count(pid)),
            pre.does_count(page_id),
            !post.does_count(page_id),
        ensures
            post.ucount(page_id.segment_id) == pre.ucount(page_id.segment_id) - 1
    {
        Self::ucount_sum_dec1(pre, post, page_id, SLICES_PER_SEGMENT as int);
        reveal(State::ucount);
    }

    pub proof fn ucount_sum_dec1(pre: Self, post: Self, page_id: PageId, idx: int)
        requires
            idx >= 0,
            forall |pid: PageId| pid != page_id ==>
                (pre.does_count(pid) <==> post.does_count(pid)),
            pre.does_count(page_id),
            !post.does_count(page_id),
        ensures
            pre.ucount_sum(page_id.segment_id, idx) - (if page_id.idx < idx { 1int } else { 0 }) == post.ucount_sum(page_id.segment_id, idx)
        decreases idx,
    {
        if idx > 0 {
            Self::ucount_sum_dec1(pre, post, page_id, idx - 1);
        }
    }

    pub proof fn ucount_eq0(&self, sid: SegmentId)
        requires
          forall |pid: PageId| pid.segment_id == sid ==>
              !self.does_count(pid)
        ensures
            self.ucount(sid) == 0
    {
        self.ucount_sum_eq0(sid, SLICES_PER_SEGMENT as int);
        reveal(State::ucount);
    }

    pub proof fn ucount_sum_eq0(&self, sid: SegmentId, idx: int)
        requires
            idx >= 0,
            forall |pid: PageId| pid.segment_id == sid ==> !self.does_count(pid)
        ensures
            self.ucount_sum(sid, idx) == 0
        decreases idx,
    {
        if idx > 0 {
            self.ucount_sum_eq0(sid, idx - 1);
        }
    }

    pub proof fn ucount_eq0_inverse(&self, page_id: PageId)
        requires self.ucount(page_id.segment_id) == 0,
            0 <= page_id.idx < SLICES_PER_SEGMENT,
        ensures
            !self.does_count(page_id)
    {
        reveal(State::ucount);
        self.ucount_sum_eq0_inverse(page_id, SLICES_PER_SEGMENT as int);
    }

    #[verifier::spinoff_prover]
    pub proof fn ucount_sum_eq0_inverse(&self, page_id: PageId, idx: int)
        requires self.ucount_sum(page_id.segment_id, idx) == 0,
            0 <= page_id.idx < idx,
        ensures
            !self.does_count(page_id)
        decreases idx,
    {
        if idx - 1 > page_id.idx {
            self.ucount_sum_eq0_inverse(page_id, idx - 1);
            assert(!self.does_count(page_id));
        } else {
            assert(idx - 1 == page_id.idx);
            assert(self.ucount_sum(page_id.segment_id, idx - 1)
              + self.one_count(PageId { segment_id: page_id.segment_id, idx: (idx - 1) as nat }) == 0);
            assert(!self.does_count(page_id));
        }
    }


    pub proof fn attached_ranges_except(pre: Self, post: Self, esid: SegmentId)
        requires
          pre.invariant(),
          forall |sid: SegmentId| sid != esid && post.segments.dom().contains(sid) ==> pre.segments.dom().contains(sid),
          forall |pid: PageId| #![auto] pid.segment_id != esid ==>
            (pre.pages.dom().contains(pid) <==> post.pages.dom().contains(pid))
            && (pre.pages.dom().contains(pid) ==> {
                &&& pre.pages[pid].count == post.pages[pid].count
                &&& (pre.pages[pid].dlist_entry.is_some() <==> post.pages[pid].dlist_entry.is_some())
                &&& pre.pages[pid].offset == post.pages[pid].offset
                &&& pre.pages[pid].is_used == post.pages[pid].is_used
                &&& pre.pages[pid].full == post.pages[pid].full
                &&& pre.pages[pid].page_header_kind == post.pages[pid].page_header_kind
              }),
          pre.if_popped_or_other_then_for(esid),
          post.if_popped_or_other_then_for(esid),
          match post.popped {
              Popped::VeryUnready(_, i, _, _) => i >= 0,
              _ => true,
          },
        ensures
          forall |sid: SegmentId| sid != esid && #[trigger] post.segments.dom().contains(sid) ==> post.attached_ranges_segment(sid)
    {
        assert forall |sid: SegmentId| sid != esid && #[trigger] post.segments.dom().contains(sid) implies post.attached_ranges_segment(sid)
        by {
            assert(pre.segments.dom().contains(sid));
            assert(pre.attached_ranges_segment(sid));
            Self::attached_rec_same(pre, post, sid, 
                pre.pages[PageId { segment_id: sid, idx: 0 }].count.unwrap() as int,
                false);
            assert(pre.good_range0(sid));

            let page_id = PageId { segment_id: sid, idx: 0 };
            let count = post.pages[page_id].count.unwrap();
            assert forall |pid: PageId| 
              #![trigger self.pages.dom().contains(pid)]
              #![trigger self.pages.index(pid)]
              pid.segment_id == page_id.segment_id
              && page_id.idx <= pid.idx < page_id.idx + count implies
                && post.pages[pid].is_used == false
                && post.pages[pid].full.is_none()
                && post.pages[pid].page_header_kind.is_none()
                && (post.pages[pid].count.is_some() <==> pid == page_id)
                && post.pages[pid].dlist_entry.is_none()
                && post.pages[pid].offset == Some((pid.idx - page_id.idx) as nat)
            by {
                assert(pre.pages[pid].is_used == false);
                //assert(post.pages[pid].is_used == false);
                //assert(post.pages[pid].full.is_none());
                //assert(post.pages[pid].page_header_kind.is_none());
                //assert((post.pages[pid].count.is_some() <==> pid == page_id));
                //assert(post.pages[pid].dlist_entry.is_none());
                //assert(post.pages[pid].offset == Some((pid.idx - page_id.idx) as nat));

            }
            assert(post.good_range0(sid));
            assert(post.attached_rec0(sid, false));
        }
    }

    pub open spec fn in_popped_range(&self, pid: PageId) -> bool {
        match self.popped {
            Popped::No | Popped::ExtraCount(_)
              | Popped::SegmentFreeing(..)
              | Popped::SegmentCreating(..) => false,
            Popped::VeryUnready(segment_id, idx, count, _) =>
                pid.segment_id == segment_id && idx <= pid.idx < idx + count,
            Popped::Ready(page_id, _)
              | Popped::Used(page_id, _) => {
                  pid.segment_id == page_id.segment_id
                    && page_id.idx <= pid.idx < page_id.idx + self.pages[page_id].count.unwrap()
            }
        }
    }

    pub proof fn attached_ranges_all(pre: Self, post: Self)
        requires
          pre.invariant(),
          Self::popped_ranges_match(pre, post),
          !pre.popped.is_SegmentFreeing(),
          !pre.popped.is_SegmentCreating(),
          !post.popped.is_SegmentFreeing(),
          pre.segments.dom() =~= post.segments.dom(),
          match post.popped {
              Popped::VeryUnready(_, i, _, _) => i >= 0,
              _ => true,
          },
          forall |pid: PageId|
            #![trigger pre.pages.dom().contains(pid)]
            #![trigger post.pages.dom().contains(pid)]
            #![trigger pre.pages[pid]]
            #![trigger post.pages[pid]]
            (pre.pages.dom().contains(pid) <==> post.pages.dom().contains(pid))
            && (pre.pages.dom().contains(pid)
                && !pre.in_popped_range(pid)
            ==> {
                &&& post.pages.dom().contains(pid)
                &&& pre.pages[pid].count == post.pages[pid].count
                &&& pre.pages[pid].dlist_entry.is_some() <==> post.pages[pid].dlist_entry.is_some()
                &&& pre.pages[pid].offset == post.pages[pid].offset
                &&& pre.pages[pid].is_used == post.pages[pid].is_used
                &&& pre.pages[pid].full == post.pages[pid].full
                &&& pre.pages[pid].page_header_kind == post.pages[pid].page_header_kind
              }),
        ensures
          forall |sid: SegmentId| #[trigger] post.segments.dom().contains(sid) ==> post.attached_ranges_segment(sid)
    {
        assert forall |segment_id: SegmentId| #[trigger] post.segments.dom().contains(segment_id) implies post.attached_ranges_segment(segment_id)
        by {
            assert(pre.attached_ranges_segment(segment_id));
            match pre.popped {
                Popped::SegmentCreating(sid) if sid == segment_id => {
                    //assert(post.attached_ranges_segment(segment_id));
                    assert(false);
                }
                Popped::SegmentFreeing(sid, idx) if sid == segment_id && idx > 0 => {
                    //Self::attached_rec_same(pre, post, segment_id, idx, false);
                    //assert(post.attached_ranges_segment(segment_id));
                    assert(false);
                }
                _ => {
                    Self::attached_rec_same(pre, post, segment_id, 
                        pre.pages[PageId { segment_id, idx: 0 }].count.unwrap() as int,
                        pre.popped_for_seg(segment_id));
                    assert(post.attached_ranges_segment(segment_id));
                }
            }
        }
    }

    pub proof fn attached_rec_same(
        pre: State, post: State,
        segment_id: SegmentId, idx: int, sp: bool
    )
        requires
          pre.invariant(),
          pre.attached_rec(segment_id, idx, sp),
          Self::popped_ranges_match_for_sid(pre, post, segment_id),
          match pre.popped {
              Popped::VeryUnready(_, i, _, _) => i >= 0,
              _ => true,
          },
          match post.popped {
              Popped::VeryUnready(_, i, _, _) => i >= 0,
              _ => true,
          },
          forall |pid: PageId|
            #![trigger pre.pages.dom().contains(pid)]
            #![trigger post.pages.dom().contains(pid)]
            #![trigger pre.pages[pid]]
            #![trigger post.pages[pid]]
            pid.segment_id == segment_id ==>
            (pre.pages.dom().contains(pid) <==> post.pages.dom().contains(pid))
            && (pre.pages.dom().contains(pid) ==> (
                (!pre.in_popped_range(pid) && pid.idx >= idx ==> {
                &&& post.pages.dom().contains(pid)
                &&& pre.pages[pid].count == post.pages[pid].count
                &&& pre.pages[pid].dlist_entry.is_some() <==> post.pages[pid].dlist_entry.is_some()
                &&& pre.pages[pid].offset == post.pages[pid].offset
                &&& pre.pages[pid].is_used == post.pages[pid].is_used
                &&& pre.pages[pid].full == post.pages[pid].full
                &&& pre.pages[pid].page_header_kind == post.pages[pid].page_header_kind
              }))),

          !sp ==> pre.popped_for_seg(segment_id) ==>
              idx >= Self::page_id_of_popped(pre.popped).idx + pre.popped_len(),
          idx >= 0,

        ensures post.attached_rec(segment_id, idx, sp),
          sp ==> pre.popped_for_seg(segment_id) ==>
              idx <= Self::page_id_of_popped(pre.popped).idx

        decreases SLICES_PER_SEGMENT - idx
    {
        reveal(State::attached_rec);
        if idx == SLICES_PER_SEGMENT {
            assert(post.attached_rec(segment_id, idx, sp));
        } else if idx > SLICES_PER_SEGMENT {
            assert(post.attached_rec(segment_id, idx, sp));
        } else if Self::is_the_popped(segment_id, idx, pre.popped) {
            Self::attached_rec_same(pre, post, segment_id, idx + pre.popped_len(), false);
            assert(post.attached_rec(segment_id, idx, sp));
        } else {
            assert(idx >= 0);
            let page_id = PageId { segment_id, idx: idx as nat };
            Self::attached_rec_same(pre, post, segment_id, idx + pre.pages[page_id].count.unwrap(), sp);
            //pre.good_range_disjoint_very_unready(page_id);

            /*let pseg = match pre.popped {
            Popped::No | Popped::ExtraCount(_)
              | Popped::SegmentFreeing(..)
              | Popped::SegmentCreating(..) => arbitrary(),
            Popped::VeryUnready(segment_id, idx, count, _) => segment_id,
            Popped::Ready(page_id, _)
              | Popped::Used(page_id, _) => page_id.segment_id,
            };*/

            /*if pre.popped.is_VeryUnready() {
                if pre.pages[page_id].is_used {
                    assert(pre.good_range_used(page_id));

                    /*assert(post.pages.dom().contains(page_id));
                    assert(post.pages[page_id].offset == Some(0nat));
                    assert(post.pages[page_id].count.is_some());
                    let count = post.pages[page_id].count.unwrap();
                    assert(page_id.idx + count <= SLICES_PER_SEGMENT);
                    assert forall |pid: PageId|
                          pid.segment_id == page_id.segment_id
                          && page_id.idx <= pid.idx < page_id.idx + count ==> 
                            post.pages.dom().contains(pid)
                            && post.pages[pid].is_used == true
                            && post.pages[pid].offset == Some((pid.idx - page_id.idx) as nat)
                            //&& (post.pages[pid].count.is_some() <==> pid == page_id)
                    by {
                        assert(!pre.in_popped_range(pid));
                    }*/
                    assert(post.good_range_used(page_id));
                    assert(post.attached_rec(segment_id, idx, sp));
                } else {
                    assert(pre.good_range_unused(page_id));
                    assert(pseg != segment_id || page_id.idx >=
                        Self::page_id_of_popped(pre.popped).idx + pre.popped_len()
                      || page_id.idx + pre.pages[page_id].count.unwrap()
                          <= Self::page_id_of_popped(pre.popped).idx);
                    assert(post.good_range_unused(page_id));
                    assert(post.attached_rec(segment_id, idx, sp));
                }
            } else {
                if pre.pages[page_id].is_used {
                    assert(pre.good_range_used(page_id));
                    assert(post.good_range_used(page_id));
                    assert(post.attached_rec(segment_id, idx, sp));
                } else {
                    assert(post.good_range_unused(page_id));
                    assert(post.attached_rec(segment_id, idx, sp));
                }
            }*/
            assert(post.attached_rec(segment_id, idx, sp));
        }
    }

    pub closed spec fn if_popped_or_other_then_for(&self, segment_id: SegmentId) -> bool {
        match self.popped {
            Popped::No => true,
            Popped::Ready(page_id, _)
                | Popped::Used(page_id, _)
                => page_id.segment_id == segment_id,
            Popped::SegmentCreating(sid) => sid == segment_id,
            Popped::SegmentFreeing(sid, _) => sid == segment_id,
            Popped::VeryUnready(sid, _, _, _) => sid == segment_id,
            Popped::ExtraCount(_) => true,
        }
    }
        
    pub proof fn unchanged_used_ll(pre: Self, post: Self)
        requires pre.invariant(),
          pre.used_lists == post.used_lists,
          pre.used_dlist_headers == post.used_dlist_headers,
          forall |page_id: PageId|
            pre.pages.dom().contains(page_id)
              && pre.pages[page_id].is_used
              ==> post.pages.dom().contains(page_id)
                && post.pages[page_id].dlist_entry == pre.pages[page_id].dlist_entry
        ensures 
          post.ll_inv_valid_used()
    {
        assert forall |i| 0 <= i < post.used_lists.len()
            implies valid_ll(post.pages, post.used_dlist_headers[i], post.used_lists[i])
        by {
            let ll = post.used_lists[i];
            assert forall |j| 0 <= j < ll.len() implies valid_ll_i(post.pages, ll, j)
            by {
                assert(valid_ll_i(pre.pages, pre.used_lists[i], j));
            }
        }
    }
 
    pub proof fn unchanged_unused_ll(pre: Self, post: Self)
        requires pre.invariant(),
          pre.unused_lists == post.unused_lists,
          pre.unused_dlist_headers == post.unused_dlist_headers,
          forall |page_id: PageId| #![auto]
            pre.pages.dom().contains(page_id)
              && !pre.pages[page_id].is_used
              ==> post.pages.dom().contains(page_id)
                && post.pages[page_id].dlist_entry == pre.pages[page_id].dlist_entry
        ensures 
          post.ll_inv_valid_unused()
    {
        assert forall |i| 0 <= i < post.unused_lists.len()
            implies valid_ll(post.pages, post.unused_dlist_headers[i], post.unused_lists[i])
        by {
            let ll = post.unused_lists[i];
            assert forall |j| 0 <= j < ll.len() implies valid_ll_i(post.pages, ll, j)
            by {
                assert(valid_ll_i(pre.pages, pre.unused_lists[i], j));
            }
        }
    }

    pub closed spec fn insert_front(ll: Seq<Seq<PageId>>, i: int, page_id: PageId) -> Seq<Seq<PageId>> {
        ll.update(i, ll[i].insert(0, page_id))
    }

    pub closed spec fn insert_back(ll: Seq<Seq<PageId>>, i: int, page_id: PageId) -> Seq<Seq<PageId>> {
        ll.update(i, ll[i].push(page_id))
    }

    pub proof fn good_range_disjoint_very_unready(&self, page_id: PageId)
        requires self.invariant(),
            self.good_range_unused(page_id) || self.good_range_used(page_id),
        ensures (match self.popped {
            Popped::VeryUnready(sid, idx, count, _) => {
                sid != page_id.segment_id
                  || idx + count <= page_id.idx
                  || idx >= page_id.idx + self.pages[page_id].count.unwrap()
            }
            _ => true,
        })
    {
        match self.popped {
            Popped::VeryUnready(segment_id, idx, count, _) => {
                if segment_id == page_id.segment_id
                  && !(idx + count <= page_id.idx)
                  && !(idx >= page_id.idx + self.pages[page_id].count.unwrap())
                {
                    if self.good_range_unused(page_id) {
                        /*let pid2 = PageId { segment_id: sid, idx: idx as nat };
                        //assert(self.good_range_very_unready(pid2));
                        assert(self.pages[page_id].offset.is_some());
                        let last_id = PageId { segment_id: page_id.segment_id,
                              idx: (page_id.idx + self.pages[page_id].count.unwrap() - 1) as nat };
                        assert(self.pages[last_id].offset.is_some());
                        //assert(page_id.idx >= pid2.idx);
                        //assert(page_id.idx < pid2.idx + );
                        assert(false);*/

                        self.rec_grd(segment_id, 
                            self.pages[PageId { segment_id, idx: 0 }].count.unwrap() as int, page_id);
                    } else {
                        assert(false);
                    }
                }
            }
            _ => { }
        }
    }

    pub proof fn rec_grd(&self, segment_id: SegmentId, idx: int, page_id: PageId)
        requires self.invariant(),
            self.good_range_unused(page_id),
            (match self.popped {
                Popped::VeryUnready(sid, idx, count, _) => {
                    sid == page_id.segment_id
                      && !(idx + count <= page_id.idx)
                      && !(idx >= page_id.idx + self.pages[page_id].count.unwrap())
                }
                _ => false,
            }),
            self.attached_rec(segment_id, idx, true),
            0 <= idx <= page_id.idx,
            page_id.segment_id == segment_id,
        ensures
            false
        decreases SLICES_PER_SEGMENT - idx
    {
        reveal(State::attached_rec);
        let pid = PageId { segment_id, idx: idx as nat };
        let lid = PageId { segment_id, idx: (idx as nat + self.pages[pid].count.unwrap() - 1) as nat };
        if idx == SLICES_PER_SEGMENT {
            assert(false);
        } else if idx > SLICES_PER_SEGMENT {
            assert(false);
        } else if Self::is_the_popped(segment_id, idx, self.popped) {
            assert(false);
        } else if idx == page_id.idx {
            self.sp_true_implies_le(idx + self.pages[pid].count.unwrap());
            //assert(self.pages[lid].offset.is_some());
            assert(false);
        } else {
            self.rec_grd(segment_id, idx + self.pages[pid].count.unwrap(), page_id);
            assert(false);
        }
    }



    /*pub proof fn good_range_disjoint_two(&self, page_id1: PageId, page_id2: PageId)
        requires self.invariant(),
            self.good_range_unused(page_id1),
            self.good_range_unused(page_id2),
            page_id1 != page_id2,
        ensures 
            page_id1.segment_id != page_id2.segment_id
              || page_id1.idx + self.pages[page_id1].count.unwrap() <= page_id2.idx
              || page_id2.idx + self.pages[page_id2].count.unwrap() <= page_id1.idx
    {
    }*/

    pub proof fn ll_unused_distinct(&self, i1: int, j1: int, i2: int, j2: int)
      requires self.invariant(),
        0 <= i1 < self.unused_lists.len(),
        0 <= j1 < self.unused_lists[i1].len(),
        0 <= i2 < self.unused_lists.len(),
        0 <= j2 < self.unused_lists[i2].len(),
        i1 != i2 || j1 != j2,
      ensures
        self.unused_lists[i1][j1] != self.unused_lists[i2][j2],
      decreases j1
    {
        if i1 != i2 {
        } else {
            assert(valid_ll_i(self.pages, self.unused_lists[i1], j1));
            assert(valid_ll_i(self.pages, self.unused_lists[i2], j2));
            if j1 > 0 && j2 > 0 {
                self.ll_unused_distinct(i1, j1 - 1, i2, j2 - 1);
            } else {
                assert(self.unused_lists[i1][j1] != self.unused_lists[i2][j2]);
            }
        }

    }

    pub proof fn ll_used_distinct(&self, i1: int, j1: int, i2: int, j2: int)
      requires self.invariant(),
        0 <= i1 < self.used_lists.len(),
        0 <= j1 < self.used_lists[i1].len(),
        0 <= i2 < self.used_lists.len(),
        0 <= j2 < self.used_lists[i2].len(),
        i1 != i2 || j1 != j2,
      ensures
        self.used_lists[i1][j1] != self.used_lists[i2][j2],
      decreases j1
    {
        if i1 != i2 {
            if valid_bin_idx(i1) && valid_bin_idx(i2) {
                crate::bin_sizes::different_bin_size(i1, i2);
                assert(self.used_lists[i1][j1] != self.used_lists[i2][j2]);
            } else {
                assert(self.used_lists[i1][j1] != self.used_lists[i2][j2]);
            }
        } else {
            assert(valid_ll_i(self.pages, self.used_lists[i1], j1));
            assert(valid_ll_i(self.pages, self.used_lists[i2], j2));
            if j1 > 0 && j2 > 0 {
                self.ll_used_distinct(i1, j1 - 1, i2, j2 - 1);
            } else {
                assert(self.used_lists[i1][j1] != self.used_lists[i2][j2]);
            }
        }
    }

    pub proof fn ll_mono_back(lls1: Seq<Seq<PageId>>, sbin_idx: int, first_page: PageId)
    requires 0 <= sbin_idx < lls1.len()
    ensures ({
        let lls2 = Self::insert_back(lls1, sbin_idx, first_page);
        forall |pid| is_in_lls(pid, lls1) ==> is_in_lls(pid, lls2)
    })
    {
        let lls2 = Self::insert_back(lls1, sbin_idx, first_page);
        assert forall |pid|
            #[trigger] is_in_lls(pid, lls1) implies is_in_lls(pid, lls2)
        by {
            let (i, j): (int, int) = choose |i, j| 0 <= i < lls1.len() && 0 <= j < lls1[i].len() && lls1[i][j] == pid;
            assert(lls2[i][j] == pid);
        }
    }

    pub proof fn ll_mono(lls1: Seq<Seq<PageId>>, sbin_idx: int, first_page: PageId)
    requires 0 <= sbin_idx < lls1.len()
    ensures ({
        let lls2 = Self::insert_front(lls1, sbin_idx, first_page);
        forall |pid| is_in_lls(pid, lls1) ==> is_in_lls(pid, lls2)
    })
    {
        let lls2 = Self::insert_front(lls1, sbin_idx, first_page);
        assert forall |pid|
            #[trigger] is_in_lls(pid, lls1) implies is_in_lls(pid, lls2)
        by {
            let (i, j): (int, int) = choose |i, j| 0 <= i < lls1.len() && 0 <= j < lls1[i].len() && lls1[i][j] == pid;
            if i == sbin_idx {
                assert(lls2[i][j + 1] == pid);
            } else {
                assert(lls2[i][j] == pid);
            }
        }

        //assert(forall |pid| is_in_lls(pid, pre.unused_lists) ==> is_in_lls(pid, post.unused_lists));
            /*assert forall |pid: PageId| #[trigger] post.pages.dom().contains(pid)
                && post.pages[pid].offset == Some(0nat)
                && pid.idx != 0
                && !post.expect_out_of_lists(pid)
                    implies is_in_lls(pid, post.used_lists) || is_in_lls(pid, post.unused_lists)
            {
                if pid == first_page {
                    assert(post.unused_lists[sbin_idx][0] == pid);
                } else if is_in_lls(pid, pre.used_lists) {
                    assert(is_in_lls(pid, post.used_lists));
                } else {
                    let (i, j) = choose |i, j| 
                        0 <= i < pre.unused_lists.len()
                        && 0 <= j < pre.unused_lists[i].len()
                        && pre.unused_lists[i][j] == pid;
                    if i == sbin_idx {
                        assert 
                    } else {
                    }
                }
            }*/
    }

    pub proof fn ll_remove(lls1: Seq<Seq<PageId>>, lls2: Seq<Seq<PageId>>, sbin_idx: int, list_idx: int)
    requires 0 <= sbin_idx < lls1.len(),
        0 <= list_idx < lls1[sbin_idx].len(),
        lls2 =~~= lls1.update(sbin_idx, lls1[sbin_idx].remove(list_idx)),
    ensures
        forall |pid| pid != lls1[sbin_idx][list_idx] ==>
            #[trigger] is_in_lls(pid, lls1) ==> is_in_lls(pid, lls2),
    {
        assert forall |pid| pid != lls1[sbin_idx][list_idx] &&
            #[trigger] is_in_lls(pid, lls1) implies is_in_lls(pid, lls2)
        by {
            let (i, j): (int, int) = choose |i, j| 0 <= i < lls1.len() && 0 <= j < lls1[i].len() && lls1[i][j] == pid;
            if i == sbin_idx && j > list_idx {
                assert(lls2[i][j - 1] == pid);
            } else {
                assert(lls2[i][j] == pid);
            }
        }
    }
}}

pub open spec fn is_header(pd: PageData) -> bool {
    pd.offset == Some(0nat)
}

pub open spec fn is_unused_header(pd: PageData) -> bool {
    pd.offset == Some(0nat) && !pd.is_used
}

pub open spec fn is_used_header(pd: PageData) -> bool {
    pd.offset == Some(0nat) && pd.is_used
}

pub open spec fn get_next(ll: Seq<PageId>, j: int) -> Option<PageId> {
    if j == ll.len() - 1 {
        None
    } else {
        Some(ll[j + 1])
    }
}

pub open spec fn get_prev(ll: Seq<PageId>, j: int) -> Option<PageId> {
    if j == 0 {
        None
    } else {
        Some(ll[j - 1])
    }
}

pub open spec fn valid_ll_i(pages: Map<PageId, PageData>, ll: Seq<PageId>, j: int) -> bool {
    0 <= j < ll.len()
      && pages.dom().contains(ll[j])
      && pages[ll[j]].dlist_entry.is_some()
      && pages[ll[j]].dlist_entry.unwrap().prev == get_prev(ll, j)
      && pages[ll[j]].dlist_entry.unwrap().next == get_next(ll, j)
}

pub open spec fn valid_ll(pages: Map<PageId, PageData>, header: DlistHeader, ll: Seq<PageId>) -> bool {
    &&& (match header.first {
        Some(first_id) => ll.len() != 0 && ll[0] == first_id,
        None => ll.len() == 0,
    })
    &&& (match header.last {
        Some(last_id) => ll.len() != 0 && ll[ll.len() - 1] == last_id,
        None => ll.len() == 0,
    })
    &&& (forall |j| 0 <= j < ll.len() ==> valid_ll_i(pages, ll, j))
}

pub open spec fn is_in_lls(page_id: PageId, s: Seq<Seq<PageId>>) -> bool {
    exists |i: int, j: int| 
        0 <= i < s.len()
        && 0 <= j < s[i].len()
        && s[i][j] == page_id
}

}
