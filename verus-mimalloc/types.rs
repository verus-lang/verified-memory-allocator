#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::modes::*;
use vstd::*;
use vstd::cell::*;
use vstd::atomic_ghost::*;
use vstd::shared::Shared;
use state_machines_macros::*;

use crate::config::*;
use crate::tokens::{Mim, PageId, ThreadId, SegmentId, HeapId, PageState, HeapState, SegmentState, TldId};
use crate::linked_list::{LL, ThreadLLSimple, ThreadLLWithDelayBits};
use crate::layout::{is_page_ptr, is_page_ptr_opt, is_heap_ptr, is_tld_ptr, block_start_at, is_segment_ptr};
use crate::page_organization::*;
use crate::os_mem::MemChunk;
use crate::commit_mask::CommitMask;
use crate::bin_sizes::{valid_bin_idx, size_of_bin, smallest_bin_fitting_size};
use crate::arena::{ArenaId, MemId};

verus!{

//// Page header data

#[repr(C)]
pub struct PageInner {
    pub flags0: u8,   // is_reset, is_committed, is_zero_init,

    pub capacity: u16,
    pub reserved: u16,
    
    pub flags1: u8,       // in_full, has_aligned
    pub flags2: u8,       // is_zero, retire_expire

    pub free: LL,

    // number of blocks that are allocated, or in `xthread_free`
    // In other words, this is the "complement" of the number
    // of blocks in `free` and `local_free`.
    pub used: u32,

    pub xblock_size: u32,
    pub local_free: LL,
}

impl PageInner {
    pub open spec fn wf(&self, page_id: PageId, page_state: PageState, mim_instance: Mim::Instance) -> bool {
        &&& page_state.block_size == self.xblock_size as nat

        &&& self.free.wf()
        &&& self.free.fixed_page()
        &&& self.free.page_id() == page_id
        &&& self.free.block_size() == page_state.block_size
        &&& self.free.instance() == mim_instance
        &&& self.free.heap_id().is_none()

        &&& self.local_free.wf()
        &&& self.local_free.fixed_page()
        &&& self.local_free.page_id() == page_id
        &&& self.local_free.block_size() == page_state.block_size
        &&& self.local_free.instance() == mim_instance
        &&& self.local_free.heap_id().is_none()

        &&& self.used + self.free.len() + self.local_free.len() == page_state.num_blocks

        &&& self.local_free.fixed_page()
        &&& self.free.fixed_page()

        &&& self.local_free.block_size() == page_state.block_size
        &&& self.free.block_size() == page_state.block_size

        &&& self.capacity <= self.reserved
        &&& self.capacity == page_state.num_blocks

        &&& self.xblock_size > 0
    }

    pub open spec fn zeroed(&self) -> bool {
        &&& self.capacity == 0
        &&& self.reserved == 0
        &&& self.free.wf() && self.free.len() == 0
        &&& self.used == 0
        &&& self.xblock_size == 0
        &&& self.local_free.wf() && self.local_free.len() == 0
    }

    pub open spec fn zeroed_except_block_size(&self) -> bool {
        &&& self.capacity == 0
        &&& self.reserved == 0
        &&& self.free.wf() && self.free.len() == 0
        &&& self.used == 0
        &&& self.local_free.wf() && self.local_free.len() == 0
    }
}

tokenized_state_machine!{ BoolAgree {
    fields {
        #[sharding(variable)] pub x: bool,
        #[sharding(variable)] pub y: bool,
    }
    init!{
        initialize(b: bool) {
            init x = b;
            init y = b;
        }
    }
    transition!{
        set(b: bool) {
            assert(pre.x == pre.y);
            update x = b;
            update y = b;
        }
    }
    property!{
        agree() {
            assert(pre.x == pre.y);
        }
    }
    #[invariant]
    pub spec fn inv_eq(&self) -> bool {
        self.x == self.y
    }
    #[inductive(initialize)] fn initialize_inductive(post: Self, b: bool) { }
    #[inductive(set)] fn set_inductive(pre: Self, post: Self, b: bool) { }
}}

struct_with_invariants!{
    pub struct AtomicHeapPtr {
        pub atomic: AtomicPtr<Heap, _, (BoolAgree::y, Option<Mim::heap_of_page>), _>,

        pub instance: Ghost<Mim::Instance>,
        pub page_id: Ghost<PageId>,
        pub emp: Tracked<BoolAgree::x>,
        pub emp_inst: Tracked<BoolAgree::Instance>,
    }

    pub open spec fn wf(&self, instance: Mim::Instance, page_id: PageId) -> bool {
        predicate {
            self.instance == instance
            && self.page_id == page_id
            && self.emp@.instance_id() == self.emp_inst@.id()
        }
        invariant
            on atomic
            with (instance, page_id, emp, emp_inst)
            is (v: *mut Heap, all_g: (BoolAgree::y, Option<Mim::heap_of_page>))
        {
            let (is_emp, g_opt) = all_g;
            is_emp.instance_id() == emp_inst@.id()
            && (match g_opt {
                None => is_emp.value(),
                Some(g) => {
                    &&& !is_emp.value()
                    &&& g.instance_id() == instance@.id()
                    &&& g.key() == page_id
                    &&& is_heap_ptr(v, g.value())
                }
            })
        }
    }
}

impl AtomicHeapPtr {
    pub open spec fn is_empty(&self) -> bool { self.emp@.value() }

    pub fn empty() -> (ahp: AtomicHeapPtr)
        ensures ahp.is_empty(),
    {
        let tracked (Tracked(emp_inst), Tracked(emp_x), Tracked(emp_y)) = BoolAgree::Instance::initialize(true);
        let ghost g = (Ghost(arbitrary()), Ghost(arbitrary()), Tracked(emp_x), Tracked(emp_inst));
        AtomicHeapPtr {
            page_id: Ghost(arbitrary()),
            instance: Ghost(arbitrary()),
            emp: Tracked(emp_x),
            emp_inst: Tracked(emp_inst),
            atomic: AtomicPtr::new(Ghost(g), core::ptr::null_mut(), Tracked((emp_y, None))),
        }
    }

    #[inline(always)]
    pub fn disable(&mut self) -> (hop: Tracked<Mim::heap_of_page>)
        requires old(self).wf(old(self).instance@, old(self).page_id@),
            !old(self).is_empty(),
        ensures
            self.is_empty(),
            hop@.instance_id() == old(self).instance@.id(),
            hop@.key() == old(self).page_id@,
    {
        let tracked mut heap_of_page;
        atomic_with_ghost!(
            &self.atomic => no_op();
            ghost g => {
                let tracked (mut y, heap_of_page_opt) = g;
                self.emp_inst.borrow().set(true, self.emp.borrow_mut(), &mut y);
                heap_of_page = heap_of_page_opt.tracked_unwrap();
                g = (y, None);
            }
        );
        Tracked(heap_of_page)
    }
}

#[repr(C)]
pub struct Page {
    pub count: PCell<u32>,
    pub offset: u32, // this value is read-only while the Page is shared

    pub inner: PCell<PageInner>,
    pub xthread_free: ThreadLLWithDelayBits,
    pub xheap: AtomicHeapPtr,
    pub prev: PCell<*mut Page>,
    pub next: PCell<*mut Page>,

    pub padding: usize,
}

pub tracked struct PageSharedAccess {
    pub tracked points_to: raw_ptr::PointsTo<Page>,
    pub tracked exposed: raw_ptr::IsExposed,
}

pub tracked struct PageLocalAccess {
    pub tracked count: cell::PointsTo<u32>,
    pub tracked inner: cell::PointsTo<PageInner>,
    pub tracked prev: cell::PointsTo<*mut Page>,
    pub tracked next: cell::PointsTo<*mut Page>,
}

pub tracked struct PageFullAccess {
    pub tracked s: PageSharedAccess,
    pub tracked l: PageLocalAccess,
}

impl Page {
    pub open spec fn wf(&self, page_id: PageId, block_size: nat, mim_instance: Mim::Instance) -> bool {
        self.xthread_free.wf()
          && !self.xthread_free.is_empty()
          && self.xthread_free.instance == mim_instance
          && self.xthread_free.page_id() == page_id
          && self.xthread_free.block_size() == block_size

          && self.xheap.wf(mim_instance, page_id)
          && !self.xheap.is_empty()
    }

    pub open spec fn wf_secondary(&self, mim_instance: Mim::Instance) -> bool {
        self.xthread_free.wf()
          && self.xthread_free.is_empty()
          && self.xthread_free.instance == mim_instance
    }

    pub open spec fn wf_unused(&self, mim_instance: Mim::Instance) -> bool {
        self.xthread_free.wf()
          && self.xthread_free.is_empty()
          && self.xthread_free.instance == mim_instance
    }
}

pub open spec fn page_differ_only_in_offset(page1: Page, page2: Page) -> bool {
    page2 == Page { offset: page2.offset, .. page1 }
}

pub open spec fn psa_differ_only_in_offset(psa1: PageSharedAccess, psa2: PageSharedAccess) -> bool {
    psa1.points_to.is_init()
    && psa2.points_to.is_init()
    && page_differ_only_in_offset(
        psa1.points_to.value(),
        psa2.points_to.value())
    && psa1.points_to.ptr() == psa2.points_to.ptr()
}

impl PageSharedAccess {
    pub open spec fn wf(&self, page_id: PageId, block_size: nat, mim_instance: Mim::Instance) -> bool {
        &&& is_page_ptr(self.points_to.ptr(), page_id)
        &&& self.points_to.is_init()
        &&& self.points_to.value().wf(page_id, block_size, mim_instance)
        &&& self.exposed.provenance() == self.points_to.ptr()@.provenance
    }

    pub open spec fn wf_secondary(&self, page_id: PageId, block_size: nat, mim_instance: Mim::Instance) -> bool {
        &&& is_page_ptr(self.points_to.ptr(), page_id)
        &&& self.points_to.is_init()
        &&& self.points_to.value().wf_secondary(mim_instance)
        &&& self.exposed.provenance() == self.points_to.ptr()@.provenance
    }

    pub open spec fn wf_unused(&self, page_id: PageId, mim_instance: Mim::Instance) -> bool {
        &&& is_page_ptr(self.points_to.ptr(), page_id)
        &&& self.points_to.is_init()
        &&& self.points_to.value().wf_unused(mim_instance)
        &&& self.exposed.provenance() == self.points_to.ptr()@.provenance
    }
}

pub open spec fn wf_reserved(block_size: int, reserved: int, count: int) -> bool {
    reserved * block_size + crate::layout::start_offset(block_size) <= count * SLICE_SIZE
}

impl PageLocalAccess {
    pub open spec fn wf(&self, page_id: PageId, page_state: PageState, mim_instance: Mim::Instance) -> bool {
        (page_state.offset == 0 ==> page_state.shared_access.wf(page_id, page_state.block_size, mim_instance))
        && (page_state.offset != 0 ==> page_state.shared_access.wf_secondary(page_id, page_state.block_size, mim_instance))
        && page_state.is_enabled

        && match page_state.shared_access.points_to.opt_value() {
            MemContents::Init(page) => {
                &&& self.inner.id() == page.inner.id()
                &&& self.count.id() == page.count.id()
                &&& self.prev.id() == page.prev.id()
                &&& self.next.id() == page.next.id()

                &&& match (self.count.mem_contents(), self.inner.mem_contents(), self.prev.mem_contents(), self.next.mem_contents()) {
                    (MemContents::Init(count), MemContents::Init(page_inner), MemContents::Init(prev), MemContents::Init(next)) => {
                        //&&& is_page_ptr_opt(prev, page_state.prev)
                        //&&& is_page_ptr_opt(next, page_state.next)

                        &&& (page_state.offset == 0 ==>
                            page_inner.wf(page_id, page_state, mim_instance)
                            && wf_reserved(page_state.block_size as int,
                                page_inner.reserved as int, count as int)
                        )
                        &&& (page_state.offset != 0 ==> page_inner.zeroed_except_block_size())
                    }
                    _ => false,
                }
            }
            MemContents::Uninit => false,
        }
    }

    pub open spec fn wf_unused(&self, page_id: PageId, shared_access: PageSharedAccess, popped: Popped, mim_instance: Mim::Instance) -> bool {
        shared_access.wf_unused(page_id, mim_instance)

        && match shared_access.points_to.opt_value() {
            MemContents::Init(page) => {
                &&& self.count.id() == page.count.id()
                &&& self.inner.id() == page.inner.id()
                &&& self.prev.id() == page.prev.id()
                &&& self.next.id() == page.next.id()

                &&& match self.inner.mem_contents() {
                    MemContents::Init(page_inner) => {
                        page_inner.zeroed_except_block_size()
                        /*&& (
                            && page_id.idx != 0 && (popped != Popped::Ready(page_id) &&
                            !(popped.is_VeryUnready() && popped.get_VeryUnready_0() == page_id.segment_id && popped.get_VeryUnready_1() == page_id.idx))
                            ==> page_inner.xblock_size == 0
                        )*/
                    }
                    _ => false,
                }
                // TODO move PageData comparison in here?
            }
            MemContents::Uninit => false,
        }
    }
}

impl PageFullAccess {
    pub open spec fn wf_empty_page_global(&self) -> bool {
        &&& self.s.points_to.is_init()
        &&& self.s.points_to.value().inner.id() == self.l.inner.id()
        &&& self.s.exposed.provenance() == self.s.points_to.ptr()@.provenance
        &&& self.s.points_to.ptr()@.metadata == Metadata::Thin
        &&& self.l.inner.is_init()
        &&& self.l.inner.value().zeroed()
    }
}

/////////////////////////////////////////////
///////////////////////////////////////////// Segments
/////////////////////////////////////////////

#[derive(Clone, Copy)]
pub enum SegmentKind {
    Normal,
    Huge,
}

#[repr(C)]
pub struct SegmentHeaderMain {
    pub memid: usize,
    pub mem_is_pinned: bool,
    pub mem_is_large: bool,
    pub mem_is_committed: bool,
    pub mem_alignment: usize,
    pub mem_align_offset: usize,
    pub allow_decommit: bool,
    pub decommit_expire: i64,
    pub decommit_mask: CommitMask,
    pub commit_mask: CommitMask,
}

#[repr(C)]
pub struct SegmentHeaderMain2 {
    pub next: *mut SegmentHeader,
    pub abandoned: usize,
    pub abandoned_visits: usize,
    pub used: usize,
    pub cookie: usize,
    pub segment_slices: usize,
    pub segment_info_slices: usize,
    pub kind: SegmentKind,
    pub slice_entries: usize,
}

struct_with_invariants!{
    #[repr(C)]
    pub struct SegmentHeader {
        pub main: PCell<SegmentHeaderMain>,
        pub abandoned_next: usize, // TODO should be atomic
        pub main2: PCell<SegmentHeaderMain2>,

        // Note: thread_id is 0 if the segment is abandoned
        pub thread_id: AtomicU64<_, Mim::thread_of_segment, _>,

        pub instance: Ghost<Mim::Instance>,
        pub segment_id: Ghost<SegmentId>,
    }

    pub open spec fn wf(&self, instance: Mim::Instance, segment_id: SegmentId) -> bool {
        predicate {
            self.instance == instance
            && self.segment_id == segment_id
        }
        invariant
            on thread_id
            with (instance, segment_id)
            is (v: u64, g: Mim::thread_of_segment)
        {
            &&& g.instance_id() == instance@.id()
            &&& g.key() == segment_id
            &&& g.value() == ThreadId { thread_id: v }
        }
    }
}

pub tracked struct SegmentSharedAccess {
    pub points_to: raw_ptr::PointsTo<SegmentHeader>,
}

impl SegmentSharedAccess {
    pub open spec fn wf(&self, segment_id: SegmentId, mim_instance: Mim::Instance) -> bool {
        &&& is_segment_ptr(self.points_to.ptr(), segment_id)
        &&& (match self.points_to.opt_value() {
            MemContents::Init(segment_header) => segment_header.wf(mim_instance, segment_id),
            MemContents::Uninit => false,
        })
    }
}

pub tracked struct SegmentLocalAccess {
    pub mem: MemChunk,
    pub main: cell::PointsTo<SegmentHeaderMain>,
    pub main2: cell::PointsTo<SegmentHeaderMain2>,
}

impl SegmentLocalAccess {
    pub open spec fn wf(&self, segment_id: SegmentId, segment_state: SegmentState, mim_instance: Mim::Instance) -> bool {
        &&& segment_state.shared_access.wf(segment_id, mim_instance)
        &&& segment_state.shared_access.points_to.value().main.id() == self.main.id()
        &&& self.main.is_init()

        &&& segment_state.shared_access.points_to.value().main2.id() == self.main2.id()
        &&& self.main2.is_init()

        &&& segment_state.is_enabled
    }
}

/////////////////////////////////////////////
///////////////////////////////////////////// Heaps
/////////////////////////////////////////////

pub struct PageQueue {
    pub first: *mut Page,
    pub last: *mut Page,
    pub block_size: usize,
}

impl Clone for PageQueue {
    fn clone(&self) -> (s: Self)
        ensures s == *self
    {
        PageQueue { first: self.first, last: self.last, block_size: self.block_size }
    }
}
impl Copy for PageQueue { }

#[repr(C)]
pub struct Heap {
    pub tld_ptr: TldPtr,

    pub pages_free_direct: PCell<[*mut Page; 129]>, // length PAGES_DIRECT
    pub pages: PCell<[PageQueue; 75]>, // length BIN_FULL + 1

    pub thread_delayed_free: ThreadLLSimple,
    pub thread_id: ThreadId,
    pub arena_id: ArenaId,
    //pub cookie: usize,
    //pub keys: usize,
    //pub random: 
    pub page_count: PCell<usize>,
    pub page_retired_min: PCell<usize>,
    pub page_retired_max: PCell<usize>,
    //pub next: HeapPtr,
    pub no_reclaim: bool,

    // TODO should be a global, but right now we don't support pointers to globals
    pub page_empty_ptr: *mut Page,
}

pub struct HeapSharedAccess {
    pub points_to: raw_ptr::PointsTo<Heap>,
}

pub struct HeapLocalAccess {
    pub pages_free_direct: cell::PointsTo<[*mut Page; 129]>,
    pub pages: cell::PointsTo<[PageQueue; 75]>,
    pub page_count: cell::PointsTo<usize>,
    pub page_retired_min: cell::PointsTo<usize>,
    pub page_retired_max: cell::PointsTo<usize>,
}

impl Heap {
    pub open spec fn wf(&self, heap_id: HeapId, tld_id: TldId, mim_instance: InstanceId) -> bool {
        &&& self.thread_delayed_free.wf()
        &&& self.thread_delayed_free.instance@.id() == mim_instance
        &&& self.thread_delayed_free.heap_id == heap_id
        &&& self.tld_ptr.wf()
        &&& self.tld_ptr.tld_id == tld_id
    }
}

impl HeapSharedAccess {
    pub open spec fn wf(&self, heap_id: HeapId, tld_id: TldId, mim_instance: InstanceId) -> bool {
        is_heap_ptr(self.points_to.ptr(), heap_id)
          && self.points_to.is_init()
          && self.points_to.value().wf(heap_id, tld_id, mim_instance)
    }

    pub open spec fn wf2(&self, heap_id: HeapId, mim_instance: InstanceId) -> bool {
        self.wf(heap_id, self.points_to.value().tld_ptr.tld_id@,
            mim_instance)
    }
}

pub open spec fn pages_free_direct_match(pfd_val: *mut Page, p_val: *mut Page, emp: *mut Page) -> bool {
    (p_val as int == 0 ==> pfd_val as int == emp as int)
    && (p_val as int != 0 ==> pfd_val as int == p_val as int)
}

pub open spec fn pages_free_direct_is_correct(pfd: Seq<*mut Page>, pages: Seq<PageQueue>, emp: *mut Page) -> bool {
    &&& pfd.len() == PAGES_DIRECT
    &&& pages.len() == BIN_FULL + 1
    &&& (forall |wsize|
      0 <= wsize < pfd.len() ==>
        pages_free_direct_match(
            #[trigger] pfd[wsize],
            pages[smallest_bin_fitting_size(wsize * INTPTR_SIZE)].first,
            emp)
    )
}

impl HeapLocalAccess {
    pub open spec fn wf(&self, heap_id: HeapId, heap_state: HeapState, tld_id: TldId, mim_instance: InstanceId, emp: *mut Page) -> bool {

        self.wf_basic(heap_id, heap_state, tld_id, mim_instance)
          && pages_free_direct_is_correct(
                self.pages_free_direct.value()@,
                self.pages.value()@,
                emp)
          && heap_state.shared_access.points_to.value().page_empty_ptr == emp
    }

    pub open spec fn wf_basic(&self, heap_id: HeapId, heap_state: HeapState, tld_id: TldId, mim_instance: InstanceId) -> bool {
      heap_state.shared_access.wf(heap_id, tld_id, mim_instance)
        && {
            let heap = heap_state.shared_access.points_to.value();
              heap.pages_free_direct.id() == self.pages_free_direct.id()
              && heap.pages.id() == self.pages.id()
              && heap.page_count.id() == self.page_count.id()
              && heap.page_retired_min.id() == self.page_retired_min.id()
              && heap.page_retired_max.id() == self.page_retired_max.id()
              && self.pages_free_direct.is_init()
              && self.pages.is_init()
              && self.page_count.is_init()
              && self.page_retired_min.is_init()
              && self.page_retired_max.is_init()

              && (forall |i: int| #[trigger] valid_bin_idx(i) ==>
                  self.pages.value()[i].block_size == size_of_bin(i))
              // 0 isn't a valid_bin_idx
              && self.pages.value()[0].block_size == 8
              && self.pages.value()[BIN_FULL as int].block_size == 
                    8 * (524288 + 2) //MEDIUM_OBJ_WSIZE_MAX + 2

              && self.pages_free_direct.value()@.len() == PAGES_DIRECT
              && self.pages.value()@.len() == BIN_FULL + 1
        }
    }
}

/////////////////////////////////////////////
///////////////////////////////////////////// Thread local data
/////////////////////////////////////////////

//pub struct OsTld {
//    pub region_idx: usize,
//}

pub struct SegmentsTld {
    pub span_queue_headers: [SpanQueueHeader; 32], // len = SEGMENT_BIN_MAX + 1
    pub count: usize,
    pub peak_count: usize,
    pub current_size: usize,
    pub peak_size: usize,
}

pub struct SpanQueueHeader {
    pub first: *mut Page,
    pub last: *mut Page,
}

impl Clone for SpanQueueHeader {
    fn clone(&self) -> (s: Self)
        ensures s == *self
    {
        SpanQueueHeader { first: self.first, last: self.last }
    }
}
impl Copy for SpanQueueHeader { }

pub struct Tld {
    // TODO mimalloc allows multiple heaps per thread
    pub heap_backing: *mut Heap,

    pub segments: SegmentsTld,
}

pub tracked struct Local {
    pub ghost thread_id: ThreadId,

    pub tracked my_inst: Mim::my_inst,
    pub tracked instance: Mim::Instance,
    pub tracked thread_token: Mim::thread_local_state,
    pub tracked checked_token: Mim::thread_checked_state,
    pub tracked is_thread: crate::thread::IsThread,

    pub ghost heap_id: HeapId,
    pub tracked heap: HeapLocalAccess,

    pub ghost tld_id: TldId,
    pub tracked tld: raw_ptr::PointsTo<Tld>,

    pub tracked segments: Map<SegmentId, SegmentLocalAccess>,

    // All pages, used and unused
    pub tracked pages: Map<PageId, PageLocalAccess>,
    pub ghost psa: Map<PageId, PageSharedAccess>,

    // All unused pages
    // (used pages are in the token system)
    pub tracked unused_pages: Map<PageId, PageSharedAccess>,

    pub ghost page_organization: PageOrg::State,

    pub tracked page_empty_global: Shared<PageFullAccess>,
}

pub open spec fn common_preserves(l1: Local, l2: Local) -> bool {
    l1.heap_id == l2.heap_id
    && l1.tld_id == l2.tld_id
    && l1.instance == l2.instance
}

impl Local {
    pub open(crate) spec fn inst(&self) -> Mim::Instance {
        self.instance
    }

    pub open(crate) spec fn wf(&self) -> bool {
        self.wf_main()
          && self.page_organization.popped == Popped::No
    }

    pub open spec fn wf_basic(&self) -> bool {
        &&& is_tld_ptr(self.tld.ptr(), self.tld_id)

        &&& self.thread_token.instance_id() == self.instance.id()
        &&& self.thread_token.key() == self.thread_id

        &&& self.thread_token.value().segments.dom() == self.segments.dom()

        &&& self.thread_token.value().heap_id == self.heap_id
        &&& self.heap.wf_basic(self.heap_id, self.thread_token.value().heap, self.tld_id, self.instance.id())

        &&& self.thread_token.value().heap.shared_access.points_to.value().page_empty_ptr == self.page_empty_global@.s.points_to.ptr()
        &&& self.page_empty_global@.wf_empty_page_global()
    }

    pub open spec fn wf_main(&self) -> bool {
        &&& is_tld_ptr(self.tld.ptr(), self.tld_id)

        &&& self.thread_token.instance_id() == self.instance.id()
        &&& self.thread_token.key() == self.thread_id
        &&& self.thread_id == self.is_thread@

        &&& self.checked_token.instance_id() == self.instance.id()
        &&& self.checked_token.key() == self.thread_id

        &&& self.my_inst.instance_id() == self.instance.id()
        &&& self.my_inst.value() == self.instance.id()

        //&&& (forall |page_id|
        //    self.thread_token.value().pages.dom().contains(page_id) <==>
        //    self.pages.dom().contains(page_id))
        //&&& self.thread_token.value().pages.dom() == self.pages.dom()
        &&& self.thread_token.value().segments.dom() == self.segments.dom()

        &&& self.thread_token.value().heap_id == self.heap_id
        &&& self.heap.wf(self.heap_id, self.thread_token.value().heap, self.tld_id, self.instance.id(), self.page_empty_global@.s.points_to.ptr())

        &&& (forall |page_id|
            #[trigger] self.pages.dom().contains(page_id) ==>
            // Page is either 'used' or 'unused'
              (self.unused_pages.dom().contains(page_id) <==>
                !self.thread_token.value().pages.dom().contains(page_id)))

        &&& self.thread_token.value().pages.dom().subset_of(self.pages.dom())
        &&& (forall |page_id|
            #[trigger] self.pages.dom().contains(page_id) ==>
              self.thread_token.value().pages.dom().contains(page_id) ==>
                self.pages.index(page_id).wf(
                  page_id,
                  self.thread_token.value().pages.index(page_id),
                  self.instance,
                )
            )

        &&& (forall |page_id|
            #[trigger] self.pages.dom().contains(page_id) ==>
              self.unused_pages.dom().contains(page_id) ==>
                self.pages.index(page_id).wf_unused(page_id, self.unused_pages[page_id], self.page_organization.popped, self.instance))

        &&& (forall |segment_id|
            #[trigger] self.segments.dom().contains(segment_id) ==>
              self.segments[segment_id].wf(
                segment_id,
                self.thread_token.value().segments.index(segment_id),
                self.instance,
              )
            )
        &&& (forall |segment_id|
            #[trigger] self.segments.dom().contains(segment_id) ==>
              self.mem_chunk_good(segment_id)
            )

        &&& self.tld.is_init()

        &&& self.page_organization_valid()

        &&& self.page_empty_global@.wf_empty_page_global()
    }

    pub open spec fn page_organization_valid(&self) -> bool
    {
        &&& self.page_organization.invariant()
        &&& self.tld.is_init()

        &&& page_organization_queues_match(self.page_organization.unused_dlist_headers,
                self.tld.value().segments.span_queue_headers@)

        &&& page_organization_used_queues_match(self.page_organization.used_dlist_headers,
                self.heap.pages.value()@)

        &&& page_organization_pages_match(self.page_organization.pages,
                self.pages, self.psa, self.page_organization.popped)

        &&& page_organization_segments_match(self.page_organization.segments, self.segments)

        &&& (forall |page_id: PageId| #[trigger] self.page_organization.pages.dom().contains(page_id) ==>
            (!self.page_organization.pages[page_id].is_used <==> self.unused_pages.dom().contains(page_id)))

        //&&& (forall |page_id: PageId|
        //  #[trigger] self.page_organization.pages.dom().contains(page_id)
        //    ==> self.page_organization.pages[page_id].is_used
        //    ==> self.page_organization.pages[page_id].offset == Some(0nat)
        //    ==> self.thread_token.value().pages[page_id].offset == 0)

        &&& (forall |page_id| 
          #[trigger] self.page_organization.pages.dom().contains(page_id)
            ==> self.page_organization.pages[page_id].is_used
            ==> page_organization_matches_token_page(
                    self.page_organization.pages[page_id],
                    self.thread_token.value().pages[page_id]))

        &&& (forall |page_id: PageId| (#[trigger] self.unused_pages.dom().contains(page_id)) ==>
            self.page_organization.pages.dom().contains(page_id))

        &&& (forall |page_id: PageId| #[trigger] self.unused_pages.dom().contains(page_id) ==>
            self.unused_pages[page_id] == self.psa[page_id])

        &&& (forall |page_id: PageId| #[trigger] self.thread_token.value().pages.dom().contains(page_id) ==>
            self.thread_token.value().pages[page_id].shared_access == self.psa[page_id])
    }

    pub open spec fn page_state(&self, page_id: PageId) -> PageState
        recommends self.thread_token.value().pages.dom().contains(page_id)
    {
        self.thread_token.value().pages.index(page_id)
    }

    pub open spec fn page_inner(&self, page_id: PageId) -> PageInner
        recommends
            self.pages.dom().contains(page_id),
            self.pages.index(page_id).inner.is_init(),
    {
        self.pages.index(page_id).inner.value()
    }


    // This is for when we need to obtain ownership of the ThreadToken
    // but when we have a &mut reference to the Local

    pub proof fn take_thread_token(tracked &mut self) -> (tracked tt: Mim::thread_local_state)
        ensures
            // All fields remain the same except thread_token which is set to an
            // arbitrary value
            *self == (Local { thread_token: self.thread_token, .. *old(self) }),
            tt == old(self).thread_token,
    {
        let tracked mut t = Mim::thread_local_state::arbitrary();
        tracked_swap(&mut t, &mut self.thread_token);
        t
    }

    pub proof fn take_checked_token(tracked &mut self) -> (tracked tt: Mim::thread_checked_state)
        ensures
            // All fields remain the same except thread_token which is set to an
            // arbitrary value
            *self == (Local { checked_token: self.checked_token, .. *old(self) }),
            tt == old(self).checked_token,
    {
        let tracked mut t = Mim::thread_checked_state::arbitrary();
        tracked_swap(&mut t, &mut self.checked_token);
        t
    }

    pub open spec fn commit_mask(&self, segment_id: SegmentId) -> CommitMask {
        self.segments[segment_id].main.value().commit_mask
    }

    pub open spec fn decommit_mask(&self, segment_id: SegmentId) -> CommitMask {
        self.segments[segment_id].main.value().decommit_mask
    }

    pub open spec fn is_used_primary(&self, page_id: PageId) -> bool {
        self.page_organization.pages.dom().contains(page_id)
          && self.page_organization.pages[page_id].is_used
          && self.page_organization.pages[page_id].offset == Some(0nat)
    }

    pub open spec fn page_reserved(&self, page_id: PageId) -> int {
        self.pages[page_id].inner.value().reserved as int
    }

    pub open spec fn page_count(&self, page_id: PageId) -> int {
        self.pages[page_id].count.value() as int
    }

    pub open spec fn page_capacity(&self, page_id: PageId) -> int {
        self.pages[page_id].inner.value().capacity as int
    }

    pub open spec fn block_size(&self, page_id: PageId) -> int {
        self.pages[page_id].inner.value().xblock_size as int
    }
}

pub open spec fn page_organization_queues_match(
    org_queues: Seq<DlistHeader>,
    queues: Seq<SpanQueueHeader>,
) -> bool {
    org_queues.len() == queues.len()
    && (forall |i: int| 0 <= i < org_queues.len() ==>
        is_page_ptr_opt((#[trigger] queues[i]).first, org_queues[i].first))
    && (forall |i: int| 0 <= i < org_queues.len() ==>
        is_page_ptr_opt((#[trigger] queues[i]).last, org_queues[i].last))
}

pub open spec fn page_organization_used_queues_match(
    org_queues: Seq<DlistHeader>,
    queues: Seq<PageQueue>,
) -> bool {
    org_queues.len() == queues.len()
    && (forall |i: int| 0 <= i < org_queues.len() ==>
        is_page_ptr_opt((#[trigger] queues[i]).first, org_queues[i].first))
    && (forall |i: int| 0 <= i < org_queues.len() ==>
        is_page_ptr_opt((#[trigger] queues[i]).last, org_queues[i].last))
}


pub open spec fn page_organization_pages_match(
    org_pages: Map<PageId, PageData>,
    pages: Map<PageId, PageLocalAccess>,
    psa: Map<PageId, PageSharedAccess>,
    popped: Popped,
) -> bool {
    &&& org_pages.dom() =~= pages.dom()
    &&& org_pages.dom() =~= psa.dom()

    //&&& (forall |page_id| #[trigger] org_pages.dom().contains(page_id)
    //    && !org_pages[page_id].is_used ==> unused_pages.dom().contains(page_id))
    //
    //&&& (forall |page_id| #[trigger] org_pages.dom().contains(page_id)
    //    && !org_pages[page_id].is_used ==> unused_pages[page_id].wf_unused(page_id))

    &&& (forall |page_id| #[trigger] org_pages.dom().contains(page_id) ==>
        page_organization_pages_match_data(org_pages[page_id], pages[page_id], psa[page_id], page_id, popped))
}

pub open spec fn page_organization_pages_match_data(
    page_data: PageData,
    pla: PageLocalAccess,
    psa: PageSharedAccess,
    page_id: PageId,
    popped: Popped) -> bool
{
    psa.points_to.is_init() && (
    match (pla.count.mem_contents(), pla.inner.mem_contents(), pla.prev.mem_contents(), pla.next.mem_contents()) {
        (MemContents::Init(count), MemContents::Init(inner), MemContents::Init(prev), MemContents::Init(next)) => {
            &&& (match page_data.count {
                None => true,
                Some(c) => count as int == c
            })
            &&& (match page_data.full {
                None => true,
                Some(b) => inner.in_full() == b,
            })
            &&& (match page_data.offset {
                None => true,
                Some(o) => psa.points_to.value().offset as int ==
                            o * SIZEOF_PAGE_HEADER
            })
            &&& (match page_data.dlist_entry {
                None => true,
                Some(page_queue_data) => {
                    &&& is_page_ptr_opt(prev, page_queue_data.prev)
                    &&& is_page_ptr_opt(next, page_queue_data.next)
                }
            })
            &&& (match page_data.page_header_kind {
                None => {
                    (page_id.idx == 0 ==> {
                      &&& !page_data.is_used
                      &&& (match popped {
                          Popped::SegmentCreating(sid) if sid == page_id.segment_id =>
                              true,
                          _ => inner.xblock_size != 0
                      })
                      &&& (!popped.is_SegmentCreating() ==> inner.xblock_size != 0)
                    })
                    && (page_id.idx != 0 ==> page_data.offset == Some(0nat) ==> (
                        (!(popped.is_Ready() && popped.get_Ready_0() == page_id) &&
                            !(popped.is_VeryUnready() && popped.get_VeryUnready_0() == page_id.segment_id && popped.get_VeryUnready_1() == page_id.idx))
                          ==>
                        (page_data.is_used <==> inner.xblock_size != 0)
                    ))
                }
                Some(PageHeaderKind::Normal(_, bsize)) => {
                    &&& page_id.idx != 0
                    &&& page_data.is_used
                    &&& inner.xblock_size != 0
                    &&& inner.xblock_size == bsize
                    &&& page_data.is_used
                    &&& page_data.offset == Some(0nat)
                }
            })
        }
        _ => false,
    })
}

pub open spec fn page_organization_segments_match(
    org_segments: Map<SegmentId, SegmentData>,
    segments: Map<SegmentId, SegmentLocalAccess>,
) -> bool {
    org_segments.dom() =~= segments.dom()
    && (forall |segment_id: SegmentId| segments.dom().contains(segment_id) ==>
        org_segments[segment_id].used == segments[segment_id].main2.value().used)
}

pub open spec fn page_organization_matches_token_page(
    page_data: PageData,
    page_state: PageState) -> bool
{
    page_data.offset.is_some()
    && page_data.offset.unwrap() == page_state.offset
    /*&& (match page_data.page_header_kind {
        Some(PageHeaderKind::Normal(bsize)) => bsize == page_state.block_size,
        _ => true,
    })*/
}


/////////////////////////////////////////////
/////////////////////////////////////////////
/////////////////////////////////////////////
/////////////////////////////////////////////
/////////////////////////////////////////////
/////////////////////////////////////////////
/////////////////////////////////////////////
////// Utilities for local access

pub struct HeapPtr {
    pub heap_ptr: *mut Heap,
    pub heap_id: Ghost<HeapId>,
}

impl Clone for HeapPtr {
    #[inline(always)]
    fn clone(&self) -> (s: Self)
        ensures *self == s
    {
        HeapPtr { heap_ptr: self.heap_ptr, heap_id: Ghost(self.heap_id@) }
    }
}
impl Copy for HeapPtr { }

impl HeapPtr {
    #[verifier(inline)]
    pub open spec fn wf(&self) -> bool {
        is_heap_ptr(self.heap_ptr, self.heap_id@)
    }

    #[verifier(inline)]
    pub open spec fn is_in(&self, local: Local) -> bool {
        local.heap_id == self.heap_id@
    }

    #[inline(always)]
    pub fn get_ref<'a>(&self, Tracked(local): Tracked<&'a Local>) -> (heap: &'a Heap)
        requires
            local.wf_basic(),
            self.wf(),
            self.is_in(*local),
        ensures
            MemContents::Init(*heap) == local.thread_token.value().heap.shared_access.points_to.opt_value(),
    {
        let tracked perm = &local.instance.thread_local_state_guards_heap(
            local.thread_id, &local.thread_token).points_to;
        ptr_ref(self.heap_ptr, Tracked(perm))
    }

    #[inline(always)]
    pub fn get_pages<'a>(&self, Tracked(local): Tracked<&'a Local>) -> (pages: &'a [PageQueue; 75])
        requires
            local.wf_basic(),
            self.wf(),
            self.is_in(*local),
        ensures
            MemContents::Init(*pages) == local.heap.pages.mem_contents()
    {
        self.get_ref(Tracked(local)).pages.borrow(Tracked(&local.heap.pages))
    }

    #[inline(always)]
    pub fn get_page_count<'a>(&self, Tracked(local): Tracked<&'a Local>) -> (page_count: usize)
        requires
            local.wf_basic(),
            self.wf(),
            self.is_in(*local),
        ensures
            MemContents::Init(page_count) == local.heap.page_count.mem_contents()
    {
        *self.get_ref(Tracked(local)).page_count.borrow(Tracked(&local.heap.page_count))
    }

    #[inline(always)]
    pub fn set_page_count<'a>(&self, Tracked(local): Tracked<&mut Local>, page_count: usize)
        requires
            old(local).wf_basic(),
            self.wf(),
            self.is_in(*old(local)),
        ensures
            local_page_count_update(*old(local), *local),
    {
        let tracked perm = &local.instance.thread_local_state_guards_heap(
            local.thread_id, &local.thread_token).points_to;
        let heap = ptr_ref(self.heap_ptr, Tracked(perm));
        let _ = heap.page_count.take(Tracked(&mut local.heap.page_count));
        heap.page_count.put(Tracked(&mut local.heap.page_count), page_count);
    }

    #[inline(always)]
    pub fn get_page_retired_min<'a>(&self, Tracked(local): Tracked<&'a Local>) -> (page_retired_min: usize)
        requires
            local.wf_basic(),
            self.wf(),
            self.is_in(*local),
        ensures
            MemContents::Init(page_retired_min) == local.heap.page_retired_min.mem_contents()
    {
        *self.get_ref(Tracked(local)).page_retired_min.borrow(Tracked(&local.heap.page_retired_min))
    }

    #[inline(always)]
    pub fn set_page_retired_min<'a>(&self, Tracked(local): Tracked<&mut Local>, page_retired_min: usize)
        requires
            old(local).wf_basic(),
            self.wf(),
            self.is_in(*old(local)),
        ensures
            local_page_retired_min_update(*old(local), *local),
    {
        let tracked perm = &local.instance.thread_local_state_guards_heap(
            local.thread_id, &local.thread_token).points_to;
        let heap = ptr_ref(self.heap_ptr, Tracked(perm));
        let _ = heap.page_retired_min.take(Tracked(&mut local.heap.page_retired_min));
        heap.page_retired_min.put(Tracked(&mut local.heap.page_retired_min), page_retired_min);
    }

    #[inline(always)]
    pub fn get_page_retired_max<'a>(&self, Tracked(local): Tracked<&'a Local>) -> (page_retired_max: usize)
        requires
            local.wf_basic(),
            self.wf(),
            self.is_in(*local),
        ensures
            MemContents::Init(page_retired_max) == local.heap.page_retired_max.mem_contents()
    {
        *self.get_ref(Tracked(local)).page_retired_max.borrow(Tracked(&local.heap.page_retired_max))
    }

    #[inline(always)]
    pub fn set_page_retired_max<'a>(&self, Tracked(local): Tracked<&mut Local>, page_retired_max: usize)
        requires
            old(local).wf_basic(),
            self.wf(),
            self.is_in(*old(local)),
        ensures
            local_page_retired_max_update(*old(local), *local),
    {
        let tracked perm = &local.instance.thread_local_state_guards_heap(
            local.thread_id, &local.thread_token).points_to;
        let heap = ptr_ref(self.heap_ptr, Tracked(perm));
        let _ = heap.page_retired_max.take(Tracked(&mut local.heap.page_retired_max));
        heap.page_retired_max.put(Tracked(&mut local.heap.page_retired_max), page_retired_max);
    }

    #[inline(always)]
    pub fn get_pages_free_direct<'a>(&self, Tracked(local): Tracked<&'a Local>) -> (pages: &'a [*mut Page; 129])
        requires
            local.wf_basic(),
            self.wf(),
            self.is_in(*local),
        ensures
            MemContents::Init(*pages) == local.heap.pages_free_direct.mem_contents()
    {
        self.get_ref(Tracked(local)).pages_free_direct.borrow(Tracked(&local.heap.pages_free_direct))
    }

    #[inline(always)]
    pub fn get_arena_id<'a>(&self, Tracked(local): Tracked<&'a Local>) -> (arena_id: ArenaId)
        requires
            local.wf_main(),
            self.wf(),
            self.is_in(*local),
        ensures
            arena_id
             == local.thread_token.value().heap.shared_access.points_to.value().arena_id,
    {
        self.get_ref(Tracked(local)).arena_id
    }

    #[inline(always)]
    pub fn get_page_empty(&self, Tracked(local): Tracked<&Local>)
        -> (res: (*mut Page, Tracked<Shared<PageFullAccess>>))
    requires
        local.wf_basic(),
        self.wf(),
        self.is_in(*local),
    ensures ({ let (page_ptr, pfa) = res; {
        pfa@@.wf_empty_page_global()
        && pfa@@.s.points_to.ptr() == page_ptr
        && page_ptr.addr() != 0
        && page_ptr == local.page_empty_global@.s.points_to.ptr()
    }})
    {
        let page_ptr = self.get_ref(Tracked(local)).page_empty_ptr;
        let tracked pfa = local.page_empty_global.clone();
        proof { const_facts(); pfa.borrow().s.points_to.is_nonnull(); }
        (page_ptr, Tracked(pfa))
    }
}

pub open spec fn local_page_count_update(loc1: Local, loc2: Local) -> bool {
    &&& loc2 == Local { heap: loc2.heap, .. loc1 }
    &&& loc2.heap == HeapLocalAccess { page_count: loc2.heap.page_count, .. loc1.heap }
    &&& loc1.heap.page_count.id() == loc2.heap.page_count.id()
    &&& loc1.heap.page_count.is_init()
    &&& loc2.heap.page_count.is_init()
}

pub open spec fn local_page_retired_min_update(loc1: Local, loc2: Local) -> bool {
    &&& loc2 == Local { heap: loc2.heap, .. loc1 }
    &&& loc2.heap == HeapLocalAccess { page_retired_min: loc2.heap.page_retired_min, .. loc1.heap }
    &&& loc1.heap.page_retired_min.id() == loc2.heap.page_retired_min.id()
    &&& loc1.heap.page_retired_min.is_init()
    &&& loc2.heap.page_retired_min.is_init()
}

pub open spec fn local_page_retired_max_update(loc1: Local, loc2: Local) -> bool {
    &&& loc2 == Local { heap: loc2.heap, .. loc1 }
    &&& loc2.heap == HeapLocalAccess { page_retired_max: loc2.heap.page_retired_max, .. loc1.heap }
    &&& loc1.heap.page_retired_max.id() == loc2.heap.page_retired_max.id()
    &&& loc1.heap.page_retired_max.is_init()
    &&& loc2.heap.page_retired_max.is_init()
}



pub struct TldPtr {
    pub tld_ptr: *mut Tld,
    pub tld_id: Ghost<TldId>,
}

impl Clone for TldPtr {
    #[inline(always)]
    fn clone(&self) -> (s: Self)
        ensures *self == s
    {
        TldPtr { tld_ptr: self.tld_ptr, tld_id: Ghost(self.tld_id@) }
    }
}
impl Copy for TldPtr { }


impl TldPtr {
    #[verifier(inline)]
    pub open spec fn wf(&self) -> bool {
        is_tld_ptr(self.tld_ptr, self.tld_id@)
    }

    #[verifier(inline)]
    pub open spec fn is_in(&self, local: Local) -> bool {
        local.tld_id == self.tld_id@
    }

    #[inline(always)]
    pub fn get_ref<'a>(&self, Tracked(local): Tracked<&'a Local>) -> (tld: &'a Tld)
        requires
            local.wf_main(),
            self.wf(),
            self.is_in(*local),
        ensures
            MemContents::Init(*tld) == local.tld.opt_value()
    {
        ptr_ref(self.tld_ptr, Tracked(&local.tld))
    }

    #[inline(always)]
    pub fn get_segments_count(&self, Tracked(local): Tracked<&Local>) -> (count: usize)
        requires
            self.wf(), self.is_in(*local), local.wf_main(),
        ensures count == local.tld.value().segments.count,
    {
        self.get_ref(Tracked(local)).segments.count
    }
}

pub struct SegmentPtr {
    pub segment_ptr: *mut SegmentHeader,
    pub segment_id: Ghost<SegmentId>,
}

impl Clone for SegmentPtr {
    #[inline(always)]
    fn clone(&self) -> (s: Self)
        ensures *self == s
    {
        SegmentPtr { segment_ptr: self.segment_ptr, segment_id: Ghost(self.segment_id@) }
    }
}
impl Copy for SegmentPtr { }

impl SegmentPtr {
    #[verifier(inline)]
    pub open spec fn wf(&self) -> bool {
        is_segment_ptr(self.segment_ptr, self.segment_id@)
    }

    #[verifier(inline)]
    pub open spec fn is_in(&self, local: Local) -> bool {
        local.segments.dom().contains(self.segment_id@)
    }

    #[inline(always)]
    pub fn is_null(&self) -> (b: bool)
        ensures b == (self.segment_ptr as int == 0)
    {
        self.segment_ptr.addr() == 0
    }

    #[inline(always)]
    pub fn null() -> (s: Self)
        ensures s.segment_ptr as int == 0
    {
        SegmentPtr { segment_ptr: core::ptr::null_mut(),
            segment_id: Ghost(arbitrary())
        }
    }

    #[inline(always)]
    pub fn get_page_header_ptr(&self, idx: usize) -> (page_ptr: PagePtr)
        requires self.wf(),
            0 <= idx <= SLICES_PER_SEGMENT
        ensures page_ptr.wf(),
            page_ptr.page_id@.segment_id == self.segment_id@,
            page_ptr.page_id@.idx == idx,
    {
        proof { const_facts(); }
        let j = self.segment_ptr.addr() + SIZEOF_SEGMENT_HEADER + idx * SIZEOF_PAGE_HEADER;
        return PagePtr {
            page_ptr: self.segment_ptr.with_addr(j) as *mut Page,
            page_id: Ghost(PageId { segment_id: self.segment_id@, idx: idx as nat }),
        };
    }

    #[inline]
    pub fn get_page_after_end(&self) -> (page_ptr: *mut Page)
        requires self.wf(),
        ensures page_ptr as int == crate::layout::page_header_start(
            PageId { segment_id: self.segment_id@, idx: SLICES_PER_SEGMENT as nat })
    {
        proof { const_facts(); }
        let j = self.segment_ptr.addr()
          + SIZEOF_SEGMENT_HEADER
          + SLICES_PER_SEGMENT as usize * SIZEOF_PAGE_HEADER;
        self.segment_ptr.with_addr(j) as *mut Page
    }

    #[inline(always)]
    pub fn get_ref<'a>(&self, Tracked(local): Tracked<&'a Local>) -> (segment: &'a SegmentHeader)
        requires
            //local.wf_main(),
            local.thread_token.value().segments.dom().contains(self.segment_id@),
            local.thread_token.value().segments[self.segment_id@].shared_access.points_to.ptr() == self.segment_ptr,
            local.thread_token.value().segments[self.segment_id@].shared_access.points_to.is_init(),
            local.thread_token.value().segments[self.segment_id@].is_enabled,
            local.thread_token.key() == local.thread_id,
            local.thread_token.instance_id() == local.instance.id(),
            self.wf(),
            self.is_in(*local),
        ensures
            MemContents::Init(*segment) == local.thread_token.value().segments.index(self.segment_id@).shared_access.points_to.opt_value(),
    {
        let tracked perm = 
            &local.instance.thread_local_state_guards_segment(
                local.thread_id, self.segment_id@, &local.thread_token).points_to;
        ptr_ref(self.segment_ptr, Tracked(perm))
    }

    #[inline(always)]
    pub fn get_main_ref<'a>(&self, Tracked(local): Tracked<&'a Local>) -> (segment_header_main: &'a SegmentHeaderMain)
        requires
            self.wf(), self.is_in(*local),
            //local.wf_main(),
            local.thread_token.value().segments.dom().contains(self.segment_id@),
            local.thread_token.value().segments[self.segment_id@].shared_access.points_to.ptr() == self.segment_ptr,
            local.thread_token.value().segments.index(self.segment_id@).shared_access.points_to.is_init(),
            local.thread_token.value().segments[self.segment_id@].is_enabled,
            local.thread_token.key() == local.thread_id,
            local.thread_token.instance_id() == local.instance.id(),
            local.thread_token.value().segments.index(self.segment_id@).shared_access.points_to.value().main.id()
                == local.segments[self.segment_id@].main.id(),
            local.segments.dom().contains(self.segment_id@),
            local.segments[self.segment_id@].main.is_init(),
        ensures MemContents::Init(*segment_header_main) == local.segments.index(self.segment_id@).main.mem_contents()
    {
        let segment = self.get_ref(Tracked(local));
        segment.main.borrow(Tracked(&local.segments.tracked_borrow(self.segment_id@).main))
    }

    #[inline(always)]
    pub fn get_main2_ref<'a>(&self, Tracked(local): Tracked<&'a Local>) -> (segment_header_main2: &'a SegmentHeaderMain2)
        requires local.wf_main(), self.wf(), self.is_in(*local),
        ensures MemContents::Init(*segment_header_main2) == local.segments.index(self.segment_id@).main2.mem_contents()
    {
        let segment = self.get_ref(Tracked(local));
        segment.main2.borrow(Tracked(&local.segments.tracked_borrow(self.segment_id@).main2))
    }

    #[inline(always)]
    pub fn get_commit_mask<'a>(&self, Tracked(local): Tracked<&'a Local>) -> (cm: &'a CommitMask)
        requires self.wf(), self.is_in(*local),
            local.wf_main(),
        ensures cm == local.segments[self.segment_id@].main.value().commit_mask
    {
        &self.get_main_ref(Tracked(local)).commit_mask
    }

    #[inline(always)]
    pub fn get_decommit_mask<'a>(&self, Tracked(local): Tracked<&'a Local>) -> (cm: &'a CommitMask)
        requires self.wf(), self.is_in(*local),
            local.wf_main(),
        ensures cm == local.segments[self.segment_id@].main.value().decommit_mask
    {
        &self.get_main_ref(Tracked(local)).decommit_mask
    }

    #[inline(always)]
    pub fn get_decommit_expire(&self, Tracked(local): Tracked<&Local>) -> (i: i64)
        requires self.wf(), self.is_in(*local),
            local.wf_main(),
        ensures i == local.segments[self.segment_id@].main.value().decommit_expire
    {
        self.get_main_ref(Tracked(local)).decommit_expire
    }


    #[inline(always)]
    pub fn get_allow_decommit(&self, Tracked(local): Tracked<&Local>) -> (b: bool)
        requires self.wf(), self.is_in(*local),
            local.wf_main(),
        ensures b == local.segments[self.segment_id@].main.value().allow_decommit
    {
        self.get_main_ref(Tracked(local)).allow_decommit
    }

    #[inline(always)]
    pub fn get_used(&self, Tracked(local): Tracked<&Local>) -> (used: usize)
        requires self.wf(), self.is_in(*local), local.wf_main(),
        ensures used == local.segments[self.segment_id@].main2.value().used,
    {
        self.get_main2_ref(Tracked(local)).used
    }

    #[inline(always)]
    pub fn get_abandoned(&self, Tracked(local): Tracked<&Local>) -> (abandoned: usize)
        requires self.wf(), self.is_in(*local), local.wf_main(),
        ensures abandoned == local.segments[self.segment_id@].main2.value().abandoned,
    {
        self.get_main2_ref(Tracked(local)).abandoned
    }

    #[inline(always)]
    pub fn get_mem_is_pinned(&self, Tracked(local): Tracked<&Local>) -> (mem_is_pinned: bool)
        requires self.wf(), self.is_in(*local), local.wf_main(),
        ensures mem_is_pinned == local.segments[self.segment_id@].main.value().mem_is_pinned,
    {
        self.get_main_ref(Tracked(local)).mem_is_pinned
    }

    #[inline(always)]
    pub fn is_abandoned(&self, Tracked(local): Tracked<&Local>) -> (is_ab: bool)
        requires self.wf(), self.is_in(*local), local.wf_main(),
    {
        self.get_ref(Tracked(local)).thread_id.load() == 0
    }

    #[inline(always)]
    pub fn get_segment_kind(&self, Tracked(local): Tracked<&Local>) -> (kind: SegmentKind)
        requires self.wf(), self.is_in(*local), local.wf_main(),
        ensures kind == local.segments[self.segment_id@].main2.value().kind,
    {
        self.get_main2_ref(Tracked(local)).kind
    }

    #[inline(always)]
    pub fn is_kind_huge(&self, Tracked(local): Tracked<&Local>) -> (b: bool)
        requires self.wf(), self.is_in(*local), local.wf_main(),
        ensures b == (local.segments[self.segment_id@].main2.value().kind == SegmentKind::Huge)
    {
        let kind = self.get_main2_ref(Tracked(local)).kind;
        matches!(kind, SegmentKind::Huge)
    }
}

pub struct PagePtr {
    pub page_ptr: *mut Page,
    pub page_id: Ghost<PageId>,
}

impl Clone for PagePtr {
    #[inline(always)]
    fn clone(&self) -> (s: Self)
        ensures *self == s
    {
        PagePtr { page_ptr: self.page_ptr, page_id: Ghost(self.page_id@) }
    }
}
impl Copy for PagePtr { }

impl PagePtr {
    #[verifier(inline)]
    pub open spec fn wf(&self) -> bool {
        is_page_ptr(self.page_ptr, self.page_id@)
          && self.page_ptr.addr() != 0
    }

    #[verifier(inline)]
    pub open spec fn is_in(&self, local: Local) -> bool {
        local.pages.dom().contains(self.page_id@)
    }

    pub open spec fn is_empty_global(&self, local: Local) -> bool {
        self.page_ptr == local.page_empty_global@.s.points_to.ptr()
    }

    #[verifier(inline)]
    pub open spec fn is_used_and_primary(&self, local: Local) -> bool {
        local.pages.dom().contains(self.page_id@)
          && local.thread_token.value().pages.dom().contains(self.page_id@)
          && local.thread_token.value().pages[self.page_id@].offset == 0
    }

    #[verifier(inline)]
    pub open spec fn is_in_unused(&self, local: Local) -> bool {
        local.unused_pages.dom().contains(self.page_id@)
    }

    #[verifier(inline)]
    pub open spec fn is_used(&self, local: Local) -> bool {
        local.pages.dom().contains(self.page_id@)
          && local.thread_token.value().pages.dom().contains(self.page_id@)
    }

    #[inline(always)]
    pub fn null() -> (s: Self)
        ensures s.page_ptr == core::ptr::null_mut::<Page>(),
    {
        PagePtr { page_ptr: core::ptr::null_mut(),
            page_id: Ghost(arbitrary())
        }
    }

    #[inline(always)]
    pub fn is_null(&self) -> (b: bool)
        ensures b == (self.page_ptr.addr() == 0)
    {
        self.page_ptr.addr() == 0
    }

    #[inline(always)]
    pub fn get_ref<'a>(&self, Tracked(local): Tracked<&'a Local>) -> (page: &'a Page)
        requires
            local.wf_main(),
            self.wf(),
            self.is_in(*local),
        ensures
            !self.is_in_unused(*local) ==>
              MemContents::Init(*page) == local.thread_token.value().pages.index(self.page_id@)
                                .shared_access.points_to.opt_value(),
            self.is_in_unused(*local) ==>
              MemContents::Init(*page) == local.unused_pages[self.page_id@].points_to.opt_value(),
    {
        let tracked perm = if self.is_in_unused(*local) {
            &local.unused_pages.tracked_borrow(self.page_id@).points_to
        } else {
            &local.instance.thread_local_state_guards_page(
                local.thread_id, self.page_id@, &local.thread_token).points_to
        };

        ptr_ref(self.page_ptr, Tracked(perm))
    }

    #[inline(always)]
    pub fn get_inner_ref<'a>(&self, Tracked(local): Tracked<&'a Local>) -> (page_inner: &'a PageInner)
        requires
            local.wf_main(),
            self.wf(),
            self.is_in(*local),
        ensures
            MemContents::Init(*page_inner) == local.pages.index(self.page_id@).inner.mem_contents()
    {
        let page = self.get_ref(Tracked(local));
        page.inner.borrow(Tracked(
            &local.pages.tracked_borrow(self.page_id@).inner
            ))
    }

    #[inline(always)]
    pub fn get_inner_ref_maybe_empty<'a>(&self, Tracked(local): Tracked<&'a Local>) -> (page_inner: &'a PageInner)
        requires
            local.wf_main(),
            !self.is_empty_global(*local) ==> (
              self.wf() && self.is_in(*local)
            )
        ensures
            !self.is_empty_global(*local) ==> (
                MemContents::Init(*page_inner) == local.pages.index(self.page_id@).inner.mem_contents()
            ),
            self.is_empty_global(*local) ==> (
                MemContents::Init(*page_inner) == local.page_empty_global@.l.inner.mem_contents()
            ),
    {
        let tracked perm = if self.is_empty_global(*local) {
            &local.page_empty_global.borrow().s.points_to
        } else if self.is_in_unused(*local) {
            &local.unused_pages.tracked_borrow(self.page_id@).points_to
        } else {
            &local.instance.thread_local_state_guards_page(
                local.thread_id, self.page_id@, &local.thread_token).points_to
        };
        let page = ptr_ref(self.page_ptr, Tracked(perm));
        page.inner.borrow(Tracked(
            if self.is_empty_global(*local) {
                &local.page_empty_global.borrow().l.inner
            } else {
                &local.pages.tracked_borrow(self.page_id@).inner
            }
            ))
    }

    #[inline(always)]
    pub fn get_count<'a>(&self, Tracked(local): Tracked<&Local>) -> (count: u32)
        requires
            local.wf_main(),
            self.wf(),
            self.is_in(*local),
        ensures
            MemContents::Init(count) == local.pages.index(self.page_id@).count.mem_contents()
    {
        let page = self.get_ref(Tracked(local));
        *page.count.borrow(Tracked(
            &local.pages.tracked_borrow(self.page_id@).count
            ))
    }

    #[inline(always)]
    pub fn get_next<'a>(&self, Tracked(local): Tracked<&Local>) -> (next: *mut Page)
        requires
            local.wf_main(),
            self.wf(),
            self.is_in(*local),
        ensures
            MemContents::Init(next) == local.pages.index(self.page_id@).next.mem_contents()
    {
        let page = self.get_ref(Tracked(local));
        *page.next.borrow(Tracked(
            &local.pages.tracked_borrow(self.page_id@).next
            ))
    }

    #[inline(always)]
    pub fn get_prev<'a>(&self, Tracked(local): Tracked<&Local>) -> (prev: *mut Page)
        requires
            local.wf_main(),
            self.wf(),
            self.is_in(*local),
        ensures
            MemContents::Init(prev) == local.pages.index(self.page_id@).prev.mem_contents()
    {
        let page = self.get_ref(Tracked(local));
        *page.prev.borrow(Tracked(
            &local.pages.tracked_borrow(self.page_id@).prev
            ))
    }

    #[inline(always)]
    pub fn add_offset(&self, count: usize) -> (p: Self)
        requires
            self.wf(),
            self.page_id@.idx + count <= SLICES_PER_SEGMENT,
        ensures
            p.wf(),
            p.page_id@.segment_id == self.page_id@.segment_id,
            p.page_id@.idx == self.page_id@.idx + count as int,
            p.page_ptr.addr() != 0,
    {
        proof {
            const_facts();
            assert(SIZEOF_PAGE_HEADER == 80);
        }
        let p = self.page_ptr.addr();
        let q = p + count * SIZEOF_PAGE_HEADER;
        PagePtr {
            page_ptr: self.page_ptr.with_addr(q),
            page_id: Ghost(PageId {
                segment_id: self.page_id@.segment_id,
                idx: (self.page_id@.idx + count) as nat,
            })
        }
    }

    #[inline(always)]
    pub fn sub_offset(&self, count: usize) -> (p: Self)
        requires
            self.wf(),
            self.page_id@.idx >= count,
        ensures
            p.wf(),
            p.page_id@.segment_id == self.page_id@.segment_id,
            p.page_id@.idx == self.page_id@.idx - count as int,
            p.page_ptr.addr() != 0,
    {
        proof {
            const_facts();
            assert(SIZEOF_PAGE_HEADER == 80);
            crate::layout::segment_start_ge0(self.page_id@.segment_id);
        }
        let p = self.page_ptr.addr();
        let q = p - count * SIZEOF_PAGE_HEADER;
        let ghost page_id = PageId {
                segment_id: self.page_id@.segment_id,
                idx: (self.page_id@.idx - count) as nat,
            };
        let q = self.page_ptr.with_addr(q);
        proof {
            crate::layout::is_page_ptr_nonzero(q, page_id);
        }
        PagePtr {
            page_ptr: q,
            page_id: Ghost(page_id)
        }
    }

    #[inline(always)]
    pub fn is_gt_0th_slice(&self, segment: SegmentPtr) -> (res: bool)
        requires self.wf(),
            segment.wf(),
            segment.segment_id@ == self.page_id@.segment_id,
    ensures
        res == (self.page_id@.idx > 0),
    {
        proof { const_facts(); }
        self.page_ptr.addr() > segment.get_page_header_ptr(0).page_ptr.addr()
    }

    #[inline(always)]
    pub fn get_index(&self) -> (idx: usize)
        requires self.wf(),
    ensures
        idx == self.page_id@.idx,
    {
        proof { const_facts(); }
        let segment = SegmentPtr::ptr_segment(*self);
        (self.page_ptr.addr() - segment.segment_ptr.addr() - SIZEOF_SEGMENT_HEADER)
            / SIZEOF_PAGE_HEADER
    }

    pub fn slice_start(&self) -> (p: usize)
        requires self.wf(),
        ensures
            p == crate::layout::page_start(self.page_id@),
    {
        proof {
            const_facts();
            assert(SLICE_SIZE as usize == 65536);
        }
        let segment = SegmentPtr::ptr_segment(*self);
        let s = segment.segment_ptr.addr();
        s +
          ((self.page_ptr.addr() - s - SIZEOF_SEGMENT_HEADER) / SIZEOF_PAGE_HEADER)
            * SLICE_SIZE as usize
    }

    #[inline(always)]
    pub fn add_offset_and_check(&self, count: usize, segment: SegmentPtr) -> (res: (Self, bool))
        requires
            self.wf(),
            self.page_id@.idx + count <= SLICES_PER_SEGMENT,
            segment.wf(),
            self.page_id@.segment_id == segment.segment_id@,
        ensures ({ let (p, b) = res; {
            b ==> ({
                &&& p.wf()
                &&& p.page_id@.segment_id == self.page_id@.segment_id
                &&& p.page_id@.idx == self.page_id@.idx + count as int
                &&& p.page_ptr.addr() != 0
            })
            && (b <==> self.page_id@.idx + count < SLICES_PER_SEGMENT)
        }})
    {
        proof {
            const_facts();
            assert(SIZEOF_PAGE_HEADER == 80);
        }
        let p = self.page_ptr.addr();
        let q = p + count * SIZEOF_PAGE_HEADER;
        let page_ptr = PagePtr {
            page_ptr: self.page_ptr.with_addr(q),
            page_id: Ghost(PageId {
                segment_id: self.page_id@.segment_id,
                idx: (self.page_id@.idx + count) as nat,
            })
        };
        let last = segment.get_page_after_end();
        (page_ptr, page_ptr.page_ptr.addr() < last.addr())
    }

    #[inline(always)]
    pub fn get_block_size(&self, Tracked(local): Tracked<&Local>) -> (bsize: u32)
        requires
            local.wf_main(),
            self.wf(),
            self.is_in(*local),
        ensures
            bsize == local.pages.index(self.page_id@).inner.value().xblock_size
    {
        self.get_inner_ref(Tracked(local)).xblock_size
    }

    #[inline(always)]
    pub fn get_heap(&self, Tracked(local): Tracked<&Local>) -> (heap: HeapPtr)
        requires
            local.wf_main(), self.wf(), self.is_in(*local),
                self.is_used_and_primary(*local),
        ensures heap.wf(), heap.is_in(*local),
    {
        let page_ref = self.get_ref(Tracked(&*local));
        let h = atomic_with_ghost!(
            &page_ref.xheap.atomic => load();
            ghost g => {
                page_ref.xheap.emp_inst.borrow().agree(page_ref.xheap.emp.borrow(), &g.0);
                let tracked heap_of_page = g.1.tracked_borrow();
                local.instance.heap_of_page_agree_with_thread_state(
                    self.page_id@,
                    local.thread_id,
                    &local.thread_token,
                    heap_of_page);
            }
        );
        HeapPtr {
            heap_ptr: h,
            heap_id: Ghost(local.heap_id),
        }
    }
}

// Use macro as a work-arounds for not supporting functions that return &mut

#[macro_export]
macro_rules! tld_get_mut {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_exec_macro_exprs!(
            $crate::types::tld_get_mut_internal!($($tail)*))
    };
}

#[macro_export]
macro_rules! tld_get_mut_internal {
    ($ptr:expr, $local:ident, $tld:ident => $body:expr) => {
        ::builtin_macros::verus_exec_expr!{ {
            let tld_ptr = ($ptr);

            let mut $tld = vstd::raw_ptr::ptr_mut_read(tld_ptr.tld_ptr, Tracked(&mut $local.tld));

            { $body }

            vstd::raw_ptr::ptr_mut_write(tld_ptr.tld_ptr, Tracked(&mut $local.tld), $tld);
        } }
    }
}

pub use tld_get_mut;
pub use tld_get_mut_internal;

#[macro_export]
macro_rules! page_get_mut_inner {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_exec_macro_exprs!(
            $crate::types::page_get_mut_inner_internal!($($tail)*))
    };
}

#[macro_export]
macro_rules! page_get_mut_inner_internal {
    ($ptr:expr, $local:ident, $page_inner:ident => $body:expr) => {
        ::builtin_macros::verus_exec_expr!{ {
            let page_ptr = $ptr;

            let tracked perm = &$local.instance.thread_local_state_guards_page(
                    $local.thread_id, page_ptr.page_id@, &$local.thread_token).points_to;
            let page = vstd::raw_ptr::ptr_ref(page_ptr.page_ptr, Tracked(perm));

            let tracked PageLocalAccess { inner: mut inner_0, prev: prev_0, next: next_0, count: count_0 } =
                $local.pages.tracked_remove(page_ptr.page_id@);
            let mut $page_inner = page.inner.take(Tracked(&mut inner_0));

            { $body }

            page.inner.put(Tracked(&mut inner_0), $page_inner);
            proof {
                $local.pages.tracked_insert(page_ptr.page_id@, PageLocalAccess {
                    inner: inner_0, prev: prev_0, next: next_0, count: count_0
                });
            }
        } }
    }
}

pub use page_get_mut_inner;
pub use page_get_mut_inner_internal;

#[macro_export]
macro_rules! unused_page_get_mut_prev {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_exec_macro_exprs!(
            $crate::types::unused_page_get_mut_prev_internal!($($tail)*))
    };
}

#[macro_export]
macro_rules! unused_page_get_mut_prev_internal {
    ($ptr:expr, $local:ident, $page_prev:ident => $body:expr) => {
        ::builtin_macros::verus_exec_expr!{ {
            let page_ptr = ($ptr);
            assert(page_ptr.wf());

            let tracked perm = &$local.unused_pages.tracked_borrow(page_ptr.page_id@).points_to;
            let page = ptr_ref(page_ptr.page_ptr, Tracked(perm));

            let tracked PageLocalAccess { inner: inner_0, prev: mut prev_0, next: next_0, count: count_0 } =
                $local.pages.tracked_remove(page_ptr.page_id@);
            let mut $page_prev = page.prev.take(Tracked(&mut prev_0));

            { $body }

            page.prev.put(Tracked(&mut prev_0), $page_prev);
            proof {
                $local.pages.tracked_insert(page_ptr.page_id@, PageLocalAccess {
                    inner: inner_0, prev: prev_0, next: next_0, count: count_0
                });
            }
        } }
    }
}

pub use unused_page_get_mut_prev;
pub use unused_page_get_mut_prev_internal;

#[macro_export]
macro_rules! unused_page_get_mut_inner {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_exec_macro_exprs!(
            $crate::types::unused_page_get_mut_inner_internal!($($tail)*))
    };
}

#[macro_export]
macro_rules! unused_page_get_mut_inner_internal {
    ($ptr:expr, $local:ident, $page_inner:ident => $body:expr) => {
        ::builtin_macros::verus_exec_expr!{ {
            let page_ptr = ($ptr);

            let tracked perm = &$local.unused_pages.tracked_borrow(page_ptr.page_id@).points_to;
            let page = vstd::raw_ptr::ptr_ref(page_ptr.page_ptr, Tracked(perm));

            let tracked PageLocalAccess { inner: mut inner_0, prev: prev_0, next: next_0, count: count_0 } =
                $local.pages.tracked_remove(page_ptr.page_id@);
            let mut $page_inner = page.inner.take(Tracked(&mut inner_0));

            { $body }

            page.inner.put(Tracked(&mut inner_0), $page_inner);
            proof {
                $local.pages.tracked_insert(page_ptr.page_id@, PageLocalAccess {
                    inner: inner_0, prev: prev_0, next: next_0, count: count_0
                });
            }
        } }
    }
}

pub use unused_page_get_mut_inner;
pub use unused_page_get_mut_inner_internal;


#[macro_export]
macro_rules! unused_page_get_mut_next {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_exec_macro_exprs!(
            $crate::types::unused_page_get_mut_next_internal!($($tail)*))
    };
}

#[macro_export]
macro_rules! unused_page_get_mut_next_internal {
    ($ptr:expr, $local:ident, $page_next:ident => $body:expr) => {
        ::builtin_macros::verus_exec_expr!{ {
            let page_ptr = ($ptr);

            let tracked perm = &$local.unused_pages.tracked_borrow(page_ptr.page_id@).points_to;
            let page = ptr_ref(page_ptr.page_ptr, Tracked(perm));

            let tracked PageLocalAccess { inner: inner_0, prev: prev_0, next: mut next_0, count: count_0 } =
                $local.pages.tracked_remove(page_ptr.page_id@);
            let mut $page_next = page.next.take(Tracked(&mut next_0));

            { $body }

            page.next.put(Tracked(&mut next_0), $page_next);
            proof {
                $local.pages.tracked_insert(page_ptr.page_id@, PageLocalAccess {
                    inner: inner_0, prev: prev_0, next: next_0, count: count_0
                });
            }
        } }
    }
}

pub use unused_page_get_mut_next;
pub use unused_page_get_mut_next_internal;

#[macro_export]
macro_rules! unused_page_get_mut_count {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_exec_macro_exprs!(
            $crate::types::unused_page_get_mut_count_internal!($($tail)*))
    };
}

#[macro_export]
macro_rules! unused_page_get_mut_count_internal {
    ($ptr:expr, $local:ident, $page_count:ident => $body:expr) => {
        ::builtin_macros::verus_exec_expr!{ {
            let page_ptr = ($ptr);

            let tracked perm = &$local.unused_pages.tracked_borrow(page_ptr.page_id@).points_to;
            let page = ptr_ref(page_ptr.page_ptr, Tracked(perm));

            let tracked PageLocalAccess { inner: inner_0, prev: prev_0, next: next_0, count: mut count_0 } =
                $local.pages.tracked_remove(page_ptr.page_id@);
            let mut $page_count = page.count.take(Tracked(&mut count_0));

            { $body }

            page.count.put(Tracked(&mut count_0), $page_count);
            proof {
                $local.pages.tracked_insert(page_ptr.page_id@, PageLocalAccess {
                    inner: inner_0, prev: prev_0, next: next_0, count: count_0
                });
            }
        } }
    }
}

pub use unused_page_get_mut_count;
pub use unused_page_get_mut_count_internal;


#[macro_export]
macro_rules! unused_page_get_mut {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_exec_macro_exprs!(
            $crate::types::unused_page_get_mut_internal!($($tail)*))
    };
}

#[macro_export]
macro_rules! unused_page_get_mut_internal {
    ($ptr:expr, $local:ident, $page:ident => $body:expr) => {
        ::builtin_macros::verus_exec_expr!{ {
            let page_ptr = ($ptr);

            let tracked psa = $local.unused_pages.tracked_remove(page_ptr.page_id@);
            let tracked PageSharedAccess { points_to: mut points_to, exposed } = psa;
            let mut $page = vstd::raw_ptr::ptr_mut_read(page_ptr.page_ptr, Tracked(&mut points_to));

            { $body }

            vstd::raw_ptr::ptr_mut_write(page_ptr.page_ptr, Tracked(&mut points_to), $page);
            proof {
                let tracked psa = PageSharedAccess { points_to: points_to, exposed };
                $local.unused_pages.tracked_insert(page_ptr.page_id@, psa);
            }
        } }
    }
}

pub use unused_page_get_mut;
pub use unused_page_get_mut_internal;


#[macro_export]
macro_rules! used_page_get_mut_prev {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_exec_macro_exprs!(
            $crate::types::used_page_get_mut_prev_internal!($($tail)*))
    };
}

#[macro_export]
macro_rules! used_page_get_mut_prev_internal {
    ($ptr:expr, $local:ident, $page_prev:ident => $body:expr) => {
        ::builtin_macros::verus_exec_expr!{ {
            let page_ptr = ($ptr);
            assert(page_ptr.wf());

            let tracked perm = &$local.instance.thread_local_state_guards_page(
                $local.thread_id, page_ptr.page_id@, &$local.thread_token).points_to;
            let page = vstd::raw_ptr::ptr_ref(page_ptr.page_ptr, Tracked(perm));

            let tracked PageLocalAccess { inner: inner_0, prev: mut prev_0, next: next_0, count: count_0 } =
                $local.pages.tracked_remove(page_ptr.page_id@);
            let mut $page_prev = page.prev.take(Tracked(&mut prev_0));

            { $body }

            page.prev.put(Tracked(&mut prev_0), $page_prev);
            proof {
                $local.pages.tracked_insert(page_ptr.page_id@, PageLocalAccess {
                    inner: inner_0, prev: prev_0, next: next_0, count: count_0
                });
            }
        } }
    }
}

pub use used_page_get_mut_prev;
pub use used_page_get_mut_prev_internal;

#[macro_export]
macro_rules! heap_get_pages {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_exec_macro_exprs!(
            $crate::types::heap_get_pages_internal!($($tail)*))
    };
}

#[macro_export]
macro_rules! heap_get_pages_internal {
    ($ptr:expr, $local:ident, $pages:ident => $body:expr) => {
        ::builtin_macros::verus_exec_expr!{ {
            let heap_ptr = ($ptr);

            let tracked perm = &$local.instance.thread_local_state_guards_heap(
                $local.thread_id, &$local.thread_token).points_to;
            let heap = vstd::raw_ptr::ptr_ref(heap_ptr.heap_ptr, Tracked(perm));
            let mut $pages = heap.pages.take(Tracked(&mut $local.heap.pages));

            { $body }

            heap.pages.put(Tracked(&mut $local.heap.pages), $pages);
        } }
    }
}

pub use heap_get_pages;
pub use heap_get_pages_internal;

#[macro_export]
macro_rules! heap_get_pages_free_direct {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_exec_macro_exprs!(
            $crate::types::heap_get_pages_free_direct_internal!($($tail)*))
    };
}

#[macro_export]
macro_rules! heap_get_pages_free_direct_internal {
    ($ptr:expr, $local:ident, $pages_free_direct:ident => $body:expr) => {
        ::builtin_macros::verus_exec_expr!{ {
            let heap_ptr = ($ptr);

            let tracked perm = &$local.instance.thread_local_state_guards_heap(
                $local.thread_id, &$local.thread_token).points_to;
            let heap = vstd::raw_ptr::ptr_ref(heap_ptr.heap_ptr, Tracked(perm));
            let mut $pages_free_direct = heap.pages_free_direct.take(Tracked(&mut $local.heap.pages_free_direct));

            { $body }

            let mut $pages_free_direct = heap.pages_free_direct.put(Tracked(&mut $local.heap.pages_free_direct), $pages_free_direct);
        } }
    }
}

pub use heap_get_pages_free_direct;
pub use heap_get_pages_free_direct_internal;



#[macro_export]
macro_rules! used_page_get_mut_next {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_exec_macro_exprs!(
            $crate::types::used_page_get_mut_next_internal!($($tail)*))
    };
}

#[macro_export]
macro_rules! used_page_get_mut_next_internal {
    ($ptr:expr, $local:ident, $page_next:ident => $body:expr) => {
        ::builtin_macros::verus_exec_expr!{ {
            let page_ptr = ($ptr);
            assert(page_ptr.wf());

            let tracked perm = &$local.instance.thread_local_state_guards_page(
                $local.thread_id, page_ptr.page_id@, &$local.thread_token).points_to;
            let page = vstd::raw_ptr::ptr_ref(page_ptr.page_ptr, Tracked(perm));

            let tracked PageLocalAccess { inner: inner_0, prev: prev_0, next: mut next_0, count: count_0 } =
                $local.pages.tracked_remove(page_ptr.page_id@);
            let mut $page_next = page.next.take(Tracked(&mut next_0));

            { $body }

            page.next.put(Tracked(&mut next_0), $page_next);
            proof {
                $local.pages.tracked_insert(page_ptr.page_id@, PageLocalAccess {
                    inner: inner_0, prev: prev_0, next: next_0, count: count_0
                });
            }
        } }
    }
}

pub use used_page_get_mut_next;
pub use used_page_get_mut_next_internal;

#[verus::trusted]
#[verifier::external_body]
pub fn print_hex(s: &'static str, u: usize) {
    println!("{:} {:x}", s, u);
}

#[verus::trusted]
#[cfg(feature = "override_system_allocator")]
#[verifier::external_body]
pub fn todo()
    ensures false
{
    std::process::abort();
}

#[verus::trusted]
#[cfg(not(feature = "override_system_allocator"))]
#[verifier::external_body]
pub fn todo()
    ensures false
{
    panic!("todo"); 
}

#[macro_export]
macro_rules! segment_get_mut_main {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_exec_macro_exprs!(
            $crate::types::segment_get_mut_main_internal!($($tail)*))
    };
}

#[macro_export]
macro_rules! segment_get_mut_main_internal {
    ($ptr:expr, $local:ident, $segment_main:ident => $body:expr) => {
        ::builtin_macros::verus_exec_expr!{ {
            let segment_ptr = $ptr;

            let tracked perm = &$local.instance.thread_local_state_guards_segment(
                    $local.thread_id, segment_ptr.segment_id@, &$local.thread_token).points_to;
            let segment = vstd::raw_ptr::ptr_ref(segment_ptr.segment_ptr, Tracked(perm));

            let tracked SegmentLocalAccess { main: mut main_0, mem: mem_0, main2: main2_0 } =
                $local.segments.tracked_remove(segment_ptr.segment_id@);
            let mut $segment_main = segment.main.take(Tracked(&mut main_0));

            { $body }

            segment.main.put(Tracked(&mut main_0), $segment_main);
            proof {
                $local.segments.tracked_insert(segment_ptr.segment_id@, SegmentLocalAccess {
                    main: main_0, mem: mem_0, main2: main2_0,
                });
            }
        } }
    }
}

pub use segment_get_mut_main;
pub use segment_get_mut_main_internal;

#[macro_export]
macro_rules! segment_get_mut_main2 {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_exec_macro_exprs!(
            $crate::types::segment_get_mut_main2_internal!($($tail)*))
    };
}

#[macro_export]
macro_rules! segment_get_mut_main2_internal {
    ($ptr:expr, $local:ident, $segment_main2:ident => $body:expr) => {
        ::builtin_macros::verus_exec_expr!{ {
            let segment_ptr = $ptr;

            let tracked perm = &$local.instance.thread_local_state_guards_segment(
                    $local.thread_id, segment_ptr.segment_id@, &$local.thread_token).points_to;
            let segment = vstd::raw_ptr::ptr_ref(segment_ptr.segment_ptr, Tracked(perm));

            let tracked SegmentLocalAccess { main: main_0, mem: mem_0, main2: mut main2_0 } =
                $local.segments.tracked_remove(segment_ptr.segment_id@);
            let mut $segment_main2 = segment.main2.take(Tracked(&mut main2_0));

            { $body }

            segment.main2.put(Tracked(&mut main2_0), $segment_main2);
            proof {
                $local.segments.tracked_insert(segment_ptr.segment_id@, SegmentLocalAccess {
                    main: main_0, mem: mem_0, main2: main2_0,
                });
            }
        } }
    }
}

pub use segment_get_mut_main2;
pub use segment_get_mut_main2_internal;

#[macro_export]
macro_rules! segment_get_mut_local {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_exec_macro_exprs!(
            $crate::types::segment_get_mut_local_internal!($($tail)*))
    };
}

#[macro_export]
macro_rules! segment_get_mut_local_internal {
    ($ptr:expr, $local:ident, $segment_local:ident => $body:expr) => {
        ::builtin_macros::verus_exec_expr!{ {
            let segment_ptr = $ptr;

            let tracked perm = &$local.instance.thread_local_state_guards_segment(
                    $local.thread_id, segment_ptr.segment_id@, &$local.thread_token).points_to;
            let segment = vstd::raw_ptr::ptr_ref(segment_ptr.segment_ptr, Tracked(perm));

            let tracked mut $segment_local =
                $local.segments.tracked_remove(segment_ptr.segment_id@);

            { $body }

            proof {
                $local.segments.tracked_insert(segment_ptr.segment_id@, $segment_local);
            }
        } }
    }
}

pub use segment_get_mut_local;
pub use segment_get_mut_local_internal;


}
