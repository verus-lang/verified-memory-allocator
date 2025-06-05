#![allow(unused_imports)]

use core::intrinsics::{unlikely, likely};

use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::*;
use vstd::modes::*;
use vstd::set_lib::*;
use vstd::set::set_int_range;
use vstd::cell::*;
use vstd::shared::Shared;

use crate::tokens::{Mim, BlockId, DelayState, ThreadState, HeapState, HeapId, TldId, ThreadId};
use crate::types::*;
use crate::layout::*;
use crate::linked_list::*;
use crate::dealloc_token::*;
use crate::alloc_generic::*;
use crate::os_mem_util::*;
use crate::config::*;
use crate::bin_sizes::*;
use crate::page_organization::*;
use crate::os_mem::*;
use crate::thread::*;

verus!{

pub tracked struct Global {
    pub(crate) tracked instance: Mim::Instance,
    pub(crate) tracked my_inst: Mim::my_inst,
}

impl Global {
    #[verifier::type_invariant]
    pub(crate) closed spec fn wf(&self) -> bool {
        self.my_inst.instance_id() == self.instance.id()
        && self.my_inst.value() == self.instance.id()
    }

    pub open(crate) spec fn wf_right_to_use_thread(&self, right: RightToUseThread, tid: ThreadId) -> bool {
        right.instance_id() == self.instance.id() && right.element() == tid
    }

    pub open(crate) spec fn inst(&self) -> MimInst {
        self.instance
    }
}

type RightToUseThread = Mim::right_to_use_thread;
type MimInst = Mim::Instance;


/*
impl RightToUseThread {
    pub open spec fn wf(tid: ThreadId) { true } // TODO
}
*/

//impl Copy for Global { }

pub proof fn global_init() -> (tracked res: (Global, IMap<ThreadId, Mim::right_to_use_thread>))    // $line_count$Trusted$
    ensures // $line_count$Trusted$
        forall |tid: ThreadId| #[trigger] res.1.dom().contains(tid) // $line_count$Trusted$
          && res.0.wf_right_to_use_thread(res.1[tid], tid) // $line_count$Trusted$
{
    let tracked (Tracked(instance), Tracked(right_to_set_inst), _, _, Tracked(rights), _, _, _, _, _, _, _, _) = Mim::Instance::initialize(
        IMap::tracked_empty(), IMap::tracked_empty(), IMap::tracked_empty(),
        );
    let tracked my_inst = instance.set_inst(instance.id(), right_to_set_inst.tracked_unwrap());
    (Global { instance, my_inst }, rights.into_map())
}

pub fn heap_init(Tracked(global): Tracked<Global>, // $line_count$Trusted$
      Tracked(right): Tracked<Mim::right_to_use_thread>, // $line_count$Trusted$
      Tracked(cur_thread): Tracked<IsThread> // $line_count$Trusted$
) -> (res: (HeapPtr, Tracked<Option<Local>>)) // $line_count$Trusted$
    requires global.wf_right_to_use_thread(right, cur_thread@), // $line_count$Trusted$
    ensures ({ let (heap, local_opt) = res; { // $line_count$Trusted$
        heap.heap_ptr.addr() != 0 ==> // $line_count$Trusted$
            local_opt@.is_some() // $line_count$Trusted$
            && local_opt@.unwrap().wf() // $line_count$Trusted$
            && local_opt@.unwrap().inst() == global.inst() // $line_count$Trusted$
            && heap.wf() // $line_count$Trusted$
            && heap.is_in(local_opt@.unwrap()) // $line_count$Trusted$
    }}) // $line_count$Trusted$
{
    proof { use_type_invariant(&global); }
    increment_thread_count();

    // TODO use a cache for thread data
    let (addr, Tracked(mem)) = thread_data_alloc();
    if addr.addr() == 0 {
        return (HeapPtr { heap_ptr: core::ptr::null_mut(), heap_id: Ghost(arbitrary()) }, Tracked(None));
    }

    proof {
        const_facts();
        assert(SIZEOF_HEAP == vstd::layout::size_of::<Heap>());
        assert(SIZEOF_TLD == vstd::layout::size_of::<Tld>());
        assert(addr as int % vstd::layout::align_of::<Heap>() as int == 0);
        assert((addr as usize + SIZEOF_HEAP) as int % vstd::layout::align_of::<Tld>() as int == 0);
    }
    vstd::layout::layout_for_type_is_valid::<Heap>(); // $line_count$Proof$
    vstd::layout::layout_for_type_is_valid::<Tld>(); // $line_count$Proof$

    let tracked points_to_heap_raw = mem.take_points_to_range(addr as int, SIZEOF_HEAP as int);
    let tracked points_to_tld_raw = mem.take_points_to_range(addr as usize + SIZEOF_HEAP, SIZEOF_TLD as int);
    let tracked mut points_to_heap = points_to_heap_raw.into_typed(addr as usize);
    let tracked mut points_to_tld = points_to_tld_raw.into_typed((addr as int + SIZEOF_HEAP) as usize);
    let heap_ptr = addr as *mut Heap;
    let tld_ptr = addr.with_addr(addr.addr() + SIZEOF_HEAP) as *mut Tld;

    let tracked (_, _, Tracked(uniq_reservation_tok)) = global.instance.reserve_uniq_identifier();
    let heap = HeapPtr { heap_ptr, heap_id: Ghost(HeapId { id: heap_ptr.addr() as nat, provenance: heap_ptr@.provenance, uniq: uniq_reservation_tok.element().uniq }) };
    let tld = TldPtr { tld_ptr, tld_id: Ghost(TldId { id: tld_ptr.addr() as nat, provenance: tld_ptr@.provenance }) };

    let page_empty_stuff = init_empty_page_ptr();
    let EmptyPageStuff { ptr: page_empty_ptr, pfa: Tracked(page_empty_ptr_access) } = page_empty_stuff;

    let mut pages_free_direct = pages_free_direct_tmp();
    let mut pages = pages_tmp();
    let mut span_queue_headers = span_queue_headers_tmp();

    let mut i = 0;
    while i < PAGES_DIRECT
        invariant 0 <= i <= PAGES_DIRECT,
          forall |j: int| 0 <= j < i ==> pages_free_direct[j] == page_empty_ptr,
    {
        pages_free_direct.set(i, page_empty_ptr);
        i = i + 1;
    }

    let mut i = 0;
    while i < SEGMENT_BIN_MAX + 1
        invariant 0 <= i <= SEGMENT_BIN_MAX + 1,
          forall |j: int| 0 <= j < i ==> (#[trigger] span_queue_headers[j]).first.addr() == 0
              && span_queue_headers[j].last.addr() == 0,
    {
        span_queue_headers.set(i, SpanQueueHeader {
            first: core::ptr::null_mut(),
            last: core::ptr::null_mut(),
        });
        i = i + 1;
    }

    /*let mut i = 0;
    while i < BIN_FULL + 1
        invariant 0 <= i <= BIN_FULL + 1
          pages.len() == i,
          forall |j: int| 0 <= j < i ==> pages[j] == PageQueue {
              
          };
    {
        pages.push(PageQueue {
            first: core::ptr::null_mut(),
            last: core::ptr::null_mut(),
            block_size: 
        });
    }*/

    let (pages_free_direct_pcell, Tracked(pages_free_direct_pointsto)) = PCell::new(pages_free_direct);
    let (pages_pcell, Tracked(pages_pointsto)) = PCell::new(pages);
    let (page_count_pcell, Tracked(page_count_pointsto)) = PCell::new(0);
    let (page_retired_min_pcell, Tracked(page_retired_min_pointsto)) = PCell::new(0);
    let (page_retired_max_pcell, Tracked(page_retired_max_pointsto)) = PCell::new(0);

    let (thread_id, Tracked(is_thread)) = crate::thread::thread_id();
    proof {
        is_thread.agrees(cur_thread);
    }

    ptr_mut_write(heap_ptr, Tracked(&mut points_to_heap), Heap {
        tld_ptr: tld,
        pages_free_direct: pages_free_direct_pcell,
        pages: pages_pcell,
        thread_delayed_free: ThreadLLSimple::empty(Ghost(global.instance), Ghost(heap.heap_id@)),
        thread_id,
        arena_id: 0,
        page_count: page_count_pcell,
        page_retired_min: page_retired_min_pcell,
        page_retired_max: page_retired_max_pcell,
        no_reclaim: false,
        page_empty_ptr,
    });

    ptr_mut_write(tld_ptr, Tracked(&mut points_to_tld), Tld {
        heap_backing: heap_ptr,
        segments: SegmentsTld {
            span_queue_headers,
            count: 0,
            peak_count: 0,
            current_size: 0,
            peak_size: 0,
        },
    });

    let tracked heap_shared_access = HeapSharedAccess { points_to: points_to_heap };
    assert(global.instance.id() == right.instance_id());
    assert(right.element() == thread_id);

    let tracked (Tracked(thread_token), Tracked(checked_token)) = global.instance.create_thread_mk_tokens(
            thread_id, 
            ThreadState {
                heap_id: heap.heap_id@,
                heap: HeapState {
                    shared_access: heap_shared_access,
                },
                segments: IMap::empty(),
                pages: IMap::empty(),
            },
            &global.my_inst,
            right,
            heap_shared_access,
            uniq_reservation_tok);

    let ghost page_organization = PageOrg::take_step::initialize();
    let tracked my_inst = global.my_inst.clone();
    let tracked local = Local {
        thread_id,
        my_inst,
        is_thread,
        instance: global.instance,
        thread_token,
        checked_token,
        heap_id: heap.heap_id@,
        heap: HeapLocalAccess {
            pages_free_direct: pages_free_direct_pointsto,
            pages: pages_pointsto,
            page_count: page_count_pointsto,
            page_retired_min: page_retired_min_pointsto,
            page_retired_max: page_retired_max_pointsto,
        },
        tld_id: tld.tld_id@,
        tld: points_to_tld,
        segments: Map::tracked_empty(),
        pages: Map::tracked_empty(),
        psa: Map::empty(),
        unused_pages: Map::tracked_empty(),
        page_organization,
        page_empty_global: page_empty_ptr_access,
    };

    proof {
        let emp = local.page_empty_global@.s.points_to.ptr();
        let pfd = local.heap.pages_free_direct.value()@;
        let pages = local.heap.pages.value()@;
        assert forall |wsize|
          0 <= wsize < pfd.len() implies
            pages_free_direct_match(
                (#[trigger] pfd[wsize]),
                pages[smallest_bin_fitting_size(wsize * INTPTR_SIZE)].first,
                emp)
        by {
            bounds_for_smallest_bin_fitting_size(wsize * INTPTR_SIZE);
            //assert(0 <= smallest_bin_fitting_size(wsize * INTPTR_SIZE));
            //assert(smallest_bin_fitting_size(wsize * INTPTR_SIZE) < pages.len());
        }

        assert(pages_free_direct_is_correct(
            local.heap.pages_free_direct.value()@,
            local.heap.pages.value()@,
            emp));
        assert(local.heap.wf_basic(local.heap_id, local.thread_token.value().heap, local.tld_id, local.instance.id()));
        assert(local.heap.wf(local.heap_id, local.thread_token.value().heap, local.tld_id, local.instance.id(), local.page_empty_global@.s.points_to.ptr()));
        assert( local.thread_token.value().segments.dom() == local.segments.dom().to_infinite() );  // extn
        assert(local.wf_main());
        assert(local.wf());
    }

    (heap, Tracked(Some(local)))
}


impl PageQueue {
    #[inline]
    fn empty(wsize: usize) -> (pq: PageQueue)
        requires wsize < 0x1_0000_0000_0000,
        ensures
          pq.first.addr() == 0,
          pq.last.addr() == 0,
          pq.block_size == wsize * INTPTR_SIZE
    {
        assert(INTPTR_SIZE as usize == 8);
        PageQueue {
            first: core::ptr::null_mut(),
            last: core::ptr::null_mut(),
            block_size: wsize * INTPTR_SIZE as usize,
        }
    }
}

#[inline]
fn pages_tmp() -> (pages: [PageQueue; 75])
    ensures pages@.len() == BIN_FULL + 1,
      forall |p| 0 <= p < pages@.len() ==> (#[trigger] pages[p]).first.addr() == 0
          && pages[p].last.addr() == 0
          && (valid_bin_idx(p) ==> pages[p].block_size == size_of_bin(p)),
      pages[0].block_size == 8,
      pages[BIN_FULL as int].block_size == 8 * (524288 + 2), //8 * (MEDIUM_OBJ_WSIZE_MAX + 2),
{
    proof { const_facts(); }
    let pages = [
        PageQueue::empty(1),

        PageQueue::empty(1),
        PageQueue::empty(2),
        PageQueue::empty(3),
        PageQueue::empty(4),
        PageQueue::empty(5),
        PageQueue::empty(6),
        PageQueue::empty(7),
        PageQueue::empty(8),

        PageQueue::empty(10),
        PageQueue::empty(12),
        PageQueue::empty(14),
        PageQueue::empty(16),
        PageQueue::empty(20),
        PageQueue::empty(24),
        PageQueue::empty(28),
        PageQueue::empty(32),

        PageQueue::empty(40),
        PageQueue::empty(48),
        PageQueue::empty(56),
        PageQueue::empty(64),
        PageQueue::empty(80),
        PageQueue::empty(96),
        PageQueue::empty(112),
        PageQueue::empty(128),

        PageQueue::empty(160),
        PageQueue::empty(192),
        PageQueue::empty(224),
        PageQueue::empty(256),
        PageQueue::empty(320),
        PageQueue::empty(384),
        PageQueue::empty(448),
        PageQueue::empty(512),

        PageQueue::empty(640),
        PageQueue::empty(768),
        PageQueue::empty(896),
        PageQueue::empty(1024),
        PageQueue::empty(1280),
        PageQueue::empty(1536),
        PageQueue::empty(1792),
        PageQueue::empty(2048),

        PageQueue::empty(2560),
        PageQueue::empty(3072),
        PageQueue::empty(3584),
        PageQueue::empty(4096),
        PageQueue::empty(5120),
        PageQueue::empty(6144),
        PageQueue::empty(7168),
        PageQueue::empty(8192),

        PageQueue::empty(10240),
        PageQueue::empty(12288),
        PageQueue::empty(14336),
        PageQueue::empty(16384),
        PageQueue::empty(20480),
        PageQueue::empty(24576),
        PageQueue::empty(28672),
        PageQueue::empty(32768),

        PageQueue::empty(40960),
        PageQueue::empty(49152),
        PageQueue::empty(57344),
        PageQueue::empty(65536),
        PageQueue::empty(81920),
        PageQueue::empty(98304),
        PageQueue::empty(114688),
        PageQueue::empty(131072),

        PageQueue::empty(163840),
        PageQueue::empty(196608),
        PageQueue::empty(229376),
        PageQueue::empty(262144),
        PageQueue::empty(327680),
        PageQueue::empty(393216),
        PageQueue::empty(458752),
        PageQueue::empty(524288),

        //PageQueue::empty(MEDIUM_OBJ_WSIZE_MAX as usize + 1),
        //PageQueue::empty(MEDIUM_OBJ_WSIZE_MAX as usize + 2),
        PageQueue::empty(524288 + 1),
        PageQueue::empty(524288 + 2),
    ];

    proof {
        assert forall |p| 0 <= p < pages@.len() implies (#[trigger] pages[p]).first.addr() == 0
            && pages[p].last.addr() == 0
            && (valid_bin_idx(p) ==> pages[p].block_size == size_of_bin(p))
        by {
            if valid_bin_idx(p) {
                reveal(size_of_bin);
                if p <= 1 { assert(p == 1); assert(size_of_bin(1) == 8) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 2 { assert(p == 2); assert(size_of_bin(2) == 16) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 3 { assert(p == 3); assert(size_of_bin(3) == 24) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 4 { assert(p == 4); assert(size_of_bin(4) == 32) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 5 { assert(p == 5); assert(size_of_bin(5) == 40) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 6 { assert(p == 6); assert(size_of_bin(6) == 48) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 7 { assert(p == 7); assert(size_of_bin(7) == 56) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 8 { assert(p == 8); assert(size_of_bin(8) == 64) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 9 { assert(p == 9); assert(size_of_bin(9) == 80) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 10 { assert(p == 10); assert(size_of_bin(10) == 96) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 11 { assert(p == 11); assert(size_of_bin(11) == 112) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 12 { assert(p == 12); assert(size_of_bin(12) == 128) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 13 { assert(p == 13); assert(size_of_bin(13) == 160) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 14 { assert(p == 14); assert(size_of_bin(14) == 192) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 15 { assert(p == 15); assert(size_of_bin(15) == 224) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 16 { assert(p == 16); assert(size_of_bin(16) == 256) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 17 { assert(p == 17); assert(size_of_bin(17) == 320) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 18 { assert(p == 18); assert(size_of_bin(18) == 384) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 19 { assert(p == 19); assert(size_of_bin(19) == 448) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 20 { assert(p == 20); assert(size_of_bin(20) == 512) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 21 { assert(p == 21); assert(size_of_bin(21) == 640) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 22 { assert(p == 22); assert(size_of_bin(22) == 768) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 23 { assert(p == 23); assert(size_of_bin(23) == 896) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 24 { assert(p == 24); assert(size_of_bin(24) == 1024) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 25 { assert(p == 25); assert(size_of_bin(25) == 1280) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 26 { assert(p == 26); assert(size_of_bin(26) == 1536) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 27 { assert(p == 27); assert(size_of_bin(27) == 1792) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 28 { assert(p == 28); assert(size_of_bin(28) == 2048) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 29 { assert(p == 29); assert(size_of_bin(29) == 2560) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 30 { assert(p == 30); assert(size_of_bin(30) == 3072) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 31 { assert(p == 31); assert(size_of_bin(31) == 3584) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 32 { assert(p == 32); assert(size_of_bin(32) == 4096) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 33 { assert(p == 33); assert(size_of_bin(33) == 5120) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 34 { assert(p == 34); assert(size_of_bin(34) == 6144) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 35 { assert(p == 35); assert(size_of_bin(35) == 7168) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 36 { assert(p == 36); assert(size_of_bin(36) == 8192) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 37 { assert(p == 37); assert(size_of_bin(37) == 10240) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 38 { assert(p == 38); assert(size_of_bin(38) == 12288) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 39 { assert(p == 39); assert(size_of_bin(39) == 14336) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 40 { assert(p == 40); assert(size_of_bin(40) == 16384) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 41 { assert(p == 41); assert(size_of_bin(41) == 20480) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 42 { assert(p == 42); assert(size_of_bin(42) == 24576) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 43 { assert(p == 43); assert(size_of_bin(43) == 28672) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 44 { assert(p == 44); assert(size_of_bin(44) == 32768) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 45 { assert(p == 45); assert(size_of_bin(45) == 40960) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 46 { assert(p == 46); assert(size_of_bin(46) == 49152) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 47 { assert(p == 47); assert(size_of_bin(47) == 57344) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 48 { assert(p == 48); assert(size_of_bin(48) == 65536) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 49 { assert(p == 49); assert(size_of_bin(49) == 81920) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 50 { assert(p == 50); assert(size_of_bin(50) == 98304) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 51 { assert(p == 51); assert(size_of_bin(51) == 114688) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 52 { assert(p == 52); assert(size_of_bin(52) == 131072) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 53 { assert(p == 53); assert(size_of_bin(53) == 163840) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 54 { assert(p == 54); assert(size_of_bin(54) == 196608) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 55 { assert(p == 55); assert(size_of_bin(55) == 229376) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 56 { assert(p == 56); assert(size_of_bin(56) == 262144) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 57 { assert(p == 57); assert(size_of_bin(57) == 327680) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 58 { assert(p == 58); assert(size_of_bin(58) == 393216) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 59 { assert(p == 59); assert(size_of_bin(59) == 458752) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 60 { assert(p == 60); assert(size_of_bin(60) == 524288) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 61 { assert(p == 61); assert(size_of_bin(61) == 655360) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 62 { assert(p == 62); assert(size_of_bin(62) == 786432) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 63 { assert(p == 63); assert(size_of_bin(63) == 917504) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 64 { assert(p == 64); assert(size_of_bin(64) == 1048576) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 65 { assert(p == 65); assert(size_of_bin(65) == 1310720) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 66 { assert(p == 66); assert(size_of_bin(66) == 1572864) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 67 { assert(p == 67); assert(size_of_bin(67) == 1835008) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 68 { assert(p == 68); assert(size_of_bin(68) == 2097152) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 69 { assert(p == 69); assert(size_of_bin(69) == 2621440) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 70 { assert(p == 70); assert(size_of_bin(70) == 3145728) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 71 { assert(p == 71); assert(size_of_bin(71) == 3670016) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else if p <= 72 { assert(p == 72); assert(size_of_bin(72) == 4194304) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                else { assert(p == 73); assert(size_of_bin(73) == 8 * (524288 + 1)) by(compute_only); assert(pages[p].block_size == size_of_bin(p)); }
                assert(pages[p].block_size == size_of_bin(p));
            }
        }
    }

    pages
}

fn pages_free_direct_tmp() -> [*mut Page; 129] {
    [
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        core::ptr::null_mut(),
    ]
}

fn span_queue_headers_tmp() -> [SpanQueueHeader; 32] {
    [
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
        SpanQueueHeader { first: core::ptr::null_mut(), last: core::ptr::null_mut() },
    ]
}

fn thread_data_alloc()
    -> (res: (*mut u8, Tracked<MemChunk>))
    ensures ({ let (p, mc) = res; {
        p.addr() != 0 ==> (
            mc@.pointsto_has_range(p as int, SIZEOF_HEAP + SIZEOF_TLD)
            && p as int + page_size() <= usize::MAX
            && p as int % 4096 == 0
            && p@.provenance == mc@.points_to.provenance()
        )
    }})
{
    let (addr, Tracked(mc)) = crate::os_mem::mmap_prot_read_write(core::ptr::null_mut(), 4096);

    if addr.addr() == MAP_FAILED {
        todo();
    }

    proof {
        //assert(set_int_range(addr as int, addr as int + 4096) <= mc.range_os_rw());
        //assert(set_int_range(addr as int, addr as int + 4096) <= mc.range_points_to());
        //assert(SIZEOF_HEAP + SIZEOF_TLD < page_size());
        //assert(mc.pointsto_has_range(addr as int, SIZEOF_HEAP + SIZEOF_TLD));
    }
    (addr, Tracked(mc))
}

///// The global 'empty page'

/*
pub fn get_page_empty()
    -> (res: (PPtr<Page>, Tracked<Shared<PageFullAccess>>))
    ensures ({ let (page_ptr, pfa) = res; {
        pfa@@.wf_empty_page_global()
        && pfa@@.s.points_to@.pptr == page_ptr.id()
        && page_ptr.id() != 0
    }})
{
    let e = get_empty_page_stuff();
    (e.ptr, Tracked(e.pfa.borrow().clone()))
}
*/

struct EmptyPageStuff {
    ptr: *mut Page,
    pfa: Tracked<Shared<PageFullAccess>>,
}

impl EmptyPageStuff {
    pub closed spec fn wf(&self) -> bool {
        self.pfa@@.wf_empty_page_global()
        && self.pfa@@.s.points_to.ptr() == self.ptr
        && self.ptr.addr() != 0
    }
}

/*
#[verifier::external]
static EMPTY_PAGE_PTR: std::sync::LazyLock<EmptyPageStuff> =
    std::sync::LazyLock::new(init_empty_page_ptr);
*/

fn init_empty_page_ptr() -> (e: EmptyPageStuff)
    ensures e.wf(),
{
    let (pt, Tracked(mut mc)) = crate::os_mem::mmap_prot_read_write(core::ptr::null_mut(), 4096);

    if pt.addr() == MAP_FAILED {
        todo();
    }

    proof { const_facts(); }

    assert(set_int_range(pt as int, pt as int + 4096) <= mc.range_os_rw());
    assert(set_int_range(pt as int, pt as int + 4096) <= mc.range_points_to());
    assert(mc.pointsto_has_range(pt as int, 4096));
    assert(mc.pointsto_has_range(pt as int, SIZEOF_PAGE_HEADER as int));
    let tracked points_to_raw = mc.take_points_to_range(pt as int, SIZEOF_PAGE_HEADER as int);
    proof {
        assert(SIZEOF_PAGE_HEADER == vstd::layout::size_of::<Page>());
        mod_trans(pt as int, 4096,
            vstd::layout::align_of::<Page>() as int);
        assert(pt as int % vstd::layout::align_of::<Page>() as int == 0);
    }
    vstd::layout::layout_for_type_is_valid::<Page>(); // $line_count$Proof$
    let tracked mut points_to = points_to_raw.into_typed::<Page>(pt as usize);
    proof { points_to.is_nonnull(); }

    let (count_pcell, Tracked(count_perm)) = PCell::empty();
    let (prev_pcell, Tracked(prev_perm)) = PCell::empty();
    let (next_pcell, Tracked(next_perm)) = PCell::empty();
    let (inner_pcell, Tracked(inner_perm)) = PCell::new(PageInner {
        flags0: 0,
        flags1: 0,
        flags2: 0,
        capacity: 0,
        reserved: 0,
        free: LL::empty(),
        used: 0,
        xblock_size: 0,
        local_free: LL::empty(),
    });

    let tracked fake_inst = global_init().0.instance;

    let page_ptr = pt as *mut Page;
    ptr_mut_write(page_ptr, Tracked(&mut points_to), Page {
        count: count_pcell,
        offset: 0,
        inner: inner_pcell,
        xthread_free: ThreadLLWithDelayBits::empty(Tracked(fake_inst)),
        xheap: AtomicHeapPtr::empty(),
        prev: prev_pcell,
        next: next_pcell,
        padding: 0,
    });
    let Tracked(exposed) = expose_provenance(page_ptr);

    let tracked pfa = Shared::new(PageFullAccess {
        s: PageSharedAccess { points_to, exposed },
        l: PageLocalAccess {
            count: count_perm,
            inner: inner_perm,
            prev: prev_perm,
            next: next_perm,
        },
    });
    EmptyPageStuff { ptr: page_ptr, pfa: Tracked(pfa) }
}

/*
#[verifier::external_body]
fn get_empty_page_stuff() -> (e: &'static EmptyPageStuff)
    ensures e.wf()
{
    &*EMPTY_PAGE_PTR
}
*/

//// Current thread count

/*
struct_with_invariants!{
    pub struct ThreadCountAtomic {
        pub atomic: AtomicUsize<_, (), _>,
    }

    pub open spec fn wf(&self) -> bool {
        invariant
            on atomic
            is (v: usize, g: ())
        {
            true
        }
    }
}

impl ThreadCountAtomic {
    #[inline]
    pub get(&self) -> usize {
        self.atomic.load()
    }

    #[inline]
    pub new(&self) -> usize {
        self.atomic.load()
    }
}
*/

exec static THREAD_COUNT: core::sync::atomic::AtomicUsize = core::sync::atomic::AtomicUsize::new(0);

//exec static THREAD_COUNT: core::sync::atomic::AtomicUsize
//  ensures true
//  { core::sync::atomic::AtomicUsize::new(0) }

#[inline]
fn increment_thread_count() {
    THREAD_COUNT.fetch_add(1, core::sync::atomic::Ordering::Relaxed);
}

#[inline]
pub fn current_thread_count() -> usize {
    THREAD_COUNT.load(core::sync::atomic::Ordering::Relaxed)
}


}
