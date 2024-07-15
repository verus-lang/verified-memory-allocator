#![feature(allocator_api)]
#![allow(unused_imports)]

use state_machines_macros::*;
use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::*;
use vstd::layout::*;

use crate::types::{SegmentHeader, Page, PagePtr, SegmentPtr, todo};
use crate::tokens::{PageId, SegmentId, BlockId, HeapId, TldId};
use crate::config::*;

// Relationship between pointers and IDs

verus!{

pub open spec fn is_page_ptr(ptr: *mut Page, page_id: PageId) -> bool {
    ptr as int == page_header_start(page_id)
        && 0 <= page_id.idx <= SLICES_PER_SEGMENT
        && segment_start(page_id.segment_id) + SEGMENT_SIZE < usize::MAX
        && ptr@.provenance == page_id.segment_id.provenance
        && ptr@.metadata == Metadata::Thin
}

pub open spec fn is_segment_ptr(ptr: *mut SegmentHeader, segment_id: SegmentId) -> bool {
    ptr as int == segment_start(segment_id)
      && ptr as int + SEGMENT_SIZE < usize::MAX
      && ptr@.provenance == segment_id.provenance
      && ptr@.metadata == Metadata::Thin
}

pub open spec fn is_heap_ptr(ptr: int, heap_id: HeapId) -> bool {
    heap_id.id == ptr
}

pub open spec fn is_tld_ptr(ptr: int, tld_id: TldId) -> bool {
    tld_id.id == ptr
}

pub closed spec fn segment_start(segment_id: SegmentId) -> int {
    segment_id.id * (SEGMENT_SIZE as int)
}

pub open spec fn page_header_start(page_id: PageId) -> int {
    segment_start(page_id.segment_id) + SIZEOF_SEGMENT_HEADER + page_id.idx * SIZEOF_PAGE_HEADER
}

pub open spec fn page_start(page_id: PageId) -> int {
    segment_start(page_id.segment_id) + SLICE_SIZE * page_id.idx
}

pub closed spec fn start_offset(block_size: int) -> int {
    // Based on _mi_segment_page_start_from_slice
    if block_size >= INTPTR_SIZE as int && block_size <= 1024 {
        3 * MAX_ALIGN_GUARANTEE
    } else {
        0
    }
}

pub open spec fn block_start_at(page_id: PageId, block_size: int, block_idx: int) -> int {
    page_start(page_id)
         + start_offset(block_size)
         + block_idx * block_size
}

pub closed spec fn block_start(block_id: BlockId) -> int {
    block_start_at(block_id.page_id, block_id.block_size as int, block_id.idx as int)
}

pub open spec fn is_block_ptr(ptr: *mut u8, block_id: BlockId) -> bool {
    &&& ptr@.provenance == block_id.page_id.segment_id.provenance
    &&& ptr@.metadata == Metadata::Thin
    &&& is_block_ptr1(ptr as int, block_id)
}

#[verifier::opaque]
pub open spec fn is_block_ptr1(ptr: int, block_id: BlockId) -> bool {
    // ptr should be in the range (segment start, segment end]
    // Yes, that's open at the start and closed at the end
    //  - segment start is invalid since that's where the SegmentHeader is
    //  - segment end is valid because there might be a huge block there
    &&& segment_start(block_id.page_id.segment_id) < ptr
        <= segment_start(block_id.page_id.segment_id) + (SEGMENT_SIZE as int)
        < usize::MAX

    // Has valid slice_idx (again this is <= to account for the huge slice)
    &&& 0 <= block_id.slice_idx <= SLICES_PER_SEGMENT

    // It also has to be in the right slice
    &&& segment_start(block_id.page_id.segment_id) + (block_id.slice_idx * SLICE_SIZE)
        <= ptr
        < segment_start(block_id.page_id.segment_id) + (block_id.slice_idx * SLICE_SIZE)
              + SLICE_SIZE

    // the pptr should actually agree with the block_id
    &&& ptr == block_start(block_id)

    &&& 0 <= block_id.page_id.segment_id.id

    // The block size must be a multiple of the word size
    &&& block_id.block_size >= size_of::<crate::linked_list::Node>()
    &&& block_id.block_size % size_of::<crate::linked_list::Node>() == 0
}

pub open spec fn is_page_ptr_opt(pptr: *mut Page, opt_page_id: Option<PageId>) -> bool {
    match opt_page_id {
        Some(page_id) => is_page_ptr(pptr, page_id) && pptr.addr() != 0,
        None => pptr.addr() == 0,
    }
}

pub proof fn block_size_ge_word()
    ensures forall |p, block_id| is_block_ptr(p, block_id) ==>
        block_id.block_size >= size_of::<crate::linked_list::Node>()
{
    reveal(is_block_ptr1);
}

#[verifier::spinoff_prover]
pub proof fn block_ptr_aligned_to_word()
    ensures forall |p, block_id| is_block_ptr(p, block_id) ==>
        p as int % align_of::<crate::linked_list::Node>() as int == 0
{
    assert forall |p, block_id| is_block_ptr(p, block_id) implies
        p as int % align_of::<crate::linked_list::Node>() as int == 0
    by {
        const_facts();
        reveal(is_block_ptr1);
        crate::linked_list::size_of_node();
        let page_id = block_id.page_id;
        assert(segment_start(page_id.segment_id) % 8 == 0);
        assert(SLICE_SIZE % 8 == 0);
        assert(page_start(page_id) % 8 == 0);
        let block_size = block_id.block_size;
        assert(start_offset(block_size as int) % 8 == 0);
        assert(block_size % 8 == 0);
        let block_idx = block_id.idx as int;
        mod_mul(block_idx, block_size as int, 8);
        assert((block_idx * block_size) % 8 == 0);
        assert(block_start(block_id) % 8 == 0);
        assert(p as int % 8 == 0);
    }
}

pub proof fn block_start_at_diff(page_id: PageId, block_size: nat,
  block_idx1: nat, block_idx2: nat)
    ensures block_start_at(page_id, block_size as int, block_idx2 as int) ==
        block_start_at(page_id, block_size as int, block_idx1 as int) + (block_idx2 - block_idx1) * block_size
{
    assert(block_idx1 as int * block_size + (block_idx2 - block_idx1) * block_size
        == block_idx2 as int * block_size) by(nonlinear_arith);

    //assert(block_idx2 as int * block_size == block_idx2 * block_size);
    //assert(block_idx1 as int * block_size == block_idx1 * block_size);

    //assert(block_start_at(page_id, block_size as int, block_idx2 as int)
    //    ==    page_start(page_id) + start_offset(block_size as int) + block_idx2 * block_size);
    //assert(block_start_at(page_id, block_size as int, block_idx1 as int)
    //    ==    page_start(page_id) + start_offset(block_size as int) + block_idx1 * block_size);
}

// Bit lemmas

/*proof fn bitmask_is_mod(t: usize)
    ensures (t & (((1usize << 26usize) - 1) as usize)) == (t % (1usize << 26usize)),
{
    //assert((t & (sub(1usize << 26usize, 1) as usize)) == (t % (1usize << 26usize)))
    //    by(bit_vector);
}*/

/*proof fn bitmask_is_rounded_down(t: usize)
    ensures (t & !(((1usize << 26usize) - 1) as usize)) == t - (t % (1usize << 26usize))
{
    assert((t & !(sub((1usize << 26usize), 1) as usize)) == sub(t, (t % (1usize << 26usize))))
        by(bit_vector);
    assert((1usize << 26usize) >= 1usize) by(bit_vector);
    assert(t >= (t % (1usize << 26usize))) by(bit_vector);
}*/

/*proof fn mod_removes_remainder(s: int, t: int, r: int)
    requires
        0 <= r < t,
        0 <= s,
    ensures (s*t + r) - ((s*t + r) % t) == s*t
{
    /*
    if s == 0 {
        assert(r % t == r) by(nonlinear_arith)
            requires 0 <= r < t;
    } else {
        let x = ((s-1)*t + r);
        assert((x % t) == (x + t) % t) by(nonlinear_arith);
    }
    */
    //assert(((s*t + r) % t) == r) by(nonlinear_arith)
    //  requires 0 <= r < t, 0 < t;

    //let x = s*t + r;
    //assert((x / t) * t + x % t == x) by(nonlinear_arith);
}*/

// Executable calculations

pub fn calculate_segment_ptr_from_block(ptr: *mut u8, Ghost(block_id): Ghost<BlockId>) -> (res: *mut SegmentHeader)
    requires is_block_ptr(ptr, block_id),
    ensures is_segment_ptr(res, block_id.page_id.segment_id),
{
    let block_p = ptr.addr();

    proof {
        reveal(is_block_ptr1);
        const_facts();
        assert(block_p > 0);

        //bitmask_is_rounded_down((block_p - 1) as usize);
        //mod_removes_remainder(block_id.page_id.segment_id.id as int, SEGMENT_SIZE as int,
        //    block_p - 1 - segment_start(block_id.page_id.segment_id));

        //assert(SEGMENT_SHIFT == 26);
        //assert(SEGMENT_SIZE >= 1);

        let id = block_id.page_id.segment_id.id as usize;
        assert(id == block_id.page_id.segment_id.id);
        assert(id < 0x7fffffffff);
        assert(
            sub(block_p, 1) & (!0x1ffffffusize) == mul(id, 0x2000000)) by(bit_vector)
          requires 
            mul(id, 0x2000000) < block_p <= add(mul(id, 0x2000000), 0x2000000),
            id < 0x7fffffffffusize;

        assert(mul(id, 0x2000000) == id * 0x2000000);
        assert(add(mul(id, 0x2000000), 0x2000000) == id * 0x2000000 + 0x2000000);
    }

    // Based on _mi_ptr_segment
    let segment_p = (block_p - 1) & (!((SEGMENT_SIZE - 1) as usize));

    /*proof {
        let s = block_id.page_id.segment_id.id;
        let t = SEGMENT_SIZE as int;
        let r = block_p - 1 - segment_start(block_id.page_id.segment_id);

        assert(block_p as int - 1 == s*t + r);
        assert(segment_p as int ==
            (block_p - 1) as int - ((block_p - 1) as int % SEGMENT_SIZE as int));
        assert(segment_p as int == (s*t + r) - ((s*t + r) % t));
    }*/

    ptr.with_addr(segment_p) as *mut SegmentHeader
}

/*
pub fn calculate_slice_idx_from_block(block_ptr: PPtr<u8>, segment_ptr: PPtr<SegmentHeader>, Ghost(block_id): Ghost<BlockId>) -> (slice_idx: usize)
    requires
        is_block_ptr(block_ptr.id(), block_id),
        is_segment_ptr(segment_ptr.id(), block_id.page_id.segment_id)
    ensures slice_idx as int == block_id.slice_idx,
{
    let block_p = block_ptr.addr();
    let segment_p = segment_ptr.addr();

    // Based on _mi_segment_page_of
    let diff = segment_p - block_p;
    diff >> (SLICE_SHIFT as usize)
}
*/

pub fn calculate_slice_page_ptr_from_block(block_ptr: *mut u8, segment_ptr: *mut SegmentHeader, Ghost(block_id): Ghost<BlockId>) -> (page_ptr: *mut Page)
    requires
        is_block_ptr(block_ptr, block_id),
        is_segment_ptr(segment_ptr, block_id.page_id.segment_id),
    ensures is_page_ptr(page_ptr, block_id.page_id_for_slice())
{
    let b = block_ptr.addr();
    let s = segment_ptr.addr();
    proof {
        reveal(is_block_ptr1);
        const_facts();
        assert(b - s <= SEGMENT_SIZE);
    }
    let q = (b - s) / SLICE_SIZE as usize;
    proof {
        assert((b - s) / SLICE_SIZE as int <= SLICES_PER_SEGMENT) by(nonlinear_arith)
          requires SLICES_PER_SEGMENT == SEGMENT_SIZE as int / SLICE_SIZE as int,
            b - s <= SEGMENT_SIZE as int,
            SLICE_SIZE > 0;
    }
    let h = s + SIZEOF_SEGMENT_HEADER + q * SIZEOF_PAGE_HEADER;
    block_ptr.with_addr(h) as *mut Page
}

#[inline(always)]
pub fn calculate_page_ptr_subtract_offset(
    page_ptr: *mut Page, offset: u32, Ghost(page_id): Ghost<PageId>, Ghost(target_page_id): Ghost<PageId>) -> (result: *mut Page)
    requires
        is_page_ptr(page_ptr, page_id),
        page_id.segment_id == target_page_id.segment_id,
        offset == (page_id.idx - target_page_id.idx) * SIZEOF_PAGE_HEADER,
    ensures
        is_page_ptr(result, target_page_id),
{
    proof {
        segment_start_ge0(page_id.segment_id);
    }

    let p = page_ptr.addr();
    let q = p - offset as usize;
    page_ptr.with_addr(q)
}

/*
pub fn calculate_page_ptr_add_offset(
    page_ptr: *mut Page, offset: u32, Ghost(page_id): Ghost<PageId>) -> (result: *mut Page)
    requires
        is_page_ptr(page_ptr as int, page_id),
        offset <= 0x1_0000,
    ensures
        is_page_ptr(result as int, PageId { idx: (page_id.idx + offset) as nat, ..page_id }),
{
    todo(); loop { }
}
*/

/*
pub fn calculate_segment_page_start(
    segment_ptr: SegmentPtr,
    page_ptr: PagePtr)
) -> (p: PPtr<u8>)
    ensures
        p as int == page_start(page_ptr.page_id)
{
}
*/

pub fn calculate_page_start(page_ptr: PagePtr, block_size: usize) -> (addr: usize)
    requires block_size > 0, page_ptr.wf(),
    ensures addr == block_start_at(page_ptr.page_id@, block_size as int, 0)
{
    let segment_ptr = SegmentPtr::ptr_segment(page_ptr);
    segment_page_start_from_slice(segment_ptr, page_ptr, block_size)
}

pub fn calculate_page_block_at(
    page_start: usize,
    block_size: usize,
    idx: usize,
    Ghost(page_id): Ghost<PageId>
) -> (p: usize)
    requires page_start == block_start_at(page_id, block_size as int, 0),
        block_start_at(page_id, block_size as int, 0)
            + idx as int * block_size as int <= segment_start(page_id.segment_id) + SEGMENT_SIZE,
        segment_start(page_id.segment_id) + SEGMENT_SIZE < usize::MAX,
    ensures
        p == block_start_at(page_id, block_size as int, idx as int),
        p == page_start + idx as int * block_size as int
{
    proof {
        const_facts();
        assert(block_size * idx >= 0) by(nonlinear_arith)
            requires block_size >= 0, idx >= 0;
        assert(block_size * idx == idx * block_size) by(nonlinear_arith);
    }
    let p = page_start + block_size * idx;
    return p;
}

pub proof fn mk_segment_id(p: *mut SegmentHeader) -> (id: SegmentId)
    requires p as int >= 0,
        p as int % SEGMENT_SIZE as int == 0,
        ((p as int + SEGMENT_SIZE as int) < usize::MAX),
        p@.metadata == Metadata::Thin,
    ensures is_segment_ptr(p, id),
{
    const_facts();
    SegmentId { id: p as nat / SEGMENT_SIZE as nat, provenance: p@.provenance, uniq: 0 }
}

pub proof fn segment_id_divis(sp: SegmentPtr)
    requires sp.wf(),
    ensures sp.segment_ptr as int % SEGMENT_SIZE as int == 0,
{
    const_facts();
}

pub fn segment_page_start_from_slice(
    segment_ptr: SegmentPtr,
    slice: PagePtr,
    xblock_size: usize)
  -> (res: usize) // start_offset
    requires
        segment_ptr.wf(), slice.wf(), slice.page_id@.segment_id == segment_ptr.segment_id@
    ensures ({ let start_offset = res; {
        &&& xblock_size == 0 ==>
            start_offset == segment_start(segment_ptr.segment_id@)
                + slice.page_id@.idx * SLICE_SIZE
        &&& xblock_size > 0 ==>
            start_offset == block_start_at(slice.page_id@, xblock_size as int, 0)
    }})
{
    proof { const_facts(); }

    let idxx = slice.page_ptr.addr() - (segment_ptr.segment_ptr.addr() + SIZEOF_SEGMENT_HEADER);
    let idx = idxx / SIZEOF_PAGE_HEADER;

    let start_offset = if xblock_size >= INTPTR_SIZE as usize && xblock_size <= 1024 {
        3 * MAX_ALIGN_GUARANTEE
    } else {
        0
    };

    segment_ptr.segment_ptr.addr() + (idx * SLICE_SIZE as usize) + start_offset
}

proof fn bitand_with_mask_gives_rounding(x: usize, y: usize)
    requires y != 0, y & sub(y, 1) == 0,
    ensures x & !sub(y, 1) == (x / y) * y,
    decreases y,
{
    if y == 1 {
        assert(x & !sub(1, 1) == x) by(bit_vector);
        assert(x & !sub(y, 1) == (x / y) * y);
    } else {
        assert((y >> 1) < y) by(bit_vector) requires y != 0usize;
        assert((y >> 1) != 0usize) by(bit_vector) requires y != 0usize, y != 1usize;
        assert(y & sub(y, 1) == 0usize ==> (y >> 1) & sub(y >> 1, 1) == 0usize) by(bit_vector)
            requires y != 0usize, y != 1usize;
        bitand_with_mask_gives_rounding(x >> 1, y >> 1);

        assert(
          x & !sub(y, 1) == mul(2, (x >> 1) & !sub(y >> 1, 1))
            && (x >> 1) & !sub(y >> 1, 1) < 0x8000_0000_0000_0000usize
        ) by(bit_vector)
          requires y != 0usize, y != 1usize, y & sub(y, 1) == 0usize;

        let y1 = y >> 1;
        let x1 = x >> 1;
        let b = x % 2;
        assert(y >> 1 == y / 2) by(bit_vector);
        assert(x >> 1 == x / 2) by(bit_vector);
        assert(y == 2 * y1) by {
            assert(y & sub(y, 1) == 0usize ==> y % 2usize == 0usize) by(bit_vector)
                requires y != 0usize, y != 1usize;
        }
        assert(x == 2 * x1 + b);
        assert((2 * x1 + b) / (2 * y1) * (2 * y1)
          == 2 * (x1 / y1 * y1)) by
        {
            let t = (2 * x1 + b) / (2 * y1);
            assert(t * (2 * y1)
                == 2 * (t * y1)) by(nonlinear_arith);
            two_mul_with_bit0(x1 as int, y1 as int);
            two_mul_with_bit1(x1 as int, y1 as int);
            assert((2 * x1 + b) / (2 * y1) == x1 / y1); // by(nonlinear_arith)
                //requires b == 0 || b == 1;
        }
        assert(
          x / y * y
            == 2 * (((x >> 1) / (y >> 1)) * (y >> 1))
        );
        //assert(((x >> 1) / (y >> 1)) * (y >> 1) == ((x >> 1) & !sub(y >> 1, 1)));
        //assert(x & !sub(y, 1) == 2 * ((x >> 1) & !sub(y >> 1, 1)));
        //assert(x & !sub(y, 1) == (x / y) * y);
    }
}

#[verifier::spinoff_prover]
proof fn two_mul_with_bit0(x1: int, y1: int)
    requires y1 != 0,
    ensures (2 * x1) / (2 * y1) == x1 / y1
{
    assert(
        (2 * x1) / (2 * y1) == ((2 * x1) / 2) / y1) by(nonlinear_arith)
        requires y1 != 0;
    assert((2 * x1) / 2 == x1);
}

#[verifier::spinoff_prover]
proof fn two_mul_with_bit1(x1: int, y1: int)
    requires y1 != 0,
    ensures (2 * x1 + 1) / (2 * y1) == x1 / y1
{
    assert(
        (2 * x1 + 1) / (2 * y1) == ((2 * x1 + 1) / 2) / y1) by(nonlinear_arith)
        requires y1 != 0;
    assert((2 * x1 + 1) / 2 == x1);
}


#[verifier::spinoff_prover]
#[inline]
pub fn align_down(x: usize, y: usize) -> (res: usize)
    requires y != 0,
    ensures
        res == (x as int / y as int) * y,
        res <= x < res + y,
        res % y == 0,
        (res / y * y) == res,
{
    let mask = y - 1;

    proof {
        assert(0 <= (x / y) * y <= x) by(nonlinear_arith)
            requires y > 0, x >= 0;

        //assert((y & mask) == 0usize ==> (x & !mask) == sub(x, x % y)) by(bit_vector)
        //    requires mask == sub(y, 1), y >= 1usize;
        if y & mask == 0usize {
            bitand_with_mask_gives_rounding(x, y);
            assert((x & !mask) == (x / y) * y);
            assert((x & !mask) == (x as int / y as int) * y);
        }

        assert((x as int / y as int) == (x / y) as int);

        assert(x / y * y + x % y == x) by(nonlinear_arith) requires y != 0;
        assert(0 <= x % y < y);
        let t = x / y;
        mul_mod_right(t as int, y as int);
        assert(y != 0 ==> (t * y) / y as int * y == t * y) by(nonlinear_arith);
    }

    if ((y & mask) == 0) { // power of two?
        x & !mask
    } else {
        (x / y) * y
    }
}

#[inline]
pub fn align_up(x: usize, y: usize) -> (res: usize)
    requires y != 0,
        x + y - 1 <= usize::MAX,
    ensures
        res == ((x + y - 1) / y as int) * y,
        x <= res <= x + y - 1,
        res % y == 0,
        (res / y * y) == res,
{
    let mask = y - 1;

    proof {
        if y & mask == 0 {
            bitand_with_mask_gives_rounding((x + y - 1) as usize, y);
            assert(((x + mask) as usize) & !mask == ((x + y - 1) / y as int) * y);
        }

        let z = x + mask;
        assert(z / y as int * y + z % y as int == z) by(nonlinear_arith) requires y != 0;

        let t = (x + y - 1) / y as int;
        mul_mod_right(t, y as int);
        assert(y != 0 ==> (t * y) / y as int * y == t * y) by(nonlinear_arith);
    }

    if ((y & mask) == 0) { // power of two?
        (x + mask) & !mask
    } else {
        ((x + mask) / y) * y
    }
}

#[verifier::integer_ring]
pub proof fn mod_trans(a: int, b: int, c: int)
    requires /*b != 0, c != 0,*/ a % b == 0, b % c == 0,
    ensures a % c == 0
{
}

#[verifier::integer_ring]
pub proof fn mod_mul(a: int, b: int, c: int)
    requires b % c == 0, // c > 0
    ensures (a * b) % c == 0,
{
}

#[verifier::integer_ring]
pub proof fn mul_mod_right(a: int, b: int)
    ensures (a * b) % b == 0,
{
}


impl SegmentPtr {
    #[inline]
    pub fn ptr_segment(page_ptr: PagePtr) -> (segment_ptr: SegmentPtr)
        requires page_ptr.wf(),
        ensures segment_ptr.wf(),
            segment_ptr.segment_id == page_ptr.page_id@.segment_id,
    {
        proof {
            const_facts();
            let p = page_ptr.page_ptr as int;
            let sid = page_ptr.page_id@.segment_id;
            assert((p / SEGMENT_SIZE as int) * SEGMENT_SIZE as int == segment_start(sid));
        }

        let p = page_ptr.page_ptr.addr();
        let s = (p / SEGMENT_SIZE as usize) * SEGMENT_SIZE as usize;
        SegmentPtr {
            segment_ptr: page_ptr.page_ptr.with_addr(s) as *mut SegmentHeader,
            segment_id: Ghost(page_ptr.page_id@.segment_id),
        }
    }
}

pub proof fn is_page_ptr_nonzero(ptr: *mut Page, page_id: PageId)
    requires is_page_ptr(ptr, page_id),
    ensures ptr as int != 0,
{
    segment_start_ge0(page_id.segment_id);
}

pub proof fn is_block_ptr_mult4(ptr: *mut u8, block_id: BlockId)
    requires is_block_ptr(ptr, block_id),
    ensures ptr as int % 4 == 0,
{
    hide(is_block_ptr);
    crate::linked_list::size_of_node();
    block_ptr_aligned_to_word();
}

pub proof fn segment_start_mult_commit_size(segment_id: SegmentId)
    ensures segment_start(segment_id) % COMMIT_SIZE as int == 0,
{
    const_facts();
    assert(COMMIT_SIZE as int == 65536);
}

pub proof fn segment_start_mult8(segment_id: SegmentId)
    ensures segment_start(segment_id) % 8 == 0,
{
    const_facts();
}

pub proof fn segment_start_ge0(segment_id: SegmentId)
    ensures segment_start(segment_id) >= 0,
{
    const_facts();
}

pub fn calculate_start_offset(block_size: usize) -> (res: u32)
    ensures res == start_offset(block_size as int),
{
    if block_size >= 8 && block_size <= 1024 {
        3 * MAX_ALIGN_GUARANTEE as u32
    } else {
        0
    }
}

pub proof fn start_offset_le_slice_size(block_size: int)
    ensures 0 <= start_offset(block_size) <= SLICE_SIZE,
        start_offset(block_size) == 0 || start_offset(block_size) == 3 * MAX_ALIGN_GUARANTEE,
{
}

pub proof fn segment_start_eq(sid: SegmentId, sid2: SegmentId)
    requires sid.id == sid2.id,
    ensures segment_start(sid) == segment_start(sid2)
{
}

pub proof fn get_block_start_from_is_block_ptr(ptr: *mut u8, block_id: BlockId)
    requires is_block_ptr(ptr, block_id),
    ensures ptr as int == block_start(block_id),
{
    reveal(is_block_ptr1);
}

pub proof fn get_block_start_defn(block_id: BlockId)
    ensures block_start(block_id)
      == block_start_at(block_id.page_id, block_id.block_size as int, block_id.idx as int),
{
}

pub proof fn sub_distribute(a: int, b: int, c: int)
    ensures a * c - b * c == (a - b) * c,
{
    assert(a * c - b * c == (a - b) * c) by(nonlinear_arith);
}

}
