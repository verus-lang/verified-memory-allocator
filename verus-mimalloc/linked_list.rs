#![allow(unused_imports)]

use state_machines_macros::*;
use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::modes::*;
use vstd::*;
use vstd::set_lib::*;
use vstd::layout::*;
use vstd::atomic_ghost::*;

use crate::tokens::{Mim, BlockId, PageId, DelayState, HeapId};
use crate::layout::{is_block_ptr, block_size_ge_word, block_ptr_aligned_to_word, block_start_at, block_start, is_block_ptr1};
use crate::types::*;
use crate::config::INTPTR_SIZE;
use core::intrinsics::unlikely;

verus!{

// Originally I wanted to do a linked list here in the proper Rust-idiomatic
// way, something like:
//
//    struct LL { next: Option<Box<LL>> }
//
// However, there were a couple of problems:
//
//  1. We need to pad each node out to the block size, which isn't statically fixed.
//     This problem isn't too hard to work around though, we just need to make our
//     own Box-like type that manages the size of the allocation.
//
//  2. Because of the way the thread-safe atomic linked list works, we need to
//     split the 'ownership' from the 'physical pointer', so we can write the pointer 
//     into a node without the ownership.
//
// Problem (2) seems more annoying to work around. At any rate, I've decided to just
// give up on the recursive datatype and do a flat list of pointers and pointer permissions.

#[repr(C)]
#[derive(Copy)]
pub struct Node {
    pub ptr: *mut Node,
}

impl Clone for Node {
    fn clone(&self) -> Node {
        Node { ptr: self.ptr }
    }
}

global layout Node is size == 8, align == 8;

pub proof fn size_of_node()
    ensures size_of::<Node>() == 8
        && align_of::<Node>() == 8
{
}

pub ghost struct LLData {
    ghost fixed_page: bool,
    ghost block_size: nat,   // only used if fixed_page=true
    ghost page_id: PageId,   // only used if fixed_page=true
    ghost heap_id: Option<HeapId>, // if set, then all blocks must have this HeapId

    ghost instance: Mim::Instance,
    ghost len: nat,
}

pub struct LL {
    first: *mut Node,

    data: Ghost<LLData>,

    // first to be popped off goes at the end
    perms: Tracked<Map<nat, (PointsTo<Node>, PointsToRaw, Mim::block, IsExposed)>>,
}

pub tracked struct LLGhostStateToReconvene {
    pub ghost block_size: nat,
    pub ghost page_id: PageId,
    pub ghost instance: Mim::Instance,

    pub tracked map: Map<nat, (PointsToRaw, Mim::block)>,
}

impl LL {
    pub closed spec fn next_ptr(&self, i: nat) -> *mut Node {
        if i == 0 {
            core::ptr::null_mut()
        } else {
            self.perms@.index((i - 1) as nat).0.ptr()
        }
    }

    pub closed spec fn valid_node(&self, i: nat, next_ptr: *mut Node) -> bool {
        0 <= i < self.data@.len ==> (
            self.perms@.dom().contains(i) && {
                  let (perm, padding, block_token, is_exposed) = self.perms@.index(i);

                  // Each node points to the next node
                  perm.is_init()
                  && perm.value().ptr.addr() == next_ptr.addr()
                  && perm.value().ptr@.metadata == Metadata::Thin

                  // The PointsToRaw makes up the rest of the block size allocation
                  && block_token@.key.block_size - size_of::<Node>() >= 0
                  && padding.is_range(perm.ptr().addr() + size_of::<Node>(),
                      block_token@.key.block_size - size_of::<Node>())
                  && padding.provenance() == perm.ptr()@.provenance
                  && is_exposed.provenance() == padding.provenance()

                  // block_token is correct
                  && block_token@.instance == self.data@.instance
                  && is_block_ptr(perm.ptr() as *mut u8, block_token@.key)
                  && perm.ptr()@.metadata == Metadata::Thin

                  && (self.data@.fixed_page ==> (
                      block_token@.key.page_id == self.data@.page_id
                      && block_token@.key.block_size == self.data@.block_size
                      //&& padding.provenance() == self.data@.page_id.segment_id.provenance
                  ))

                  && (match self.data@.heap_id {
                      Some(heap_id) => block_token@.value.heap_id == Some(heap_id),
                      None => true,
                  })
            }
        )
    }

    pub closed spec fn wf(&self) -> bool {
        &&& (forall |i: nat| self.perms@.dom().contains(i) ==> 0 <= i < self.data@.len)
        &&& self.first.addr() == self.next_ptr(self.data@.len).addr()
        &&& self.first@.metadata == Metadata::Thin
        &&& (forall |i: nat| self.valid_node(i, #[trigger] self.next_ptr(i)))
    }

    pub closed spec fn len(&self) -> nat {
        self.data@.len
    }

    pub closed spec fn page_id(&self) -> PageId {
        self.data@.page_id
    }

    pub closed spec fn block_size(&self) -> nat {
        self.data@.block_size
    }

    pub closed spec fn fixed_page(&self) -> bool {
        self.data@.fixed_page
    }

    pub closed spec fn instance(&self) -> Mim::Instance {
        self.data@.instance
    }

    pub closed spec fn heap_id(&self) -> Option<HeapId> {
        self.data@.heap_id
    }

    pub closed spec fn ptr(&self) -> *mut Node {
        self.first
    }

    /*spec fn is_valid_page_address(&self, ptr: int) -> bool {
        // We need this to save a ptr at this address
        // this is probably redundant since we also have is_block_ptr 
        ptr as int % size_of::<Node>() as int == 0
    }*/

    #[inline(always)]
    pub fn insert_block(&mut self, ptr: *mut u8, Tracked(points_to_raw): Tracked<PointsToRaw>, Tracked(block_token): Tracked<Mim::block>)
        requires old(self).wf(),
            points_to_raw.is_range(ptr as int, block_token@.key.block_size as int),
            points_to_raw.provenance() == ptr@.provenance,
            //old(self).is_valid_page_address(points_to_raw.ptr()),
            block_token@.instance == old(self).instance(),
            is_block_ptr(ptr, block_token@.key),
            old(self).fixed_page() ==> (
                block_token@.key.page_id == old(self).page_id()
                && block_token@.key.block_size == old(self).block_size()
            ),
            old(self).heap_id().is_none(),
        ensures
            self.wf(),
            self.block_size() == old(self).block_size(),
            self.len() == old(self).len() + 1,
            self.instance() == old(self).instance(),
            self.page_id() == old(self).page_id(),
            self.fixed_page() == old(self).fixed_page(),
            self.heap_id() == old(self).heap_id(),
    {
        let tracked mut mem1;
        let tracked mut mem2;
        vstd::layout::layout_for_type_is_valid::<Node>(); // $line_count$Proof$
        proof {
            block_size_ge_word();
            block_ptr_aligned_to_word();

            let tracked (m1, m2) = points_to_raw.split(set_int_range(ptr as int, ptr as int + size_of::<Node>() as int));
            mem1 = m1.into_typed::<Node>(ptr.addr());
            mem2 = m2;
        }

        let ptr = ptr as *mut Node;
        ptr_mut_write(ptr, Tracked(&mut mem1), Node { ptr: self.first });
        self.first = ptr;
        let Tracked(is_exposed) = expose_provenance(ptr);

        proof {
            let tracked tuple = (mem1, mem2, block_token, is_exposed);
            self.perms.borrow_mut().tracked_insert(self.data@.len, tuple);
            self.data@.len = self.data@.len + 1;

            let ghost len = self.data@.len;

            assert forall |i: nat| self.perms@.dom().contains(i) implies 0 <= i < self.data@.len
            by {
                if i + 1 < len { 
                    assert(old(self).perms@.dom().contains(i));
                }
            }

            assert forall |i: nat| #[trigger] self.valid_node(i, self.next_ptr(i))
            by {
                assert(old(self).valid_node(i, old(self).next_ptr(i)));
                if i > 0 {
                    let j = (i - 1) as nat;
                    assert(old(self).valid_node(j, old(self).next_ptr(j)));
                }
                /*if i < len {
                    if i != 0 {
                        assert(self.perms@.index((i - 1) as nat)
                          == old(self).perms@.index((i - 1) as nat));
                    }
                    assert(old(self).next_ptr(i) == self.next_ptr(i));
                    if i + 1 == len {
                        assert(self.valid_node(i, self.next_ptr(i)));
                    } else {
                        assert(self.valid_node(i, self.next_ptr(i)));
                    }
                }*/
            }
        }
    }

    // This is like insert_block but it only does the operation "ghostily".
    // This is used by the ThreadLL
    //
    // It requires the pointer writer has already been done, so it's just arranging
    // ghost data in a ghost LL.

    pub proof fn ghost_insert_block(
        tracked &mut self,
        tracked ptr: *mut Node,
        tracked points_to_ptr: PointsTo<Node>,
        tracked points_to_raw: PointsToRaw,
        tracked block_token: Mim::block,
        tracked is_exposed: IsExposed,
     )
        requires old(self).wf(),
            block_token@.instance == old(self).instance(),
            is_block_ptr(ptr as *mut u8, block_token@.key),

            // Require that the pointer has already been written:
            points_to_ptr.ptr() == ptr,
            points_to_ptr.is_init(),
            points_to_ptr.value().ptr.addr() == old(self).ptr().addr(),
            points_to_ptr.value().ptr@.metadata == Metadata::Thin,

            // Require the padding to be correct
            points_to_raw.is_range(
                ptr as int + size_of::<Node>(),
                block_token@.key.block_size - size_of::<Node>()),
            points_to_raw.provenance() == is_exposed.provenance(),
            points_to_raw.provenance() == ptr@.provenance,
            block_token@.key.block_size - size_of::<Node>() >= 0,
            ptr@.metadata == Metadata::Thin,

            old(self).fixed_page() ==> (
                block_token@.key.page_id == old(self).page_id()
                && block_token@.key.block_size == old(self).block_size()
            ),
            (match old(self).heap_id() {
                Some(heap_id) => block_token@.value.heap_id == Some(heap_id),
                None => true,
            }),
        ensures
            self.wf(),
            self.block_size() == old(self).block_size(),
            self.len() == old(self).len() + 1,
            self.instance() == old(self).instance(),
            self.page_id() == old(self).page_id(),
            self.fixed_page() == old(self).fixed_page(),
            self.heap_id() == old(self).heap_id(),
            self.ptr() == ptr
    {
        self.first = ptr;

        let tracked tuple = (points_to_ptr, points_to_raw, block_token, is_exposed);
        self.perms.borrow_mut().tracked_insert(self.data@.len, tuple);
        self.data@.len = self.data@.len + 1;

        let ghost len = self.data@.len;

        assert forall |i: nat| self.perms@.dom().contains(i) implies 0 <= i < self.data@.len
        by {
            if i + 1 < len { 
                assert(old(self).perms@.dom().contains(i));
            }
        }

        assert forall |i: nat| #[trigger] self.valid_node(i, self.next_ptr(i))
        by {
            assert(old(self).valid_node(i, old(self).next_ptr(i)));
            if i > 0 {
                let j = (i - 1) as nat;
                assert(old(self).valid_node(j, old(self).next_ptr(j)));
            }
            /*if i < len {
                if i != 0 {
                    assert(self.perms@.index((i - 1) as nat)
                      == old(self).perms@.index((i - 1) as nat));
                }
                assert(old(self).next_ptr(i) == self.next_ptr(i));
                if i + 1 == len {
                    assert(self.valid_node(i, self.next_ptr(i)));
                } else {
                    assert(self.valid_node(i, self.next_ptr(i)));
                }
            }*/
        }
    }

    proof fn is_empty_iff_null(tracked &self)
        requires self.wf(),
        ensures self.len() == 0 <==> self.first.addr() == 0
    {
        if self.first.addr() == 0 {
            if self.len() != 0 {
                let n = (self.len() - 1) as nat;
                assert(self.valid_node(n, self.next_ptr(n)));
                self.perms.borrow().tracked_borrow(n).0.is_nonnull();
                assert(false);
            }
        } else {
            assert(self.len() != 0);
        }
    }

    #[inline(always)]
    pub fn is_empty(&self) -> (b: bool)
        requires self.wf(),
        ensures b <==> (self.len() == 0)
    {
        proof {
            self.is_empty_iff_null();
        }
        self.first.addr() == 0
    }

    #[inline(always)]
    pub fn pop_block(&mut self) -> (x: (*mut u8, Tracked<PointsToRaw>, Tracked<Mim::block>))
        requires old(self).wf(),
            old(self).len() != 0,
        ensures ({
            let (ptr, points_to, block_token) = x;
            {
                &&& self.wf()
                &&& self.block_size() == old(self).block_size()
                &&& self.len() + 1 == old(self).len()
                &&& self.instance() == old(self).instance()
                &&& self.page_id() == old(self).page_id()
                &&& self.fixed_page() == old(self).fixed_page()
                &&& self.heap_id() == old(self).heap_id()

                &&& points_to@.is_range(ptr as int, block_token@@.key.block_size as int)
                &&& points_to@.provenance() == ptr@.provenance

                &&& block_token@@.instance == old(self).instance()
                &&& is_block_ptr(ptr, block_token@@.key)

                &&& (self.fixed_page() ==> (
                    block_token@@.key.page_id == self.page_id()
                    && block_token@@.key.block_size == self.block_size()
                ))
                &&& (match self.heap_id() {
                    Some(heap_id) => block_token@@.value.heap_id == Some(heap_id),
                    None => true,
                })
            }
        })
    {
        proof {
            let i = (self.data@.len - 1) as nat;
            assert(self.valid_node(i, self.next_ptr(i)));
        }
        let tracked (mut points_to_node, points_to_raw, block, is_exposed) = self.perms.borrow_mut().tracked_remove((self.data@.len - 1) as nat);

        let ptr: *mut Node = with_exposed_provenance(self.first.addr(), Tracked(is_exposed));
        //assert(ptr.addr() == points_to_node.ptr().addr());
        //assert(points_to_node.ptr()@.metadata == Metadata::Thin);
        //assert(ptr@.metadata == points_to_node.ptr()@.metadata);
        //assert(ptr@.provenance == points_to_node.ptr()@.provenance);
        let node = ptr_mut_read(ptr, Tracked(&mut points_to_node));
        self.first = node.ptr;

        let tracked points_to_raw = points_to_node.into_raw().join(points_to_raw);
        let ptru = ptr as *mut u8;

        proof {
            self.data@.len = (self.data@.len - 1) as nat;
            assert forall |i: nat| self.valid_node(i, #[trigger] self.next_ptr(i))
            by {
                assert(old(self).valid_node(i, old(self).next_ptr(i)));
                if i > 0 {
                    let j = (i - 1) as nat;
                    assert(old(self).valid_node(j, old(self).next_ptr(j)));
                }
            }
            let j = self.data@.len;
            assert(old(self).valid_node(j, old(self).next_ptr(j)));
            assert(old(self).valid_node((j-1) as nat, old(self).next_ptr((j-1) as nat)));
            assert((forall |i: nat| self.perms@.dom().contains(i) ==> 0 <= i < self.data@.len));
            /*if j > 0 {
                //assert(old(self).perms@.dom().contains(j - 1));
                //assert(self.perms@.dom().contains(j - 1));
                assert(self.next_ptr(j) == old(self).next_ptr(j));
                assert(self.first.id() == self.next_ptr(self.data@.len));
            } else {
                assert(self.first.id() == self.next_ptr(self.data@.len));
            }*/
            assert(self.wf());
        }

        assert(block@.key.block_size >= size_of::<Node>());

        return (ptru, Tracked(points_to_raw), Tracked(block))
    }

    // helper for clients using ghost_insert_block

    #[inline(always)]
    pub fn block_write_ptr(ptr: *mut Node, Tracked(perm): Tracked<PointsToRaw>, next: *mut Node)
        -> (res: (Tracked<PointsTo<Node>>, Tracked<PointsToRaw>))
        requires
            perm.contains_range(ptr as int, size_of::<Node>() as int),
            perm.provenance() == ptr@.provenance,
            ptr as int % align_of::<crate::linked_list::Node>() as int == 0,
            ptr@.metadata == Metadata::Thin,
        ensures ({
            let points_to = res.0@;
            let points_to_raw = res.1@;

            points_to.ptr() == ptr
              && points_to.opt_value() == MemContents::Init(Node { ptr: next })

              && points_to_raw.dom() == perm.dom().difference(set_int_range(ptr as int, ptr as int + size_of::<Node>()))
              && points_to_raw.provenance() == ptr@.provenance
        }),
    {
        let tracked (points_to, rest) = perm.split(set_int_range(ptr as int, ptr as int + size_of::<Node>()));
        
        vstd::layout::layout_for_type_is_valid::<Node>(); // $line_count$Proof$
        let tracked mut points_to_node = points_to.into_typed::<Node>(ptr.addr());
        ptr_mut_write(ptr, Tracked(&mut points_to_node), Node { ptr: next });
        (Tracked(points_to_node), Tracked(rest))
    }

    #[inline(always)]
    pub fn new(Ghost(page_id): Ghost<PageId>,
        Ghost(fixed_page): Ghost<bool>,
        Ghost(instance): Ghost<Mim::Instance>,
        Ghost(block_size): Ghost<nat>,
        Ghost(heap_id): Ghost<Option<HeapId>>,
    ) -> (ll: LL)
        ensures ll.wf(),
            ll.page_id() == page_id,
            ll.fixed_page() == fixed_page,
            ll.instance() == instance,
            ll.block_size() == block_size,
            ll.heap_id() == heap_id,
            ll.len() == 0,
    {
        LL {
            first: core::ptr::null_mut(),
            data: Ghost(LLData {
                fixed_page, block_size, page_id, instance, len: 0, heap_id,
            }),
            perms: Tracked(Map::tracked_empty()),
        }
    }

    #[inline(always)]
    pub fn empty() -> (ll: LL)
        ensures ll.wf(),
            ll.len() == 0,
    {
        LL::new(Ghost(arbitrary()), Ghost(arbitrary()), Ghost(arbitrary()), Ghost(arbitrary()), Ghost(arbitrary()))
    }


    #[inline(always)]
    pub fn set_ghost_data(
        &mut self,
        Ghost(page_id): Ghost<PageId>,
        Ghost(fixed_page): Ghost<bool>,
        Ghost(instance): Ghost<Mim::Instance>,
        Ghost(block_size): Ghost<nat>,
        Ghost(heap_id): Ghost<Option<HeapId>>,
    )
        requires old(self).wf(), old(self).len() == 0,
        ensures
            self.wf(),
            self.page_id() == page_id,
            self.fixed_page() == fixed_page,
            self.instance() == instance,
            self.block_size() == block_size,
            self.heap_id() == heap_id,
            self.len() == 0,
    {
        proof {
            self.data@.fixed_page = fixed_page;
            self.data@.block_size = block_size;
            self.data@.page_id = page_id;
            self.data@.instance = instance;
            self.data@.heap_id = heap_id;
        }
    }


    // Traverse `other` to find the tail, append `self`,
    // and leave the resulting list in `self`.
    // Returns the # of entries in `other`

    #[inline(always)]
    pub fn append(&mut self, other: &mut LL) -> (other_len: u32)
        requires
            old(self).wf() && old(other).wf(),
            old(self).page_id() == old(other).page_id(),
            old(self).block_size() == old(other).block_size(),
            old(self).fixed_page() == old(other).fixed_page(),
            old(self).instance() == old(other).instance(),
            old(self).heap_id().is_none(),
            old(other).heap_id().is_none(),
            old(other).len() < u32::MAX,
        ensures 
            // Book-keeping junk:
            self.wf() && other.wf(),
            self.page_id() == old(self).page_id(),
            self.block_size() == old(self).block_size(),
            self.fixed_page() == old(self).fixed_page(),
            self.instance() == old(self).instance(),
            self.heap_id() == old(self).heap_id(),
            other.page_id() == old(other).page_id(),
            other.block_size() == old(other).block_size(),
            other.fixed_page() == old(other).fixed_page(),
            other.instance() == old(other).instance(),
            other.heap_id() == old(other).heap_id(),

            // What you're here for:
            self.len() == old(self).len() + old(other).len(),
            other.len() == 0,

            other_len as int == old(other).len(),
    {
        proof {
            other.is_empty_iff_null();
        }
        if other.first.addr() == 0 {
            return 0;
        }

        let mut count = 1;
        let mut p = other.first;
        loop
            invariant
                1 <= count <= other.len(),
                other.len() < u32::MAX,
                other.wf(),
                p.addr() == other.perms@[(other.len() - count) as nat].0.ptr().addr(),
                p@.metadata == Metadata::Thin,
            ensures
                count == other.len(),
                p == other.perms@[0].0.ptr(),
        {
            proof {
                let ghost i = (other.len() - count) as nat;
                let ghost j = (i - 1) as nat;
                assert(other.valid_node(i, other.next_ptr(i)));
                assert(other.valid_node(j, other.next_ptr(j)));
                if i != 0 {
                    other.perms.borrow().tracked_borrow(j).0.is_nonnull();
                }
            }

            p = with_exposed_provenance(p.addr(),
                Tracked(other.perms.borrow().tracked_borrow((other.len() - count) as nat).3));

            let next = *ptr_ref(p, Tracked(&other.perms.borrow().tracked_borrow((other.len() - count) as nat).0));
            if next.ptr.addr() != 0 {
                count += 1;
                p = next.ptr;
            } else {
                break;
            }
        }

        let ghost old_other = *other;
        let ghost old_self = *self;

        assert(other.valid_node(0, other.next_ptr(0)));
        let tracked mut perm = other.perms.borrow_mut().tracked_remove(0);
        let tracked (mut a, b, c, exposed) = perm;
        let _ = ptr_mut_read(p, Tracked(&mut a));
        ptr_mut_write(p, Tracked(&mut a), Node { ptr: self.first });

        proof {
            other.perms.borrow_mut().tracked_insert(0, (a, b, c, exposed));

            let other_len = other.data@.len;
            let self_len = self.data@.len;
            self.data@.len = self.data@.len + other.data@.len;
            other.data@.len = 0;

            let tracked mut other_map = Map::tracked_empty();
            tracked_swap(other.perms.borrow_mut(), &mut other_map);

            let tracked mut self_map = Map::tracked_empty();
            tracked_swap(self.perms.borrow_mut(), &mut self_map);

            let key_map = Map::<nat, nat>::new(
                    |i: nat| self_len <= i < self_len + other_len,
                    |i: nat| (i - self_len) as nat,
                );
            assert forall|j| key_map.dom().contains(j) implies other_map.dom().contains(key_map.index(j))
            by {
                let r = (j - self_len) as nat;
                assert(old_other.valid_node(r, old_other.next_ptr(r)));
            }
            
            other_map.tracked_map_keys_in_place(key_map);
            other_map.tracked_union_prefer_right(self_map);
            self.perms@ = other_map;
        }

        self.first = other.first;
        other.first = core::ptr::null_mut();

        proof {
            assert forall |i: nat| self.valid_node(i, #[trigger] self.next_ptr(i))
            by {
                assert(old_self.valid_node(i, old_self.next_ptr(i)));
                assert(old_self.valid_node((i-1) as nat, old_self.next_ptr((i-1) as nat)));
                let k = (i - old_self.data@.len) as nat;
                let k1 = (k - 1) as nat;
                assert(old_other.valid_node(k, old_other.next_ptr(k)));
                assert(old_other.valid_node(k1, old_other.next_ptr(k1)));

                if i < old_self.data@.len {
                    assert(self.valid_node(i, self.next_ptr(i)));
                } else if i < self.data@.len {
                    assert(self.valid_node(i, self.next_ptr(i)));
                } else {
                    assert(self.valid_node(i, self.next_ptr(i)));
                }
            }
        }

        return count;
    }

    // don't need this?
    /*// Despite being 'exec', this function is a no-op
    #[inline(always)]
    pub fn mark_each_block_allocated(&mut self, tracked thread_token: &mut ThreadToken)
        requires
            self.wf(),
            self.fixed_page(),
            self.page_id() == old(self).page_id(),
        ensures 
            // Book-keeping junk:
            self.wf()
            self.page_id() == old(self).page_id(),
            self.block_size() == old(self).block_size(),
            self.fixed_page() == old(self).fixed_page(),
            self.instance() == old(self).instance(),
    {
    } */

    #[inline(always)]
    pub fn prepend_contiguous_blocks(
        &mut self,
        start: *mut u8,
        last: *mut u8,
        bsize: usize,

        Ghost(cap): Ghost<nat>,     // current capacity
        Ghost(extend): Ghost<nat>,  // spec we're extending to

        Tracked(points_to_raw_r): Tracked<&mut PointsToRaw>,
        Tracked(tokens): Tracked<&mut Map<int, Mim::block>>,
    )
        requires
            old(self).wf(),
            old(self).fixed_page(),
            old(self).block_size() == bsize as nat,
            old(self).heap_id().is_none(),
            INTPTR_SIZE <= bsize,
            start as int % INTPTR_SIZE as int == 0,
            bsize as int % INTPTR_SIZE as int == 0,

            old(points_to_raw_r).is_range(start as int, extend as int * bsize as int),
            old(points_to_raw_r).provenance() == start@.provenance,
            start@.metadata == Metadata::Thin,
            start@.provenance == old(self).page_id().segment_id.provenance,
            start as int + extend * bsize <= usize::MAX,

            start as int ==
                block_start_at(old(self).page_id(), old(self).block_size() as int, cap as int),

            extend >= 1,
            last as int == start as int + ((extend as int - 1) * bsize as int),

            (forall |i: int| cap <= i < cap + extend ==> old(tokens).dom().contains(i)),
            (forall |i: int| cap <= i < cap + extend ==> old(tokens).index(i)@.instance == old(self).instance()),
            (forall |i: int| cap <= i < cap + extend ==> old(tokens).index(i)@.key.page_id == old(self).page_id()),
            (forall |i: int| cap <= i < cap + extend ==> old(tokens).index(i)@.key.idx == i),
            (forall |i: int| cap <= i < cap + extend ==> old(tokens).index(i)@.key.block_size == bsize),
            (forall |i: int| cap <= i < cap + extend ==> is_block_ptr1(
                block_start(old(tokens).index(i)@.key),
                old(tokens).index(i)@.key)
            )
        ensures
            self.wf(),
            self.page_id() == old(self).page_id(),
            self.block_size() == old(self).block_size(),
            self.fixed_page() == old(self).fixed_page(),
            self.instance() == old(self).instance(),
            self.heap_id() == old(self).heap_id(),

            self.len() == old(self).len() + extend,

            //points_to_raw.ptr() == old(points_to_raw).ptr() + extend * (bsize as int),
            //points_to_raw@.size == old(points_to_raw)@.size - extend * (bsize as int),
            tokens == old(tokens).remove_keys(
                set_int_range(cap as int, cap as int + extend)),
    {
        // based on mi_page_free_list_extend

        let tracked mut points_to_raw = PointsToRaw::empty(start@.provenance);
        let tracked mut new_map: Map<nat, (PointsTo<Node>, PointsToRaw, Mim::block, IsExposed)> = Map::tracked_empty();
        proof {
            tracked_swap(&mut points_to_raw, points_to_raw_r);
        }

        let mut block = start.addr();
        let Tracked(exposed) = expose_provenance(start);
        let ghost mut i: int = 0;
        let ghost tokens_snap = *tokens;
        while block < last.addr()
            invariant 0 <= i < extend,
              start as int + extend * bsize <= usize::MAX,
              block == start as int + i * bsize,
              last as int == start.addr() + (extend - 1) * bsize,
              points_to_raw.is_range(block as int, (extend - i) * bsize),
              points_to_raw.provenance() == start@.provenance,
              start@.metadata == Metadata::Thin,
              start@.provenance == self.data@.page_id.segment_id.provenance,
              start@.provenance == exposed.provenance(),
              INTPTR_SIZE as int <= bsize,
              block as int % INTPTR_SIZE as int == 0,
              bsize as int % INTPTR_SIZE as int == 0,
              *tokens =~= tokens_snap.remove_keys(
                  set_int_range(cap as int, cap as int + i)),

              forall |j| #![trigger tokens.dom().contains(j)]
                  #![trigger tokens.index(j)]
                cap + i <= j < cap + extend ==>
                  tokens.dom().contains(j) && tokens[j] == tokens_snap[j],
              forall |j| (self.data@.len + extend - i <= j < self.data@.len + extend)
                    <==> #[trigger] new_map.dom().contains(j),
              *old(self) == *self,
              forall |j|
                  #![trigger new_map.dom().contains(j)]
                  #![trigger new_map.index(j)]
                ((self.data@.len + extend - i <= j < self.data@.len + extend)
                    ==> { let k = self.data@.len + extend - 1 - j; {
                      &&& new_map[j].2 == tokens_snap[cap + k]
                      &&& new_map[j].0.ptr() as int == start as int + k * bsize
                      &&& new_map[j].0.ptr()@.provenance == start@.provenance
                      &&& new_map[j].0.ptr()@.metadata == Metadata::Thin
                      &&& new_map[j].0.is_init()
                      &&& new_map[j].0.value().ptr as int == start.addr() + (k+1) * bsize
                      &&& new_map[j].0.value().ptr@.provenance == start@.provenance
                      &&& new_map[j].0.value().ptr@.metadata == Metadata::Thin
                      &&& new_map[j].1.is_range(
                         start.addr() + k * bsize + size_of::<Node>(),
                         bsize - size_of::<Node>())
                      &&& new_map[j].1.provenance() == start@.provenance
                      &&& new_map[j].3.provenance() == start@.provenance
                }})
        {
            proof {
                assert(i < extend);
                assert((i + 1) * bsize == i * bsize + bsize) by(nonlinear_arith);
                assert((extend - i) * bsize == (extend - (i + 1)) * bsize + bsize)
                    by(nonlinear_arith);
                assert(bsize <= (extend - i) * bsize)
                    by(nonlinear_arith) requires bsize >= 0, extend - i >= 1;
                assert(i * bsize + bsize <= extend * bsize)
                    by(nonlinear_arith) requires bsize >= 0, extend - i >= 1;
                assert(block + bsize <= start as int + extend * bsize);
                assert(size_of::<Node>() == 8);
            }

            let next: *mut Node = start.with_addr(block + bsize) as *mut Node;

            let tracked (points_to, rest) = points_to_raw.split(set_int_range(block as int, block as int + bsize as int));
            let tracked (points_to1, points_to2) = points_to.split(set_int_range(block as int, block as int + size_of::<Node>() as int));
            vstd::layout::layout_for_type_is_valid::<Node>(); // $line_count$Proof$
            let tracked mut points_to_node = points_to1.into_typed::<Node>(block);

            let block_ptr = next.with_addr(block);
            ptr_mut_write(block_ptr, Tracked(&mut points_to_node), Node { ptr: next });

            block = next.addr();

            proof {
                points_to_raw = rest;
                let ghost old_tokens = *tokens;
                let tracked block = tokens.tracked_remove(cap + i);
                let ghost the_key = (self.data@.len + extend - 1 - i) as nat;
                new_map.tracked_insert(
                    (self.data@.len + extend - 1 - i) as nat,
                    (points_to_node, points_to2, block, exposed));
                i = i + 1;

                /*assert forall
                      #![trigger new_map.dom().contains(j)]
                      #![trigger new_map.index(j)]
                      |j|
                    (self.data@.len + extend - i <= j < self.data@.len + extend)
                        implies ({ let k = self.data@.len + extend - 1 - j; {
                          &&& new_map[j].2 == tokens_snap[cap + k]
                          &&& new_map[j].0.ptr() == start.id() + k * bsize
                          &&& new_map[j].0@.value.is_some()
                          &&& new_map[j].0@.value.unwrap().ptr.id() == start.id() + (k+1) * bsize
                          &&& new_map[j].1.ptr() == start.id() + k * bsize + size_of::<Node>()
                          &&& new_map[j].1@.size == bsize - size_of::<Node>()
                    }})
                by
                {
                    let k = self.data@.len + extend - 1 - j;
                    if j == self.data@.len + extend - i {
                        assert(j == the_key);
                        assert(i-1 == k);
                        assert(new_map[j].2 == block);
                        assert(new_map[j].2 == old_tokens[cap + i - 1]);
                        assert(old_tokens[cap + i - 1] == tokens_snap[cap + i - 1]);
                        assert(new_map[j].2 == tokens_snap[cap + k]);
                        assert(new_map[j].0.ptr() == start.id() + k * bsize);
                        assert(new_map[j].0@.value.is_some());
                        assert(new_map[j].0@.value.unwrap().ptr.id() == start.id() + (k+1) * bsize);
                        assert(new_map[j].1.ptr() == start.id() + k * bsize + size_of::<Node>());
                        assert(new_map[j].1@.size == bsize - size_of::<Node>());
                    } else {
                        assert(new_map[j].2 == tokens_snap[cap + k]);
                        assert(new_map[j].0.ptr() == start.id() + k * bsize);
                        assert(new_map[j].0@.value.is_some());
                        assert(new_map[j].0@.value.unwrap().ptr.id() == start.id() + (k+1) * bsize);
                        assert(new_map[j].1.ptr() == start.id() + k * bsize + size_of::<Node>());
                        assert(new_map[j].1@.size == bsize - size_of::<Node>());
                    }
                }*/
            }
        }

        assert((i + 1) * bsize == i * bsize + bsize) by(nonlinear_arith);
        assert((extend - i) * bsize == (extend - (i + 1)) * bsize + bsize) by(nonlinear_arith);
        assert(bsize <= (extend - i) * bsize)
            by(nonlinear_arith) requires bsize >= 0, extend - i >= 1;
        assert(i * bsize + bsize <= extend * bsize)
            by(nonlinear_arith) requires bsize >= 0, extend - i >= 1;
        assert(block + bsize <= start as int + extend * bsize);
        assert(i == extend - 1) by {
            if i < extend - 1 {
                assert(i * bsize < (extend as int - 1) * bsize)
                  by(nonlinear_arith) requires bsize > 0, i < extend as int - 1;
                assert(false);
            }
        }

        let tracked (points_to, rest) = points_to_raw.split(set_int_range(block as int, block as int + bsize as int));
        let tracked (points_to1, points_to2) = points_to.split(set_int_range(block as int, block as int + size_of::<Node>() as int));
        proof { points_to_raw = rest; }
        vstd::layout::layout_for_type_is_valid::<Node>(); // $line_count$Proof$
        let tracked mut points_to_node = points_to1.into_typed::<Node>(block);

        let block_ptr = start.with_addr(block) as *mut Node;
        ptr_mut_write(block_ptr, Tracked(&mut points_to_node), Node { ptr: self.first });

        self.first = start as *mut Node;

        proof {
            let tracked block = tokens.tracked_remove(cap + i);
            let ghost the_key = (self.data@.len + extend - 1 - i) as nat;
            new_map.tracked_insert(
                (self.data@.len + extend - 1 - i) as nat,
                (points_to_node, points_to2, block, exposed));

            let old_len = self.data@.len;
            self.data@.len = self.data@.len + extend;
            self.perms.borrow_mut().tracked_union_prefer_right(new_map);

            assert_maps_equal!(*tokens == tokens_snap.remove_keys(
                set_int_range(cap as int, cap as int + extend)));
            assert forall |j: nat| self.valid_node(j, #[trigger] self.next_ptr(j))
            by {
                let (perm, padding, block_token, exposed) = self.perms@.index(j);
                if j < old_len {
                    assert(old(self).valid_node(j, old(self).next_ptr(j)));
                    assert(!new_map.dom().contains(j));
                    assert(self.perms@.index(j) == old(self).perms@.index(j));

                    if j > 0 {
                        assert(old(self).valid_node((j-1) as nat, old(self).next_ptr((j-1) as nat)));
                        assert(self.perms@.index((j-1) as nat) == old(self).perms@.index((j-1) as nat));
                        assert(self.perms@.index((j - 1) as nat)
                            == old(self).perms@.index((j - 1) as nat));
                    }
                    assert(old(self).next_ptr(j) == self.next_ptr(j));

                    /*if self.fixed_page() {
                        assert(old(self).fixed_page());
                        assert(self.data@.page_id == old(self).data@.page_id);

                        assert(block_token == old(self).perms@.index(j).2);
                        assert(0 <= j < old(self).data@.len);
                        assert(old(self).perms@.dom().contains(j));
                        assert(old(self).data@.page_id == 
                            old(self).perms@.index(j).2@.key.page_id);

                        assert(block_token@.key.page_id == self.data@.page_id);
                    }*/

                    assert(self.valid_node(j, self.next_ptr(j)));
                } else if j < self.data@.len {
                    let (perm, padding, block_token, exposed) = self.perms@.index(j);
                    let next_ptr = self.next_ptr(j);

                    assert(block_token@.key.block_size == bsize);
                    assert(is_block_ptr(perm.ptr() as *mut u8, block_token@.key)) by {
                        let block_id = block_token@.key;
                        crate::layout::get_block_start_defn(block_id);
                        let k = old_len + extend - 1 - j;
                        crate::layout::block_start_at_diff(block_id.page_id, bsize as nat, cap as nat, (cap + k) as nat);
                        //assert(perm.ptr() == block_start(old(tokens).index(k)@.key));
                        //assert(is_block_ptr(
                            //block_start(old(tokens).index(i)@.key),
                            //old(tokens).index(i)@.key)
                        //)

                        //assert(block_token@.key.page_id == self.page_id());

                        //let ptr = perm.ptr() as *mut u8;
                        //let block_id = block_token@.key;
                        //assert(ptr@.provenance == block_id.page_id.segment_id.provenance);
                        //assert(ptr@.metadata == Metadata::Thin);
                        //assert(is_block_ptr1(ptr as int, block_id));
                    }

                    if j == old_len {
                        if j > 0 {
                            assert(old(self).valid_node((j-1) as nat, old(self).next_ptr((j-1) as nat)));
                            assert(self.perms@.index((j-1) as nat) == old(self).perms@.index((j-1) as nat));
                            assert(self.perms@.index((j - 1) as nat)
                                == old(self).perms@.index((j - 1) as nat));
                        }
                        assert(perm.value().ptr.addr() == next_ptr.addr());
                    } else {
                        assert(perm.value().ptr.addr() == next_ptr.addr());
                    }

                    //assert(padding@.size + size_of::<Node>() == block_token@.key.block_size);
                    assert(self.valid_node(j, self.next_ptr(j)));
                }
            }
            assert(self.wf());
        }
    }

    pub fn make_empty(&mut self) -> (llgstr: Tracked<LLGhostStateToReconvene>)
        requires old(self).wf(),
            old(self).fixed_page(),
        ensures
            llgstr_wf(llgstr@),
            llgstr@.block_size == old(self).block_size(),
            llgstr@.page_id == old(self).page_id(),
            llgstr@.instance == old(self).instance(),
            llgstr@.map.len() == old(self).len(),
            self.wf(),
            self.len() == 0,
    {
        proof {
            assert(forall |i: nat| #[trigger] self.perms@.dom().contains(i) ==>
                self.valid_node(i, self.next_ptr(i)));
        }

        self.first = core::ptr::null_mut();

        let ghost block_size = self.block_size();
        let ghost page_id = self.page_id();
        let ghost instance = self.instance();
        let tracked map;
        proof {

            let len = self.data@.len;
            self.data@.len = 0;
            let tracked mut m = Map::tracked_empty();
            tracked_swap(&mut m, self.perms.borrow_mut());

            assert forall |i: nat| (#[trigger] m.dom().contains(i) <==> 0 <= i < len)
              /*&& (m.dom().contains(i) ==> ({
                  let (perm, padding, block_token) = m[i];
                    perm@.value.is_some()
                    && block_token@.key.block_size - size_of::<Node>() >= 0
                    && padding.is_range(perm.ptr() + size_of::<Node>(),
                        block_token@.key.block_size - size_of::<Node>())
                    && block_token@.instance == instance
                    && is_block_ptr(perm.ptr(), block_token@.key)
                    && block_token@.key.page_id == page_id
                    && block_token@.key.block_size == block_size
              }))*/
            by {
                if 0 <= i < len {
                    assert(old(self).valid_node(i, old(self).next_ptr(i)));
                    assert(m.dom().contains(i));
                }
                /*if m.dom().contains(i) {
                    assert(0 <= i < len);
                }*/
            }

            map = Self::convene_pt_map(m, len, instance, page_id, block_size);
        }
        Tracked(LLGhostStateToReconvene {
            map: map,
            block_size,
            page_id,
            instance,
        })
    }

    pub proof fn convene_pt_map(
        tracked m: Map<nat, (PointsTo<Node>, PointsToRaw, Mim::block, IsExposed)>,
        len: nat,
        instance: Mim::Instance,
        page_id: PageId,
        block_size: nat,
    ) -> (tracked m2: Map<nat, (PointsToRaw, Mim::block)>)
        requires
            forall |i: nat| (#[trigger] m.dom().contains(i) <==> 0 <= i < len)
              && (m.dom().contains(i) ==> ({
                  let (perm, padding, block_token, exposed) = m[i];
                    perm.is_init()
                    && block_token@.key.block_size - size_of::<Node>() >= 0
                    && padding.is_range(perm.ptr() as int + size_of::<Node>(),
                        block_token@.key.block_size - size_of::<Node>())
                    && padding.provenance() == page_id.segment_id.provenance
                    && padding.provenance() == exposed.provenance()
                    && block_token@.instance == instance
                    && is_block_ptr(perm.ptr() as *mut u8, block_token@.key)
                    && block_token@.key.page_id == page_id
                    && block_token@.key.block_size == block_size
              }))
        ensures
            m2.len() == len, m2.dom().finite(),
            forall |i: nat| (#[trigger] m2.dom().contains(i) <==> 0 <= i < len)
              && (m2.dom().contains(i) ==> ({
                  let (padding, block_token) = m2[i];
                    && block_token@.key.block_size - size_of::<Node>() >= 0
                    && padding.is_range(
                        block_start(block_token@.key),
                        block_token@.key.block_size as int)
                    && padding.provenance() == page_id.segment_id.provenance
                    && block_token@.instance == instance
                    && block_token@.key.page_id == page_id
                    && block_token@.key.block_size == block_size
              })),
        decreases len,
    {
        if len == 0 {
            let tracked m = Map::tracked_empty();
            assert(m.dom() =~= Set::empty());
            assert(m.len() == 0);
            m
        } else {
            let i = (len - 1) as nat;
            let tracked mut m = m;
            assert(m.dom().contains(i));
            let tracked (mut perm, padding, block_token, exposed) = m.tracked_remove(i);
            let tracked mut m2 = Self::convene_pt_map(m, i, instance, page_id, block_size);
            crate::layout::get_block_start_from_is_block_ptr(perm.ptr() as *mut u8, block_token@.key);
            perm.leak_contents();
            let tracked mut permraw = perm.into_raw();
            let tracked ptraw = permraw.join(padding);
            let mj = m2;
            m2.tracked_insert(i, (ptraw, block_token));
            assert(mj.dom().contains(i) == false);
            assert(m2.dom() =~= mj.dom().insert(i));
            assert(m2.dom().len() == mj.dom().len() + 1);
            assert(m2.len() == len);
            m2
        }
    }

    pub proof fn reconvene_state(
        tracked inst: Mim::Instance,
        tracked ts: &Mim::thread_local_state,
        tracked llgstr1: LLGhostStateToReconvene,
        tracked llgstr2: LLGhostStateToReconvene,
        n_blocks: int,
    ) -> (tracked res: (PointsToRaw, Map<BlockId, Mim::block>))
        requires
            llgstr_wf(llgstr1),
            llgstr_wf(llgstr2),
            llgstr1.block_size == llgstr2.block_size,
            llgstr1.page_id == llgstr2.page_id,
            llgstr1.instance == inst,
            llgstr2.instance == inst,
            ts@.instance == inst,
            n_blocks >= 0,
            llgstr1.map.len() + llgstr2.map.len() == n_blocks,
            ts@.value.pages.dom().contains(llgstr1.page_id),
            ts@.value.pages[llgstr1.page_id].num_blocks == n_blocks,
        ensures ({ let (points_to, map) = res; {
            &&& map.dom().finite() && map.len() == n_blocks
            &&& (forall |block_id| map.dom().contains(block_id) ==>
                    block_id.page_id == llgstr1.page_id)
            &&& (forall |block_id| map.dom().contains(block_id) ==>
                    map[block_id]@.key == block_id)
            &&& (forall |block_id| map.dom().contains(block_id) ==>
                    map[block_id]@.instance == inst)

            &&& points_to.is_range(block_start_at(llgstr1.page_id, llgstr1.block_size as int, 0), n_blocks * llgstr1.block_size)
            &&& points_to.provenance() == llgstr1.page_id.segment_id.provenance
        }})
    {
        let tracked llgstr = Self::llgstr_merge(llgstr1, llgstr2);
        let idxmap = Map::<nat, nat>::new(
            |p| llgstr.map.dom().contains(p),
            |p| llgstr.map[p].1@.key.idx);
        if exists |p| llgstr.map.dom().contains(p) && !(0 <= idxmap[p] < n_blocks) {
            let p = choose |p| llgstr.map.dom().contains(p) && !(0 <= idxmap[p] < n_blocks);
            let tracked LLGhostStateToReconvene { map: mut map, .. } = llgstr;
            assert(map.dom().contains(p));
            let tracked (_, block_p) = map.tracked_remove(p);
            assert(block_p@.instance == inst);
            inst.block_in_range(ts@.key, block_p@.key, ts, &block_p);
            assert(false);
            proof_from_false()
        } else if exists |i| 0 <= i < n_blocks && !has_idx(llgstr.map, i) {
            let i = choose |i| 0 <= i < n_blocks && !has_idx(llgstr.map, i);
            let (p, q) = crate::pigeonhole::pigeonhole_missing_idx_implies_double(idxmap, i, llgstr.map.len());
            let tracked LLGhostStateToReconvene { map: mut map, .. } = llgstr;
            let tracked (_, block_p) = map.tracked_remove(p);
            let tracked (_, block_q) = map.tracked_remove(q);
            inst.block_tokens_distinct(block_p@.key, block_q@.key, block_p, block_q);
            assert(false);
            proof_from_false()
        } else {
            let tracked LLGhostStateToReconvene { map, .. } = llgstr;
            Self::reconvene_rec(map, map.len(), llgstr.instance, llgstr.page_id, llgstr.block_size)
        }
    }

    pub proof fn llgstr_merge(
        tracked llgstr1: LLGhostStateToReconvene,
        tracked llgstr2: LLGhostStateToReconvene,
    ) -> (tracked llgstr: LLGhostStateToReconvene)
        requires
            llgstr_wf(llgstr1),
            llgstr_wf(llgstr2),
            llgstr1.block_size == llgstr2.block_size,
            llgstr1.page_id == llgstr2.page_id,
            llgstr1.instance == llgstr2.instance,
        ensures
            llgstr_wf(llgstr),
            llgstr.block_size == llgstr2.block_size,
            llgstr.page_id == llgstr2.page_id,
            llgstr.instance == llgstr2.instance,
            llgstr.map.len() == llgstr1.map.len() + llgstr2.map.len(),
    {
        let tracked LLGhostStateToReconvene { map: mut map1, .. } = llgstr1;
        let tracked LLGhostStateToReconvene { map: mut map2, .. } = llgstr2;
        map2.tracked_map_keys_in_place(Map::<nat, nat>::new(
            |k: nat| map1.len() <= k < map1.len() + map2.len(),
            |k: nat| (k - map1.len()) as nat,
        ));
        map1.tracked_union_prefer_right(map2);
        assert(map1.dom() =~= set_nat_range(0, 
            llgstr1.map.len() + llgstr2.map.len()));
        lemma_nat_range(0, llgstr1.map.len() + llgstr2.map.len());
        assert(map1.len() == llgstr1.map.len() + llgstr2.map.len());
        let tracked llgstr = LLGhostStateToReconvene {
            map: map1,
            block_size: llgstr1.block_size,
            page_id: llgstr1.page_id,
            instance: llgstr1.instance,
        };

        let len = llgstr.map.len();
        let map = llgstr.map;
        let block_size = llgstr.block_size;
        let page_id = llgstr.page_id;
        let instance = llgstr.instance;
        assert forall |i: nat| (#[trigger] map.dom().contains(i) <==> 0 <= i < len)
        by { }

        assert forall |i: nat|
            #[trigger] map.dom().contains(i) implies ({
                let (padding, block_token) = map[i];
                  && block_token@.key.block_size - size_of::<Node>() >= 0
                  && padding.is_range(
                      block_start(block_token@.key),
                      block_token@.key.block_size as int)
                  && padding.provenance() == page_id.segment_id.provenance
                  && block_token@.instance == instance
                  && block_token@.key.page_id == page_id
                  && block_token@.key.block_size == block_size
            })
        by {
            let (padding, block_token) = map[i];
            if i < llgstr1.map.len() {
                assert(block_token@.key.block_size - size_of::<Node>() >= 0);
            } else {
                let t = (i - llgstr1.map.len()) as nat;
                assert(llgstr2.map.dom().contains(t));
                assert(block_token@.key.block_size - size_of::<Node>() >= 0);
            }
        }

        llgstr
    }

    pub proof fn reconvene_rec(
        tracked m: Map<nat, (PointsToRaw, Mim::block)>,
        len: nat,
        instance: Mim::Instance,
        page_id: PageId,
        block_size: nat,
    ) -> (tracked res: (PointsToRaw, Map<BlockId, Mim::block>))
        requires
            forall |j: nat| 0 <= j < len ==> #[trigger] has_idx(m, j),
            forall |i: nat|
                  (m.dom().contains(i) ==> ({
                      let (padding, block_token) = m[i];
                        && block_token@.key.block_size - size_of::<Node>() >= 0
                        && padding.is_range(
                            block_start(block_token@.key),
                            block_token@.key.block_size as int)
                        && padding.provenance() == page_id.segment_id.provenance
                        && block_token@.instance == instance
                        && block_token@.key.page_id == page_id
                        && block_token@.key.block_size == block_size
                  })),
        ensures ({ let (points_to, map) = res; {
            &&& map.dom().finite() && map.len() == len
            &&& (forall |block_id| map.dom().contains(block_id) ==>
                    block_id.page_id == page_id)
            &&& (forall |block_id| map.dom().contains(block_id) ==>
                    map[block_id]@.key == block_id)
            &&& (forall |block_id| map.dom().contains(block_id) ==>
                    map[block_id]@.instance == instance)
            &&& (forall |block_id| map.dom().contains(block_id) ==>
                    0 <= block_id.idx < len)
            &&& points_to.is_range(block_start_at(page_id, block_size as int, 0), (len * block_size) as int)
            &&& points_to.provenance() == page_id.segment_id.provenance
        }})
        decreases len,
    {
        if len == 0 {
            (PointsToRaw::empty(page_id.segment_id.provenance), Map::tracked_empty())
        } else {
            let j = (len - 1) as nat;
            assert(has_idx(m, j));
            let i = choose |i: nat| m.dom().contains(i) && m[i].1@.key.idx == j;
            let old_m = m;
            let tracked mut m = m;
            let tracked (ptraw, block) = m.tracked_remove(i);
            assert forall |k: nat| 0 <= k < (len - 1) as nat implies has_idx(m, k) by {
                assert(has_idx(old_m, k));
                let p = choose |p: nat| old_m.dom().contains(p) && old_m[p].1@.key.idx == k;
                assert(m.dom().contains(p) && m[p].1@.key.idx == k);
            }
            let tracked (ptraw1, mut blocks) = Self::reconvene_rec(m, (len - 1) as nat, instance, page_id, block_size);

            let tracked ptraw2 = ptraw1.join(ptraw);
            let old_blocks = blocks;
            blocks.tracked_insert(block@.key, block);

            assert(block@.key.idx == len - 1);
            assert(old_blocks.dom().contains(block@.key) == false);
            assert(blocks.dom() =~= old_blocks.dom().insert(block@.key));
            assert(blocks.dom().len() == len);

            assert((len - 1) * block_size + block_size == len * block_size) by(nonlinear_arith);
            crate::layout::get_block_start_defn(block@.key);

            (ptraw2, blocks)
        }
    }
}

pub closed spec fn has_idx(map: Map<nat, (PointsToRaw, Mim::block)>, i: nat) -> bool {
    exists |p: nat| map.dom().contains(p) && map[p].1@.key.idx == i
}

pub open spec fn set_nat_range(lo: nat, hi: nat) -> Set<nat> {
    Set::new(|i: nat| lo <= i && i < hi)
}

pub proof fn lemma_nat_range(lo: nat, hi: nat)
    requires
        lo <= hi,
    ensures
        set_nat_range(lo, hi).finite(),
        set_nat_range(lo, hi).len() == hi - lo,
    decreases
        hi - lo,
{
    if lo == hi {
        assert(set_nat_range(lo, hi) =~= Set::empty());
    } else {
        lemma_nat_range(lo, (hi - 1) as nat);
        assert(set_nat_range(lo, (hi - 1) as nat).insert((hi - 1) as nat) =~= set_nat_range(lo, hi));
    }
}

pub closed spec fn llgstr_wf(llgstr: LLGhostStateToReconvene) -> bool {
    let len = llgstr.map.len();
    let map = llgstr.map;
    let block_size = llgstr.block_size;
    let page_id = llgstr.page_id;
    let instance = llgstr.instance;

    forall |i: nat| (#[trigger] map.dom().contains(i) <==> 0 <= i < len)
        && (map.dom().contains(i) ==> ({
            let (padding, block_token) = map[i];
              && block_token@.key.block_size - size_of::<Node>() >= 0
              && padding.is_range(
                  block_start(block_token@.key),
                  block_token@.key.block_size as int)
              && padding.provenance() == page_id.segment_id.provenance
              && block_token@.instance == instance
              && block_token@.key.page_id == page_id
              && block_token@.key.block_size == block_size
        }))
}

#[inline(always)]
pub fn bound_on_2_lists(
    Tracked(instance): Tracked<Mim::Instance>,
    Tracked(thread_token): Tracked<&Mim::thread_local_state>,
    ll1: &mut LL, ll2: &mut LL,
)
    requires thread_token@.instance == instance,
        old(ll1).wf(), old(ll2).wf(),
        old(ll1).fixed_page(),
        old(ll2).fixed_page(),
        old(ll1).instance() == instance,
        old(ll2).instance() == instance,
        old(ll1).page_id() == old(ll2).page_id(),
        // shouldn't really be necessary, but I'm reusing llgstr_merge
        // which requires it
        old(ll1).block_size() == old(ll2).block_size(),
        thread_token@.value.pages.dom().contains(old(ll1).page_id()),
    ensures *ll1 == *old(ll1), *ll2 == *old(ll2),
        ll1.len() + ll2.len() <= thread_token@.value.pages[ll1.page_id()].num_blocks,
{
    proof {
        assert(forall |i: nat| #[trigger] ll1.perms@.dom().contains(i) ==>
            ll1.valid_node(i, ll1.next_ptr(i)));
        assert(forall |i: nat| #[trigger] ll2.perms@.dom().contains(i) ==>
            ll2.valid_node(i, ll2.next_ptr(i)));

        let page_id = ll1.page_id();
        let block_size = ll1.block_size();
        let n_blocks = thread_token@.value.pages[ll1.page_id()].num_blocks;
        if ll1.len() + ll2.len() > n_blocks {
            let len = ll1.len();
            let tracked mut m = Map::tracked_empty();
            tracked_swap(&mut m, ll1.perms.borrow_mut());
            assert forall |i: nat| (#[trigger] m.dom().contains(i) <==> 0 <= i < len)
            by {
                if 0 <= i < len {
                    assert(old(ll1).valid_node(i, old(ll1).next_ptr(i)));
                    assert(m.dom().contains(i));
                }
            }
            let tracked mut map = LL::convene_pt_map(m, len, instance, page_id, block_size);
            let tracked llgstr1 = LLGhostStateToReconvene { map: map, block_size, page_id, instance };

            let len = ll2.len();
            let tracked mut m = Map::tracked_empty();
            tracked_swap(&mut m, ll2.perms.borrow_mut());
            assert forall |i: nat| (#[trigger] m.dom().contains(i) <==> 0 <= i < len)
            by {
                if 0 <= i < len {
                    assert(old(ll2).valid_node(i, old(ll2).next_ptr(i)));
                    assert(m.dom().contains(i));
                }
            }
            let tracked mut map = LL::convene_pt_map(m, len, instance, page_id, block_size);
            let tracked llgstr2 = LLGhostStateToReconvene { map: map, block_size, page_id, instance };

            let tracked llgstr = LL::llgstr_merge(llgstr1, llgstr2);
            let tracked LLGhostStateToReconvene { map: mut map, .. } = llgstr;

            let idxmap = Map::<nat, nat>::new(
                |p| map.dom().contains(p),
                |p| map[p].1@.key.idx);
            if exists |p| map.dom().contains(p) && !(0 <= idxmap[p] < n_blocks) {
                let p = choose |p| map.dom().contains(p) && !(0 <= idxmap[p] < n_blocks);
                assert(map.dom().contains(p));
                let tracked (_, block_p) = map.tracked_remove(p);
                assert(block_p@.instance == instance);
                instance.block_in_range(thread_token@.key, block_p@.key, thread_token, &block_p);
                assert(false);
            } else {
                let (p, q) = crate::pigeonhole::pigeonhole_too_many_elements_implies_double(idxmap, (map.len() - 1) as nat);
                let tracked (_, block_p) = map.tracked_remove(p);
                let tracked (_, block_q) = map.tracked_remove(q);
                instance.block_tokens_distinct(block_p@.key, block_q@.key, block_p, block_q);
                assert(false);
            }
        }
    }
}

#[inline(always)]
pub fn bound_on_1_lists(
    Tracked(instance): Tracked<Mim::Instance>,
    Tracked(thread_token): Tracked<&Mim::thread_local_state>,
    ll1: &mut LL,
)
    requires thread_token@.instance == instance,
        old(ll1).wf(),
        old(ll1).fixed_page(),
        old(ll1).instance() == instance,
        thread_token@.value.pages.dom().contains(old(ll1).page_id()),
    ensures *ll1 == *old(ll1),
        ll1.len() <= thread_token@.value.pages[ll1.page_id()].num_blocks,
{
    proof {
        assert(forall |i: nat| #[trigger] ll1.perms@.dom().contains(i) ==>
            ll1.valid_node(i, ll1.next_ptr(i)));

        let page_id = ll1.page_id();
        let block_size = ll1.block_size();
        let n_blocks = thread_token@.value.pages[ll1.page_id()].num_blocks;
        if ll1.len() > n_blocks {
            let len = ll1.len();
            let tracked mut m = Map::tracked_empty();
            tracked_swap(&mut m, ll1.perms.borrow_mut());

            assert forall |i: nat| (#[trigger] m.dom().contains(i) <==> 0 <= i < len)
            by {
                if 0 <= i < len {
                    assert(old(ll1).valid_node(i, old(ll1).next_ptr(i)));
                    assert(m.dom().contains(i));
                }
            }

            let tracked mut map = LL::convene_pt_map(m, len, instance, page_id, block_size);

            let idxmap = Map::<nat, nat>::new(
                |p| map.dom().contains(p),
                |p| map[p].1@.key.idx);
            if exists |p| map.dom().contains(p) && !(0 <= idxmap[p] < n_blocks) {
                let p = choose |p| map.dom().contains(p) && !(0 <= idxmap[p] < n_blocks);
                assert(map.dom().contains(p));
                let tracked (_, block_p) = map.tracked_remove(p);
                assert(block_p@.instance == instance);
                instance.block_in_range(thread_token@.key, block_p@.key, thread_token, &block_p);
                assert(false);
            } else {
                let (p, q) = crate::pigeonhole::pigeonhole_too_many_elements_implies_double(idxmap, (map.len() - 1) as nat);
                let tracked (_, block_p) = map.tracked_remove(p);
                let tracked (_, block_q) = map.tracked_remove(q);
                instance.block_tokens_distinct(block_p@.key, block_q@.key, block_p, block_q);
                assert(false);
            }
        }
    }
}



struct_with_invariants!{
    pub struct ThreadLLSimple {
        pub instance: Ghost<Mim::Instance>,
        pub heap_id: Ghost<HeapId>,

        pub atomic: AtomicPtr<Node, _, LL, _>,
    }

    pub closed spec fn wf(&self) -> bool {
        invariant
            on atomic
            with (instance, heap_id)
            is (v: *mut Node, ll: LL)
        {
            // Valid linked list

            ll.wf()
            && ll.instance() == instance
            && !ll.fixed_page()
            && ll.heap_id() == Some(heap_id@)

            // The usize value stores the pointer and the delay state

            && v == ll.ptr()
        }
    }
}

impl ThreadLLSimple {
    #[inline(always)]
    pub fn empty(Ghost(instance): Ghost<Mim::Instance>, Ghost(heap_id): Ghost<HeapId>) -> (s: Self)
        ensures s.wf(),
            s.instance@ == instance,
            s.heap_id@ == heap_id,
    {
        let p: *mut Node = core::ptr::null_mut();
        Self {
            instance: Ghost(instance),
            heap_id: Ghost(heap_id),
            atomic: AtomicPtr::new(Ghost((Ghost(instance), Ghost(heap_id))), core::ptr::null_mut(), Tracked(LL { first: p, data: Ghost(LLData { fixed_page: false, block_size: arbitrary(), page_id: arbitrary(), instance, len: 0, heap_id: Some(heap_id), }), perms: Tracked(Map::tracked_empty()), }),),
        }
    }

    // Oughta have a similar spec as LL:insert_block except that
    //  (i) self argument is a & reference so we don't need to talk about how it updates
    //  (ii) is we don't expose the length

    #[inline(always)]
    pub fn atomic_insert_block(&self, ptr: *mut Node,
        Tracked(points_to_raw): Tracked<PointsToRaw>,
        Tracked(block_token): Tracked<Mim::block>,
    )
        requires self.wf(),
            points_to_raw.is_range(ptr as int, block_token@.key.block_size as int),
            points_to_raw.provenance() == ptr@.provenance,
            ptr@.metadata == Metadata::Thin,
            block_token@.instance == self.instance,
            block_token@.value.heap_id == Some(self.heap_id@),
            is_block_ptr(ptr as *mut u8, block_token@.key),
    {
        let tracked mut points_to_raw = points_to_raw;
        let tracked mut block_token_opt = Some(block_token);

        let Tracked(exposed) = expose_provenance(ptr);

        loop
            invariant_except_break
                block_token_opt == Some(block_token),

                self.wf(),
                points_to_raw.is_range(ptr as int, block_token@.key.block_size as int),
                points_to_raw.provenance() == ptr@.provenance,
                ptr@.metadata == Metadata::Thin,
                exposed.provenance() == ptr@.provenance,

                block_token@.instance == self.instance,
                block_token@.value.heap_id == Some(self.heap_id@),
                is_block_ptr(ptr as *mut u8, block_token@.key),
        {
            let next_ptr = atomic_with_ghost!(
                &self.atomic => load(); ghost g => { });

            proof {
                block_size_ge_word();
                block_ptr_aligned_to_word();
            }

            let (Tracked(ptr_mem0), Tracked(raw_mem0)) = LL::block_write_ptr(ptr, Tracked(points_to_raw), next_ptr);

            let cas_result = atomic_with_ghost!(
                &self.atomic => compare_exchange_weak(next_ptr, ptr);
                returning cas_result;
                ghost ghost_ll =>
            {
                let tracked mut ptr_mem = ptr_mem0;
                let tracked raw_mem = raw_mem0;

                let ghost ok = cas_result.is_Ok();

                if ok {
                    let tracked block_token = block_token_opt.tracked_unwrap();
                    ghost_ll.ghost_insert_block(ptr, ptr_mem, raw_mem, block_token, exposed);
                    block_token_opt = None;

                    points_to_raw = PointsToRaw::empty(ptr@.provenance);
                } else {
                    ptr_mem.leak_contents();
                    points_to_raw = ptr_mem.into_raw().join(raw_mem);
                }
            });

            match cas_result {
                Result::Ok(_) => { break; }
                _ => { }
            }
        }
    }

    #[inline(always)]
    pub fn take(&self) -> (ll: LL)
        requires self.wf()
        ensures
            ll.wf(),
            ll.instance() == self.instance,
            ll.heap_id() == Some(self.heap_id@),
    {
        let res = self.atomic.load();
        if res.addr() == 0 {
            return LL::new(Ghost(arbitrary()), Ghost(arbitrary()),
                Ghost(self.instance@), Ghost(arbitrary()), Ghost(Some(self.heap_id@)));
        }

        let tracked ll: LL;
        let p = core::ptr::null_mut::<Node>();
        let res = atomic_with_ghost!(
            &self.atomic => swap(core::ptr::null_mut());
            ghost g => {
                ll = g;
                let mut data = ll.data@;
                data.len = 0;
                let tracked new_ll = LL {
                    first: p,
                    data: Ghost(data),
                    perms: Tracked(Map::tracked_empty()),
                };
                g = new_ll;
            }
        );
        let new_ll = LL {
            first: res,
            data: Ghost(ll.data@),
            perms: Tracked(ll.perms.get()),
        };

        assert(forall |i: nat| ll.valid_node(i, ll.next_ptr(i))
            ==> new_ll.valid_node(i, new_ll.next_ptr(i)));

        new_ll
    }
}

pub struct BlockSizePageId {
    pub block_size: nat,
    pub page_id: PageId,
}

tokenized_state_machine!{ StuffAgree {
    fields {
        #[sharding(variable)] pub x: Option<BlockSizePageId>,
        #[sharding(variable)] pub y: Option<BlockSizePageId>,
    }
    init!{
        initialize(b: Option<BlockSizePageId>) {
            init x = b;
            init y = b;
        }
    }
    transition!{
        set(b: Option<BlockSizePageId>) {
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

    #[inductive(initialize)]
    fn initialize_inductive(post: Self, b: Option<BlockSizePageId>) { }
   
    #[inductive(set)]
    fn set_inductive(pre: Self, post: Self, b: Option<BlockSizePageId>) { }
}}


struct_with_invariants!{
    pub struct ThreadLLWithDelayBits {
        pub instance: Tracked<Mim::Instance>,

        // In order to make an 'atomic' LL, we store a ghost LL with the atomic usize.
        // Note that the only physical field in an LL is the pointer, so we can obtain
        // a real LL by combining the 'ghost LL' with the pointer value.

        // The pointer value is stored in the usize of the atomic.
        // We also use the lower 2 bits of the usize to store the delay state.

        pub atomic: AtomicPtr<Node, _, (StuffAgree::y, Option<(Mim::delay, LL)>), _>,

        pub emp: Tracked<StuffAgree::x>,
        pub emp_inst: Tracked<StuffAgree::Instance>,
    }

    pub open spec fn wf(&self) -> bool {
        predicate {
            self.emp@@.instance == self.emp_inst@
        }
        invariant
            on atomic
            with (instance, emp_inst)
            is (v: *mut Node, all_g: (StuffAgree::y, Option<(Mim::delay, LL)>))
        {
            let (is_emp, g_opt) = all_g;
            is_emp@.instance == emp_inst@
            && (match (g_opt, is_emp@.value) {
                (None, None) => {
                    v == core::ptr::null_mut::<Node>()
                }
                (Some(g), Some(stuff)) => {
                    let (delay_token, ll) = g;
                    let page_id = stuff.page_id;
                    let block_size = stuff.block_size;

                    // Valid linked list

                    ll.wf()
                    && ll.block_size() == block_size
                    && ll.instance() == instance@
                    && ll.page_id() == page_id
                    && ll.fixed_page()
                    && ll.heap_id().is_none()

                    // Valid delay_token

                    && delay_token@.instance == instance@
                    && delay_token@.key == page_id

                    // The usize value stores the pointer and the delay state

                    && v as int == ll.ptr() as int + delay_token@.value.to_int()
                    && v@.metadata == ll.ptr()@.metadata
                    && v@.metadata == Metadata::Thin

                    // Verus should be smart enough to figure out the
                    // encoding is injective from this:
                    && ll.ptr() as int % 4 == 0

                    //&& (v as int != 0 ==> ({
                    //  &&& ll.ptr()@.provenance == page_id.segment_id.provenance
                    //}))
                    //&& (v as int == 0 ==> ({
                    //  &&& ll.ptr() == core::ptr::null_mut::<Node>()
                    //}))
                }
                _ => false,
            })
        }
    }
}

impl ThreadLLWithDelayBits {
    pub open spec fn is_empty(&self) -> bool {
        self.emp@@.value.is_none()
    }

    pub open spec fn block_size(&self) -> nat {
        self.emp@@.value.unwrap().block_size
    }

    pub open spec fn page_id(&self) -> PageId {
        self.emp@@.value.unwrap().page_id
    }

    pub fn empty(Tracked(instance): Tracked<Mim::Instance>) -> (ll: ThreadLLWithDelayBits)
        ensures ll.is_empty(),
            ll.wf(),
            ll.instance == instance,
    {
        let tracked (Tracked(emp_inst), Tracked(emp_x), Tracked(emp_y)) = StuffAgree::Instance::initialize(None);
        let emp = Tracked(emp_x);
        let emp_inst = Tracked(emp_inst);
        ThreadLLWithDelayBits {
            instance: Tracked(instance),
            atomic: AtomicPtr::new(Ghost((Tracked(instance), emp_inst)), core::ptr::null_mut(), Tracked((emp_y, None))),
            emp,
            emp_inst,
        }
    }

    #[inline(always)]
    pub fn enable(&mut self,
        Ghost(block_size): Ghost<nat>,
        Ghost(page_id): Ghost<PageId>,
        Tracked(instance): Tracked<Mim::Instance>,
        Tracked(delay_token): Tracked<Mim::delay>,
    )
        requires old(self).is_empty(),
            old(self).wf(),
            old(self).instance == instance,
            delay_token@.instance == instance,
            delay_token@.key == page_id,
            delay_token@.value == DelayState::UseDelayedFree,
        ensures
            self.wf(),
            !self.is_empty(),
            self.block_size() == block_size,
            self.page_id() == page_id,
            self.instance == instance,
    {
        let p = core::ptr::null_mut::<Node>();
        let ghost data = LLData {
            fixed_page: true, block_size, page_id, instance, len: 0, heap_id: None,
        };
        let tracked new_ll = LL {
            first: p,
            data: Ghost(data),
            perms: Tracked(Map::tracked_empty()),
        };
        atomic_with_ghost!(
            &self.atomic => no_op();
            update old_v -> v;
            ghost g => {
                let tracked (mut y, g_opt) = g;
                let bspi = BlockSizePageId { block_size, page_id };
                self.emp_inst.borrow().set(Some(bspi), self.emp.borrow_mut(), &mut y);
                g = (y, Some((delay_token, new_ll)));

                    /*let instance = self.instance;
                    let emp = self.emp;
                    let emp_inst = self.emp_inst;
                    assert(g.1.is_some());
                    assert(y@.value.is_some());
                    assert(g.0@.instance == self.emp_inst@);
                    assert(g.0@.instance == emp_inst@);
                    let (delay_token, ll) = g.1.unwrap();
                    let stuff = y@.value.unwrap();
                    let page_id = stuff.page_id;
                    let block_size = stuff.block_size;

                    // Valid linked list

                    assert(ll.wf());
                    assert(ll.block_size() == block_size);
                    assert(ll.instance() == instance@);
                    assert(ll.page_id() == page_id);
                    assert(ll.fixed_page());

                    // Valid delay_token

                    assert(delay_token@.instance == instance);
                    assert(delay_token@.key == page_id);

                    // The usize value stores the pointer and the delay state

                    assert(v as int == ll.ptr() as int + delay_token@.value.to_int());
                    assert(ll.ptr().id() % 4 == 0);*/

            }
        );
    }

    #[inline(always)]
    pub fn disable(&mut self) -> (delay: Tracked<Mim::delay>)
        requires !old(self).is_empty(),
            old(self).wf(),
        ensures
            self.wf(),
            self.is_empty(),
            self.instance == old(self).instance,
            delay@@.instance == old(self).instance,
            delay@@.key == old(self).page_id(),
    {
        let mut tmp = Self::empty(Tracked(self.instance.borrow().clone()));
        core::mem::swap(&mut *self, &mut tmp);

        let ThreadLLWithDelayBits { instance: Tracked(instance),
            atomic: ato,
            emp: Tracked(emp), emp_inst: Tracked(emp_inst) } = tmp;
        let (v, Tracked(g)) = ato.into_inner();
        let tracked (y, g_opt) = g;
        proof {
            emp_inst.agree(&emp, &y);
        }
        Tracked(g_opt.tracked_unwrap().0)
    }

    /*#[inline(always)]
    pub fn exit_delaying_state(
        &self,
        Tracked(delay_actor_token): Tracked<Mim::delay_actor>,
    )
        requires self.wf(),
            !self.is_empty(),
            delay_actor_token@.key == self.page_id,
            delay_actor_token@.instance == self.instance,
    {
        // DelayState::Freeing -> DelayState::NoDelayedFree

        // Note: the original implementation in _mi_free_block_mt
        // uses a compare-and-swap loop. But we can just use fetch_xor so I thought
        // I'd simplify it

        atomic_with_ghost!(
            &self.atomic => fetch_xor(3);
            update v_old -> v_new;
            ghost g => {
                let tracked (mut delay_token, ll) = g;
                delay_token = self.instance.borrow().delay_leave_freeing(self.page_id@,
                    delay_token, delay_actor_token);

                // TODO right now this only works for fixed-width architecture
                //verus_proof_expr!{ { // TODO fix atomic_with_ghost
                //    assert(v_old % 4 == 1usize ==> (v_old ^ 3) == add(v_old, 1)) by (bit_vector);
                //} }

                g = (delay_token, ll);
            }
        );
    }*/

    #[inline(always)]
    pub fn check_is_good(
        &self,
        Tracked(thread_tok): Tracked<&Mim::thread_local_state>,
        Tracked(tok): Tracked<Mim::thread_checked_state>,
    ) -> (new_tok: Tracked<Mim::thread_checked_state>)
        requires self.wf(), !self.is_empty(),
            thread_tok@.instance == self.instance,
            thread_tok@.value.pages.dom().contains(self.page_id()),
            thread_tok@.value.pages[self.page_id()].num_blocks == 0,
            tok@.instance == self.instance,
            tok@.key == thread_tok@.key,
        ensures
            new_tok@@.instance == tok@.instance,
            new_tok@@.key == tok@.key,
            new_tok@@.value == (crate::tokens::ThreadCheckedState {
                pages: tok@.value.pages.insert(self.page_id()),
            }),
    {
        let tracked mut tok0 = tok;
        loop
            invariant self.wf(), !self.is_empty(),
                thread_tok@.instance == self.instance,
                thread_tok@.value.pages.dom().contains(self.page_id()),
                thread_tok@.value.pages[self.page_id()].num_blocks == 0,
                tok@.instance == self.instance,
                tok@.key == thread_tok@.key,
                tok0 == tok,
        {
            let ghost mut the_ptr;
            let ghost mut the_delay;
            let tfree = atomic_with_ghost!(&self.atomic => load(); ghost g => {
                self.emp_inst.borrow().agree(self.emp.borrow(), &g.0);
                the_ptr = g.1.unwrap().1.ptr();
                the_delay = g.1.unwrap().0.view().value;

                if the_delay != DelayState::Freeing {
                    let tracked new_tok = self.instance.borrow().page_check_delay_state(
                        tok0@.key,
                        self.page_id(),
                        thread_tok,
                        &g.1.tracked_borrow().0,
                        tok0);
                    tok0 = new_tok;
                }
            });

            let old_delay = masked_ptr_delay_get_delay(tfree, Ghost(the_delay), Ghost(the_ptr));
            if unlikely(old_delay == 1) { // Freeing
                atomic_yield();
            } else {
                return Tracked(tok0);
            }
        }
    }

    #[inline(always)]
    pub fn try_use_delayed_free(
        &self,
        delay: usize,
        override_never: bool,
    ) -> (b: bool)
        requires self.wf(), !self.is_empty(),
            !override_never && delay == 0, // UseDelayedFree
    {
        let mut yield_count = 0;
        loop
            invariant self.wf(), !self.is_empty(), !override_never, delay == 0,
        {
            let ghost mut the_ptr;
            let ghost mut the_delay;
            let tfree = atomic_with_ghost!(&self.atomic => load(); ghost g => {
                self.emp_inst.borrow().agree(self.emp.borrow(), &g.0);
                the_ptr = g.1.unwrap().1.ptr();
                the_delay = g.1.unwrap().0.view().value;
            });

            let tfreex = masked_ptr_delay_set_delay(tfree, delay, Ghost(the_delay), Ghost(the_ptr));
            let old_delay = masked_ptr_delay_get_delay(tfree, Ghost(the_delay), Ghost(the_ptr));
            if unlikely(old_delay == 1) { // Freeing
                if yield_count >= 4 {
                    return false;
                }
                yield_count += 1;
                atomic_yield();
            } else if delay == old_delay {
                return true;
            } else if !override_never && old_delay == 3 {
                return true;
            }

            if old_delay != 1 {
                let res = atomic_with_ghost!(
                    &self.atomic => compare_exchange_weak(tfree, tfreex);
                    returning cas_result;
                    ghost g => {
                        self.emp_inst.borrow().agree(self.emp.borrow(), &g.0);
                        if cas_result.is_ok() {
                            let tracked (emp_token, pair_opt) = g;
                            let tracked pair = pair_opt.tracked_unwrap();
                            let tracked (delay_token, ghost_ll) = pair;
                            let tracked dt = self.instance.borrow().set_use_delayed_free(self.page_id(), delay_token);
                            g = (emp_token, Some((dt, ghost_ll)));
                        }
                    }
                );

                if res.is_ok() {
                    return true;
                }
            }
        }
    }

    // Clears the list (but leaves the 'delay' bit intact)
    #[inline(always)]
    pub fn take(&self) -> (ll: LL)
        requires self.wf(), !self.is_empty(),
        ensures
            ll.wf(),
            ll.page_id() == self.page_id(),
            ll.block_size() == self.block_size(),
            ll.instance() == self.instance,
            ll.heap_id().is_none(),
            ll.fixed_page(),
    {
        let tracked ll: LL;
        let p = core::ptr::null_mut::<Node>();
        let res = atomic_with_ghost!(
            &self.atomic => fetch_and(3);
            update old_v -> new_v;
            ghost g => {
                assert(old_v@.addr & 3 == new_v@.addr);
                assert(old_v@.provenance == new_v@.provenance);
                assert(old_v@.metadata == new_v@.metadata);
                assert(old_v@.metadata == Metadata::Thin);
                assert(new_v@.metadata == Metadata::Thin);

                self.emp_inst.borrow().agree(self.emp.borrow(), &g.0);
                let tracked (emp_token, pair_opt) = g;
                let tracked pair = pair_opt.tracked_unwrap();
                let tracked (delay, _ll) = pair;
                ll = _ll;
                let mut data = ll.data@;
                data.len = 0;
                let tracked new_ll = LL {
                    first: p,
                    data: Ghost(data),
                    perms: Tracked(Map::tracked_empty()),
                };
                g = (emp_token, Some((delay, new_ll)));

                let x = ll.first as usize;
                let y = delay@.value.to_int() as usize;
                assert(add(x, y) & 3usize == y) by(bit_vector)
                    requires x % 4 == 0usize, 0usize <= y < 4usize;
                assert(add(x, y) & !3 == x) by(bit_vector)
                    requires x % 4 == 0usize, 0usize <= y < 4usize;

                //assert(new_v@.provenance == ll.ptr()@.provenance);
                //assert(new_v@.metadata == ll.ptr()@.metadata);
                //assert(new_ll.ptr()@.metadata == Metadata::Thin);
                //assert((new_ll.ptr() as int != 0 ==> new_v@.provenance == new_ll.ptr()@.provenance));
                //assert(new_v@.metadata == new_ll.ptr()@.metadata);
                //assert(new_v as int == new_ll.ptr() as int + delay@.value.to_int());
            }
        );
        let ret_ll = LL {
            first: res.with_addr(res.addr() & !3),
            data: Ghost(ll.data@),
            perms: Tracked(ll.perms.get()),
        };
        proof {
            assert forall |i: nat| ret_ll.valid_node(i, #[trigger] ret_ll.next_ptr(i))
            by {
                assert(ll.valid_node(i, ll.next_ptr(i)));
            }
        }
        ret_ll
    }
}

#[inline(always)]
pub fn masked_ptr_delay_get_is_use_delayed(v: *mut Node,
    Ghost(expected_delay): Ghost<DelayState>,
    Ghost(expected_ptr): Ghost<*mut Node>) -> (b: bool)
  requires v as int == expected_ptr as int + expected_delay.to_int(),
      expected_ptr as int % 4 == 0,
  ensures b <==> (expected_delay == DelayState::UseDelayedFree)
{
    v.addr() % 4 == 0
}

#[inline(always)]
pub fn masked_ptr_delay_get_delay(v: *mut Node,
    Ghost(expected_delay): Ghost<DelayState>,
    Ghost(expected_ptr): Ghost<*mut Node>) -> (d: usize)
  requires v as int == expected_ptr as int + expected_delay.to_int(),
      expected_ptr as int % 4 == 0,
  ensures d == expected_delay.to_int()
{
    v.addr() % 4
}

#[inline(always)]
pub fn masked_ptr_delay_get_ptr(v: *mut Node,
    Ghost(expected_delay): Ghost<DelayState>,
    Ghost(expected_ptr): Ghost<*mut Node>) -> (ptr: *mut Node)
  requires v as int == expected_ptr as int + expected_delay.to_int(),
      expected_ptr as int % 4 == 0, v@.metadata == Metadata::Thin,
  ensures ptr.addr() == expected_ptr.addr(), ptr@.metadata == Metadata::Thin,
{
    proof {
        let v = v.addr();
        assert((v & !3) == sub(v, (v % 4))) by(bit_vector);
    }
    v.with_addr(v.addr() & !3)
}

#[inline(always)]
pub fn masked_ptr_delay_set_ptr(v: *mut Node, new_ptr: *mut Node,
    Ghost(expected_delay): Ghost<DelayState>,
    Ghost(expected_ptr): Ghost<*mut Node>) -> (v2: *mut Node)
  requires v as int == expected_ptr as int + expected_delay.to_int(),
      expected_ptr as int % 4 == 0,
      new_ptr as int % 4 == 0, v@.metadata == Metadata::Thin, new_ptr@.metadata == Metadata::Thin,
  ensures v2 as int == new_ptr as int + expected_delay.to_int(), v2@.provenance == new_ptr@.provenance, v2@.metadata == Metadata::Thin,
{
    proof {
        let v = v as usize;
        assert((v & 3) == (v % 4)) by(bit_vector);
        let u = new_ptr as usize;
        assert(u % 4 == 0usize ==> ((v&3) | u) == add(v&3, u)) by(bit_vector);
    }
    new_ptr.with_addr((v.addr() & 3) | new_ptr.addr())
}

#[inline(always)]
pub fn masked_ptr_delay_set_freeing(v: *mut Node,
    Ghost(expected_delay): Ghost<DelayState>,
    Ghost(expected_ptr): Ghost<*mut Node>) -> (v2: *mut Node)
  requires v as int == expected_ptr as int + expected_delay.to_int(),
      expected_ptr as int % 4 == 0, v@.metadata == Metadata::Thin,
  ensures v2 as int == expected_ptr as int + DelayState::Freeing.to_int(), v2@.provenance == v@.provenance, v2@.metadata == Metadata::Thin,
{
    proof {
        let v = v as usize;
        assert(((v & !3) | 1) == add(sub(v, (v % 4)), 1)) by(bit_vector);
    }
    v.with_addr((v.addr() & !3) | 1)
}

#[inline(always)]
pub fn masked_ptr_delay_set_delay(v: *mut Node, new_delay: usize,
    Ghost(expected_delay): Ghost<DelayState>,
    Ghost(expected_ptr): Ghost<*mut Node>) -> (v2: *mut Node)
  requires v as int == expected_ptr as int + expected_delay.to_int(),
      expected_ptr as int % 4 == 0, new_delay <= 3,
  ensures v2 as int == expected_ptr as int + new_delay,
      v2@.provenance == v@.provenance,
      v2@.metadata == v@.metadata,
{
    proof {
        let v = v.addr();
        assert(((v & !3) | new_delay) == add(sub(v, (v % 4)), new_delay)) by(bit_vector)
            requires new_delay <= 3usize;
    }
    v.with_addr((v.addr() & !3) | new_delay)
}

/*
#[inline(always)]
fn free_delayed_block(ll: &mut LL, Tracked(local): Tracked<&mut Local>) -> (b: bool)
    requires old(local).wf(), old(ll).wf(), old(ll).len() != 0,
        old(ll).instance() == old(local).instance,
    ensures
        local.wf(),
        common_preserves(*old(local), *local),
        ll.instance() == old(ll).instance(),
{
    let ghost i = (ll.data@.len - 1) as nat;
    assert(ll.valid_node(i, ll.next_ptr(i)));
    let tracked (points_to_node, points_to_raw, block) = self.perms.borrow_mut().tracked_remove(i);
    let node = *ptr.borrow(Tracked(&points_to_node));

    let ghost block_id = block@.key;

    assert(crate::dealloc_token::valid_block_token(block, local.instance));

    let ptr = PPtr::<u8>::from_usize(ll.first.to_usize());
    let segment = crate::layout::calculate_segment_ptr_from_block(ptr, Ghost(block_id));

    let slice_page_ptr = crate::layout::calculate_slice_page_ptr_from_block(ptr, segment, Ghost(block_id));
    let tracked page_slice_shared_access: &PageSharedAccess =
        local.instance.alloc_guards_page_slice_shared_access(
            block_id,
            &block,
        );
    let slice_page: &Page = slice_page_ptr.borrow(
        Tracked(&page_slice_shared_access.points_to));
    let offset = slice_page.offset;
    let page_ptr = crate::layout::calculate_page_ptr_subtract_offset(
        slice_page_ptr,
        offset,
        Ghost(block_id.page_id_for_slice()),
        Ghost(block_id.page_id),
    );
    assert(crate::layout::is_page_ptr(page_ptr.id(), block_id.page_id));

    let page = PageId { page_ptr: page_ptr, page_id: Ghost(block_id.page_id) };
    if !crate::page::page_try_use_delayed_free(page, 0, false) {
        proof {
            self.perms.borrow_mut().tracked_insert((points_to_node, points_to_raw, block));
        }
        return false;
    }

    crate::alloc_generic::page_free_collect(page, false, Tracked(&mut *local));

    proof { points_to_node.leak_contents(); }
    let tracked points_to_raw = points_to_node.into_raw().join(points_to_raw);
    let tracked dealloc = MimDeallocInner {
        mim_instance: local.instance,
        mim_block: block,
        ptr: ptr.id(),
    };

    crate::free::free_block(page, true, ptr,
        Tracked(points_to_raw), Tracked(dealloc), Tracked(&mut *local));

    return true;
}
*/

#[inline(always)]
fn atomic_yield() {
    std::thread::yield_now();
}

}
