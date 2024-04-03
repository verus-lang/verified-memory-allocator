#![feature(core_intrinsics)]
#![feature(lazy_cell)]
#![allow(unused_imports)]
#![allow(non_snake_case)]
#![allow(unused_assignments)]
#![allow(unused_macros)]
#![feature(thread_id_value)]

// bottom bread

mod os_mem;
mod thread;

// fundamentals and definitions

mod tokens;
mod types;
mod flags;
mod layout;
mod config;
mod bin_sizes;
mod dealloc_token;
mod page_organization;
mod os_mem_util;

// utilities

mod atomic_ghost_modified;
mod pigeonhole;

// implementation

mod linked_list;
mod bitmap;
mod commit_mask;

mod arena;
mod alloc_fast;
mod alloc_generic;
mod free;
mod realloc;
mod segment;
mod commit_segment;
mod os_commit;
mod os_alloc;
mod page;
mod queues;
mod init;

use vstd::prelude::*;

verus!{

use crate::types::print_hex;

#[verus::line_count::ignore]
fn main() {
    let tracked (global, mut rights) = init::global_init();
    let tracked is_thread = crate::thread::ghost_thread_id();
    assert(rights.dom().contains(is_thread@));
    let tracked right = rights.tracked_remove(is_thread@);
    let (heap, Tracked(local)) = init::heap_init(Tracked(global), Tracked(right), Tracked(is_thread));

    if heap.heap_ptr.to_usize() != 0 {
        let tracked mut local = local.tracked_unwrap();

        let (p1, u1, Tracked(d1)) = crate::alloc_fast::heap_malloc(heap, 24, Tracked(&mut local));
        print_hex(vstd::string::new_strlit("allocated: "), p1.to_usize());

        let (p2, u2, Tracked(d2)) = crate::alloc_fast::heap_malloc(heap, 24, Tracked(&mut local));
        print_hex(vstd::string::new_strlit("allocated: "), p2.to_usize());

        let (p3, u3, Tracked(d3)) = crate::alloc_fast::heap_malloc(heap, 24, Tracked(&mut local));
        print_hex(vstd::string::new_strlit("allocated: "), p3.to_usize());

        let (p4, u4, Tracked(d4)) = crate::alloc_fast::heap_malloc(heap, 24, Tracked(&mut local));
        print_hex(vstd::string::new_strlit("allocated: "), p4.to_usize());

        crate::free::free(p1, u1, Tracked(Some(d1)), Tracked(&mut local));
        crate::free::free(p2, u2, Tracked(Some(d2)), Tracked(&mut local));
        crate::free::free(p3, u3, Tracked(Some(d3)), Tracked(&mut local));
        crate::free::free(p4, u4, Tracked(Some(d4)), Tracked(&mut local));

        let (p5, u5, Tracked(d5)) = crate::alloc_fast::heap_malloc(heap, 24, Tracked(&mut local));
        print_hex(vstd::string::new_strlit("allocated: "), p5.to_usize());

        crate::free::free(p5, u5, Tracked(Some(d5)), Tracked(&mut local));
    }

    big_test(heap);
}

}

#[verifier::external_body]
fn big_test(heap: crate::types::HeapPtr) {
    for j in 0 .. 30 {
        dbg!(j);
        let mut v = Vec::new();
        for i in 0 .. 100000 {
            let (p, _, _) = crate::alloc_fast::heap_malloc(heap, 100, Tracked::assume_new());
            v.push(p);
        }
        for (i, p) in v.iter().enumerate() {
            crate::free::free(*p, Tracked::assume_new(), Tracked::assume_new(), Tracked::assume_new());
        }
    }
}

// Called from C overrides

// verus_mi_thread_init_default_heap should be called once-per-thread,
// and must be called before verus_mi_heap_malloc

use core::ffi::c_void;
use crate::types::todo;

#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn verus_mi_thread_init_default_heap() -> *mut c_void {
    // heap_init takes a `right_to_use_thread` token. That's why we can only call
    // verus_mi_thread_init_default_heap once per thread.

    // TODO note that the thread id u64s MAY be re-used.
    // However, we only get one `right_to_use_thread` token per available ID.
    // So we either need to:
    //  - destroy the thread local state at the end of a thread's lifetime
    //      (reclaiming the right_to_use_thread token)
    //    This requires implementing abandoned segments
    // OR
    //  - check that the thread ID is unused

    let (heap, _) = crate::init::heap_init(Tracked::assume_new(), Tracked::assume_new(), Tracked::assume_new());
    heap.heap_ptr.uptr as *mut c_void
}

#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn verus_mi_heap_malloc(heap: *mut c_void, size: usize) -> *mut c_void {
    let heap = crate::types::HeapPtr {
        heap_ptr: vstd::ptr::PPtr { uptr: heap as *mut crate::types::Heap },
        heap_id: Ghost::assume_new(),
    };
    let (p, _, _) = crate::alloc_fast::heap_malloc(heap, size, Tracked::assume_new());
    p.uptr as *mut c_void
}

#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn verus_mi_free(ptr: *mut c_void) {
    let p = vstd::ptr::PPtr { uptr: ptr as *mut u8 };
    crate::free::free(p, Tracked::assume_new(), Tracked::assume_new(), Tracked::assume_new());
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn malloc(size: usize) -> *mut c_void {
    verus_mi_heap_malloc(get_default_heap(), size)
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn calloc(number: usize, size: usize) -> *mut c_void {
    // calloc is required to zero its memory.
    // TODO we should implement calloc in the verified code with a specification that
    // the memory is zeroed.
    unsafe {
        let (sz, ov) = count_size_overflow(number, size);
        let p = malloc(sz);
        if p != core::ptr::null_mut() {
            core::ptr::write_bytes(p, 0, sz)
        }
        p
    }
}

verus!{

#[inline(always)]
#[verifier::external_body]
#[verus::line_count::ignore]
pub fn count_size_overflow(count: usize, size: usize) -> (x: (usize, bool))
    ensures x.1 <==> (count * size >= usize::MAX),
          !x.1 ==> x.0 == count * size
{
    if count == 1 {
        (size, false)
    } else {
        count.overflowing_mul(size)
    }
}

}


#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn realloc(ptr: *mut c_void, size: usize) -> *mut c_void {
    todo(); loop{}
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn free(ptr: *mut c_void) {
    verus_mi_free(ptr)
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn reallocf(ptr: *mut c_void, newsize: usize) -> *mut c_void {
    todo(); loop{}
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn malloc_size(ptr: *mut c_void) -> usize {
    todo(); loop{}
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn malloc_usable_size(ptr: *mut c_void) -> usize {
    todo(); loop{}
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn valloc(size: usize) -> *mut c_void {
    todo(); loop{}
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn vfree(ptr: *mut c_void) {
    todo(); loop{}
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn malloc_good_size(size: usize) -> usize {
    todo(); loop{}
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn posix_memalign(p: *mut *mut c_void, alignment: usize, size: usize) -> i32 {
    todo(); loop{}
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn aligned_alloc(alignment: usize, size: usize) -> *mut c_void {
    todo(); loop{}
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn cfree(ptr: *mut c_void) {
    todo(); loop{}
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn pvalloc(size: usize) -> *mut c_void {
    todo(); loop{}
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn reallocarray(ptr: *mut c_void, count: usize, size: usize) -> *mut c_void {
    todo(); loop{}
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn reallocarr(ptr: *mut c_void, count: usize, size: usize) -> i32 {
    todo(); loop{}
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn memalign(alignment: usize, size: usize) -> *mut c_void {
    todo(); loop{}
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn _aligned_malloc(alignment: usize, size: usize) -> *mut c_void {
    todo(); loop{}
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn __libc_malloc(size: usize) -> *mut c_void {
    verus_mi_heap_malloc(get_default_heap(), size)
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn __libc_calloc(number: usize, size: usize) -> *mut c_void {
    todo(); loop{}
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn __libc_realloc(ptr: *mut c_void, size: usize) -> *mut c_void {
    todo(); loop{}
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn __libc_free(ptr: *mut c_void) {
    verus_mi_free(ptr)
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn __libc_cfree(ptr: *mut c_void) {
    verus_mi_free(ptr)
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn __libc_valloc(size: usize) -> *mut c_void {
    todo(); loop{}
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn __libc_pvalloc(size: usize) -> *mut c_void {
    todo(); loop{}
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn __libc_memalign(alignment: usize, size: usize) -> *mut c_void {
    todo(); loop{}
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn __posix_memalign(p: *mut *mut c_void, alignment: usize, size: usize) -> i32 {
    todo(); loop{}
}











// TODO need to figure out how to override the C++ new / delete operators

#[cfg(feature = "override_system_allocator")]
extern "C" {
    #[verifier::external]
    #[no_mangle]
    pub fn get_default_heap() -> *mut c_void;

    #[verifier::external]
    #[no_mangle]
    pub fn thread_id_helper() -> u64;

/*
    #[verifier::external]
    #[no_mangle]
    pub fn malloc(size: usize) -> *mut c_void;

    #[no_mangle]
    fn calloc(number: usize, size: usize) -> *mut c_void;

    #[no_mangle]
    fn realloc(ptr: *mut c_void, size: usize) -> *mut c_void;

    #[verifier::external]
    #[no_mangle]
    pub fn free(ptr: *mut c_void);
    */
}
