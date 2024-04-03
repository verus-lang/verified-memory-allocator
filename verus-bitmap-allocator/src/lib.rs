#![feature(allocator_api)]
#![allow(unused_imports)]

use builtin::*;
use builtin_macros::*;

mod bit_support;
mod bitmap;
mod arena;
mod interface;

#[macro_export]
use vstd::invariant::*;

use interface::*;
use vstd::ptr::*;
use vstd::layout::*;
use vstd::prelude::*;

verus!{

fn test() {
    // Create allocator
    let num_words: usize = 0xffff00;
    assert(is_power_2(8)) by(compute);
    let (ptr, Tracked(mem), Tracked(dealloc)) = PPtr::alloc(num_words * 8, 8);
    let allocator = Allocator::new(ptr, num_words as u64, Tracked(mem));

    // Allocate some stuff

    let alloc1 = match allocator.alloc(5) { Some(x) => x, None => { return; } };
    let alloc2 = match allocator.alloc(12) { Some(x) => x, None => { return; } };

    allocator.dealloc(alloc1, 5);
    allocator.dealloc(alloc2, 12);
}

}
