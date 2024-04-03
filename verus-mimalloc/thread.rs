#![allow(unused_imports)]

use vstd::prelude::*;

verus!{

// Note that ThreadIds may be re-used since we use the u64 version

#[verus::trusted]
pub struct ThreadId {
    pub thread_id: u64,
}

/// Proof object that guarantees the owning thread has the given ThreadId.

#[verus::trusted]
#[cfg(verus_keep_ghost)]
#[verifier(external_body)]
pub tracked struct IsThread { }

#[verus::trusted]
#[cfg(verus_keep_ghost)]
impl !Sync for IsThread { }

#[verus::trusted]
#[cfg(verus_keep_ghost)]
impl !Send for IsThread { }

// TODO: remove this when !Sync, !Send are supported by stable Rust
#[cfg(not(verus_keep_ghost))]
#[verifier(external_body)]
#[verus::trusted]
pub tracked struct IsThread { _no_send_sync: core::marker::PhantomData<*const ()> }

#[verus::trusted]
impl IsThread {
    pub spec fn view(&self) -> ThreadId;

    /// Guarantees that any two `IsThread` objects on the same thread
    /// will have the same ID.

    #[verifier(external_body)]
    pub proof fn agrees(tracked self, tracked other: IsThread)
        ensures self@ == other@,
    { unimplemented!(); }

    #[verifier(external_body)]
    pub proof fn nonzero(tracked self)
        ensures self@.thread_id != 0,
    { unimplemented!(); }
}

#[verus::trusted]
#[verifier(external)]
impl Clone for IsThread {
    #[cfg(verus_keep_ghost)]
    fn clone(&self) -> Self {
        IsThread { }
    }
    #[cfg(not(verus_keep_ghost))]
    fn clone(&self) -> Self {
        IsThread { _no_send_sync: Default::default() }
    }
}

#[verus::trusted]
impl Copy for IsThread { }

// Note: NO guarantee that a thread is not re-used

#[verus::trusted]
#[cfg(feature = "override_system_allocator")]
#[cfg(target_os = "linux")]
#[verifier::external_body]
pub fn thread_id() -> (res: (ThreadId, Tracked<IsThread>))
    ensures res.1@@ == res.0,
{
    //let id: i32 = unsafe { libc::gettid() };
    //let id_u64: u64 = ((id as u64) << 1) | 1; // make sure it's nonzero
    let id_u64: u64 = unsafe { crate::thread_id_helper() };
    let id = ThreadId { thread_id: id_u64 };
    (id, Tracked::assume_new())
}

// NOTE: std::thread recursively calls malloc, so this can't be used when doing override

#[verus::trusted]
#[cfg(not(feature = "override_system_allocator"))]
#[verifier::external_body]
pub fn thread_id() -> (res: (ThreadId, Tracked<IsThread>))
    ensures res.1@@ == res.0,
{
    let id: std::thread::ThreadId = std::thread::current().id();
    let id = ThreadId { thread_id: id.as_u64().into() };
    (id, Tracked::assume_new())
}


/// Returns _just_ the ghost object, without physically obtaining the thread ID.

#[verus::trusted]
#[verifier::external_body]
pub proof fn ghost_thread_id() -> (tracked res: IsThread)
{
    unimplemented!();
}

#[verus::trusted]
#[verifier::external_fn_specification]
pub fn ex_yield_now() {
    std::thread::yield_now()
}

}
