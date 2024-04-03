use core::intrinsics::{unlikely, likely};
use vstd::prelude::*;
use vstd::set_lib::*;
use vstd::ptr::*;
use crate::config::*;
use crate::os_mem::*;
use crate::layout::*;
use crate::types::todo;
use vstd::set_lib::set_int_range;


verus!{

pub fn os_commit(addr: usize, size: usize, Tracked(mem): Tracked<&mut MemChunk>)
    -> (res: (bool, bool))
    requires old(mem).wf(), 
        old(mem).os_has_range(addr as int, size as int),
        addr as int % page_size() == 0,
        size as int % page_size() == 0,
        addr != 0,
        addr + size <= usize::MAX,
        //old(mem).has_pointsto_for_all_read_write(),
    ensures ({
        let (success, is_zero) = res;
        mem.wf()
        //&& mem.has_pointsto_for_all_read_write()
        //&& (success ==> mem.os_has_range_read_write(addr as int, size as int))
        && mem.has_new_pointsto(&*old(mem))
        && mem.os.dom() == old(mem).os.dom()

        && (success ==>
            mem.os_has_range_read_write(addr as int, size as int))
    })
{
    os_commitx(addr, size, true, false, Tracked(&mut *mem))
}

pub fn os_decommit(addr: usize, size: usize, Tracked(mem): Tracked<&mut MemChunk>)
    -> (success: bool)
    requires old(mem).wf(), 
        old(mem).os_has_range(addr as int, size as int),
        old(mem).pointsto_has_range(addr as int, size as int),
        addr as int % page_size() == 0,
        size as int % page_size() == 0,
        addr != 0,
        addr + size <= usize::MAX,
    ensures
        mem.wf(),
        mem.os.dom() =~= old(mem).os.dom(),

        mem.points_to@.dom().subset_of(old(mem).points_to@.dom()),
        mem.os_rw_bytes().subset_of(old(mem).os_rw_bytes()),

        old(mem).points_to@.dom() - mem.points_to@.dom()
            =~= old(mem).os_rw_bytes() - mem.os_rw_bytes(),
        old(mem).os_rw_bytes() - mem.os_rw_bytes()
            <= set_int_range(addr as int, addr + size),
{
    let tracked mut t = mem.split(addr as int, size as int);
    let ghost t1 = t;
    let (success, _) = os_commitx(addr, size, false, true, Tracked(&mut t));
    proof {
        mem.join(t);

        assert(t.os_rw_bytes().subset_of(t1.os_rw_bytes()));
        assert forall |p| mem.os_rw_bytes().contains(p)
            implies old(mem).os_rw_bytes().contains(p)
        by {
            if addr <= p < addr + size {
                assert(t1.os_rw_bytes().contains(p));
                assert(t.os_rw_bytes().contains(p));
                assert(old(mem).os_rw_bytes().contains(p));
            } else {
                assert(old(mem).os_rw_bytes().contains(p));
            }
        }
        assert_sets_equal!(old(mem).points_to@.dom() - mem.points_to@.dom(),
            old(mem).os_rw_bytes() - mem.os_rw_bytes(),
            p =>
        {
            if (old(mem).points_to@.dom() - mem.points_to@.dom()).contains(p) {
                if addr <= p < addr + size {
                    assert((t1.points_to@.dom() - t.points_to@.dom()).contains(p));
                    assert((t1.os_rw_bytes() - t.os_rw_bytes()).contains(p));
                    assert((old(mem).os_rw_bytes() - mem.os_rw_bytes()).contains(p));
                } else {
                    assert((old(mem).os_rw_bytes() - mem.os_rw_bytes()).contains(p));
                }
            }
            if (old(mem).os_rw_bytes() - mem.os_rw_bytes()).contains(p) {
                if addr <= p < addr + size {
                    assert((t1.os_rw_bytes() - t.os_rw_bytes()).contains(p));
                    assert((t1.points_to@.dom() - t.points_to@.dom()).contains(p));
                    assert((old(mem).points_to@.dom() - mem.points_to@.dom()).contains(p));
                } else {
                    assert((old(mem).points_to@.dom() - mem.points_to@.dom()).contains(p));
                }
            }
        });
        assert(mem.os_rw_bytes().subset_of(old(mem).os_rw_bytes()));
    }
    success
}

fn os_page_align_areax(conservative: bool, addr: usize, size: usize)
    -> (res: (usize, usize))
    requires
        addr as int % page_size() == 0,
        size as int % page_size() == 0,
        addr != 0,
        addr + size <= usize::MAX,
    ensures
        ({ let (start, csize) = res;
            start as int % page_size() == 0
            && csize as int % page_size() == 0
            && (size != 0 ==> start == addr)
            && (size != 0 ==> csize == size)
            && (size == 0 ==> start == 0 && csize == 0)
        })
{
    if size == 0 || addr == 0 {
        return (0, 0);
    }

    let start = if conservative {
        align_up(addr, get_page_size())
    } else {
        align_down(addr, get_page_size())
    };
    let end = if conservative {
        align_down(addr + size, get_page_size())
    } else {
        align_up(addr + size, get_page_size())
    };

    let diff = end - start;
    if diff <= 0 {
        return (0, 0);
    }
    (start, diff)
}

fn os_commitx(
    addr: usize, size: usize, commit: bool, conservative: bool,
    Tracked(mem): Tracked<&mut MemChunk>
) -> (res: (bool, bool))
    requires old(mem).wf(), 
        old(mem).os_has_range(addr as int, size as int),
        addr as int % page_size() == 0,
        size as int % page_size() == 0,
        addr != 0,
        addr + size <= usize::MAX,
        !commit ==> old(mem).pointsto_has_range(addr as int, size as int),
    ensures
        mem.wf(),
        mem.os.dom() =~= old(mem).os.dom(),
        commit ==> mem.has_new_pointsto(&*old(mem)),
        commit ==> res.0 ==> mem.os_has_range_read_write(addr as int, size as int),
        !commit ==> mem.points_to@.dom().subset_of(old(mem).points_to@.dom()),
        !commit ==> mem.os_rw_bytes().subset_of(old(mem).os_rw_bytes()),
        !commit ==> old(mem).points_to@.dom() - mem.points_to@.dom()
                    =~= old(mem).os_rw_bytes() - mem.os_rw_bytes(),
{
    let is_zero = false;
    let (start, csize) = os_page_align_areax(conservative, addr, size);
    if csize == 0 {
        return (true, is_zero);
    }
    let err = 0;

    let p = PPtr::from_usize(start);

    let tracked weird_extra = mem.take_points_to_set(
          mem.points_to@.dom() - mem.os_rw_bytes());
    let tracked mut exact_mem = mem.split(addr as int, size as int);
    let ghost em = exact_mem;

    if commit {
        mprotect_prot_read_write(p, csize, Tracked(&mut exact_mem));
    } else {
        // TODO madvise?
        mprotect_prot_none(p, csize, Tracked(&mut exact_mem));
    }

    proof {
        mem.join(exact_mem);
        mem.give_points_to_range(weird_extra);
        //assert( mem.os.dom() == old(mem).os.dom(),
        if commit {
        }
        if !commit {
            /*assert(em.points_to@.dom()
                =~= set_int_range(addr as int, addr + size as int));
            assert(em.points_to@.dom() - exact_mem.points_to@.dom()
                =~= set_int_range(addr as int, addr + size as int));

            assert(exact_mem.range_os_rw().disjoint(exact_mem.range_os_none()));
            assert(exact_mem.os_rw_bytes() =~= Set::empty());

            assert(em.os_rw_bytes() - exact_mem.os_rw_bytes()
                =~= set_int_range(addr as int, addr + size as int));

            assert(old(mem).points_to@.dom() - mem.points_to@.dom()
                =~= set_int_range(addr as int, addr + size as int));
            assert(old(mem).os_rw_bytes() - mem.os_rw_bytes()
                =~= set_int_range(addr as int, addr + size as int));
            */
        }
        assert(mem.os.dom() =~= old(mem).os.dom());
    }

    // TODO bubble up error instead of panicking
    return (true, is_zero);
}

}

