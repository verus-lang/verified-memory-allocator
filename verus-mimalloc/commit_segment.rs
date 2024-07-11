#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::set_lib::*;

use crate::commit_mask::*;
use crate::types::*;
use crate::layout::*;
use crate::config::*;
use crate::segment::*;
use crate::os_mem_util::*;
use crate::tokens::*;
use crate::os_mem::*;

verus!{

fn clock_now() -> i64 {
    let t = clock_gettime_monotonic();
    t.tv_sec.wrapping_mul(1000).wrapping_add( (((t.tv_nsec as u64) / 1000000) as i64) )
}

// Should not be called for huge segments, I think? TODO can probably optimize out some checks
fn segment_commit_mask(
    segment_ptr: *mut u8,
    conservative: bool,
    p: usize,
    size: usize,
    cm: &mut CommitMask)
 -> (res: (*mut u8, usize)) // start_p, full_size
    requires
        segment_ptr as int % SEGMENT_SIZE as int == 0,
        segment_ptr as int + SEGMENT_SIZE <= usize::MAX,
        p >= segment_ptr as int,
        p + size <= segment_ptr as int + SEGMENT_SIZE,
        old(cm)@ == Set::<int>::empty(),
    ensures ({ let (start_p, full_size) = res; {
        (cm@ == Set::<int>::empty() ==> !conservative ==> size == 0)
        && (cm@ != Set::<int>::empty() ==>
            (conservative ==> p <= start_p as int <= start_p as int + full_size <= p + size)
            && (!conservative ==> start_p as int <= p <= p + size <= start_p as int + full_size)
            && start_p as int >= segment_ptr as int
            && start_p as int + full_size <= segment_ptr as int + SEGMENT_SIZE
            //&& (!conservative ==> set_int_range((p - segment_ptr) / COMMIT_SIZE as int,
            //    (((p + size - 1 - segment_ptr as int) / COMMIT_SIZE as int) + 1)).subset_of(cm@))
            //&& (conservative ==> cm@ <= set_int_range((p - segment_ptr) / COMMIT_SIZE as int,
            //    (((p + size - 1 - segment_ptr as int) / COMMIT_SIZE as int) + 1)))
            && start_p as int % COMMIT_SIZE as int == 0
            && full_size as int % COMMIT_SIZE as int == 0
            && cm@ =~= 
                set_int_range((start_p as int - segment_ptr as int) / COMMIT_SIZE as int,
                    (((start_p as int + full_size - segment_ptr as int) / COMMIT_SIZE as int)))
            && start_p@.provenance == segment_ptr@.provenance
        )
        && (!conservative ==> forall |i| #[trigger] cm@.contains(i) ==>
            start_p as int <= segment_ptr as int + i * SLICE_SIZE
            && start_p as int + full_size >= segment_ptr as int + (i + 1) * SLICE_SIZE
        )
        //&& start_p as int % SLICE_SIZE as int == 0
        //&& full_size as int % SLICE_SIZE as int == 0
    }})
{
    proof { const_facts(); }

    if size == 0 || size > SEGMENT_SIZE as usize {
        return (core::ptr::null_mut(), 0);
    }

    let segstart: usize = SLICE_SIZE as usize;
    let segsize: usize = SEGMENT_SIZE as usize;

    if p >= segment_ptr.addr() + segsize {
        return (core::ptr::null_mut(), 0);
    }

    let pstart: usize = p - segment_ptr.addr();

    let mut start: usize;
    let mut end: usize;
    if conservative {
        start = align_up(pstart, COMMIT_SIZE as usize);
        end = align_down(pstart + size, COMMIT_SIZE as usize);
    } else {
        start = align_down(pstart, COMMIT_SIZE as usize);
        end = align_up(pstart + size, COMMIT_SIZE as usize);
    }

    if pstart >= segstart && start < segstart {
        start = segstart;
    }

    if end > segsize {
        end = segsize;
    }

    let start_p = segment_ptr.with_addr(segment_ptr.addr() + start);
    let full_size = if end > start { end - start } else { 0 };
    if full_size == 0 {
        return (start_p, full_size);
    }

    let bitidx = start / COMMIT_SIZE as usize;
    let bitcount = full_size / COMMIT_SIZE as usize;
    cm.create(bitidx, bitcount);

    proof {
        let start_p = start_p as int;
        if conservative {
            assert(p <= start_p);
            assert(start_p + full_size <= p + size);
        } else {
            assert(start_p <= p);

            assert(start_p + full_size == segment_ptr as int + end);
            assert(p + size == segment_ptr as int + pstart + size);
            assert(end >= pstart + size);

            assert(p + size <= start_p + full_size);

            assert((p - segment_ptr as int) / COMMIT_SIZE as int >= bitidx);
            assert((((p + size - 1 - segment_ptr as int) / COMMIT_SIZE as int) + 1) <= bitidx + bitcount);
        }
        if full_size > 0 {
            assert(cm@.contains(bitidx as int));
        }
    }

    return (start_p, full_size);
}

#[verifier::spinoff_prover]
fn segment_commitx(
    segment: SegmentPtr,
    commit: bool,
    p: usize,
    size: usize,
    Tracked(local): Tracked<&mut Local>,
) -> (success: bool)
    requires old(local).wf_main(),
        segment.wf(),
        segment.is_in(*old(local)),
        p >= segment.segment_ptr.addr(),
        p + size <= segment.segment_ptr.addr() + SEGMENT_SIZE,
        // !commit ==> old(local).segments[segment.segment_id@]
        //    .mem.os_has_range_read_write(p as int, size as int),
        // !commit ==> old(local).segments[segment.segment_id@]
        //    .mem.pointsto_has_range(p as int, size as int),
        !commit ==> 
            set_int_range(p as int, p + size)
             <= old(local).decommit_mask(segment.segment_id@).bytes(segment.segment_id@),
    ensures
        local.wf_main(),
        common_preserves(*old(local), *local),
        commit ==> success ==> local.segments[segment.segment_id@]
            .mem.os_has_range_read_write(p as int, size as int),
        commit ==> success ==> set_int_range(p as int, p + size) <=
            local.commit_mask(segment.segment_id@).bytes(segment.segment_id@)
             - local.decommit_mask(segment.segment_id@).bytes(segment.segment_id@),

        local.page_organization == old(local).page_organization,
        local.pages == old(local).pages,
        local.psa == old(local).psa,
{
    let ghost sid = segment.segment_id@;
    proof {
        segment_id_divis(segment);
        const_facts();
        local.instance.thread_local_state_guards_segment(
           local.thread_id, segment.segment_id@, &local.thread_token).points_to.is_nonnull();
        decommit_subset_of_pointsto(*local, sid);
    }

    let mut mask: CommitMask = CommitMask::empty();
    let (start, full_size) = segment_commit_mask(
        segment.segment_ptr as *mut u8, !commit, p, size, &mut mask);

    if mask.is_empty() || full_size == 0 {
        return true;
    }

    if commit && !segment.get_commit_mask(Tracked(&*local)).all_set(&mask) {
        proof {
            let ghost sid = segment.segment_id@;
            assert(local.mem_chunk_good(sid));
            assert(segment_start(sid) <= start as int);
            assert(start as int + full_size <= segment_start(sid) + SEGMENT_SIZE);
            //assert(local.segments[sid].mem.os_exact_range(
            //    segment_start(sid), SEGMENT_SIZE as int));
        }

        let mut is_zero = false;
        let mut cmask = CommitMask::empty();
        segment.get_commit_mask(Tracked(&*local)).create_intersect(&mask, &mut cmask);

        let success;
        segment_get_mut_local!(segment, local, l => {
            let (_success, _is_zero) =
                crate::os_commit::os_commit(start, full_size, Tracked(&mut l.mem));
            success = _success;
        });
        if (!success) {
            proof {
                preserves_mem_chunk_good_on_commit(*old(local), *local, sid);
                assert(local.mem_chunk_good(sid));
                assert forall |sid1| sid1 != sid && old(local).mem_chunk_good(sid1)
                    implies local.mem_chunk_good(sid1)
                by {
                    preserves_mem_chunk_good_on_commit(*old(local), *local, sid1);
                }
                assert(local.wf_main());
            }
            return false;
        }

        segment_get_mut_main!(segment, local, main => {
            main.commit_mask.set(&mask);
        });
    }
    else if !commit && segment.get_commit_mask(Tracked(&*local)).any_set(&mask) {
        let mut cmask = CommitMask::empty();
        segment.get_commit_mask(Tracked(&*local)).create_intersect(&mask, &mut cmask);
        if segment.get_allow_decommit(Tracked(&*local)) {
            segment_get_mut_local!(segment, local, l => {
                crate::os_commit::os_decommit(start, full_size, Tracked(&mut l.mem));
            });
        }
        segment_get_mut_main!(segment, local, main => {
            main.commit_mask.clear(&mask);
        });
    }

    if commit && segment.get_main_ref(Tracked(&*local)).decommit_mask.any_set(&mask) {
        segment_get_mut_main!(segment, local, main => {
            main.decommit_expire = clock_now().wrapping_add(option_decommit_delay());
        });
    }

    segment_get_mut_main!(segment, local, main => {
        main.decommit_mask.clear(&mask);
    });
    
    proof {
        let cm = local.segments[sid].main@.value.unwrap().commit_mask@;
        let old_cm = old(local).segments[sid].main@.value.unwrap().commit_mask@;

        if commit {
            assert(local.decommit_mask(sid).bytes(sid).subset_of( old(local).decommit_mask(sid).bytes(sid) ) && old(local).commit_mask(sid).bytes(sid).subset_of( local.commit_mask(sid).bytes(sid) )) by { reveal(CommitMask::bytes); }
            assert((old(local).segments[sid].mem.os_rw_bytes() + (local.commit_mask(sid).bytes(sid) - old(local).commit_mask(sid).bytes(sid))).subset_of(local.segments[sid].mem.os_rw_bytes())) by { reveal(CommitMask::bytes); }
            preserves_mem_chunk_good_on_commit_with_mask_set(*old(local), *local, sid);
            assert(local.mem_chunk_good(sid));
            assert forall |sid1| sid1 != sid && old(local).mem_chunk_good(sid1)
                implies local.mem_chunk_good(sid1)
            by {
                preserves_mem_chunk_good_on_commit(*old(local), *local, sid1);
            }
            assert(local.wf_main());

            assert forall |j: int| set_int_range(p as int, p + size).contains(j)
                implies local.commit_mask(sid).bytes(sid).contains(j)
            by {
                assert(segment_start(sid) == segment.segment_ptr.addr());
                let k = (j - segment_start(sid)) / COMMIT_SIZE as int;
                assert(mask@.contains(k));
                reveal(CommitMask::bytes);
            }
            assert(set_int_range(p as int, p + size) <= local.commit_mask(segment.segment_id@).bytes(segment.segment_id@) - local.decommit_mask(segment.segment_id@).bytes(segment.segment_id@)) by { reveal(CommitMask::bytes); };
        } else {
            assert forall |sid1| sid1 != sid && old(local).mem_chunk_good(sid1)
                implies local.mem_chunk_good(sid1)
            by {
                preserves_mem_chunk_good_on_commit_with_mask_set(*old(local), *local, sid1);
            }

            let local1 = *old(local);
            let local2 = *local;
            assert(local2.commit_mask(sid).bytes(sid) =~=
                local1.commit_mask(sid).bytes(sid) -
                (local1.decommit_mask(sid).bytes(sid) - local2.decommit_mask(sid).bytes(sid)))
            by {
                reveal(CommitMask::bytes);
            }
            assert(local2.decommit_mask(sid).bytes(sid) <= local1.decommit_mask(sid).bytes(sid))
            by {
                reveal(CommitMask::bytes);
            }
            assert((local1.segments[sid].mem.os_rw_bytes() - local2.segments[sid].mem.os_rw_bytes())
                <= (local1.decommit_mask(sid).bytes(sid) - local2.decommit_mask(sid).bytes(sid)))
            by {
                reveal(CommitMask::bytes);
            }

            preserves_mem_chunk_good_on_decommit(*old(local), *local, sid);
            assert(local.mem_chunk_good(sid));

            assert(local.wf_main());
        }
    }

    return true;
}

pub fn segment_ensure_committed(
    segment: SegmentPtr,
    p: usize,
    size: usize,
    Tracked(local): Tracked<&mut Local>
) -> (success: bool)
    requires old(local).wf_main(),
        segment.wf(),
        segment.is_in(*old(local)),
        p >= segment.segment_ptr.addr(),
        p + size <= segment.segment_ptr.addr() + SEGMENT_SIZE,
    ensures
        local.wf_main(),
        common_preserves(*old(local), *local),
        success ==> set_int_range(p as int, p + size) <=
            local.commit_mask(segment.segment_id@).bytes(segment.segment_id@)
            - local.decommit_mask(segment.segment_id@).bytes(segment.segment_id@),

        local.page_organization == old(local).page_organization,
{
    if segment.get_commit_mask(Tracked(&*local)).is_full()
        && segment.get_decommit_mask(Tracked(&*local)).is_empty()
    {
        proof {
            //assert forall |j: int| set_int_range(p as int, p + size).contains(j)
            //  implies local.commit_mask(segment.segment_id@).bytes(segment.segment_id@).contains(j)
            //by {
                const_facts();
                reveal(CommitMask::bytes);
            //}
        }

        return true;
    }

    segment_commitx(segment, true, p, size, Tracked(local))
}

pub fn segment_perhaps_decommit(
    segment: SegmentPtr,
    p: usize,
    size: usize,
    Tracked(local): Tracked<&mut Local>,
)
    requires old(local).wf_main(),
        segment.wf(),
        segment.is_in(*old(local)),
        p >= segment.segment_ptr.addr(),
        p + size <= segment.segment_ptr.addr() + SEGMENT_SIZE,
        set_int_range(p as int, p + size).disjoint(
            segment_info_range(segment.segment_id@)
                + old(local).segment_pages_used_total(segment.segment_id@)
        )
    ensures
        local.wf_main(),
        common_preserves(*old(local), *local),
        local.page_organization == old(local).page_organization,
        local.pages == old(local).pages,
        local.psa == old(local).psa,
{
    if !segment.get_allow_decommit(Tracked(&*local)) {
        return;
    }

    if option_decommit_delay() == 0 {
        todo();
    } else {
        proof {
            segment_id_divis(segment);
        }

        let mut mask: CommitMask = CommitMask::empty();
        let (start, full_size) =
            segment_commit_mask(segment.segment_ptr as *mut u8, true, p, size, &mut mask);

        if mask.is_empty() || full_size == 0 {
            return;
        }

        let mut cmask = CommitMask::empty();
        segment_get_mut_main!(segment, local, main => {
            main.commit_mask.create_intersect(&mask, &mut cmask);
            main.decommit_mask.set(&cmask);
        });

        proof {
            const_facts();
            reveal(CommitMask::bytes);
            let segment_id = segment.segment_id@;
            segment_start_mult_commit_size(segment_id);
            assert(segment.segment_ptr as int % COMMIT_SIZE as int == 0);
            /*assert forall |addr| mask.bytes(segment_id).contains(addr)
                implies set_int_range(p as int, p + size).contains(addr)
            by {
                assert(mask@.contains((addr - segment.segment_ptr.addr()) / COMMIT_SIZE as int));
                assert((addr - segment.segment_ptr.addr()) / COMMIT_SIZE as int
                    >= (start - segment.segment_ptr.addr()) / COMMIT_SIZE as int);
                assert(addr >= start);
                assert(addr >= p);
                assert(addr < p + size);
            }*/
            assert(mask.bytes(segment_id)
                <= set_int_range(p as int, p + size));
            assert(cmask.bytes(segment_id)
                <= set_int_range(p as int, p + size));
            assert(local.decommit_mask(segment_id).bytes(segment_id) =~=
                old(local).decommit_mask(segment_id).bytes(segment_id) + cmask.bytes(segment_id));
            assert(old(local).mem_chunk_good(segment_id));
            preserve_totals(*old(local), *local, segment_id);
            //assert(local.segment_pages_used_total(segment_id)
            //    =~= old(local).segment_pages_used_total(segment_id));
            //assert(local.segment_pages_range_total(segment_id)
            //    =~= old(local).segment_pages_range_total(segment_id));
            preserves_mem_chunk_good_except(*old(local), *local, segment.segment_id@);
            assert(mem_chunk_good1(
                local.segments[segment_id].mem,
                segment_id,
                local.commit_mask(segment_id).bytes(segment_id),
                local.decommit_mask(segment_id).bytes(segment_id),
                local.segment_pages_range_total(segment_id),
                local.segment_pages_used_total(segment_id),
            ));
            assert(local.mem_chunk_good(segment.segment_id@));
            assert(local.wf_main());
        }
        let ghost local_snap = *local;

        let now = clock_now();
        if segment.get_decommit_expire(Tracked(&*local)) == 0 {
            segment_get_mut_main!(segment, local, main => {
                main.decommit_expire = now.wrapping_add(option_decommit_delay());
            });
            proof { preserves_mem_chunk_good(local_snap, *local); }
        } else if segment.get_decommit_expire(Tracked(&*local)) <= now {
            let ded = option_decommit_extend_delay();
            if segment.get_decommit_expire(Tracked(&*local)).wrapping_add(option_decommit_extend_delay()) <= now {
                segment_delayed_decommit(segment, true, Tracked(&mut *local));
            } else {
                segment_get_mut_main!(segment, local, main => {
                    main.decommit_expire = now.wrapping_add(option_decommit_extend_delay());
                });
                proof { preserves_mem_chunk_good(local_snap, *local); }
            }
        } else {
            segment_get_mut_main!(segment, local, main => {
                main.decommit_expire =
                    main.decommit_expire.wrapping_add(option_decommit_extend_delay());
            });
            proof { preserves_mem_chunk_good(local_snap, *local); }
        }
    }
}

pub fn segment_delayed_decommit(
    segment: SegmentPtr,
    force: bool,
    Tracked(local): Tracked<&mut Local>,
)
    requires old(local).wf_main(),
        segment.wf(),
        segment.is_in(*old(local)),
    ensures
        local.wf_main(),
        common_preserves(*old(local), *local),
        local.page_organization == old(local).page_organization,
        local.pages == old(local).pages,
        local.psa == old(local).psa,
{
    if !segment.get_allow_decommit(Tracked(&*local))
        || segment.get_decommit_mask(Tracked(&*local)).is_empty()
    {
        return;
    }

    let now = clock_now();
    if !force && now < segment.get_decommit_expire(Tracked(&*local)) {
        return;
    }

    proof { const_facts(); }

    let mut idx = 0;
    loop
        invariant_except_break
            local.wf_main(),
            segment.wf(),
            segment.is_in(*local),
            0 <= idx < COMMIT_MASK_BITS,
        invariant
            local.wf_main(),
            common_preserves(*old(local), *local),
            local.page_organization == old(local).page_organization,
            local.pages == old(local).pages,
            local.psa == old(local).psa,
    {
        proof {
            const_facts();
            reveal(CommitMask::bytes);
        }

        let mask = segment.get_decommit_mask(Tracked(&*local));
        let (next_idx, count) = mask.next_run(idx);
        if count == 0 {
            break;
        }
        idx = next_idx;

        let p = segment.segment_ptr.addr() + idx * COMMIT_SIZE as usize;
        let size = count * COMMIT_SIZE as usize;
        segment_commitx(segment, false, p, size, Tracked(&mut *local));
    }
}

}
