#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::set_lib::*;
use vstd::assert_by_contradiction;

verus!{

// TODO: This belongs in set_lib
proof fn singleton_set_unique_elt<T>(s: Set<T>, a:T, b:T)
    requires
        s.finite(),
        s.len() == 1,
        s.contains(a),
        s.contains(b),
    ensures
        a == b,
{
    assert_by_contradiction!(a == b, {
        let empty = s.remove(a);
        assert(empty.len() == 0);
        assert(empty.contains(b));
    });
}

proof fn set_mismatch(s1:Set<nat>, s2:Set<nat>, missing:nat)
    requires
        s1.finite(),
        s2.finite(),
        s1.len() == s2.len(),
        forall |elt| s2.contains(elt) ==> s1.contains(elt),
        s1.contains(missing),
        !s2.contains(missing),
    ensures
        false,
    decreases s1.len(),
{
    if s1.len() == 1 {
        let elt = s2.choose();
        assert(s2.contains(elt));
        assert(s1.contains(elt));
        singleton_set_unique_elt(s1, elt, missing);
        assert(elt == missing);
        assert(false);
    } else {
        let elt = s2.choose();
        assert(s2.contains(elt));
        assert(s1.contains(elt));
        let s1_smaller = s1.remove(elt);
        set_mismatch(s1_smaller, s2.remove(elt), missing);
    }
}

/* TODO: These next two should be derived from the set_int_range and lemma_int_range in 
 *       set_lib.rs, but it's surprisingly painful to do so */

/// Creates a finite set of nats in the range [lo, hi).
pub open spec fn set_nat_range(lo: nat, hi: nat) -> Set<nat> {
    Set::int_range(lo as int, hi as int).map(|i| i as nat)
}

pub broadcast proof fn lemma_nat_range_contains(lo: nat, hi: nat)
ensures
    #![trigger set_nat_range(lo, hi)]
    forall |x: nat| lo <= x < hi <==> #[trigger] set_nat_range(lo, hi).contains(x)
{
    assert forall |x: nat| lo <= x < hi implies set_nat_range(lo, hi).contains(x) by {
        assert(Set::int_range(lo as int, hi as int).contains(x as int));    // witness exists
    }
}

/// If a set solely contains nats in the range [a, b), then its size is
/// bounded by b - a.
pub proof fn lemma_nat_range(lo: nat, hi: nat)
    requires
        lo <= hi,
    ensures
        set_nat_range(lo, hi).finite(),
        set_nat_range(lo, hi).len() == hi - lo,
    decreases
        hi - lo,
{
    broadcast use lemma_nat_range_contains;
    if lo == hi {
        assert(set_nat_range(lo, hi) =~= Set::empty());
    } else {
        lemma_nat_range(lo, (hi - 1) as nat);
        assert(set_nat_range(lo, (hi - 1) as nat).insert((hi - 1) as nat) =~= set_nat_range(lo, hi));
    }
}


proof fn nat_set_size(s:Set<nat>, bound:nat)
    requires
        forall |i: nat| (0 <= i < bound <==> s.contains(i)),
    ensures
        s.finite(),
        s.len() == bound,
{
    broadcast use lemma_nat_range_contains;
    let nats = set_nat_range(0, bound);
    lemma_nat_range(0, bound);
    assert(s =~= nats);
}

        

pub proof fn pigeonhole_missing_idx_implies_double_helper(
    m: Map<nat, nat>,
    missing: nat,
    len: nat,
    prev_vals: Set<nat>,
    k: nat,
) -> (dup2: nat)
    requires
        len >= 2,
        forall |i: nat| (0 <= i < len <==> m.dom().contains(i)),
        forall |i: nat| (#[trigger] m.dom().contains(i) ==> (
            0 <= m[i] < len && m[i] != missing
        )),
        0 <= missing < len,
        0 <= k < len,
        prev_vals.finite(),
        prev_vals.len() == k,
        //forall |j| 0 <= j < k ==> #[trigger] prev_vals.contains(m[j]),
        forall |elt| #[trigger] prev_vals.contains(elt) ==> exists |j| 0 <= j < k && m[j] == elt,
    ensures 
        m.dom().contains(dup2),
        exists |dup1| #![auto] dup1 != dup2 && m.dom().contains(dup1) && 0 <= dup1 < len && m[dup1] == m[dup2],
    decreases len - k,
{
    if prev_vals.contains(m[k]) {
        let dup1 = choose |j| 0 <= j < k && m[j] == m[k];
        dup1
    } else {
        if k < len - 1 {
            pigeonhole_missing_idx_implies_double_helper(m, missing, len, prev_vals.insert(m[k]), k + 1)
        } else {
            assert forall |elt| prev_vals.contains(elt) implies 0 <= elt < len && elt != missing by {
                let j = choose |j| 0 <= j < k && m[j] == elt;
                assert(m.dom().contains(j));
            }
            let new_prev_vals = prev_vals.insert(m[k]);
            assert forall |elt| new_prev_vals.contains(elt) implies 0 <= elt < len && elt != missing by {
                if prev_vals.contains(elt) {
                } else {
                    assert(elt == m[k]);
                    assert(m.dom().contains(k));
                }
            };
            nat_set_size(m.dom(), len);
            set_mismatch(m.dom(), new_prev_vals, missing);
            1
        }
    }
}

pub proof fn pigeonhole_missing_idx_implies_double(
    m: Map<nat, nat>,
    missing: nat,
    len: nat,
) -> (r: (nat, nat))
    requires
        forall |i: nat| (0 <= i < len <==> m.dom().contains(i)),
        forall |i: nat| (#[trigger] m.dom().contains(i) ==> (
            0 <= m[i] < len && m[i] != missing
        )),
        0 <= missing < len,
    ensures ({ let (i, j) = r;
        i != j
          && m.dom().contains(i)
          && m.dom().contains(j)
          && m[i] == m[j]
    })
{
    assert(len >= 2) by {
        assert(len >= 1);
        if len == 1 {
            assert(m.dom().contains(0));
            assert(m[0] != missing);
        }
    };
    let dup2 = pigeonhole_missing_idx_implies_double_helper(m, missing, len, Set::empty(), 0);
    let dup1 = choose |dup1| #![auto] dup1 != dup2 && m.dom().contains(dup1) && 0 <= dup1 < len && m[dup1] == m[dup2];
    (dup1, dup2)
}

pub proof fn pigeonhole_too_many_elements_implies_double(
    m: Map<nat, nat>,
    len: nat,
) -> (r: (nat, nat))
    requires
        forall |i: nat| (0 <= i < len + 1 <==> m.dom().contains(i)),
        forall |i: nat| #[trigger] m.dom().contains(i) ==> 0 <= m[i] < len,
    ensures ({ let (i, j) = r;
        i != j
          && m.dom().contains(i)
          && m.dom().contains(j)
          && m[i] == m[j]
    })
{
    pigeonhole_missing_idx_implies_double(m, len, len + 1)
}

}
