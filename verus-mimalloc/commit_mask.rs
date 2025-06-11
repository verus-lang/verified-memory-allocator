use vstd::prelude::*;
use crate::config::*;
use crate::tokens::*;
use crate::layout::*;
use crate::types::*;

verus!{

proof fn lemma_map_distribute<S,T>(s1: ISet<S>, s2: ISet<S>, f: spec_fn(S) -> T)
    ensures s1.union(s2).map(f) == s1.map(f).union(s2.map(f))
{
    assert forall|x:T| #![auto] s1.map(f).union(s2.map(f)).contains(x) implies s1.union(s2).map(f).contains(x) by {
        if s1.map(f).contains(x) {
            assert(s1.union(s2).contains(choose|y:S| s1.contains(y) && f(y) == x));
        } else {
            assert(s1.union(s2).contains(choose|y:S| s2.contains(y) && f(y) == x));
        }
    }
    assert(s1.union(s2).map(f) =~= s1.map(f).union(s2.map(f)));
}

proof fn lemma_map_distribute_auto<S,T>()
    ensures forall|s1: ISet<S>, s2: ISet<S>, f: spec_fn(S) -> T| s1.union(s2).map(f) == #[trigger] s1.map(f).union(s2.map(f))
{
    assert forall|s1: ISet<S>, s2: ISet<S>, f: spec_fn(S) -> T| s1.union(s2).map(f) == #[trigger] s1.map(f).union(s2.map(f)) by {
        lemma_map_distribute(s1, s2, f);
    }
}

// used for triggering
spec fn mod64(x: usize) -> usize { x % 64 }
spec fn div64(x: usize) -> usize { x / 64 }

#[verifier::opaque]
spec fn is_bit_set(a: usize, b: usize) -> bool {
    a & (1usize << b) == (1usize << b)
}

#[allow(unused_macros)]
macro_rules! is_bit_set {
    ($a:expr, $b:expr) => {
        $a & (1u64 << $b) == (1u64 << $b)
    }
}

proof fn lemma_bitmask_to_is_bit_set(n: usize, o: usize)
    requires
        n < 64,
        o <= 64 - n,
    ensures ({
        let m = sub(1usize << n, 1) << o;
        &&& forall|j: usize| j < o           ==> !is_bit_set(m, j)
        &&& forall|j: usize| o <= j < o + n  ==> is_bit_set(m, j)
        &&& forall|j: usize| o + n <= j < 64 ==> !is_bit_set(m, j)
    })
{
    let m = (sub(1usize << n, 1) << o) as usize;
    assert forall|j: usize| {
        &&& (j < o           ==> !is_bit_set(m, j))
        &&& (o <= j < o + n  ==> is_bit_set(m, j))
        &&& (o + n <= j < 64 ==> !is_bit_set(m, j))
    } by {
        let j = j as u64; let m = m as u64; let o = o as u64; let n = n as u64;
        reveal(is_bit_set);
        if j < 64 {
            assert(j < o               ==> !is_bit_set!(m, j)) by (bit_vector)
                requires j < 64, m == (sub(1u64 << n, 1) << o) as u64;
            assert(o <= j < add(o, n)  ==> is_bit_set!(m, j)) by (bit_vector)
                requires j < 64, m == (sub(1u64 << n, 1) << o) as u64;
            assert(add(o, n) <= j < 64 ==> !is_bit_set!(m, j)) by (bit_vector)
                requires n < 64, j < 64, m == (sub(1u64 << n, 1) << o) as u64;
        } else { }
    }
}

proof fn lemma_obtain_bit_index_3_aux(a: u64, b: u64, hi: u64) -> (i: u64)
    requires
        a & b != b,
        hi <= 64,
        a >> hi == 0,
        b >> hi == 0,
    ensures
        i < hi,
        !is_bit_set!(a, i),
        is_bit_set!(b, i),
    decreases hi
{
    assert(hi != 0) by (bit_vector)
        requires a & b != b, hi <= 64, a >> hi == 0, b >> hi == 0;
    assert(1u64 << 0 == 1) by (bit_vector);
    if a & 1 != 1 && b & 1 == 1 {
        return 0;
    } else {
        assert((a >> 1) & (b >> 1) != (b >> 1) && (a >> 1) >> sub(hi, 1) == 0 && (b >> 1) >> sub(hi, 1) == 0) by (bit_vector)
            requires !(a & 1 != 1 && b & 1 == 1), a & b != b, a >> hi == 0, b >> hi == 0;
        let j = lemma_obtain_bit_index_3_aux(a >> 1, b >> 1, sub(hi, 1));
        assert(!is_bit_set!(a, add(j, 1)) && is_bit_set!(b, add(j, 1))) by (bit_vector)
            requires !is_bit_set!(a >> 1u64, j), is_bit_set!(b >> 1u64, j), j < 64;
        add(j, 1)
    }
}

proof fn lemma_obtain_bit_index_3(a: usize, b: usize) -> (i: usize)
    requires a & b != b
    ensures
        i < 64,
        !is_bit_set(a, i),
        is_bit_set(b, i),
{
    reveal(is_bit_set);
    assert(a as u64 >> 64 == 0) by (bit_vector);
    assert(b as u64 >> 64 == 0) by (bit_vector);
    lemma_obtain_bit_index_3_aux(a as u64, b as u64, 64) as usize
}

proof fn lemma_obtain_bit_index_2(a: usize) -> (b: usize)
    requires a != !0usize
    ensures
        b < 64,
        !is_bit_set(a, b)
{
    reveal(is_bit_set);
    assert(!a != 0usize) by (bit_vector)
        requires a != !0usize;
    let b = lemma_obtain_bit_index_1(!a) as u64;
    let a = a as u64;
    assert(!is_bit_set!(a, b)) by (bit_vector)
        requires b < 64 && !a & (1u64 << b) == (1usize << b);
    b as usize
}

proof fn lemma_obtain_bit_index_1_aux(a: u64, hi: u64) -> (i: u64)
    requires
        a != 0,
        hi <= 64,
        a >> hi == 0,
    ensures
        i < hi,
        is_bit_set!(a, i),
    decreases hi
{
    assert(hi != 0) by (bit_vector)
        requires a != 0, hi <= 64, a >> hi == 0;
    assert(1u64 << 0 == 1) by (bit_vector);
    if a & 1 == 1 {
        return 0;
    } else {
        assert((a >> 1) != 0 && (a >> 1) >> sub(hi, 1) == 0) by (bit_vector)
            requires a & 1 != 1, a != 0, a >> hi == 0;
        let j = lemma_obtain_bit_index_1_aux(a >> 1, sub(hi, 1));
        assert(is_bit_set!(a, add(j, 1))) by (bit_vector)
            requires is_bit_set!(a >> 1u64, j) && j < 64;
        add(j, 1)
    }
}

proof fn lemma_obtain_bit_index_1(a: usize) -> (b: usize)
    requires a != 0
    ensures
        b < 64,
        is_bit_set(a, b)
{
    reveal(is_bit_set);
    assert(a as u64 >> 64 == 0) by (bit_vector);
    lemma_obtain_bit_index_1_aux(a as u64, 64) as usize
}

// I don't think there's a good reason that some of these would need `j < 64` and others don't but
// for some the bitvector assertions without it succeeds and for others it doesn't.
proof fn lemma_is_bit_set()
    ensures
        forall|j: usize| j < 64 ==> !(#[trigger] is_bit_set(0, j)),
        forall|j: usize| is_bit_set(!0usize, j),
        forall|a: usize, b: usize, j: usize| #[trigger] is_bit_set(a | b, j)  <==> is_bit_set(a, j) || is_bit_set(b, j),
        forall|a: usize, b: usize, j: usize| j < 64 ==> (#[trigger] is_bit_set(a & !b, j) <==> is_bit_set(a, j) && !is_bit_set(b, j)),
        forall|a: usize, b: usize, j: usize| #[trigger] is_bit_set(a & b, j)  <==> is_bit_set(a, j) && is_bit_set(b, j),
        // Implied by previous properties, possibly too aggressive trigger
        forall|a: usize, b: usize, j: usize| j < 64 ==> (a & b == 0) ==> !(#[trigger] is_bit_set(a, j) && #[trigger] is_bit_set(b, j)),
{
    reveal(is_bit_set);
    assert(forall|j: u64| #![auto] j < 64 ==> !is_bit_set!(0, j)) by (bit_vector);
    assert(forall|j: u64| #![auto] is_bit_set!(!0, j)) by (bit_vector);
    assert(forall|a: u64, b: u64, j: u64|
           (is_bit_set!(a | b, j) <==> is_bit_set!(a, j) || is_bit_set!(b, j))) by (bit_vector);
    assert(forall|a: u64, b: u64, j: u64| j < 64 ==>
           (is_bit_set!(a & !b, j) <==> is_bit_set!(a, j) && !is_bit_set!(b, j))) by (bit_vector);
    assert(forall|a: u64, b: u64, j: u64|
           (is_bit_set!(a & b, j) <==> is_bit_set!(a, j) && is_bit_set!(b, j))) by (bit_vector);
}

pub struct CommitMask {
    mask: [usize; 8],     // size = COMMIT_MASK_FIELD_COUNT
}

impl CommitMask {
    pub closed spec fn view(&self) -> ISet<int> {
        ISet::new(|t: (int, usize)|
                 0 <= t.0 < 8 && t.1 < 64
                 && is_bit_set(self.mask[t.0], t.1)
        ).map(|t: (int, usize)| t.0 * 64 + t.1)
    }

    proof fn lemma_view(&self)
        ensures
        // forall|i: int| self@.contains(i) ==> i < 512,
        // TODO: this isn't currently used but probably will need it (-> check later)
        (forall|i: int| self@.contains(i) ==> {
            let a = i / usize::BITS as int;
            let b = (i % usize::BITS as int) as usize;
            &&& a * 64 + b == i
            &&& is_bit_set(self.mask[a], b)
        }),
        forall|a: int, b: usize| 0 <= a < 8 && b < 64 && is_bit_set(self.mask[a], b)
            ==> #[trigger] self@.contains(a * 64 + b),
    {
        assert forall|a: int, b: usize| 0 <= a < 8 && b < 64 && is_bit_set(self.mask[a], b)
            implies self@.contains(a * 64 + b)
        by {
            assert(ISet::new(|t: (int, usize)|
                     0 <= t.0 < 8 && t.1 < 64
                     && is_bit_set(self.mask[t.0], t.1)
            ).contains((a, b))) by (nonlinear_arith)
                requires 0 <= a < 8 && b < 64 && is_bit_set(self.mask[a], b);
        }
    }

    pub open spec fn i_bytes(&self, segment_id: SegmentId) -> ISet<int> {
        ISet::<int>::new(|addr: int|
            self@.contains(
                (addr - segment_start(segment_id)) / COMMIT_SIZE as int
            )
        )
    }

    // An explicit construction of view to prove view is finite
    pub closed spec fn finite_view(&self) -> Set<int> {
        Set::int_range(0, 8).product(|t0| Set::int_range(0, 64).map(|t1| (t0, t1 as usize)))
            .filter(|t: (int, usize)| is_bit_set(self.mask[t.0], t.1))
            .map(|t: (int, usize)| t.0 * 64 + t.1)
    }

    pub proof fn finite_view_ensures(&self)
    ensures self@.congruent(self.finite_view())
    {
        let ipre = ISet::new(|t: (int, usize)|
                 0 <= t.0 < 8 && t.1 < 64
                 && is_bit_set(self.mask[t.0], t.1));
        let fpre = Set::int_range(0, 8).product(|t0| Set::int_range(0, 64).map(|t1| (t0, t1 as usize)))
            .filter(|t: (int, usize)| is_bit_set(self.mask[t.0], t.1));
        assert forall |a| ipre.contains(a) implies fpre.contains(a) by {
            assert( Set::int_range(0, 8).contains(a.0) );   // witness to product
            assert( Set::int_range(0, 64).contains(a.1 as int) ); // witness to map
        }
        assert( ipre.congruent(fpre) ); // trigger filter congruence
    }

    pub broadcast proof fn i_bytes_ensures(&self, segment_id: SegmentId)
    ensures #![trigger self.bytes(segment_id)] self.i_bytes(segment_id).finite()
    {
        self.finite_view_ensures();
        let fset = self.finite_view().product(|elt: int|
                Set::int_range(0, COMMIT_SIZE as int).map(|r| elt*COMMIT_SIZE+segment_start(segment_id)+r));
        let iset = self.i_bytes(segment_id);

        assert forall |addr| iset.contains(addr) implies fset.contains(addr) by {
            let off = addr - segment_start(segment_id);
            let elt = off/(COMMIT_SIZE as int);
            let r = off - elt * COMMIT_SIZE;
            assert( Set::int_range(0, COMMIT_SIZE as int).contains(r) );    // witness to product.map
        }
        fset.congruent_infiniteness(iset);

            // Can't do this proof by surj_on because that's private to vstd::set. :v( Others may
            // someday want to prove finiteness... TODO(jonh): make discussion?
//         assert(self.i_bytes(segment_id).finite()) by {
//             let (f1, ub1) = choose|f: spec_fn(int) -> nat, ub: nat| #[trigger]
//                 vstd::set::trigger_finite(f, ub) && vstd::set::surj_on(f, self@) && (forall|e| self@.contains(e) ==> f(e) < ub);
//             assert( vstd::set::surj_on(f1, self@) && (forall|e| self@.contains(e) ==> f(e) < ub1) );
// 
//             let base = segment_start(segment_id);
//             let f = |addr| f1((addr-base) / COMMIT_SIZE as int) * COMMIT_SIZE + base;
//             let ub = f(ub1) + COMMIT_SIZE;
// 
//             assert(vstd::set::surj_on(f, self.i_bytes(segment_id)));
//             assert forall |a| self.i_bytes(segment_id).contains(a) ==> f(a) < ub by {}
//             assert(vstd::set::trigger_finite(f, ub));
//         }
        reveal(CommitMask::bytes);
    }

    #[verifier::opaque]
    pub open spec fn bytes(&self, segment_id: SegmentId) -> Set<int> {
        ISet::<int>::new(|addr: int|
            self@.contains(
                (addr - segment_start(segment_id)) / COMMIT_SIZE as int
            )
        ).to_finite()
    }

    pub fn empty() -> (cm: CommitMask)
        ensures cm@ == ISet::<int>::empty()
    {
        let res = CommitMask { mask: [ 0, 0, 0, 0, 0, 0, 0, 0 ] };
        proof {
            lemma_is_bit_set();
            res.lemma_view();
            assert(res@ =~= ISet::<int>::empty());
        }
        res
    }

    pub fn all_set(&self, other: &CommitMask) -> (res: bool)
        ensures res == other@.subset_of(self@)
    {
        let mut i = 0;
        while i < 8
            invariant forall|j: int| #![auto] 0 <= j < i ==> self.mask[j] & other.mask[j] == other.mask[j]
        {
            if self.mask[i] & other.mask[i] != other.mask[i] {
                proof {
                    self.lemma_view();
                    other.lemma_view();
                    lemma_is_bit_set();
                    let j = lemma_obtain_bit_index_3(self.mask[i as int], other.mask[i as int]);
                    assert(!self@.contains(i * 64 + j) && other@.contains(i * 64 + j));
                }
                return false;
            }
            i = i + 1;
        }
        proof {
            lemma_is_bit_set();
            self.lemma_view();
            other.lemma_view();
        }
        return true;
    }

    pub fn any_set(&self, other: &CommitMask) -> (res: bool)
        ensures res == !self@.disjoint(other@)
    {
        let mut i = 0;
        while i < 8
            invariant forall|j: int| #![auto] 0 <= j < i ==> self.mask[j] & other.mask[j] == 0
        {
            if self.mask[i] & other.mask[i] != 0 {
                proof {
                    self.lemma_view();
                    other.lemma_view();
                    lemma_is_bit_set();
                    let j = lemma_obtain_bit_index_1(self.mask[i as int] & other.mask[i as int]);
                    assert(self@.contains(i * 64 + j) && other@.contains(i * 64 + j));
                }
                return true;
            }
            i += 1;
        }
        proof {
            lemma_is_bit_set();
            self.lemma_view();
            other.lemma_view();
            assert(self@.disjoint(other@));
        }
        return false;
    }

    pub fn create_intersect(&self, other: &CommitMask, res: &mut CommitMask)
        ensures res@ == self@.intersect(other@)
    {
        let mut i = 0;
        while i < 8
            invariant
                forall|j: int| 0 <= j < i ==> #[trigger] res.mask[j] == self.mask[j] & other.mask[j],
        {
            res.mask.set(i, self.mask[i] & other.mask[i]);
            i += 1;
        }
        proof {
            self.lemma_view();
            other.lemma_view();
            res.lemma_view();
            lemma_is_bit_set();
            assert(res@ =~= self@.intersect(other@));
        }
    }

    pub fn clear(&mut self, other: &CommitMask)
        ensures self@ == old(self)@.difference(other@)
    {
        let mut i = 0;
        while i < 8
            invariant
                forall|j: int| 0 <= j < i ==> #[trigger] self.mask[j] == old(self).mask[j] & !other.mask[j],
                forall|j: int| i <= j < 8 ==> #[trigger] self.mask[j] == old(self).mask[j]
        {
            let m = self.mask[i];
            self.mask.set(i, m & !other.mask[i]);
            i += 1;
        }
        proof {
            old(self).lemma_view();
            other.lemma_view();
            self.lemma_view();
            lemma_is_bit_set();
            assert(self@ =~= old(self)@.difference(other@));
        }
    }

    pub fn set(&mut self, other: &CommitMask)
        ensures self@ == old(self)@.union(other@)
    {
        let mut i = 0;
        while i < 8
            invariant
                forall|j: int| 0 <= j < i ==> #[trigger] self.mask[j] == old(self).mask[j] | other.mask[j],
                forall|j: int| i <= j < 8 ==> #[trigger] self.mask[j] == old(self).mask[j]
        {
            let m = self.mask[i];
            self.mask.set(i, m | other.mask[i]);
            i += 1;
        }
        proof {
            old(self).lemma_view();
            other.lemma_view();
            self.lemma_view();
            lemma_is_bit_set();
            assert(self@ =~= old(self)@.union(other@));
        }
    }

    proof fn lemma_change_one_entry(&self, other: &Self, i: int)
        requires
            0 <= i < 8,
            self.mask[i] == 0,
            forall|j: int| 0 <= j < i ==> other.mask[j] == self.mask[j],
            forall|j: int| i < j < 8 ==> other.mask[j] == self.mask[j],
        ensures
            other@ == self@.union(ISet::new(|b: usize| b < 64 && is_bit_set(other.mask[i], b)).map(|b: usize| 64 * i + b)),
    {
        let s_un = ISet::new(|b: usize| b < 64 && is_bit_set(other.mask[i], b));
        let f_un = |b: usize| 64 * i + b;
        let f = |t: (int, usize)| t.0 * 64 + t.1;
        let s_full = ISet::new(|t: (int, usize)| 0 <= t.0 < 8 && t.1 < 64 && is_bit_set(self.mask[t.0], t.1));
        let s_full_o = ISet::new(|t: (int, usize)| 0 <= t.0 < 8 && t.1 < 64 && is_bit_set(other.mask[t.0], t.1));
        let s1 = ISet::new(|t: (int, usize)| 0 <= t.0 < i && t.1 < 64 && is_bit_set(self.mask[t.0], t.1));
        let s2 = ISet::new(|t: (int, usize)| t.0 == i && t.1 < 64 && is_bit_set(self.mask[i], t.1));
        let s2o = ISet::new(|t: (int, usize)| t.0 == i && t.1 < 64 && is_bit_set(other.mask[i], t.1));
        let s3 = ISet::new(|t: (int, usize)| i <  t.0 < 8 && t.1 < 64 && is_bit_set(self.mask[t.0], t.1));
        assert(s_full =~= s1.union(s2).union(s3));
        assert(s2 =~= ISet::empty()) by { lemma_is_bit_set(); }
        lemma_map_distribute_auto::<(int,usize),int>();
        assert(s_full.map(f) =~= s1.map(f).union(s2.map(f)).union(s3.map(f)));
        assert(s_full_o =~= s_full.union(s2o));
        assert forall|x| #![auto] s_un.map(f_un).contains(x) implies s2o.map(f).contains(x) by {
            assert(s2o.contains((i, choose|y| s_un.contains(y) && f_un(y) == x)));
        };
        assert forall|x| #![auto] s2o.map(f).contains(x) implies s_un.map(f_un).contains(x) by {
            let y = choose|y| s2o.contains(y) && f(y) == x;
            assert(ISet::new(|b: usize| b < 64 && is_bit_set(other.mask[i], b)).contains(y.1));
        };
        assert(s_un.map(f_un) =~= s2o.map(f));
    }

    pub fn create(&mut self, idx: usize, count: usize)
        requires
            idx + count <= COMMIT_MASK_BITS,
            old(self)@ == ISet::<int>::empty(),
        ensures self@ == ISet::new(|i: int| idx <= i < idx + count),
    {
        proof {
            const_facts();
            lemma_is_bit_set();
            self.lemma_view();
            assert forall|i: int| 0 <= i < 8 implies self.mask[i] == 0 by {
                if self.mask[i] != 0 {
                    let j = lemma_obtain_bit_index_1(self.mask[i]);
                    assert(self@.contains(i * 64 + j));
                }
            }
        }
        if count == COMMIT_MASK_BITS as usize {
            self.create_full();
        } else if count == 0 {
            assert(self@ =~= ISet::new(|i: int| idx <= i < idx + count));
        } else {
            let mut i = idx / usize::BITS as usize;
            let mut ofs: usize = idx % usize::BITS as usize;
            let mut bitcount = count;
            assert(ISet::new(|j: int| idx <= j < idx + (count - bitcount)) =~= ISet::empty());
            while bitcount > 0
                invariant
                    self@ == ISet::new(|j: int| idx <= j < idx + (count - bitcount)),
                    ofs == if count == bitcount { idx % 64 } else { 0 },
                    bitcount > 0 ==> 64 * i + ofs == idx + (count - bitcount),
                    idx + count <= 512,
                    forall|j: int| i <= j < 8 ==> self.mask[j] == 0,
                    bitcount <= count,
            {
                assert(i < 8) by (nonlinear_arith)
                    requires
                        idx + (count - bitcount) < 512,
                        i == (idx + (count - bitcount)) / 64;
                let avail = usize::BITS as usize - ofs;
                let c = if bitcount > avail { avail } else { bitcount };
                let mask = if c >= usize::BITS as usize {
                    !0usize
                } else {
                    assert((1usize << c) > 0usize) by (bit_vector) requires c < 64usize;
                    ((1usize << c) - 1) << ofs
                };
                let old_self = Ghost(*self);
                self.mask.set(i, mask);
                let oi = Ghost(i);
                let obc = Ghost(bitcount);
                let oofs = Ghost(ofs);
                bitcount -= c;
                ofs = 0;
                i += 1;
                proof {
                    assert(forall|a: u64| a << 0u64 == a) by (bit_vector);
                    let oi   = oi@;
                    let obc  = obc@;
                    let oofs = oofs@;
                    lemma_is_bit_set();
                    old_self@.lemma_change_one_entry(self, oi as int);
                    assert(self@ == old_self@@.union(ISet::new(|b: usize| b < 64 && is_bit_set(self.mask[oi as int], b)).map(|b: usize| 64 * oi + b)));
                    // TODO: a lot of duplicated proof structure here, should be able to
                    // somehow lift that structure out of the if-else
                    if oofs > 0 { // first iteration
                        assert(ISet::new(|j: int| idx <= j < idx + (count - bitcount))
                               =~= ISet::new(|j: int| idx + (count - obc) <= j < idx + (count - bitcount)));
                        if obc < 64 {
                            assert(mask == sub(1usize << c, 1usize) << oofs);
                            lemma_bitmask_to_is_bit_set(c, oofs);
                            assert(ISet::new(|j: int| idx + (count - obc) <= j < idx + (count - bitcount))
                                   =~= ISet::new(|b: usize| b < 64 && is_bit_set(self.mask[oi as int], b)).map(|b: usize| 64 * oi + b))
                            by {
                                let s1 = ISet::new(|j: int| idx + (count - obc) <= j < idx + (count - bitcount));
                                let s2 = ISet::new(|b: usize| b < 64 && is_bit_set(self.mask[oi as int], b)).map(|b: usize| 64 * oi + b);
                                assert(forall|j: usize| idx + (count - obc) <= j < idx + (count - bitcount) ==> #[trigger] is_bit_set(self.mask[oi as int], mod64(j)));
                                assert forall|x: int| s1.contains(x) implies s2.contains(x) by {
                                    let b = x % 64;
                                    assert(ISet::new(|b: usize| b < 64 && is_bit_set(self.mask[oi as int], b)).contains((x % 64) as usize));
                                }
                            }
                            assert(ISet::new(|j: int| idx + (count - obc) <= j < idx + (count - bitcount))
                                   =~= ISet::new(|b: usize| b < 64 && is_bit_set(self.mask[oi as int], b)).map(|b: usize| 64 * oi + b));
                        } else {
                            assert(mask == sub(1usize << sub(64usize, oofs), 1usize) << oofs);
                            lemma_bitmask_to_is_bit_set(sub(64, oofs), oofs);
                            assert(ISet::new(|j: int| idx + (count - obc) <= j < idx + (count - bitcount))
                                   =~= ISet::new(|b: usize| b < 64 && is_bit_set(self.mask[oi as int], b)).map(|b: usize| 64 * oi + b))
                            by {
                                let s1 = ISet::new(|j: int| idx + (count - obc) <= j < idx + (count - bitcount));
                                let s2 = ISet::new(|b: usize| b < 64 && is_bit_set(self.mask[oi as int], b)).map(|b: usize| 64 * oi + b);
                                assert forall|x: int| s1.contains(x) implies s2.contains(x) by { // unstable
                                    assert(ISet::new(|b: usize| b < 64 && is_bit_set(self.mask[oi as int], b)).contains((x % 64) as usize));
                                }
                            }
                            assert(ISet::new(|j: int| idx + (count - obc) <= j < idx + (count - bitcount))
                                   =~= ISet::new(|b: usize| b < 64 && is_bit_set(self.mask[oi as int], b)).map(|b: usize| 64 * oi + b));
                        }
                    } else if obc < 64 { // last iteration
                        assert(ISet::new(|j: int| idx <= j < idx + (count - bitcount))
                               =~= ISet::new(|j: int| idx <= j < idx + (count - obc))
                                   .union(ISet::new(|j: int| idx + (count - obc) <= j < idx + count)));
                        assert(mask == (1usize << obc) - 1usize);
                        lemma_bitmask_to_is_bit_set(obc, 0);
                        assert(ISet::new(|j: int| idx + (count - obc) <= j < idx + count)
                               =~= ISet::new(|b: usize| b < 64 && is_bit_set(self.mask[oi as int], b)).map(|b: usize| 64 * oi + b))
                        by {
                            let s1 = ISet::new(|j: int| idx + (count - obc) <= j < idx + count);
                            let s2 = ISet::new(|b: usize| b < 64 && is_bit_set(self.mask[oi as int], b)).map(|b: usize| 64 * oi + b);
                            assert forall|x: int| s1.contains(x) implies s2.contains(x) by {
                                assert(ISet::new(|b: usize| b < 64 && is_bit_set(self.mask[oi as int], b)).contains((x % 64) as usize));
                            }
                        }
                        assert(ISet::new(|j: int| idx + (count - obc) <= j < idx + count)
                               =~= ISet::new(|b: usize| b < 64 && is_bit_set(self.mask[oi as int], b)).map(|b: usize| 64 * oi + b));
                    } else {
                        assert(ISet::new(|j: int| idx <= j < idx + (count - bitcount))
                               =~= ISet::new(|j: int| idx <= j < idx + (count - obc))
                                   .union(ISet::new(|j: int| idx + (count - obc) <= j < idx + (count - obc) + 64)));
                        assert(mask == !0usize);
                        let new = ISet::new(|j: int| idx + (count - obc) <= j < idx + (count - obc) + 64);
                        assert(ISet::new(|j: int| 64 * oi <= j < 64 * oi + 64)
                               =~= ISet::new(|b: usize| b < 64 && is_bit_set(self.mask[oi as int], b)).map(|b: usize| 64 * oi + b))
                        by {
                            let s1 = ISet::new(|j: int| 64 * oi <= j < 64 * oi + 64);
                            let s2 = ISet::new(|b: usize| b < 64 && is_bit_set(self.mask[oi as int], b)).map(|b: usize| 64 * oi + b);
                            assert forall|x: int| s1.contains(x) implies s2.contains(x) by {
                                assert(ISet::new(|b: usize| b < 64 && is_bit_set(self.mask[oi as int], b)).contains((x % 64) as usize));
                            }
                        }
                        assert(ISet::new(|j: int| 64 * oi <= j < 64 * oi + 64)
                               =~= ISet::new(|b: usize| b < 64 && is_bit_set(self.mask[oi as int], b)).map(|b: usize| 64 * oi + b));
                    }
                }
                assert(self@ =~= ISet::new(|j: int| idx <= j < idx + (count - bitcount)));
            }
        }
    }

    pub fn create_empty(&mut self)
        ensures self@ == ISet::<int>::empty(),
    {
        let mut i = 0;
        while i < 8
            invariant forall|j: int| 0 <= j < i ==> self.mask[j] == 0
        {
            self.mask.set(i, 0);
            i += 1;
        }
        proof {
            lemma_is_bit_set();
            self.lemma_view();
            assert(self@ =~= ISet::<int>::empty());
        }
    }

    pub fn create_full(&mut self)
        ensures self@ == ISet::new(|i: int| 0 <= i < COMMIT_MASK_BITS),
    {
        let mut i = 0;
        while i < 8
            invariant forall|j: int| 0 <= j < i ==> self.mask[j] == !0usize
        {
            self.mask.set(i, !0usize);
            i += 1;
        }
        proof {
            const_facts();
            lemma_is_bit_set();
            self.lemma_view();
            let seq_set = ISet::new(|i: int| 0 <= i < COMMIT_MASK_BITS);
            let bit_set = ISet::new(|t: (int, int)| 0 <= t.0 < 8 && 0 <= t.1 < 64)
                   .map(|t: (int, int)| t.0 * 64 + t.1);
            assert forall|i: int| seq_set.contains(i) implies bit_set.contains(i) by {
                assert(ISet::new(|t: (int, int)| 0 <= t.0 < 8 && 0 <= t.1 < 64).contains((i / 64, i % 64)));
            }
            assert(seq_set =~= bit_set);
            assert(self@ =~= ISet::new(|i: int| 0 <= i < COMMIT_MASK_BITS));
        }
    }

    pub fn committed_size(&self, total: usize) -> usize
    {
        todo(); loop { }
    }

    pub fn next_run(&self, idx: usize) -> (res: (usize, usize))
        requires 0 <= idx < COMMIT_MASK_BITS,
        ensures ({ let (next_idx, count) = res;
            next_idx + count <= COMMIT_MASK_BITS
            && (forall |t| next_idx <= t < next_idx + count ==> self@.contains(t))
        }),
        // This should be true, but isn't strictly needed to prove safety:
        //forall |t| idx <= t < next_idx ==> !self@.contains(t),
        // Likewise we could have a condition that `count` is not smaller than necessary
    {
        proof { const_facts(); }
        // Starting at idx, scan to find the first bit.

        let mut i: usize = idx / usize::BITS as usize;
        let mut ofs: usize = idx % usize::BITS as usize;
        let mut mask: usize = 0;

        assert(ofs < 64) by (nonlinear_arith)
            requires ofs == idx % usize::BITS as usize;
        // Changed loop condition to use 8 rather than COMMIT_MASK_FIELD_COUNT due to
        // https://github.com/verus-lang/verus/issues/925
        while i < 8
            invariant
                ofs < 64,
            ensures
                i < 8 ==> mask == self.mask[i as int] >> ofs,
                i < 8 ==> ofs < 64,
                i < 8 ==> mask & 1 == 1
        {
            mask = self.mask[i] >> ofs;
            if mask != 0 {
                while mask & 1 == 0
                    invariant
                        i < 8,
                        ofs < 64,
                        mask == self.mask[i as int] >> ofs,
                        mask != 0,
                {
                    assert((mask >> 1usize) != 0usize) by (bit_vector)
                        requires mask != 0usize, mask & 1 == 0usize;
                    assert(forall|m:u64,n:u64| #![auto] n < 64 ==> (m >> n) >> 1u64 == m >> add(n, 1u64)) by (bit_vector);
                    assert(forall|m: u64| #![auto] (m >> 63u64) >> 1u64 == 0u64) by (bit_vector);
                    mask = mask >> 1usize;
                    ofs += 1;
                }
                assert(mask & 1 == 1usize) by (bit_vector) requires mask & 1 != 0usize;
                break;
            }
            i += 1;
            ofs = 0;
        }

        if i >= COMMIT_MASK_FIELD_COUNT as usize {
            (COMMIT_MASK_BITS as usize, 0)
        } else {
            // Count 1 bits in this run
            let mut count: usize = 0;
            let next_idx = i * usize::BITS as usize + ofs;
            assert((i * 64 + ofs) % 64 == ofs) by (nonlinear_arith)
                requires ofs < 64;
            loop
                invariant_except_break
                    mask & 1 == 1,
                    i < 8,
                    mask == self.mask[i as int] >> mod64((next_idx + count) as usize),
                    (next_idx + count) / 64 == i,
                invariant
                    forall|j: usize| next_idx <= j < next_idx + count ==> #[trigger] is_bit_set(self.mask[div64(j) as int], mod64(j)),
                ensures
                    next_idx + count <= 512
            {
                proof { const_facts(); }
                loop
                    invariant_except_break
                        mask & 1 == 1,
                        i < 8,
                        mask == self.mask[i as int] >> mod64((next_idx + count) as usize),
                        (next_idx + count) / 64 == i,
                    invariant
                        forall|j: usize| next_idx <= j < next_idx + count ==> #[trigger] is_bit_set(self.mask[div64(j) as int], mod64(j)),
                    ensures
                        mask & 1 == 0,
                        (next_idx + count) / 64 == if mod64((next_idx + count) as usize) == 0 { i + 1 } else { i as int }
                {
                    proof {
                        assert(forall|m: u64, b: u64| b < 64 && #[trigger] ((m >> b) & 1) == 1 ==> is_bit_set!(m, b)) by (bit_vector);
                        reveal(is_bit_set);
                        assert(forall|j: u64, m: u64| j < 64 ==> #[trigger] ((m >> j) >> 1) == m >> add(j, 1)) by (bit_vector);
                        assert(forall|m: u64, j: u64| j >= 64 ==> #[trigger] ((m >> j) & 1) != 1) by (bit_vector);
                    }
                    count += 1;
                    mask = mask >> 1usize;

                    if (mask & 1) != 1 {
                        assert(mask & 1 == 0usize) by (bit_vector) requires mask & 1 != 1usize;
                        break;
                    }
                }

                if ((next_idx + count) % usize::BITS as usize) == 0 {
                    i += 1;
                    if i >= COMMIT_MASK_FIELD_COUNT as usize {
                        break;
                    }
                    mask = self.mask[i];
                    assert(forall|m: u64| m >> 0u64 == m) by (bit_vector);
                    ofs = 0;
                }

                if (mask & 1) != 1 {
                    break;
                }
            }

            assert forall |j: usize| next_idx <= j < next_idx + count implies self@.contains(j as int) by {
                self.lemma_view();
                assert(self@.contains(div64(j) * 64 + mod64(j)));
            };

            (next_idx, count)
        }
    }

    pub fn is_empty(&self) -> (b: bool)
    ensures b == (self@ == ISet::<int>::empty())
    {
        let mut i = 0;
        while i < 8
            invariant forall|j: int| #![auto] 0 <= j < i ==> self.mask[j] == 0
        {
            if self.mask[i] != 0 {
                proof {
                    lemma_is_bit_set();
                    self.lemma_view();
                    let j = lemma_obtain_bit_index_1(self.mask[i as int]);
                    assert(self@.contains(i * 64 + j));
                }
                return false;
            }
            i += 1;
        }
        proof {
            lemma_is_bit_set();
            self.lemma_view();
            assert(self@ =~= ISet::<int>::empty());
        }
        return true;
    }

    pub fn is_full(&self) -> (b: bool)
    ensures b == (self@ == ISet::new(|i: int| 0 <= i < COMMIT_MASK_BITS))
    {
        let mut i = 0;
        while i < 8
            invariant forall|j: int| #![auto] 0 <= j < i ==> self.mask[j] == !0usize
        {
            if self.mask[i] != (!0usize) {
                proof {
                    const_facts();
                    lemma_is_bit_set();
                    self.lemma_view();
                    let j = lemma_obtain_bit_index_2(self.mask[i as int]);
                    assert(!self@.contains(i * 64 + j));
                    assert(i * 64 + j < 512) by (nonlinear_arith) requires i < 8 && j < 64;
                }
                return false;
            }
            i = i + 1;
        }
        proof {
            lemma_is_bit_set();
            const_facts();
            self.lemma_view();
            assert forall |k: int| 0 <= k < COMMIT_MASK_BITS
                implies self@.contains(k)
            by {
                let t = k / 64;
                let u = (k % 64) as usize;
                assert(t * 64 + u == k);
                assert(is_bit_set(self.mask[t], u));
                assert(0 <= t < 8);
                assert(0 <= u < 64);
                assert(self@.contains(t * 64 + u));
            }
            assert(self@ =~= ISet::new(|i: int| 0 <= i < COMMIT_MASK_BITS));
        }
        return true;
    }
}

pub proof fn set_int_range_commit_size(sid: SegmentId, mask: CommitMask)
    requires mask@.contains(0)
    ensures ISet::int_range(segment_start(sid), segment_start(sid) + COMMIT_SIZE) <= mask.bytes(sid)
{
    mask.i_bytes_ensures(sid);
    reveal(CommitMask::bytes);
}


}
