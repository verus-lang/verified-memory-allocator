use vstd::prelude::*;

verus!{

pub open spec fn is_trailing_zeros(n: usize, tz: u32) -> bool {
    0 <= tz <= usize::BITS
    && if tz == usize::BITS {
        n == 0
    } else {
        (n >> (tz as usize)) << (tz as usize) == n
        &&
        ((n >> (tz as usize)) & 1) != 0
    }
}

#[verifier(external_body)]
#[inline(always)]
pub fn trailing_zeros(n: usize) -> (lz: u32)
    ensures is_trailing_zeros(n, lz)
{
    n.trailing_zeros()
}

pub open spec fn is_leading_zeros(n: usize, lz: u32) -> bool {
    0 <= lz <= usize::BITS
    && {
        let shift = (usize::BITS - lz as usize) as usize;
        (n >> shift) == 0
          && (shift != 0 ==> (n >> sub(shift, 1)) != 0)
    }
}

#[verifier(external_body)]
#[inline(always)]
pub fn leading_zeros(n: usize) -> (lz: u32)
    ensures is_leading_zeros(n, lz)
{
    n.leading_zeros()
}

}
