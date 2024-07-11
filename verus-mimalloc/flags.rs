#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::modes::*;
use vstd::*;
use vstd::cell::*;

use crate::types::*;

verus!{

pub closed spec fn flags0_is_reset(u: u8) -> bool { u & 1 != 0 }
pub closed spec fn flags0_is_committed(u: u8) -> bool { u & 2 != 0 }
pub closed spec fn flags0_is_zero_init(u: u8) -> bool { u & 4 != 0 }

pub closed spec fn flags1_in_full(u: u8) -> bool { u & 1 != 0 }
pub closed spec fn flags1_has_aligned(u: u8) -> bool { u & 2 != 0 }

pub closed spec fn flags2_is_zero(u: u8) -> bool { u & 1 != 0 }
pub closed spec fn flags2_retire_expire(u: u8) -> int { (u >> 1u8) as int }

impl PageInner {
    pub open spec fn is_reset(&self) -> bool { flags0_is_reset(self.flags0) }
    pub open spec fn is_committed(&self) -> bool { flags0_is_committed(self.flags0) }
    pub open spec fn is_zero_init(&self) -> bool { flags0_is_zero_init(self.flags0) }

    pub open spec fn in_full(&self) -> bool { flags1_in_full(self.flags1) }
    pub open spec fn has_aligned(&self) -> bool { flags1_has_aligned(self.flags1) }

    pub open spec fn is_zero(&self) -> bool { flags2_is_zero(self.flags2) }
    pub open spec fn retire_expire(&self) -> int { flags2_retire_expire(self.flags2) }

    // getters

    #[inline(always)]
    pub fn get_is_reset(&self) -> (b: bool)
        ensures b == self.is_reset()
    {
        (self.flags0 & 1) != 0
    }

    #[inline(always)]
    pub fn get_is_committed(&self) -> (b: bool)
        ensures b == self.is_committed()
    {
        (self.flags0 & 2) != 0
    }

    #[inline(always)]
    pub fn get_is_zero_init(&self) -> (b: bool)
        ensures b == self.is_zero_init()
    {
        (self.flags0 & 4) != 0
    }

    #[inline(always)]
    pub fn get_in_full(&self) -> (b: bool)
        ensures b == self.in_full()
    {
        (self.flags1 & 1) != 0
    }

    #[inline(always)]
    pub fn get_has_aligned(&self) -> (b: bool)
        ensures b == self.has_aligned()
    {
        (self.flags1 & 2) != 0
    }

    #[inline(always)]
    pub fn get_is_zero(&self) -> (b: bool)
        ensures b == self.is_zero()
    {
        (self.flags2 & 1) != 0
    }

    #[inline(always)]
    pub fn get_retire_expire(&self) -> (u: u8)
        ensures u == self.retire_expire(),
            u <= 127,
    {
        let x = self.flags2 >> 1u8;
        proof {
            assert(x == (self.flags2 >> 1u8));
            let y = self.flags2;
            assert((y >> 1u8) <= 127) by(bit_vector);
        }
        x
    }

    #[inline(always)]
    pub fn not_full_nor_aligned(&self) -> (b: bool)
        ensures b ==> (!self.in_full() && !self.has_aligned())
    {
        proof {
            let x = self.flags1;
            assert(x == 0 ==> (x & 1u8 == 0u8) && (x & 2u8 == 0u8)) by(bit_vector);
        }
        self.flags1 == 0
    }

    // setters

    #[inline(always)]
    pub fn set_retire_expire(&mut self, u: u8)
        requires u <= 127,
        ensures 
            *self == (PageInner { flags2: self.flags2, .. *old(self) }),
            self.is_zero() == old(self).is_zero(),
            self.retire_expire() == u,
    {
        proof {
            let x = self.flags2;
            assert(((x & 1) | (u << 1)) & 1 == (x & 1)) by(bit_vector);
            assert(((x & 1) | (u << 1)) >> 1 == u) by(bit_vector)
                requires u <= 127;

        }
        self.flags2 = (self.flags2 & 1) | (u << 1u8);
    }

    #[inline(always)]
    pub fn set_is_reset(&mut self, b: bool)
        ensures *self == (PageInner { flags0: self.flags0, .. *old(self) }),
            self.is_reset() == b,
            self.is_committed() == old(self).is_committed(),
            self.is_zero_init() == old(self).is_zero_init(),
    {
        proof {
            let y = (if b { 1 } else { 0 });
            let x = self.flags0;
            assert(y == 1 || y == 0 ==> ((x & !1) | y) & 2 == x & 2) by(bit_vector);
            assert(y == 1 || y == 0 ==> ((x & !1) | y) & 4 == x & 4) by(bit_vector);
            assert(y == 1 || y == 0 ==> ((x & !1) | y) & 1 == y) by(bit_vector);
        }
        self.flags0 = (self.flags0 & !1) | (if b { 1 } else { 0 })
    }

    #[inline(always)]
    pub fn set_is_committed(&mut self, b: bool)
        ensures *self == (PageInner { flags0: self.flags0, .. *old(self) }),
            self.is_reset() == old(self).is_reset(),
            self.is_committed() == b,
            self.is_zero_init() == old(self).is_zero_init(),
    {
        proof {
            let y: u8 = (if b { 1 } else { 0 });
            let x = self.flags0;
            assert(y == 1 || y == 0 ==> ((x & !2) | (y << 1)) & 1 == x & 1) by(bit_vector);
            assert(y == 1 || y == 0 ==> ((x & !2) | (y << 1)) & 4 == x & 4) by(bit_vector);
            assert(y == 1 || y == 0 ==> (((x & !2) | (y << 1)) & 2 == 0 <==> y == 0)) by(bit_vector);
        }
        self.flags0 = (self.flags0 & !2) | ((if b { 1 } else { 0 }) << 1u8)

    }

    #[inline(always)]
    pub fn set_is_zero_init(&mut self, b: bool)
        ensures *self == (PageInner { flags0: self.flags0, .. *old(self) }),
            self.is_reset() == old(self).is_reset(),
            self.is_committed() == old(self).is_committed(),
            self.is_zero_init() == b,
    {
        proof {
            let y: u8 = (if b { 1 } else { 0 });
            let x = self.flags0;
            assert(y == 1 || y == 0 ==> ((x & !4) | (y << 2)) & 1 == x & 1) by(bit_vector);
            assert(y == 1 || y == 0 ==> ((x & !4) | (y << 2)) & 2 == x & 2) by(bit_vector);
            assert(y == 1 || y == 0 ==> (((x & !4) | (y << 2)) & 4 == 0 <==> y == 0)) by(bit_vector);
        }
        self.flags0 = (self.flags0 & !4) | ((if b { 1 } else { 0 }) << 2u8)

    }

    #[inline(always)]
    pub fn set_in_full(&mut self, b: bool)
        ensures *self == (PageInner { flags1: self.flags1, .. *old(self) }),
            self.has_aligned() == old(self).has_aligned(),
            self.in_full() == b,
    {
        proof {
            let y = (if b { 1 } else { 0 });
            let x = self.flags1;
            assert(y == 1 || y == 0 ==> ((x & !1) | y) & 2 == x & 2) by(bit_vector);
            assert(y == 1 || y == 0 ==> ((x & !1) | y) & 1 == y) by(bit_vector);
        }
        self.flags1 = (self.flags1 & !1) | (if b { 1 } else { 0 })
    }

    #[inline(always)]
    pub fn set_has_aligned(&mut self, b: bool)
        ensures *self == (PageInner { flags1: self.flags1, .. *old(self) }),
            self.has_aligned() == b,
            self.in_full() == old(self).in_full(),
    {
        proof {
            let y: u8 = (if b { 1 } else { 0 });
            let x = self.flags1;
            assert(y == 1 || y == 0 ==> ((x & !2) | (y << 1)) & 1 == x & 1) by(bit_vector);
            assert(y == 1 || y == 0 ==> (((x & !2) | (y << 1)) & 2 == 0 <==> y == 0)) by(bit_vector);
        }
        self.flags1 = (self.flags1 & !2) | ((if b { 1 } else { 0 }) << 1u8);
    }

}

}
