//! Provides sequentially-consistent atomic memory locations with associated ghost state.
//! See the [`atomic_with_ghost!`] documentation for more information.

#![allow(unused_imports)]

use builtin::*;
use builtin_macros::*;
use state_machines_macros::*;
use vstd::invariant::*;
use vstd::atomic::*;
use vstd::modes::*;
use vstd::prelude::*;

macro_rules! declare_atomic_type {
    ($at_ident:ident, $patomic_ty:ident, $perm_ty:ty, $value_ty: ty, $atomic_pred_ty: ident) => {
        verus!{

        pub struct $atomic_pred_ty<Pred> { p: Pred }

        impl<K, G, Pred> InvariantPredicate<(K, Cancellable::Instance, int), (Option<($perm_ty, G)>, Cancellable::a)> for $atomic_pred_ty<Pred>
            where Pred: vstd::atomic_ghost::AtomicInvariantPredicate<K, $value_ty, G>
        {
            open spec fn inv(k_loc: (K, Cancellable::Instance, int), perm_g: (Option<($perm_ty, G)>, Cancellable::a)) -> bool {
                let (k, instance, loc) = k_loc;
                let (opt, canc_a) = perm_g;

                equal(canc_a.view().instance, instance)
                && (match opt {
                    Some((perm, g)) =>
                        perm.view().patomic == loc
                          && Pred::atomic_inv(k, perm.view().value, g),
                    None =>
                        canc_a.view().value == true,
                })
            }
        }

        #[doc = concat!(
            "Sequentially-consistent atomic memory location storing a `",
            stringify!($value_ty),
            "` and associated ghost state."
        )]
        ///
        /// See the [`atomic_with_ghost!`] documentation for usage information.

        pub struct $at_ident<K, G, Pred>
            //where Pred: vstd::atomic_ghost::AtomicInvariantPredicate<K, $value_ty, G>
        {
            #[doc(hidden)]
            pub patomic: $patomic_ty,

            #[doc(hidden)]
            pub atomic_inv: Tracked<Duplicable<AtomicInvariant<
                (K, Cancellable::Instance, int),
                (Option<($perm_ty, G)>, Cancellable::a),
                $atomic_pred_ty<Pred>
              >>>,

            #[doc(hidden)]
            pub cancellable_instance: Tracked<Cancellable::Instance>,

            #[doc(hidden)]
            pub not_cancelled_token: Tracked<Cancellable::b>,
        }

        impl<K, G, Pred> $at_ident<K, G, Pred>
            where Pred: vstd::atomic_ghost::AtomicInvariantPredicate<K, $value_ty, G>
        {
            pub open spec fn well_formed(&self) -> bool {
                equal(self.atomic_inv@@.constant().1, self.cancellable_instance@)
                 && self.atomic_inv@@.constant().2 == self.patomic.id()
                 && equal(self.not_cancelled_token@@.instance, self.cancellable_instance@)
                 && self.not_cancelled_token@@.value == false
            }

            pub open spec fn constant(&self) -> K {
                self.atomic_inv@@.constant().0
            }

            #[inline(always)]
            pub fn new(Ghost(k): Ghost<K>, u: $value_ty, Tracked(g): Tracked<G>) -> (t: Self)
                requires Pred::atomic_inv(k, u, g),
                ensures t.well_formed() && equal(t.constant(), k),
            {
                let (patomic, Tracked(perm)) = $patomic_ty::new(u);

                let tracked (Tracked(inst), Tracked(tok_a), Tracked(tok_b)) = Cancellable::Instance::initialize();
                let tracked pair = (Some((perm, g)), tok_a);
                let tracked atomic_inv = AtomicInvariant::new(
                    (k, inst, patomic.id()),
                    pair,
                    0);

                $at_ident {
                    patomic,
                    atomic_inv: Tracked(Duplicable::new(atomic_inv)),
                    cancellable_instance: Tracked(inst),
                    not_cancelled_token: Tracked(tok_b),
                }
            }

            pub fn load(&self) -> $value_ty
                requires self.well_formed(),
            {
                my_atomic_with_ghost!(self => load(); g => { })
            }

            pub fn into_inner(self) -> (res: ($value_ty, Tracked<G>))
                requires self.well_formed(),
                ensures
                    Pred::atomic_inv(self.constant(), res.0, res.1@),
            {
                let $at_ident { patomic, atomic_inv: Tracked(atomic_inv), cancellable_instance: Tracked(cancellable_instance), not_cancelled_token: Tracked(not_cancelled_token) } = self;
                let tracked atomic_inv = atomic_inv.borrow();
                let tracked perm;
                let tracked g;
                open_atomic_invariant!(atomic_inv => pair => {
                    let tracked (opt_stuff, mut cancel_token) = pair;
                    proof {
                        cancellable_instance.agree(
                            &cancel_token, &not_cancelled_token);
                        cancellable_instance.cancel(
                            &mut cancel_token, &mut not_cancelled_token);
                    }
                    let tracked (_perm, _g) = opt_stuff.tracked_unwrap();
                    proof { perm = _perm; g = _g; }
                    proof { pair = (None, cancel_token); }
                });
                let v = patomic.into_inner(Tracked(perm));
                (v, Tracked(g))
            }
        }

        }
    }
}

tokenized_state_machine!(Cancellable {
    fields {
        #[sharding(variable)]
        pub a: bool,

        #[sharding(variable)]
        pub b: bool,
    }

    init!{
        initialize() {
            init a = false;
            init b = false;
        }
    }

    #[invariant]
    pub fn inv_agreement(&self) -> bool {
        self.a == self.b
    }

    property!{
        agree() {
            assert(pre.a == pre.b);
        }
    }

    transition!{
        cancel() {
            update a = true;
            update b = true;
        }
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self) { }
   
    #[inductive(cancel)]
    fn cancel_inductive(pre: Self, post: Self) { }
});


tokenized_state_machine!(Dupe<T> {
    fields {
        #[sharding(storage_option)]
        pub storage: Option<T>,

        #[sharding(constant)]
        pub val: T,
    }

    init!{
        initialize_one(t: T) {
            // Initialize with a single reader
            init storage = Option::Some(t);
            init val = t;
        }
    }

    #[invariant]
    pub fn agreement(&self) -> bool {
        self.storage === Option::Some(self.val)
    }

    property!{
        borrow() {
            guard storage >= Some(pre.val);
        }
    }

     #[inductive(initialize_one)]
     fn initialize_one_inductive(post: Self, t: T) { }
});

verus!{

pub tracked struct Duplicable<T> {
    pub tracked inst: Dupe::Instance<T>,
}

impl<T> Duplicable<T> {
    pub open spec fn wf(self) -> bool {
        true
    }

    pub open spec fn view(self) -> T {
        self.inst.val()
    }

    pub proof fn new(tracked t: T) -> (tracked s: Self)
        ensures s.wf() && s@ === t,
    {
        let tracked inst = Dupe::Instance::initialize_one(/* spec */ t, Option::Some(t));
        Duplicable {
            inst,
        }
    }

    pub proof fn clone(tracked &self) -> (tracked other: Self)
        requires self.wf(),
        ensures other.wf() && self@ === other@,
    {
        Duplicable { inst: self.inst.clone() }
    }

    pub proof fn borrow(tracked &self) -> (tracked t: &T)
        requires self.wf(),
        ensures *t === self@,
    {
        self.inst.borrow()
    }
}

}

declare_atomic_type!(AtomicU64, PAtomicU64, PermissionU64, u64, AtomicPredU64);
/*
declare_atomic_type!(AtomicU32, PAtomicU32, PermissionU32, u32, AtomicPredU32);
declare_atomic_type!(AtomicU16, PAtomicU16, PermissionU16, u16, AtomicPredU16);
declare_atomic_type!(AtomicU8, PAtomicU8, PermissionU8, u8, AtomicPredU8);

declare_atomic_type!(AtomicI64, PAtomicI64, PermissionI64, i64, AtomicPredI64);
declare_atomic_type!(AtomicI32, PAtomicI32, PermissionI32, i32, AtomicPredI32);
declare_atomic_type!(AtomicI16, PAtomicI16, PermissionI16, i16, AtomicPredI16);
declare_atomic_type!(AtomicI8, PAtomicI8, PermissionI8, i8, AtomicPredI8);

declare_atomic_type!(AtomicBool, PAtomicBool, PermissionBool, bool, AtomicPredBool);
*/

declare_atomic_type!(AtomicUsize, PAtomicUsize, PermissionUsize, usize, AtomicPredUsize);


#[macro_export]
macro_rules! my_atomic_with_ghost {
    ($($tokens:tt)*) => {
        // The helper is used to parse things using Verus syntax
        // The helper then calls atomic_with_ghost_inner, below:
        ::builtin_macros::atomic_with_ghost_helper!(
            $crate::atomic_ghost_modified::my_atomic_with_ghost_inner,
            $($tokens)*)
    }
}

pub use my_atomic_with_ghost;
pub use my_atomic_with_ghost as atomic_with_ghost;

#[doc(hidden)]
#[macro_export]
macro_rules! my_atomic_with_ghost_inner {
    (load, $e:expr, (), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
        crate::atomic_ghost_modified::my_atomic_with_ghost_load!($e, $prev, $next, $ret, $g, $b)
    };
    (store, $e:expr, ($operand:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
        crate::atomic_ghost_modified::my_atomic_with_ghost_store!($e, $operand, $prev, $next, $ret, $g, $b)
    };
    (swap, $e:expr, ($operand:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
        crate::atomic_ghost_modified::my_atomic_with_ghost_update_with_1_operand!(
            swap, $e, $operand, $prev, $next, $ret, $g, $b)
    };

    (fetch_or, $e:expr, ($operand:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
        crate::atomic_ghost_modified::my_atomic_with_ghost_update_with_1_operand!(
            fetch_or, $e, $operand, $prev, $next, $ret, $g, $b)
    };
    (fetch_and, $e:expr, ($operand:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
        crate::atomic_ghost_modified::my_atomic_with_ghost_update_with_1_operand!(
            fetch_and, $e, $operand, $prev, $next, $ret, $g, $b)
    };
    (fetch_xor, $e:expr, ($operand:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
        crate::atomic_ghost_modified::my_atomic_with_ghost_update_with_1_operand!(
            fetch_xor, $e, $operand, $prev, $next, $ret, $g, $b)
    };
    (fetch_nand, $e:expr, ($operand:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
        crate::atomic_ghost_modified::my_atomic_with_ghost_update_with_1_operand!(
            fetch_nand, $e, $operand, $prev, $next, $ret, $g, $b)
    };
    (fetch_max, $e:expr, ($operand:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
        crate::atomic_ghost_modified::my_atomic_with_ghost_update_with_1_operand!(
            fetch_max, $e, $operand, $prev, $next, $ret, $g, $b)
    };
    (fetch_min, $e:expr, ($operand:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
        crate::atomic_ghost_modified::my_atomic_with_ghost_update_with_1_operand!(
            fetch_min, $e, $operand, $prev, $next, $ret, $g, $b)
    };
    (fetch_add_wrapping, $e:expr, ($operand:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
        crate::atomic_ghost_modified::my_atomic_with_ghost_update_with_1_operand!(
            fetch_add_wrapping, $e, $operand, $prev, $next, $ret, $g, $b)
    };
    (fetch_sub_wrapping, $e:expr, ($operand:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
        crate::atomic_ghost_modified::my_atomic_with_ghost_update_with_1_operand!(
            fetch_sub_wrapping, $e, $operand, $prev, $next, $ret, $g, $b)
    };

    (fetch_add, $e:expr, ($operand:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
        crate::atomic_ghost_modified::my_atomic_with_ghost_update_fetch_add!(
            $e, $operand, $prev, $next, $ret, $g, $b)
    };
    (fetch_sub, $e:expr, ($operand:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
        crate::atomic_ghost_modified::my_atomic_with_ghost_update_fetch_sub!(
            $e, $operand, $prev, $next, $ret, $g, $b)
    };

    (compare_exchange, $e:expr, ($operand1:expr, $operand2:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
        crate::atomic_ghost_modified::my_atomic_with_ghost_update_with_2_operand!(
            compare_exchange, $e, $operand1, $operand2, $prev, $next, $ret, $g, $b)
    };
    (compare_exchange_weak, $e:expr, ($operand1:expr, $operand2:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
        crate::atomic_ghost_modified::my_atomic_with_ghost_update_with_2_operand!(
            compare_exchange_weak, $e, $operand1, $operand2, $prev, $next, $ret, $g, $b)
    };
    (no_op, $e:expr, (), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
        crate::atomic_ghost_modified::my_atomic_with_ghost_no_op!($e, $prev, $next, $ret, $g, $b)
    };
}

pub use my_atomic_with_ghost_inner;

#[doc(hidden)]
#[macro_export]
macro_rules! my_atomic_with_ghost_store {
    ($e:expr, $operand:expr, $prev:pat, $next:pat, $res:pat, $g:ident, $b:block) => {
        ::builtin_macros::verus_exec_expr!{ {
            let atomic = &($e);
            ::vstd::open_atomic_invariant!(&atomic.atomic_inv => pair => {
                #[allow(unused_mut)]
                let tracked (mut permtmp, mut $g) = pair;
                let ghost $prev = permtmp.view().value;
                atomic.patomic.store(Tracked(&mut permtmp), $operand);
                let ghost $next = permtmp.view().value;
                let ghost $res = ();

                proof { $b }

                proof { pair = (permtmp, $g); }
            });
        } }
    }
}
pub use my_atomic_with_ghost_store;

#[doc(hidden)]
#[macro_export]
macro_rules! my_atomic_with_ghost_load {
    ($e:expr, $prev:pat, $next: pat, $res: pat, $g:ident, $b:block) => {
        ::builtin_macros::verus_exec_expr!{ {
            let result;
            let atomic = &($e);
            let tracked atomic_inv = atomic.atomic_inv.borrow().borrow();
            ::vstd::open_atomic_invariant!(atomic_inv => pair => {
                let tracked (opt_stuff, cancel_token) = pair;
                proof { atomic.cancellable_instance.borrow().agree(
                    &cancel_token, atomic.not_cancelled_token.borrow()); }
                #[allow(unused_mut)]
                let tracked (permtmp, mut $g) = opt_stuff.tracked_unwrap();
                result = atomic.patomic.load(Tracked(&permtmp));
                let ghost $res = result;
                let ghost $prev = result;
                let ghost $next = result;

                proof { $b }

                proof { pair = (Some((permtmp, $g)), cancel_token); }
            });
            result
        } }
    }
}

pub use my_atomic_with_ghost_load;

#[doc(hidden)]
#[macro_export]
macro_rules! my_atomic_with_ghost_no_op {
    ($e:expr, $prev:pat, $next: pat, $res: pat, $g:ident, $b:block) => {
        ::builtin_macros::verus_exec_expr!{ {
            let atomic = &($e);
            let tracked atomic_inv = atomic.atomic_inv.borrow().borrow();
            ::vstd::open_atomic_invariant!(atomic_inv => pair => {
                let tracked (opt_stuff, cancel_token) = pair;
                proof { atomic.cancellable_instance.borrow().agree(
                    &cancel_token, atomic.not_cancelled_token.borrow()); }
                #[allow(unused_mut)]
                let tracked (permtmp, mut $g) = opt_stuff.tracked_unwrap();

                let ghost result = permtmp.view().value;
                let ghost $res = result;
                let ghost $prev = result;
                let ghost $next = result;

                proof { $b }

                proof { pair = (Some((permtmp, $g)), cancel_token); }
            });
        } }
    }
}

pub use my_atomic_with_ghost_no_op;

#[doc(hidden)]
#[macro_export]
macro_rules! my_atomic_with_ghost_update_with_1_operand {
    ($name:ident, $e:expr, $operand:expr, $prev:pat, $next:pat, $res: pat, $g:ident, $b:block) => {
        ::builtin_macros::verus_exec_expr!{ {
            let result;
            let atomic = &($e);
            let operand = $operand;
            let tracked atomic_inv = atomic.atomic_inv.borrow().clone();
            let tracked atomic_inv = atomic_inv.borrow();
            ::vstd::open_atomic_invariant!(atomic_inv => pair => {
                let tracked (opt_stuff, cancel_token) = pair;
                proof { atomic.cancellable_instance.borrow().agree(
                    &cancel_token, atomic.not_cancelled_token.borrow()); }
                #[allow(unused_mut)]
                let tracked (mut permtmp, mut $g) = opt_stuff.tracked_unwrap();

                let ghost $prev = permtmp.view().value;
                result = atomic.patomic.$name(Tracked(&mut permtmp), operand);
                let ghost $res = result;
                let ghost $next = permtmp.view().value;

                proof { $b }

                proof { pair = (Some((permtmp, $g)), cancel_token); }
            });
            result
        } }
    }
}

pub use my_atomic_with_ghost_update_with_1_operand;

#[doc(hidden)]
#[macro_export]
macro_rules! my_atomic_with_ghost_update_with_2_operand {
    ($name:ident, $e:expr, $operand1:expr, $operand2:expr, $prev:pat, $next:pat, $res: pat, $g:ident, $b:block) => {
        ::builtin_macros::verus_exec_expr!{ {
            let result;
            let atomic = &($e);
            let operand1 = $operand1;
            let operand2 = $operand2;
            let tracked atomic_inv = atomic.atomic_inv.borrow().clone();
            let tracked atomic_inv = atomic_inv.borrow();
            ::vstd::open_atomic_invariant!(atomic_inv => pair => {
                let tracked (opt_stuff, cancel_token) = pair;
                proof { atomic.cancellable_instance.borrow().agree(
                    &cancel_token, atomic.not_cancelled_token.borrow()); }
                #[allow(unused_mut)]
                let tracked (mut permtmp, mut $g) = opt_stuff.tracked_unwrap();

                let ghost $prev = permtmp.view().value;
                result = atomic.patomic.$name(Tracked(&mut permtmp), operand1, operand2);
                let ghost $res = result;
                let ghost $next = permtmp.view().value;

                proof { $b }

                proof { pair = (Some((permtmp, $g)), cancel_token); }
            });
            result
        } }
    }
}

pub use my_atomic_with_ghost_update_with_2_operand;

#[doc(hidden)]
#[macro_export]
macro_rules! my_atomic_with_ghost_update_fetch_add {
    ($e:expr, $operand:expr, $prev:pat, $next:pat, $res: pat, $g:ident, $b:block) => {
        (::builtin_macros::verus_exec_expr!( {
            let result;
            let atomic = &($e);
            let operand = $operand;
            ::vstd::open_atomic_invariant!(&atomic.atomic_inv => pair => {
                #[allow(unused_mut)]
                let tracked (mut permtmp, mut $g) = pair;

                proof {
                    let ghost $prev = permtmp.view().value as int;
                    let ghost $res = permtmp.view().value as int;
                    let ghost $next = permtmp.view().value as int + (operand as int);

                    { $b }
                }

                result = atomic.patomic.fetch_add(Tracked(&mut permtmp), operand);

                proof { pair = (permtmp, $g); }
            });
            result
        } ))
    }
}

pub use my_atomic_with_ghost_update_fetch_add;

#[doc(hidden)]
#[macro_export]
macro_rules! my_atomic_with_ghost_update_fetch_sub {
    ($e:expr, $operand:expr, $prev:pat, $next:pat, $res: pat, $g:ident, $b:block) => {
        ::builtin_macros::verus_exec_expr!{ {
            let result;
            let atomic = &($e);
            let operand = $operand;
            ::vstd::open_atomic_invariant!(&atomic.atomic_inv => pair => {
                #[allow(unused_mut)]
                let tracked (mut permtmp, mut $g) = pair;

                proof {
                    let ghost $prev = permtmp.view().value as int;
                    let ghost $res = permtmp.view().value as int;
                    let ghost $next = permtmp.view().value as int - (operand as int);

                    { $b }
                }

                result = atomic.patomic.fetch_sub(Tracked(&mut permtmp), operand);

                proof { pair = (permtmp, $g); }
            });
            result
        } }
    }
}

pub use my_atomic_with_ghost_update_fetch_sub;
