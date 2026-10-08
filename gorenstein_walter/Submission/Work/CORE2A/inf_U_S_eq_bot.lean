/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CORE2A area (fundmath3-gorenstein_walter)
-/
import Mathlib
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE2A.Basic

/-!
# `U ⊓ S = 1` for Bender's notation on p. 219

`U = O(H) = oddCoreIn B.H` is the largest normal subgroup of `H = C_G(t)` of odd order, and
`S` is the Sylow `2`-subgroup of `G`.  An element of `U ⊓ S` has order dividing both an odd
number (`|U|`, `Work.CORE2A.bSetup_U_odd`) and a power of two (`|S|`, since `S` is a `2`-group),
so it is trivial.

The mathematical content is isolated in the general lemma
`Work.CORE2A.inf_eq_bot_of_odd_of_isPGroup_two`: an odd-order subgroup and a `2`-subgroup have
trivial intersection.  This is Bender's `U ∩ S = 1`, used throughout §2.
-/

namespace Work.CORE2A

open Subgroup

/-- A subgroup of odd order and a `2`-subgroup have trivial intersection: an element of the
intersection has order dividing an odd number and a power of two. -/
theorem inf_eq_bot_of_odd_of_isPGroup_two {G : Type} [Group G] {U S : Subgroup G}
    (hU : Odd (Nat.card U)) (hS : IsPGroup 2 S) : U ⊓ S = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hxU, hxS⟩ := hx
  -- `orderOf x` divides the odd number `|U|`, hence is odd.
  have hoddx : Odd (orderOf x) :=
    Odd.of_dvd_nat hU (Subgroup.orderOf_dvd_natCard U hxU)
  -- `S` is a `2`-group, so `x ^ 2 ^ k = 1` for some `k`, i.e. `orderOf x ∣ 2 ^ k`.
  obtain ⟨k, hk⟩ := hS ⟨x, hxS⟩
  have hdvd2 : orderOf x ∣ 2 ^ k := by
    apply orderOf_dvd_iff_pow_eq_one.mpr
    have := congrArg Subtype.val hk
    simpa using this
  -- An odd number dividing `2 ^ k` is `1`.
  exact orderOf_eq_one_iff.mp (((hoddx.coprime_two_right).pow_right k).eq_one_of_dvd hdvd2)

/-- **Bender p. 219**: `U ∩ S = 1`.  `U = O(H)` has odd order (`bSetup_U_odd`) and `S` is a
Sylow `2`-subgroup, hence a `2`-group. -/
theorem inf_U_S_eq_bot {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G) :
    B.U ⊓ (B.S : Subgroup G) = ⊥ :=
  inf_eq_bot_of_odd_of_isPGroup_two (bSetup_U_odd B) B.S.isPGroup'

end Work.CORE2A
