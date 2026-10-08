/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GLUE area (fundmath3-gorenstein_walter)
-/
import Mathlib
import Submission.Work.GLUE.Defs

/-!
# `O(G) = O_{2'}(G)`: the glue between our notation and the odd-order library

We prove that our `Work.GW2.oddCore` — the largest normal subgroup of odd order — is the
library's `O_π(G)` for `π = {q | q ≠ 2}` (`OddOrder.Isaacs.Ch03.oPiCore`).

Both sides are defined as a supremum, closed under `normalCore`:

* `Work.GW2.oddCore G = (sSup {N | N.Normal ∧ Odd (Nat.card N)}).normalCore`
* `OddOrder.Isaacs.Ch03.oPiCore π G = ⨆ H : {H // H.Normal ∧ H.IsPiSubgroup π}, H`

So the proof is in three steps.

1. For a subgroup `N` of a *finite* group, `N` has odd order iff all prime divisors of
   `Nat.card N` are different from `2`.  Finiteness is used here: an infinite subgroup has
   `Nat.card = 0`, whose `primeFactors` is empty, so the `IsPiSubgroup` condition would hold
   vacuously while `Odd 0` fails.
2. `sSup {N | N.Normal ∧ N.IsPiSubgroup π} = OddOrder.Isaacs.Ch03.oPiCore π G`
   (pure lattice bookkeeping: `sSup` of a set of subgroups is the `iSup` over its subtype).
3. `normalCore` of that supremum is itself, since `oPiCore π G` is normal.
-/

namespace Work.GLUE

/-- A subgroup of a finite group has odd order exactly when all prime divisors of its
cardinality are `≠ 2`. -/
theorem odd_iff_isPiSubgroup_ne_two {G : Type*} [Group G] [Finite G] (N : Subgroup G) :
    Odd (Nat.card N) ↔ Subgroup.IsPiSubgroup ({q : ℕ | q ≠ 2}) N := by
  unfold Subgroup.IsPiSubgroup
  have hne : Nat.card ↥N ≠ 0 := (Nat.card_pos (α := ↥N)).ne'
  constructor
  · intro hodd q hq hq2
    rw [hq2] at hq
    exact (Nat.not_even_iff_odd.mpr hodd)
      (even_iff_two_dvd.mpr (Nat.mem_primeFactors.mp hq).2.1)
  · intro h
    rw [← Nat.not_even_iff_odd]
    intro heven
    exact h 2 (Nat.mem_primeFactors.mpr
      ⟨by norm_num, even_iff_two_dvd.mp heven, hne⟩) rfl

/-- The supremum of the normal `π`-subgroups is the library's `O_π(G)`. -/
theorem sSup_normal_isPiSubgroup_eq_oPiCore {G : Type*} [Group G] (π : Set ℕ) :
    sSup {N : Subgroup G | N.Normal ∧ Subgroup.IsPiSubgroup π N}
      = OddOrder.Isaacs.Ch03.oPiCore π G := by
  rw [OddOrder.Isaacs.Ch03.oPiCore]
  refine le_antisymm (sSup_le ?_) (iSup_le ?_)
  · rintro N ⟨hN, hpN⟩
    exact le_iSup_of_le ⟨N, hN, hpN⟩ le_rfl
  · rintro ⟨N, hN1, hN2⟩
    exact le_sSup ⟨hN1, hN2⟩

/-- `O_π(G)` is a normal subgroup, so taking `normalCore` of it changes nothing. -/
theorem normalCore_oPiCore {G : Type*} [Group G] (π : Set ℕ) :
    (OddOrder.Isaacs.Ch03.oPiCore π G).normalCore = OddOrder.Isaacs.Ch03.oPiCore π G :=
  Subgroup.normalCore_eq_self _

theorem oddCore_eq_oPiCore {G : Type*} [Group G] [Finite G] :
    Work.GW2.oddCore G = OddOrder.Isaacs.Ch03.oPiCore {q : ℕ | q ≠ 2} G := by
  have hset : {N : Subgroup G | N.Normal ∧ Odd (Nat.card N)}
      = {N : Subgroup G | N.Normal ∧ Subgroup.IsPiSubgroup ({q : ℕ | q ≠ 2}) N} := by
    ext N
    exact and_congr_right fun _ => odd_iff_isPiSubgroup_ne_two N
  rw [Work.GW2.oddCore, hset, sSup_normal_isPiSubgroup_eq_oPiCore,
    normalCore_oPiCore]

end Work.GLUE
