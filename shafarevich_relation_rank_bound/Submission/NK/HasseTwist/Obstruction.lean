/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Sha² obstruction of a finite level, with `μ_p`-coefficients

This module makes the *kernel* of the localisation map explicit at the level of the finite levels,
for the cyclotomic twist `μ_p`.  It is the twisted counterpart of
`Submission/Work/HassePrinciple/Obstruction.lean`.

For a closed subgroup `U ≤ Gal(K'/K)` and a finite Galois level `L`, the **level obstruction**

`NK.HasseTwist.levelObstruction p U L ⊆ H²(U/(U ∩ Gal(K'/L)), μ_p(L))`

is the intersection of the kernels of the level-wise localisation maps `locLevel p U A L`, i.e. the
group of classes that vanish locally at *every* place of `K'` over a finite prime of `K`.  It is the
finitary shadow of the "Sha²" of the Hasse principle:

* `NK.HasseTwist.mem_levelObstruction_iff` — `a` lies in the obstruction exactly when the level
  class `a` is locally trivial (`levelLocTrivial`);
* `NK.HasseTwist.levelMap_mem_levelObstruction` — the obstruction is a *subsystem* of the
  filtered system: inflation maps the obstruction at level `L` into the obstruction at level `L'`;
* `NK.HasseTwist.loc_eq_zero_iff_exists` — the kernel of the localisation map on the colimit
  `H²(U, μ_p)` consists exactly of the classes represented at some finite level whose level class
  dies locally at every place in the *colimit* sense `levelLocVanishing`.

The Hasse principle `NK.BrauerTwist.Sha2Vanishing` is the statement that this kernel is trivial;
the classical computation of the obstruction (Hasse–Brauer–Noether with cyclotomic coefficients,
`Br(M)[p] ↪ ∏_v Br(M_v)[p]`) is what makes it vanish, see
`Submission/Work/HasseTwist/Inputs.lean`.
-/

import Submission.NK.HasseTwist.Defs
import Submission.NK.BrauerTwist.levelMap_locLevel_apply

open CategoryTheory
open scoped Pointwise

set_option autoImplicit false

universe u

namespace NK.HasseTwist

open NK.BrauerTwist

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **The obstruction of a finite level.**  The intersection of the kernels of the level-wise
localisation maps `locLevel p U A L`, `A` running over the places of `K'` over the finite primes
of `K`: the classes of the level `L` that are locally trivial. -/
noncomputable def levelObstruction (p : ℕ) (U : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') : Submodule CoeffInt (LevelH2 p U L) :=
  ⨅ (A : OverFinitePrime K K'), (locLevel p U A.1 L).hom.ker

/-- Membership in the level obstruction is local triviality at the level. -/
lemma mem_levelObstruction_iff (p : ℕ) (U : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') (a : LevelH2 p U L) :
    a ∈ levelObstruction p U L ↔ levelLocTrivial p U L a := by
  simp only [levelObstruction, Submodule.mem_iInf, LinearMap.mem_ker, levelLocTrivial]

/-- The zero class is locally trivial, i.e. lies in the obstruction. -/
lemma zero_mem_levelObstruction (p : ℕ) (U : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') : (0 : LevelH2 p U L) ∈ levelObstruction p U L := by
  rw [mem_levelObstruction_iff]
  exact levelLocTrivial_zero p L

/-- **The obstruction is a subsystem**: inflation maps the obstruction at a smaller level into the
obstruction at a larger level. -/
lemma levelMap_mem_levelObstruction (p : ℕ) {U : Subgroup Gal(K'/K)}
    {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L') {a : LevelH2 p U L}
    (ha : a ∈ levelObstruction p U L) :
    (levelMap p U h) a ∈ levelObstruction p U L' := by
  rw [mem_levelObstruction_iff] at ha ⊢
  intro A
  rw [levelMap_locLevel_apply (p := p) (U := U) (A := A.1) (h := h) a, ha A, map_zero]

/-- **Local triviality is stable under inflation.** -/
lemma levelLocTrivial_levelMap (p : ℕ) {U : Subgroup Gal(K'/K)}
    {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L') {a : LevelH2 p U L}
    (ha : levelLocTrivial p U L a) :
    levelLocTrivial p U L' ((levelMap p U h) a) := by
  intro A
  rw [levelMap_locLevel_apply (p := p) (U := U) (A := A.1) (h := h) a, ha A, map_zero]

/-- **The kernel of the localisation map, described at the finite levels.**  A class of
`H²(U, μ_p)` has vanishing localisation at every place of `K'` over a finite prime of `K` if and
only if it is represented at some finite level by a class that dies locally at every place after
inflation to a (place-dependent) larger level. -/
theorem loc_eq_zero_iff_exists (p : ℕ) (U : Subgroup Gal(K'/K))
    (x : H2Twist p U) :
    (∀ A : OverFinitePrime K K', H2Twist.loc p U x A = 0) ↔
      ∃ (L : FiniteGaloisIntermediateField K K') (a : LevelH2 p U L),
        x = H2Twist.ofLevel p U L a ∧ levelLocVanishing p U L a := by
  constructor
  · intro hx
    obtain ⟨L, a, rfl⟩ := H2Twist.ofLevel_surjective (p := p) (U := U) x
    exact ⟨L, a, rfl, (levelLocVanishing_iff (p := p) (U := U) L a).mpr hx⟩
  · rintro ⟨L, a, rfl, ha⟩
    exact (levelLocVanishing_iff (p := p) (U := U) L a).mp ha

end NK.HasseTwist
