/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Monotonicity of `levelLocVanishing` in the level, for `μ_p`-coefficients

This is the twisted (`μ_p`-coefficient) counterpart of
`Submission/Work/HassePrinciple/levelLocVanishing_mono.lean`.

`NK.HasseTwist.levelLocVanishing p U L a` says that the level class `a` dies, locally at every
place, after inflation to some larger (place-dependent) finite Galois level.  The statement below
records that this property is *monotone in the level*: replacing the level `L` by a larger level
`M` and `a` by its inflation `levelMap p U h a` does not destroy the property.  This is what makes
`levelLocVanishing` well defined on the filtered system of levels, and it is used whenever a level
class is moved up in the tower.

The only input from the level machinery is that the local levels form a **filtered system**: the
transition maps `localLevelMap` compose (`NK.BrauerTwist.localLevelMap_comp`) and depend only on
the two levels, not on the proof of the inclusion.  Given a place `A` and a witness level `N ≥ L`
for `a`, the witness for the inflated class is the join `N ⊔ M`, and the inflation `L → M` is
absorbed into the composite `L → M → N ⊔ M`.
-/

import Mathlib
import Submission.NK.HasseTwist.Restrict
import Submission.NK.BrauerTwist.localLevelMap_comp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open CategoryTheory

universe u

namespace NK.HasseTwist

open NK.BrauerTwist

/-- Elementwise form of `localLevelMap_comp`: the local inflation maps of the level system
compose. -/
private lemma localLevelMap_comp_apply {K K' : Type u} [Field K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] (p : ℕ) (U : Subgroup Gal(K'/K)) (A : ValuationSubring K')
    {L₁ L₂ L₃ : FiniteGaloisIntermediateField K K'} (h₁ : L₁ ≤ L₂) (h₂ : L₂ ≤ L₃)
    (a : LocalLevelH2 p U A L₁) :
    localLevelMap p U A h₂ (localLevelMap p U A h₁ a) =
      localLevelMap p U A (h₁.trans h₂) a := by
  have h := ModuleCat.comp_apply (localLevelMap p U A h₁) (localLevelMap p U A h₂) a
  rw [localLevelMap_comp p U A h₁ h₂] at h
  exact h.symm

/-- The local inflation maps of the level system depend only on the two levels, not on the proof of
the inclusion. -/
private lemma localLevelMap_congr_apply {K K' : Type u} [Field K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] (p : ℕ) (U : Subgroup Gal(K'/K)) (A : ValuationSubring K')
    {L L' : FiniteGaloisIntermediateField K K'} {h h' : L ≤ L'} (a : LocalLevelH2 p U A L) :
    localLevelMap p U A h a = localLevelMap p U A h' a := by
  simp only [localLevelMap]

set_option maxHeartbeats 1600000 in
/-- **Monotonicity of `levelLocVanishing` in the level.**  If the level class `a` of
`H²(U, μ_p(L))` dies locally at every place after inflation to a larger level, then so does its
inflation `levelMap p U h a` to any larger level `M ≥ L`. -/
theorem levelLocVanishing_mono (p : ℕ) {K K' : Type u} [Field K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] {U : Subgroup Gal(K'/K)} {L M : FiniteGaloisIntermediateField K K'}
    (h : L ≤ M) {a : NK.BrauerTwist.LevelH2 p U L}
    (ha : NK.HasseTwist.levelLocVanishing p U L a) :
    NK.HasseTwist.levelLocVanishing p U M (NK.BrauerTwist.levelMap p U h a) := by
  intro A
  obtain ⟨N, hN, hzero⟩ := ha A
  refine ⟨N ⊔ M, le_sup_right, ?_⟩
  rw [levelMap_locLevel_apply (p := p) (U := U) (A := A.1) (h := h) a]
  rw [localLevelMap_comp_apply p U A.1 h (le_sup_right : M ≤ N ⊔ M)]
  rw [localLevelMap_congr_apply p U A.1
    (h := h.trans (le_sup_right : M ≤ N ⊔ M))
    (h' := hN.trans (le_sup_left : N ≤ N ⊔ M)) (locLevel p U A.1 L a)]
  rw [← localLevelMap_comp_apply p U A.1 hN (le_sup_left : N ≤ N ⊔ M)]
  rw [hzero, map_zero]

end NK.HasseTwist
