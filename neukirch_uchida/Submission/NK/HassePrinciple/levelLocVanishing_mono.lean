import Mathlib
import Submission.NK.HassePrinciple.Defs
import Submission.NK.BrauerHasse.localLevelMap_comp

namespace NK.HassePrinciple

open CategoryTheory

open NK.BrauerHasse

/-! ## Monotonicity of `levelLocVanishing` in the level

`levelLocVanishing p U L a` says that the level class `a` dies, locally at every place, after
inflation to some larger (place-dependent) finite Galois level.  The statement below records that
this property is *monotone in the level*: replacing the level `L` by a larger level `L'` and `a` by
its inflation does not destroy the property.  This is what makes `levelLocVanishing` well defined on
the filtered system of levels, and it is used whenever a level class is moved up in the tower.

The only input from the level machinery is that the local levels form a **filtered system**: the
transition maps `localLevelMap` compose (`NK.BrauerHasse.localLevelMap_comp`) and depend only on
the two levels, not on the proof of the inclusion.  Given a place `A` and a witness level `M ≥ L`
for `a`, the witness for the inflated class is the join `M ⊔ L'`, and the inflation `L → L'` is
absorbed into the composite `L → L' → M ⊔ L'`. -/

private lemma localLevelMap_comp_apply {K K' : Type} [Field K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] (p : ℕ) (U : Subgroup Gal(K'/K)) (A : ValuationSubring K')
    {L₁ L₂ L₃ : FiniteGaloisIntermediateField K K'} (h₁ : L₁ ≤ L₂) (h₂ : L₂ ≤ L₃)
    (a : LocalLevelH2 p U A L₁) :
    localLevelMap p U A h₂ (localLevelMap p U A h₁ a) = localLevelMap p U A (h₁.trans h₂) a := by
  have h := ModuleCat.comp_apply (localLevelMap p U A h₁) (localLevelMap p U A h₂) a
  rw [localLevelMap_comp p U A h₁ h₂] at h
  exact h.symm

private lemma localLevelMap_congr_apply {K K' : Type} [Field K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] (p : ℕ) (U : Subgroup Gal(K'/K)) (A : ValuationSubring K')
    {L L' : FiniteGaloisIntermediateField K K'} {h h' : L ≤ L'} (a : LocalLevelH2 p U A L) :
    localLevelMap p U A h a = localLevelMap p U A h' a := by
  simp only [localLevelMap]

set_option maxHeartbeats 1600000 in
theorem levelLocVanishing_mono {K K' : Type} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K'] (p : ℕ) (U : Subgroup (K' ≃ₐ[K] K')) {L L' : FiniteGaloisIntermediateField K K'} (h : (L : IntermediateField K K') ≤ (L' : IntermediateField K K')) {a : NK.BrauerHasse.LevelH2 p U L} (ha : NK.HassePrinciple.levelLocVanishing p U L a) : NK.HassePrinciple.levelLocVanishing p U L' ((NK.BrauerHasse.levelMap p (U := U) h) a) := by
  intro A
  obtain ⟨M, hM, hzero⟩ := ha A
  refine ⟨M ⊔ L', le_sup_right, ?_⟩
  rw [levelMap_locLevel_apply (p := p) (U := U) (A := A.1) (h := h) a]
  rw [localLevelMap_comp_apply p U A.1 h (le_sup_right : L' ≤ M ⊔ L')]
  rw [localLevelMap_congr_apply p U A.1
    (h := h.trans (le_sup_right : L' ≤ M ⊔ L'))
    (h' := hM.trans (le_sup_left : M ≤ M ⊔ L')) (locLevel p U A.1 L a)]
  rw [← localLevelMap_comp_apply p U A.1 hM (le_sup_left : M ≤ M ⊔ L')]
  rw [hzero, map_zero]

end NK.HassePrinciple
