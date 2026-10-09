import Mathlib
import Submission.Commons.RingTheory.Henselian.units_mem_pow_of_residue_mem_pow
import Submission.Commons.RingTheory.Henselian.adicCompletionIntegers_henselianLocalRing
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PinnedTwin

-- Hints: this is `Mathlib` + the workspace's Hensel lemma
-- `Commons.RingTheory.Henselian.units_mem_pow_of_residue_mem_pow` (see also
-- `Submission/Work/SSGRoute/NodeS37/henselUnitSquare.lean`, theorem
-- `Work.SSGRoute.NodeS37.exists_sq_of_residue_isSquare`, whose proof is the model to follow);
-- the inverse direction is the elementary valuation argument route.
theorem isSquare_unitGroup_iff_isSquare_residue {K : Type} [Field K] [NumberField K]
    (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (h2 : IsUnit (2 : P.adicCompletionIntegers K))
    (u : (P.adicCompletionIntegers K).unitGroup) :
    IsSquare ((u : (P.adicCompletion K)ˣ) : P.adicCompletion K) ↔
      IsSquare ((P.adicCompletionIntegers K).unitGroupToResidueFieldUnits u) := by
  constructor
  · -- Forward: a square root `c` of the unit `u` in the completion is again a unit of the
    -- integers (its valuation must be `1`), so its residue is a square root of the residue of `u`.
    intro h
    obtain ⟨c, hc⟩ := h
    have hu : Valued.v ((u : (P.adicCompletion K)ˣ) : P.adicCompletion K) = 1 :=
      (Valuation.mem_unitGroup_iff (P.adicCompletion K) (Valued.v)
        (u : (P.adicCompletion K)ˣ)).mp u.2
    have hvalc : Valued.v c = 1 := by
      have hmul : Valued.v c * Valued.v c = 1 := by
        rw [← map_mul, ← hc, hu]
      have hsq : Valued.v c ^ 2 = 1 := by rw [pow_two]; exact hmul
      exact sq_eq_one.mp hsq
    have hc0 : c ≠ 0 := by
      intro h0
      have : ((u : (P.adicCompletion K)ˣ) : P.adicCompletion K) = 0 := by
        rw [hc, h0, mul_zero]
      exact (Units.ne_zero (u : (P.adicCompletion K)ˣ)) this
    let gK : (P.adicCompletion K)ˣ := Units.mk0 c hc0
    have hgKval : Valued.v ((gK : (P.adicCompletion K)ˣ) : P.adicCompletion K) = 1 := by
      rw [Units.val_mk0]; exact hvalc
    let g : (P.adicCompletionIntegers K).unitGroup :=
      ⟨gK, (Valuation.mem_unitGroup_iff (P.adicCompletion K) (Valued.v) gK).mpr hgKval⟩
    have hgg : g * g = u := by
      apply Subtype.ext
      apply Units.ext
      change c * c = ((u : (P.adicCompletion K)ˣ) : P.adicCompletion K)
      rw [hc]
    exact IsSquare.map _ (hgg ▸ IsSquare.mul_self g)
  · -- Backward: Hensel's lemma lifts the square root of the residue to a square root of the
    -- unit in the integers of the completion.
    intro hsq
    have : HenselianLocalRing (P.adicCompletionIntegers K) :=
      Commons.RingTheory.Henselian.adicCompletionIntegers_henselianLocalRing
        (R := NumberField.RingOfIntegers K) (K := K) P
    obtain ⟨w, hw⟩ := hsq
    let uA : (P.adicCompletionIntegers K)ˣ := (P.adicCompletionIntegers K).unitGroupMulEquiv u
    have hmem : Units.map (IsLocalRing.residue (P.adicCompletionIntegers K)).toMonoidHom uA ∈
        (powMonoidHom 2).range := by
      refine ⟨w, ?_⟩
      rw [powMonoidHom_apply, pow_two]
      rw [← hw]
      exact rfl
    obtain ⟨b, hb⟩ := Commons.RingTheory.Henselian.units_mem_pow_of_residue_mem_pow
      (R := P.adicCompletionIntegers K) 2 (by simpa using h2) uA hmem
    rw [powMonoidHom_apply] at hb
    have hb2 : b * b = uA := by rwa [pow_two] at hb
    have hg2 : (P.adicCompletionIntegers K).unitGroupMulEquiv.symm b *
        (P.adicCompletionIntegers K).unitGroupMulEquiv.symm b = u := by
      apply (P.adicCompletionIntegers K).unitGroupMulEquiv.injective
      simp only [map_mul, MulEquiv.apply_symm_apply, hb2]
      rfl
    have h1 : (((P.adicCompletionIntegers K).unitGroupMulEquiv.symm b :
        (P.adicCompletionIntegers K).unitGroup) : (P.adicCompletion K)ˣ) *
        ((((P.adicCompletionIntegers K).unitGroupMulEquiv.symm b :
        (P.adicCompletionIntegers K).unitGroup) : (P.adicCompletion K)ˣ)) =
        (u : (P.adicCompletion K)ˣ) := by
      rw [← Subgroup.coe_mul, hg2]
    refine ⟨(((P.adicCompletionIntegers K).unitGroupMulEquiv.symm b :
      (P.adicCompletionIntegers K).unitGroup) : (P.adicCompletion K)ˣ) |>.val, ?_⟩
    have h2' := congrArg (fun x : (P.adicCompletion K)ˣ => (x : P.adicCompletion K)) h1
    simp only [Units.val_mul] at h2'
    exact h2'.symm

end Work.SSGRoute.PinnedTwin
