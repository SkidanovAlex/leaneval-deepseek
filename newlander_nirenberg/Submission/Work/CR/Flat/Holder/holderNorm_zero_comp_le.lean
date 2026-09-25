import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Holder.Bilinear

namespace Work.CR.Flat.Holder

open scoped NNReal ENNReal
open Set

/-- Elementary real inequality behind the composition estimate: if `0 < p ≤ M * q` and `M, r ≥ 0`,
then `r / q ^ α ≤ M ^ α * (r / p ^ α)`.  Indeed `p ^ α ≤ M ^ α * q ^ α`, and multiplying by the
nonnegative number `r / (p ^ α * q ^ α)` gives the claim. -/
private lemma div_rpow_le_mul_div_rpow {r M p q α : ℝ} (hr : 0 ≤ r) (hM : 0 ≤ M) (hα : 0 < α)
    (hp : 0 < p) (hpq : p ≤ M * q) :
    r / q ^ α ≤ M ^ α * (r / p ^ α) := by
  have hq : 0 < q := by
    by_contra h
    have hq0 : q ≤ 0 := le_of_not_gt h
    have : M * q ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hM hq0
    linarith
  have hpq' : p ^ α ≤ M ^ α * q ^ α := by
    calc p ^ α ≤ (M * q) ^ α := Real.rpow_le_rpow hp.le hpq hα.le
      _ = M ^ α * q ^ α := Real.mul_rpow hM hq.le
  have hpα : 0 < p ^ α := Real.rpow_pos_of_pos hp α
  have hqα : 0 < q ^ α := Real.rpow_pos_of_pos hq α
  rw [← mul_div_assoc, le_div_iff₀ hpα, div_mul_eq_mul_div, div_le_iff₀ hqα]
  calc r * p ^ α ≤ r * (M ^ α * q ^ α) := mul_le_mul_of_nonneg_left hpq' hr
    _ = M ^ α * r * q ^ α := by ring

/-- Composition of the `C^{0,α}` norm with a Lipschitz map: if `Φ` maps `Ω` into `Ω'` and is
`M`-Lipschitz on `Ω`, then the `C^{0,α}` norm of `U ∘ Φ` on `Ω` is bounded by
`max 1 M^α` times the `C^{0,α}` norm of `U` on `Ω'`. -/
theorem holderNorm_zero_comp_le {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {α M : ℝ} (hα : 0 < α) (hM : 0 ≤ M)
    {Ω : Set X} {Ω' : Set Y} {Φ : X → Y} {U : Y → ℂ} (hΦ : Set.MapsTo Φ Ω Ω')
    (hLip : ∀ x ∈ Ω, ∀ y ∈ Ω, ‖Φ x - Φ y‖ ≤ M * ‖x - y‖) :
    Work.CR.Flat.holderNorm 0 α (fun x => U (Φ x)) Ω
      ≤ max 1 (ENNReal.ofReal (M ^ α)) * Work.CR.Flat.holderNorm 0 α U Ω' := by
  have hC1 : (1 : ℝ≥0∞) ≤ max 1 (ENNReal.ofReal (M ^ α)) := le_max_left _ _
  have hMc : ENNReal.ofReal (M ^ α) ≤ max 1 (ENNReal.ofReal (M ^ α)) := le_max_right _ _
  have hMα : (0 : ℝ) ≤ M ^ α := Real.rpow_nonneg hM α
  -- Sup-norm part: `Φ` maps `Ω` into `Ω'`, and `1 ≤ max 1 M^α`.
  have hA : Work.CR.Flat.iterDerivNorm 0 (fun x => U (Φ x)) Ω
      ≤ max 1 (ENNReal.ofReal (M ^ α)) * Work.CR.Flat.iterDerivNorm 0 U Ω' := by
    refine le_trans ?_ (le_mul_of_one_le_left' hC1)
    rw [Work.CR.Flat.iterDerivNorm_zero, Work.CR.Flat.iterDerivNorm_zero]
    exact iSup₂_le fun x hx => le_iSup₂_of_le (Φ x) (hΦ hx) le_rfl
  -- Hölder part: the Lipschitz bound gives a factor `M^α` on the denominators.
  have hB : Work.CR.Flat.holderSeminorm 0 α (fun x => U (Φ x)) Ω
      ≤ max 1 (ENNReal.ofReal (M ^ α)) * Work.CR.Flat.holderSeminorm 0 α U Ω' := by
    refine le_trans ?_ (mul_le_mul_left hMc _)
    refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
    rw [norm_iteratedFDerivWithin_zero_sub]
    by_cases h : Φ x = Φ y
    · rw [h, sub_self, norm_zero, zero_div, ENNReal.ofReal_zero]
      exact bot_le
    · have h1 := Work.CR.Flat.le_holderSeminorm 0 α U Ω' (hΦ hx) (hΦ hy) h
      rw [norm_iteratedFDerivWithin_zero_sub] at h1
      refine le_trans ?_ (mul_le_mul_right h1 (ENNReal.ofReal (M ^ α)))
      rw [← ENNReal.ofReal_mul hMα]
      refine ENNReal.ofReal_le_ofReal ?_
      exact div_rpow_le_mul_div_rpow (norm_nonneg _) hM hα (norm_pos_iff.mpr (sub_ne_zero.mpr h))
        (hLip x hx y hy)
  rw [Work.CR.Flat.holderNorm, Work.CR.Flat.holderNorm, Finset.sum_range_one,
    Finset.sum_range_one]
  calc Work.CR.Flat.iterDerivNorm 0 (fun x => U (Φ x)) Ω
        + Work.CR.Flat.holderSeminorm 0 α (fun x => U (Φ x)) Ω
      ≤ max 1 (ENNReal.ofReal (M ^ α)) * Work.CR.Flat.iterDerivNorm 0 U Ω'
        + max 1 (ENNReal.ofReal (M ^ α)) * Work.CR.Flat.holderSeminorm 0 α U Ω' :=
        add_le_add hA hB
    _ = max 1 (ENNReal.ofReal (M ^ α))
          * (Work.CR.Flat.iterDerivNorm 0 U Ω'
              + Work.CR.Flat.holderSeminorm 0 α U Ω') := (mul_add _ _ _).symm

end Work.CR.Flat.Holder
