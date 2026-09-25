import Mathlib
import Submission.Work.NN.Newton.DefectDefs
import Submission.Work.NN.Newton.Defect.fderiv_lamC_apply

/-!
# The differential of `A` is bounded by the `C^{1,α}`-bound of its columns

`Work.NN.Newton.CVBound A α a P` says that, for every `w` with `‖w‖ ≤ 1` and every coordinate
`j`, the function `z ↦ (A z w)_j` has `C^{1,α}(P)`-norm at most `a`.  This module extracts from
that hypothesis the bound on the *differential* of `A`:

  `‖fderiv ℝ A z‖ ≤ a`  for `z ∈ P`.

The point is that `(fderiv ℝ A z) v w j = fderiv ℝ (fun z' => (A z' w) j) z v`: the derivative
of the column `z ↦ (A z' w)_j` in the direction `v` is the `(w,j)`-entry of the derivative of
`A`, so the `C^0`-part of `fderivWithin ℝ (fun z' => (A z' w) j) P z` is bounded by `a`, giving
`|(fderiv ℝ A z) v w j| ≤ a ‖v‖`; taking the supremum over the unit ball of `ℂⁿ` in both `w`
and `j` yields the bound on `‖fderiv ℝ A z‖` itself.
-/

namespace Work.NN.Newton.Defect

open scoped NNReal ENNReal
open Set

theorem norm_fderiv_le_of_CVBound {n : ℕ}
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    {α a r : ℝ} (ha0 : 0 ≤ a)
    (hAc : ContDiffOn ℝ 1 A (Work.NN.Newton.polydiscR n r))
    (hA : Work.NN.Newton.CVBound A α a (Work.NN.Newton.polydiscR n r)) :
    ∀ z ∈ Work.NN.Newton.polydiscR n r, ‖fderiv ℝ A z‖ ≤ a := by
  intro z hz
  have hΩo : IsOpen (Work.NN.Newton.polydiscR n r) := Work.NN.Newton.isOpen_polydiscR n r
  have hdiff : DifferentiableAt ℝ A z :=
    (hAc.contDiffAt (hΩo.mem_nhds hz)).differentiableAt (by norm_num)
  -- For a *unit* vector `w`, the derivative `v ↦ ((DA_z v) w)_j` is bounded by `a`.
  have hunit : ∀ (w : Work.NN.Core.Cn n) (j : Fin n), ‖w‖ ≤ 1 →
      ‖(Work.NN.Newton.lamC j).comp ((fderiv ℝ A z).flip w)‖ ≤ a := by
    intro w j hw
    have hCLM : ((Work.NN.Newton.lamC j).comp ((fderiv ℝ A z).flip w))
        = fderiv ℝ (fun z' => Work.NN.Newton.lamC j (A z' w)) z := by
      ext X
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
        fderiv_lamC_apply A j w hdiff X]
    rw [hCLM]
    have ha : ENNReal.ofReal
        ‖fderivWithin ℝ (fun z' => Work.NN.Newton.lamC j (A z' w))
          (Work.NN.Newton.polydiscR n r) z‖ ≤ ENNReal.ofReal a := by
      rw [← norm_iteratedFDerivWithin_one (fun z' => Work.NN.Newton.lamC j (A z' w))
        (hΩo.uniqueDiffOn z hz)]
      exact (Work.CR.Flat.le_iterDerivNorm 1 _ _ hz).trans
        ((Work.CR.Flat.iterDerivNorm_le_holderNorm 1 α _ _ le_rfl).trans (hA w hw j))
    rw [← fderivWithin_of_isOpen hΩo hz]
    exact (ENNReal.ofReal_le_ofReal_iff ha0).mp ha
  -- Scaling in `w`.
  have hscale : ∀ (w : Work.NN.Core.Cn n) (j : Fin n),
      ‖(Work.NN.Newton.lamC j).comp ((fderiv ℝ A z).flip w)‖ ≤ a * ‖w‖ := by
    intro w j
    rcases eq_or_ne w 0 with rfl | hw
    · simp
    · have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
      have hnorm : ‖(‖w‖)⁻¹ • w‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg w),
          inv_mul_cancel₀ (ne_of_gt hpos)]
      have h1 := hunit ((‖w‖)⁻¹ • w) j (le_of_eq hnorm)
      have h2 : (fderiv ℝ A z).flip w
          = ‖w‖ • (fderiv ℝ A z).flip ((‖w‖)⁻¹ • w) := by
        rw [← ContinuousLinearMap.map_smul, smul_inv_smul₀ (ne_of_gt hpos) w]
      rw [h2, ContinuousLinearMap.comp_smul, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg w)]
      calc ‖w‖ * ‖(Work.NN.Newton.lamC j).comp
              ((fderiv ℝ A z).flip ((‖w‖)⁻¹ • w))‖
          ≤ ‖w‖ * a := mul_le_mul_of_nonneg_left h1 (norm_nonneg w)
        _ = a * ‖w‖ := mul_comm _ _
  -- Assemble the operator-norm bound.
  rw [ContinuousLinearMap.opNorm_le_iff ha0]
  intro v
  rw [ContinuousLinearMap.opNorm_le_iff (mul_nonneg ha0 (norm_nonneg v))]
  intro w
  rw [pi_norm_le_iff_of_nonneg
    (mul_nonneg (mul_nonneg ha0 (norm_nonneg v)) (norm_nonneg w))]
  intro j
  have hvv : ((Work.NN.Newton.lamC j).comp ((fderiv ℝ A z).flip w)) v
      = ((fderiv ℝ A z) v w) j := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
    rfl
  calc ‖((fderiv ℝ A z) v w) j‖
      = ‖((Work.NN.Newton.lamC j).comp ((fderiv ℝ A z).flip w)) v‖ := by rw [hvv]
    _ ≤ ‖(Work.NN.Newton.lamC j).comp ((fderiv ℝ A z).flip w)‖ * ‖v‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ (a * ‖w‖) * ‖v‖ := mul_le_mul_of_nonneg_right (hscale w j) (norm_nonneg v)
    _ = (a * ‖v‖) * ‖w‖ := by ring

end Work.NN.Newton.Defect
