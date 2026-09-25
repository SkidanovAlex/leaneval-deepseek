import Mathlib
import Submission.Work.NN.Newton.DefectDefs
import Submission.Work.NN.Newton.Defect.fderiv_lamC_apply
import Submission.Work.NN.Core.holderNorm_fderiv_le_dir
import Submission.Work.NN.Newton.Defect.norm_sub_le_of_holderSeminorm_zero
import Submission.Work.NN.Newton.Defect.holderNorm_zero_fderiv_coord_le_of_CVBound

/-!
# The `C^{0,α}` bound on the derivative of the perturbation `A`

If `A : ℂⁿ → (ℂⁿ →L[ℝ] ℂⁿ)` has `C^{1,α}`-norm at most `a` on the polydisc `P_r` — i.e.
every coefficient `z ↦ A z w j` (`‖w‖ ≤ 1`) is `C^{1,α}` of norm `≤ a` there — then the
derivative `z ↦ DA_z` is `α`-Hölder with constant `a`:

  `‖DA_z − DA_{z'}‖ ≤ a · ‖z − z'‖^α`   for `z, z' ∈ P_r`.

The proof has three steps.

* For a fixed unit vector `w` and coordinate `j` the function `u(z) = A z w j` is `C¹` on the
  (open) polydisc, and `CVBound` gives `holderNorm 1 α u P ≤ ofReal a`.  The `C^{0,α}` norm of
  its directional derivative `z ↦ du_z v` is at most `ofReal ‖v‖ * holderNorm 1 α u P`
  (`Work.NN.Core.holderNorm_fderiv_le_dir`), hence at most `ofReal (‖v‖ * a)`; this is
  `holderNorm_zero_fderiv_coord_le_of_CVBound`.
* The order-zero Hölder seminorm is a pointwise bound
  (`norm_sub_le_of_holderSeminorm_zero`), so for unit `v`, `w` and all `j`,
  `‖(DA_z v) w j − (DA_{z'} v) w j‖ ≤ a ‖z − z'‖^α`.
* The operator norm of `DA_z − DA_{z'}` is the supremum of these coordinates over the unit
  balls (`ContinuousLinearMap.opNorm_le_of_unit_norm` applied twice), giving the claim.
-/

namespace Work.NN.Newton.Defect

open scoped NNReal ENNReal

theorem norm_fderiv_sub_le_of_CVBound {n : ℕ}
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    {α a r : ℝ} (ha0 : 0 ≤ a)
    (hAc : ContDiffOn ℝ 1 A (Work.NN.Newton.polydiscR n r))
    (hA : Work.NN.Newton.CVBound A α a (Work.NN.Newton.polydiscR n r)) :
    ∀ z ∈ Work.NN.Newton.polydiscR n r, ∀ z' ∈ Work.NN.Newton.polydiscR n r,
      ‖fderiv ℝ A z - fderiv ℝ A z'‖ ≤ a * ‖z - z'‖ ^ α := by
  intro z hz z' hz'
  by_cases hzz : z = z'
  · subst hzz
    have h2 : fderiv ℝ A z - fderiv ℝ A z = 0 := by ext x y; simp
    rw [h2, ContinuousLinearMap.opNorm_zero]
    exact mul_nonneg ha0 (Real.rpow_nonneg (norm_nonneg _) α)
  · have hK : (0 : ℝ) ≤ a * ‖z - z'‖ ^ α :=
      mul_nonneg ha0 (Real.rpow_nonneg (norm_nonneg _) α)
    -- The coordinatewise bound on the unit balls.
    have hentry : ∀ v w : Work.NN.Core.Cn n, ‖v‖ ≤ 1 → ‖w‖ ≤ 1 →
        ‖((fderiv ℝ A z - fderiv ℝ A z') v) w‖ ≤ a * ‖z - z'‖ ^ α := by
      intro v w hv hw
      rw [pi_norm_le_iff_of_nonneg hK]
      intro j
      have hsub : ‖((fderiv ℝ A z) v) w j - ((fderiv ℝ A z') v) w j‖
          ≤ ‖v‖ * a * ‖z - z'‖ ^ α := by
        have hb := holderNorm_zero_fderiv_coord_le_of_CVBound A ha0 hAc hA hw j v
        have hsem : Work.CR.Flat.holderSeminorm 0 α (fun ζ => ((fderiv ℝ A ζ) v) w j)
            (Work.NN.Newton.polydiscR n r) ≤ ENNReal.ofReal (‖v‖ * a) :=
          le_trans (Work.CR.Flat.holderSeminorm_le_holderNorm 0 α _ _ (le_refl 0)) hb
        exact norm_sub_le_of_holderSeminorm_zero (K := ‖v‖ * a)
          (g := fun ζ => ((fderiv ℝ A ζ) v) w j)
          (mul_nonneg (norm_nonneg v) ha0) hsem hz hz'
      have h1 : ‖v‖ * a * ‖z - z'‖ ^ α ≤ a * ‖z - z'‖ ^ α :=
        mul_le_mul_of_nonneg_right (by
          calc ‖v‖ * a ≤ 1 * a := mul_le_mul_of_nonneg_right hv ha0
            _ = a := one_mul a) (Real.rpow_nonneg (norm_nonneg _) α)
      simp only [sub_apply, Pi.sub_apply]
      exact hsub.trans h1
    -- Assemble: the operator norm is the supremum of the entries over the unit balls.
    exact ContinuousLinearMap.opNorm_le_of_unit_norm hK (fun v hv =>
      ContinuousLinearMap.opNorm_le_of_unit_norm hK (fun w hw =>
        hentry v w (le_of_eq hv) (le_of_eq hw)))

end Work.NN.Newton.Defect
