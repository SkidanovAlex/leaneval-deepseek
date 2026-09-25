import Mathlib
import Submission.Work.NN.Newton.DefectDefs
import Submission.Work.NN.Newton.Defect.fderiv_lamC_apply
import Submission.Work.NN.Core.holderNorm_fderiv_le_dir

namespace Work.NN.Newton.Defect

open scoped NNReal ENNReal Topology
open Set

/-!
# `C^{0,α}` bound for the entries of the differential of `A`

If the coefficients `z ↦ A z w j` of `A` (`‖w‖ ≤ 1`) have `C^{1,α}`-norm at most `a` on the
polydisc `P = polydiscR n r` (`CVBound A α a P`), then for every `‖w‖ ≤ 1`, every coordinate `j`
and every vector `v` the function

  `z ↦ ((DA_z v) w)_j`

has `C^{0,α}`-norm at most `‖v‖ · a` on `P`.

Indeed the entry `((DA_z v) w)_j` is the directional derivative in direction `v` of the
coefficient `z ↦ (A z w)_j` (`fderiv_lamC_apply`), so the claim is the statement that a
directional derivative lowers the Hölder order by one (`Work.NN.Core.holderNorm_fderiv_le_dir`,
with `k = 0`), the `C^{1,α}`-norm of the coefficient being bounded by `a` by `CVBound`.
-/

-- The hypothesis `ha0` is part of the requested signature but is not needed here: the
-- estimate holds for every real `a`.
set_option linter.unusedVariables false in
/-- The `C^{0,α}` bound for the `(w,j)`-entry of `z ↦ (DA_z v)`. -/
theorem holderNorm_zero_fderiv_coord_le_of_CVBound {n : ℕ}
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    {α a r : ℝ} (ha0 : 0 ≤ a)
    (hAc : ContDiffOn ℝ 1 A (Work.NN.Newton.polydiscR n r))
    (hA : Work.NN.Newton.CVBound A α a (Work.NN.Newton.polydiscR n r))
    {w : Work.NN.Core.Cn n} (hw : ‖w‖ ≤ 1) (j : Fin n) (v : Work.NN.Core.Cn n) :
    Work.CR.Flat.holderNorm 0 α (fun z => ((fderiv ℝ A z) v) w j)
      (Work.NN.Newton.polydiscR n r) ≤ ENNReal.ofReal (‖v‖ * a) := by
  have hΩ : IsOpen (Work.NN.Newton.polydiscR n r) := Work.NN.Newton.isOpen_polydiscR n r
  -- the coefficient `z ↦ (A z w)_j` is `C^1` as a composition of the linear map `T ↦ (T w)_j`
  -- with the `C^1` map `A`
  have hu : ContDiffOn ℝ ((0+1 : ℕ) : WithTop ℕ∞) (fun z => Work.NN.Newton.lamC j (A z w))
      (Work.NN.Newton.polydiscR n r) :=
    (ContinuousLinearMap.contDiff
      ((Work.NN.Newton.lamC j).comp (ContinuousLinearMap.apply ℝ (Work.NN.Core.Cn n) w))
      (n := ((0+1 : ℕ) : WithTop ℕ∞))).comp_contDiffOn hAc
  -- a directional derivative lowers the Hölder order
  have hmain := Work.NN.Core.holderNorm_fderiv_le_dir (α := α) hΩ 0 hu v
  -- the `C^{1,α}` bound on the coefficient, from `CVBound`
  have hcol : Work.CR.Flat.holderNorm (0+1) α (fun z => Work.NN.Newton.lamC j (A z w))
      (Work.NN.Newton.polydiscR n r) ≤ ENNReal.ofReal a := hA w hw j
  -- on the polydisc the derivative of the coefficient is the corresponding entry of `DA`
  have hid : ∀ z ∈ Work.NN.Newton.polydiscR n r,
      fderiv ℝ (fun z' => Work.NN.Newton.lamC j (A z' w)) z v = ((fderiv ℝ A z) v) w j := by
    intro z hz
    have hdiff : DifferentiableAt ℝ A z :=
      (hAc.contDiffAt (hΩ.mem_nhds hz)).differentiableAt (by norm_num)
    simpa only [Work.NN.Newton.lamC_apply] using
      Work.NN.Newton.Defect.fderiv_lamC_apply A j w hdiff v
  calc Work.CR.Flat.holderNorm 0 α (fun z => ((fderiv ℝ A z) v) w j)
        (Work.NN.Newton.polydiscR n r)
      = Work.CR.Flat.holderNorm 0 α
          (fun z => fderiv ℝ (fun z' => Work.NN.Newton.lamC j (A z' w)) z v)
          (Work.NN.Newton.polydiscR n r) :=
        (Work.NN.Core.holderNorm_congr_eqOn hid).symm
    _ ≤ ENNReal.ofReal ‖v‖ * Work.CR.Flat.holderNorm (0+1) α
          (fun z => Work.NN.Newton.lamC j (A z w)) (Work.NN.Newton.polydiscR n r) := hmain
    _ ≤ ENNReal.ofReal ‖v‖ * ENNReal.ofReal a := mul_le_mul_right hcol _
    _ = ENNReal.ofReal (‖v‖ * a) := (ENNReal.ofReal_mul (norm_nonneg v)).symm

end Work.NN.Newton.Defect
