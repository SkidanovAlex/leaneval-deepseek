/-
# `Work.CoreResiduals.BiotSavart.TaylorDefs` — the second-order Taylor residual of the kernel

The far-field `C^{1,1}` estimate for the Biot–Savart field needs a bound for the *Taylor
remainder* of the Newtonian kernel `kf b = ‖b‖⁻³ • b`,

  `resid h y = kf (y + h) - kf y - kDerivCLM y h`,

uniformly in the direction `h` and with the correct homogeneity in `‖y‖` and `‖h‖`.

This file fixes `resid` and proves the two elementary pointwise input bounds:

* `norm_resid_le_crude`: the triangle-inequality bound
  `‖resid h y‖ ≤ ‖y+h‖⁻² + ‖y‖⁻² + 4‖y‖⁻³‖h‖`,
  valid everywhere (the term `4‖y‖⁻³‖h‖` is the operator-norm estimate for `kDerivCLM`);
* `norm_kf_eq`: `‖kf b‖ = ‖b‖⁻²`.

The homogeneous/mean-value bound in the *far* regime `2‖h‖ ≤ ‖y‖` lives in
`Work.CoreResiduals.BiotSavart.resid_le_far`.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.StabilityFar.Decay.KernelDefs
import Submission.Work.StabilityFar.Decay.norm_kDerivCLM_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

namespace Work.CoreResiduals.BiotSavart

open Work.StabilityFar.Decay (kf kDerivCLM crossL)

/-- The second-order Taylor residual of the Newtonian kernel:
`resid h y = kf (y + h) - kf y - kDerivCLM y h`. -/
noncomputable def resid (h y : Work.LWP.R3) : Work.LWP.R3 :=
  kf (y + h) - kf y - kDerivCLM y h

/-- The Biot–Savart Taylor residual seen at the shifted argument: `kf (x+h-a) - kf (x-a)
- kDerivCLM (x-a) h = resid h (x - a)`. -/
theorem resid_shift (x h a : Work.LWP.R3) :
    kf (x + h - a) - kf (x - a) - kDerivCLM (x - a) h = resid h (x - a) := by
  rw [resid, show x + h - a = (x - a) + h by abel]

/-- `(aⁿ)⁻¹ = a^{-n}` for `a ≥ 0`. -/
lemma inv_natPow_eq_rpow_neg (a : ℝ) (ha : 0 ≤ a) (n : ℕ) : (a ^ n)⁻¹ = a ^ (-(n:ℝ)) := by
  rw [← Real.rpow_natCast a n]
  exact (Real.rpow_neg ha n).symm

/-- The norm of the Newtonian kernel: `‖kf b‖ = ‖b‖⁻²`. -/
theorem norm_kf_eq (b : Work.LWP.R3) : ‖kf b‖ = ‖b‖ ^ (-2 : ℝ) := by
  rw [Work.StabilityFar.Decay.kf, norm_smul, Real.norm_of_nonneg (by positivity)]
  rcases eq_or_lt_of_le (norm_nonneg b) with h | h
  · rw [← h]; simp
  · have h2 : ((‖b‖ ^ (3:ℕ))⁻¹) * ‖b‖ = (‖b‖ ^ (2:ℕ))⁻¹ := by
      rw [show ‖b‖ ^ (3:ℕ) = ‖b‖ ^ (2:ℕ) * ‖b‖ by ring, mul_inv]
      field_simp
    rw [h2, Real.rpow_neg (norm_nonneg b) 2]
    congr 1
    exact (Real.rpow_natCast ‖b‖ 2).symm

/-- `kDerivCLM` vanishes at the origin. -/
theorem kDerivCLM_zero : kDerivCLM (0 : Work.LWP.R3) = 0 := by
  ext v
  simp [Work.StabilityFar.Decay.kDerivCLM]

/-- **Crude pointwise bound for the Taylor residual**: from the triangle inequality and the
operator-norm bound `‖kDerivCLM y‖ ≤ 4/‖y‖³`.  (For `y = 0` both sides are `‖h‖⁻²`.) -/
theorem norm_resid_le_crude (h y : Work.LWP.R3) :
    ‖resid h y‖ ≤
      ‖y + h‖ ^ (-2 : ℝ) + ‖y‖ ^ (-2 : ℝ) + 4 * ‖y‖ ^ (-3 : ℝ) * ‖h‖ := by
  have h1 := norm_kf_eq (y + h)
  have h2 := norm_kf_eq y
  have h4 : ‖kDerivCLM y h‖ ≤ 4 * ‖y‖ ^ (-3 : ℝ) * ‖h‖ := by
    rcases eq_or_lt_of_le (norm_nonneg y) with hh | hh
    · have hy0 : y = 0 := by rw [← norm_eq_zero]; exact hh.symm
      rw [hy0, kDerivCLM_zero, zero_apply, norm_zero]
      simp
    · have hb := Work.StabilityFar.Decay.norm_kDerivCLM_le y ‖y‖ hh le_rfl
      have h5 : (4:ℝ)/‖y‖^3 = 4 * ‖y‖^(-3:ℝ) := by
        rw [div_eq_mul_inv, inv_natPow_eq_rpow_neg ‖y‖ (norm_nonneg y) 3]
        congr 1
      calc ‖kDerivCLM y h‖ ≤ ‖kDerivCLM y‖ * ‖h‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ (4 / ‖y‖ ^ 3) * ‖h‖ := by gcongr
        _ = 4 * ‖y‖ ^ (-3:ℝ) * ‖h‖ := by rw [h5]
  have hb := norm_sub_le (kf (y + h)) (kf y)
  have hc := norm_sub_le (kf (y + h) - kf y) (kDerivCLM y h)
  rw [resid]
  linarith [h1, h2, h4, hb, hc]

end Work.CoreResiduals.BiotSavart
