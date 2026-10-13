import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Submission.Work.FTS.PressureOn.Auxiliary.HeatKernel

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Gaussian integrability and the Gaussian integral on `ℝ³`

Two elementary facts about the Gaussian weight `w ↦ exp (-(a ‖w‖²))` on `ℝ³` (`a > 0`):
integrability, and the value `(π/a)^{3/2}` of the integral.  They are the analytic input of the
`L¹` modulus of continuity of the heat kernel
(`Work.FTS.PressureOn.Auxiliary.integral_abs_heatKernel_sub_le`) and of the shear-averaging lemma
`Work.FTS.PressureOn.Auxiliary.ihak_interval_shift_mean`.

Both are immediate from Mathlib's `GaussianFourier.integrable_cexp_neg_mul_sq_norm_add` /
`GaussianFourier.integral_rexp_neg_mul_sq_norm` (the Gaussian integral in an arbitrary
finite dimensional real inner product space), specialised to `V = ℝ³`.
-/

open MeasureTheory
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn.Auxiliary

noncomputable section

/-- The Gaussian `w ↦ exp (-(a ‖w‖²))` is integrable on `ℝ³` for `a > 0`. -/
theorem ihak_integrable_rexp_normSq (a : ℝ) (ha : 0 < a) :
    Integrable (fun w : R3 => Real.exp (-(a * ‖w‖ ^ 2))) volume := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := R3)
    (b := (a : ℂ)) (by simpa using ha) 0 0
  simp only [zero_mul, add_zero] at h
  refine (h.norm).congr (Filter.Eventually.of_forall fun v => ?_)
  dsimp only
  rw [show (-(↑a : ℂ)) * (↑‖v‖ : ℂ) ^ 2 = ↑(-(a * ‖v‖ ^ 2)) by push_cast; ring,
    Complex.norm_exp, Complex.ofReal_re]

/-- The Gaussian integral on `ℝ³`: `∫ w, exp (-(a ‖w‖²)) = (π/a)^{3/2}` for `a > 0`. -/
theorem ihak_integral_rexp_normSq (a : ℝ) (ha : 0 < a) :
    ∫ w : R3, Real.exp (-(a * ‖w‖ ^ 2)) = (Real.pi / a) ^ ((3 : ℝ) / 2) := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := R3) (b := a) ha
  simp only [neg_mul] at h ⊢
  rw [h, finrank_euclideanSpace_fin]
  norm_num

/-- Translation invariance of the Gaussian integrability. -/
theorem ihak_integrable_rexp_normSq_sub (a : ℝ) (ha : 0 < a) (g : R3) :
    Integrable (fun w : R3 => Real.exp (-(a * ‖w - g‖ ^ 2))) volume := by
  simpa using (ihak_integrable_rexp_normSq a ha).comp_sub_right g

/-- Translation invariance of the Gaussian integral. -/
theorem ihak_integral_rexp_normSq_sub (a : ℝ) (ha : 0 < a) (g : R3) :
    ∫ w : R3, Real.exp (-(a * ‖w - g‖ ^ 2)) = (Real.pi / a) ^ ((3 : ℝ) / 2) := by
  rw [MeasureTheory.integral_sub_right_eq_self (fun w : R3 => Real.exp (-(a * ‖w‖ ^ 2))) g]
  exact ihak_integral_rexp_normSq a ha

end

end Work.FTS.PressureOn.Auxiliary
