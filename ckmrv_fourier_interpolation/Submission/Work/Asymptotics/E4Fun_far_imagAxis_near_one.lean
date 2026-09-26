import Mathlib
import Submission.Work.Residues.QExpansionTail
import Submission.Work.Residues.E4FunSecondOrder
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Asymptotics.E4Fun_sub_one_explicit

/-!
# `E₄` is within `1/2` of `1` on the far imaginary axis

For `Im τ ≥ 3` the value of the weight-four Eisenstein series `E₄` is within `1/2` of its
constant term `1`.  This is the region used by the `d = 24` funnel tail estimates.

The quantitative cusp expansion `Work.Asymptotics.E4Fun_sub_one_explicit` gives
`‖E₄ τ - 1‖ ≤ 20000 ‖q(τ)‖` for `Im τ ≥ 1`, with `‖q(τ)‖ = e^{-2π Im τ}`.  On `Im τ ≥ 3` we
have `2π Im τ ≥ 6π > 12`, so `‖q(τ)‖ ≤ e^{-12} ≤ 1/40000` and hence
`‖E₄ τ - 1‖ ≤ 20000/40000 = 1/2`.
-/

namespace Work.Asymptotics

open UpperHalfPlane

noncomputable section

/-- `e^{-12} ≤ 1/40000`, since `e^{12} = (e^1)^{12} ≥ 2.7^{12} ≥ 40000`. -/
private lemma exp_neg_twelve_le : Real.exp (-(12 : ℝ)) ≤ 1 / 40000 := by
  have h4 : Real.exp (12 : ℝ) = (Real.exp 1) ^ 12 := by
    rw [show (12 : ℝ) = ((12 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
  have h5 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h6 : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) h5 12
  have h7 : (40000 : ℝ) ≤ (2.7 : ℝ) ^ 12 := by norm_num
  have hExp : (40000 : ℝ) ≤ Real.exp (12 : ℝ) := by rw [h4]; linarith
  rw [Real.exp_neg]
  have := (inv_le_inv₀ (Real.exp_pos 12) (show (0 : ℝ) < 40000 by norm_num)).mpr hExp
  simpa using this

/-- For `12 ≤ x` one has `e^{-x} ≤ 1/40000`. -/
private lemma exp_neg_le_inv40000 {x : ℝ} (hx : 12 ≤ x) : Real.exp (-x) ≤ 1 / 40000 := by
  have h1 : Real.exp (-x) ≤ Real.exp (-(12 : ℝ)) := by
    rw [Real.exp_le_exp]; linarith
  exact le_trans h1 exp_neg_twelve_le

/-- **Main lemma.**  For `Im τ ≥ 3` the weight-four Eisenstein series is within `1/2` of `1`. -/
theorem E4Fun_far_imagAxis_near_one :
    ∀ z : UpperHalfPlane, 3 ≤ z.im → ‖Work.Kernels.E4Fun z - 1‖ ≤ 1 / 2 := by
  intro z hz
  have h1 : (1 : ℝ) ≤ z.im := by linarith
  -- the quantitative cusp bound `‖E₄ z - 1‖ ≤ 20000 ‖q(z)‖`
  have hb := E4Fun_sub_one_explicit (w := z) h1
  rw [norm_qParamFun] at hb
  -- `‖q(z)‖ = e^{-2π Im z}`, exponentially small on `Im z ≥ 3`
  have h12 : (12 : ℝ) ≤ 2 * Real.pi * z.im := by nlinarith [Real.pi_gt_three, hz]
  have hq : Real.exp (-(2 * Real.pi * z.im)) ≤ 1 / 40000 := exp_neg_le_inv40000 h12
  have hkey : (20000 : ℝ) * Real.exp (-(2 * Real.pi * z.im)) ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left hq (by norm_num : (0 : ℝ) ≤ 20000)
    linarith
  exact le_trans hb hkey

end

end Work.Asymptotics
