/-
# ZeroFreeTables/XY/SupEcAbs

`|E(λ,t)| ≤ E₀(λ)` for the oscillatory integral
`E(λ,t) = ∫₀^{3/4} g(x)(cosh(λx) - 1)cos(tx) dx` and its non-oscillatory companion
`E₀(λ) = ∫₀^{3/4} g(x)(cosh(λx) - 1) dx`.

The integrand of `E₀` dominates that of `E` pointwise on the interval: the weight
`g(x)(cosh(λx) - 1)` is non-negative there (`g ≥ 0` by `xyG_nonneg` and `cosh ≥ 1`
by `Real.one_le_cosh`), and `|cos(tx)| ≤ 1`. So the triangle inequality for the
interval integral (`intervalIntegral.abs_integral_le_integral_abs`) followed by
monotonicity (`intervalIntegral.integral_mono_on`) gives the claim. The hypothesis
`0 ≤ λ` is not needed for this step.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.XY.LamPrimeData

open MeasureTheory

namespace Work.ZeroFreeTables.XY

theorem SupEcAbs (lam t : ℝ) (h0 : 0 ≤ lam) :
    |Work.ZeroFreeTables.XY.Ec lam t| ≤ Work.ZeroFreeTables.XY.E0c lam := by
  unfold Ec E0c
  have hcosh : Continuous fun x : ℝ => Real.cosh (lam * x) - 1 :=
    (Real.continuous_cosh.comp (continuous_const.mul continuous_id)).sub continuous_const
  have hf : Continuous fun x : ℝ =>
      xyG x * (Real.cosh (lam * x) - 1) * Real.cos (t * x) :=
    (xyG_cont.mul hcosh).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))
  have hg : Continuous fun x : ℝ => xyG x * (Real.cosh (lam * x) - 1) :=
    xyG_cont.mul hcosh
  refine le_trans (intervalIntegral.abs_integral_le_integral_abs (by norm_num)) ?_
  refine intervalIntegral.integral_mono_on (by norm_num)
    (hf.abs.intervalIntegrable 0 (3/4)) (hg.intervalIntegrable 0 (3/4)) ?_
  intro x _
  have hm : 0 ≤ Real.cosh (lam * x) - 1 := by linarith [Real.one_le_cosh (lam * x)]
  have hgx : 0 ≤ xyG x := xyG_nonneg x
  rw [abs_mul, abs_mul, abs_of_nonneg hgx, abs_of_nonneg hm]
  calc xyG x * (Real.cosh (lam * x) - 1) * |Real.cos (t * x)|
      ≤ xyG x * (Real.cosh (lam * x) - 1) * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (mul_nonneg hgx hm)
    _ = xyG x * (Real.cosh (lam * x) - 1) := by ring

end Work.ZeroFreeTables.XY
