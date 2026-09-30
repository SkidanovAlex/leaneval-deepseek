import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open MeasureTheory

/-- The function `w ↦ exp(-|w|³)` is integrable on `ℝ`.

We dominate it by the constant multiple `exp 1 * exp(-w²)` of the Gaussian,
which is integrable (`integrable_exp_neg_mul_sq`).  The domination reduces to
the elementary inequality `t² - t³ ≤ 1` for `t = |w| ≥ 0`. -/
lemma integrable_exp_neg_abs_cube :
    MeasureTheory.Integrable (fun w : ℝ => Real.exp (-(|w| ^ 3))) := by
  have hg0 : Integrable (fun x : ℝ => Real.exp (-(x ^ 2))) := by
    simpa using (integrable_exp_neg_mul_sq (b := 1) one_pos)
  have hg : Integrable (fun x : ℝ => Real.exp 1 * Real.exp (-(x ^ 2))) :=
    hg0.const_mul _
  refine hg.mono' (by fun_prop) ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_add, Real.exp_le_exp]
  have hsq : x ^ 2 = |x| ^ 2 := by rw [sq_abs]
  rw [hsq]
  rcases le_or_gt |x| 1 with h1 | h1
  · have h2 : |x| ^ 2 ≤ 1 := by nlinarith [abs_nonneg x, h1]
    have h3 : 0 ≤ |x| ^ 3 := pow_nonneg (abs_nonneg x) 3
    linarith
  · have h2 : |x| ^ 2 ≤ |x| ^ 3 := by nlinarith [abs_nonneg x, h1]
    linarith

end Work.BMF
