import Mathlib
import Submission.Work.CKFinal.LineDecay.Defs

/-!
# Norm bounds for the CKMRV prefactor `sinSqC` and the Gaussian weight `gaussWeight`

`sinSqC r = 4 sin²(πr²/2)` and `gaussWeight r t = e^{-πr²t}`.  Both are used as
uniformly bounded factors throughout the line-decay computation (they are the
constants that survive the `L¹` dominance estimates), and here we record the two
elementary bounds

  `‖sinSqC r‖ ≤ 4`   and   `‖gaussWeight r t‖ ≤ 1`  for `t ≥ 0`.

For `sinSqC` the argument `πr²/2` of the sine is real, so `sinSqC r` is the real
number `4 sin²(πr²/2)`, whose absolute value is at most `4`.  For `gaussWeight`
the exponent `-πr²t` is nonpositive for `r` real and `t ≥ 0`, and `‖e^z‖ = e^{re z}`.
-/

noncomputable section

namespace Work.CKFinal.LineDecay

open Complex

/-- `sinSqC r` is the real number `4 sin²(πr²/2)`, viewed in `ℂ`. -/
lemma sinSqC_eq_ofReal (r : ℝ) :
    Work.Asymptotics.sinSqC r
      = ((4 * Real.sin (Real.pi * r ^ 2 / 2) ^ 2 : ℝ) : ℂ) := by
  rw [Work.Asymptotics.sinSqC]
  have h : Real.pi * (r : ℂ) ^ 2 / 2 = ((Real.pi * r ^ 2 / 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [h, ← Complex.ofReal_sin]
  push_cast
  ring

/-- `‖sinSqC r‖ ≤ 4`. -/
lemma norm_sinSqC_le (r : ℝ) : ‖Work.Asymptotics.sinSqC r‖ ≤ 4 := by
  rw [sinSqC_eq_ofReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  have h := Real.sin_sq_le_one (Real.pi * r ^ 2 / 2)
  linarith

/-- `‖gaussWeight r t‖ ≤ 1` for `t ≥ 0`. -/
lemma norm_gaussWeight_le_one (r t : ℝ) (ht : 0 ≤ t) :
    ‖Work.Asymptotics.gaussWeight r t‖ ≤ 1 := by
  rw [Work.Asymptotics.norm_gaussWeight, Real.exp_le_one_iff]
  have h : (0 : ℝ) ≤ Real.pi * r ^ 2 * t := by positivity
  linarith

theorem sinSqC_gaussWeight_bound (r t : ℝ) (ht : 0 ≤ t) :
    ‖Work.Asymptotics.sinSqC r‖ ≤ 4 ∧ ‖Work.Asymptotics.gaussWeight r t‖ ≤ 1 :=
  ⟨norm_sinSqC_le r, norm_gaussWeight_le_one r t ht⟩

end Work.CKFinal.LineDecay
