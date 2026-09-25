import Mathlib
import Submission.Commons.Analysis.SpecialFunctions.Log.convex_combo_log_le
import Submission.Commons.Analysis.SpecialFunctions.Log.log_strip_bound_A_nonneg
import Submission.Commons.Analysis.SpecialFunctions.Log.log_strip_bound_B_nonneg

/-!
# The log-strip bound for large `x` and small `t` (Heath-Brown 1992, Lemma 2)

For `1 ≤ x ≤ 8` and `0 ≤ t ≤ 1`,

    log x + t / x + (t/x)^2 / 2 + 1 / (2x) ≤ log (2 + t) + 3/2 .

Write `G(x,t)` for the right-hand side minus the left-hand side.  For fixed
`x > 0` the function `t ↦ G(x,t)` is concave in `t` (indeed it is the sum of
`log (2+t)`, an affine term and a concave quadratic), so its minimum on
`[0,1]` is attained at one of the endpoints; equivalently

    G(x,t) = (1-t) · G(x,0) + t · G(x,1)
             + [log (2+t) - (1-t) log 2 - t log 3] + t (1-t) / (2 x²) ,

an identity verified below by clearing denominators.  The first two summands
are non-negative because `G(x,0) = log 2 + 3/2 - log x - 1/(2x) ≥ 0` and
`G(x,1) = log 3 + 3/2 - log x - 1/x - 1/(2x²) - 1/(2x) ≥ 0` for
`1 ≤ x ≤ 8` (`log_strip_bound_A_nonneg`, `log_strip_bound_B_nonneg`); the
third is the chord inequality for the concave logarithm
(`convex_combo_log_le` with `a = 2`, `b = 3`); the fourth is non-negative
because `0 ≤ t ≤ 1` and `x > 0`.
-/

namespace Commons.Analysis.SpecialFunctions.Log

theorem log_strip_large_x_small_t (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8)
    (ht1 : 0 ≤ t) (ht2 : t ≤ 1) :
    Real.log x + t / x + (t / x) ^ 2 / 2 + (1 : ℝ) / (2 * x) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hx1
  have hxne : x ≠ 0 := ne_of_gt hxpos
  let A : ℝ := Real.log 2 + (3 : ℝ) / 2 - Real.log x - (1 : ℝ) / (2 * x)
  let B : ℝ :=
    Real.log 3 + (3 : ℝ) / 2 - Real.log x - (1 : ℝ) / x - (1 : ℝ) / (2 * x ^ 2) -
      (1 : ℝ) / (2 * x)
  let C : ℝ := Real.log (2 + t) - (1 - t) * Real.log 2 - t * Real.log 3
  let D : ℝ := t * (1 - t) / (2 * x ^ 2)
  let G : ℝ :=
    Real.log (2 + t) + (3 : ℝ) / 2 -
      (Real.log x + t / x + (t / x) ^ 2 / 2 + (1 : ℝ) / (2 * x))
  have hA : 0 ≤ A := by
    dsimp [A]
    exact log_strip_bound_A_nonneg x hx1 hx2
  have hB : 0 ≤ B := by
    dsimp [B]
    exact log_strip_bound_B_nonneg x hx1 hx2
  have hC : 0 ≤ C := by
    dsimp [C]
    have harg : (1 - t) * 2 + t * 3 = 2 + t := by ring
    have h := convex_combo_log_le (2 : ℝ) 3 t (by norm_num) (by norm_num) ht1 ht2
    rw [harg] at h
    linarith
  have hD : 0 ≤ D := by
    dsimp [D]
    have htm : 0 ≤ 1 - t := by linarith
    exact div_nonneg (mul_nonneg ht1 htm) (by positivity)
  have hEq : G = (1 - t) * A + t * B + C + D := by
    dsimp [A, B, C, D, G]
    field_simp [hxne]
    ring
  have hG : 0 ≤ G := by
    rw [hEq]
    have h1 : 0 ≤ (1 - t) * A := mul_nonneg (by linarith : 0 ≤ 1 - t) hA
    have h2 : 0 ≤ t * B := mul_nonneg ht1 hB
    linarith
  dsimp [G] at hG
  linarith

end Commons.Analysis.SpecialFunctions.Log
