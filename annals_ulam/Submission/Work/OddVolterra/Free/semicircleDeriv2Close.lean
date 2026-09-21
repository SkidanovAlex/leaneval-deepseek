import Mathlib
import Submission.Work.OddEnvelope.Defs
import Submission.Work.OddCurve.LowSlope.radial_derivs_le_of_profile

/-!
# The second derivative of the semicircle is Lipschitz near the origin

The target of this file is

`semicircleDeriv2Close`: for `|u| < 4/5`, `|a - 1| ≤ ν` and `|a * u| ≤ 17/20`,

    |f''(a * u) - f''(u)| ≤ 300 * (ν + ν²),

where `f = Work.OddEnvelope.semicircle`, `f t = √(1 - t²)`.

The proof is purely analytic and quantitative:

* On `(-1,1)`, `f''(t) = -1/(√(1 - t²))³` (see `semicircle_deriv2_eq`, from
  `Work.OddCurve.LowSlope.radialAux_deriv_deriv_sqrt`).
* Writing `P = √(1 - x²)`, `Q = √(1 - y²)`, an algebraic manipulation gives the exact
  identity
  `1/P³ - 1/Q³ = (x - y)(x + y)(P² + PQ + Q²)/((P + Q)P³Q³)`,
  so on `|x|,|y| ≤ 17/20` the ratio `|f'' x - f'' y| / |x - y|` is bounded by
  `2 · 3 / (111/400)³ < 375` (using `|x + y| ≤ 2`, `P² + PQ + Q² ≤ 3`, `P + Q ≥ 1` and
  `PQ ≥ 111/400`). This is `semicircle_deriv2_lipschitz`.
* Finally `|a * u - u| = |a - 1| · |u| ≤ (4/5)ν`, and `375 · (4/5) = 300`.
-/

namespace Work.OddVolterra.Free

open Work.OddEnvelope

set_option maxHeartbeats 800000

/-- On `(-1,1)` the second derivative of the unit semicircle is
`t ↦ -1/(√(1 - t²))³`. -/
lemma semicircle_deriv2_eq {z : ℝ} (hz : |z| < 1) :
    deriv (deriv OddEnvelope.semicircle) z = -1 / (Real.sqrt (1 - z ^ 2)) ^ 3 := by
  change deriv (deriv fun t : ℝ => Real.sqrt (1 - t ^ 2)) z = _
  exact Work.OddCurve.LowSlope.radialAux_deriv_deriv_sqrt hz

/-- The second derivative of the unit semicircle is `375`-Lipschitz on `[-17/20, 17/20]`. -/
lemma semicircle_deriv2_lipschitz {x y : ℝ} (hx : |x| ≤ 17 / 20) (hy : |y| ≤ 17 / 20) :
    |deriv (deriv OddEnvelope.semicircle) x - deriv (deriv OddEnvelope.semicircle) y|
      ≤ 375 * |x - y| := by
  have hx1 : |x| < 1 := by linarith
  have hy1 : |y| < 1 := by linarith
  have hx2 : x ^ 2 ≤ 289 / 400 := by
    have h := sq_le_sq' (abs_le.mp hx).1 (abs_le.mp hx).2
    norm_num at h
    linarith
  have hy2 : y ^ 2 ≤ 289 / 400 := by
    have h := sq_le_sq' (abs_le.mp hy).1 (abs_le.mp hy).2
    norm_num at h
    linarith
  rw [semicircle_deriv2_eq hx1, semicircle_deriv2_eq hy1]
  set P : ℝ := Real.sqrt (1 - x ^ 2) with hPdef
  set Q : ℝ := Real.sqrt (1 - y ^ 2) with hQdef
  have hxpos : 0 < 1 - x ^ 2 := by nlinarith
  have hypos : 0 < 1 - y ^ 2 := by nlinarith
  have hPpos : 0 < P := by rw [hPdef]; exact Real.sqrt_pos.2 hxpos
  have hQpos : 0 < Q := by rw [hQdef]; exact Real.sqrt_pos.2 hypos
  have hPsq : P ^ 2 = 1 - x ^ 2 := by rw [hPdef]; exact Real.sq_sqrt hxpos.le
  have hQsq : Q ^ 2 = 1 - y ^ 2 := by rw [hQdef]; exact Real.sq_sqrt hypos.le
  have hPne : P ≠ 0 := ne_of_gt hPpos
  have hQne : Q ≠ 0 := ne_of_gt hQpos
  have hPQne : P + Q ≠ 0 := by positivity
  have hden : 0 < (P + Q) * P ^ 3 * Q ^ 3 := by positivity
  have hnumpos : 0 < P ^ 2 + P * Q + Q ^ 2 := by positivity
  -- the exact expression of the difference of the two second derivatives
  have hident : 1 / P ^ 3 - 1 / Q ^ 3 =
      (x - y) * (x + y) * (P ^ 2 + P * Q + Q ^ 2) / ((P + Q) * P ^ 3 * Q ^ 3) := by
    have hnum : (x - y) * (x + y) = (Q - P) * (Q + P) := by
      have h : x ^ 2 - y ^ 2 = Q ^ 2 - P ^ 2 := by nlinarith [hPsq, hQsq]
      nlinarith [h]
    rw [hnum]
    field_simp [hPne, hQne, hPQne]
    ring
  have habs : |-1 / P ^ 3 - -1 / Q ^ 3| = |1 / P ^ 3 - 1 / Q ^ 3| := by
    rw [show (-1 / P ^ 3 - -1 / Q ^ 3 : ℝ) = -(1 / P ^ 3 - 1 / Q ^ 3) by ring, abs_neg]
  rw [habs, hident]
  have hsplit : |(x - y) * (x + y) * (P ^ 2 + P * Q + Q ^ 2) / ((P + Q) * P ^ 3 * Q ^ 3)|
      = |x - y| * (|x + y| * (P ^ 2 + P * Q + Q ^ 2) / ((P + Q) * P ^ 3 * Q ^ 3)) := by
    rw [abs_div, abs_mul, abs_mul, abs_of_pos hden, abs_of_pos hnumpos]
    ring
  rw [hsplit]
  -- it remains to bound the quotient, the factor `|x - y|` being pulled out
  have hfrac : |x + y| * (P ^ 2 + P * Q + Q ^ 2) / ((P + Q) * P ^ 3 * Q ^ 3) ≤ 375 := by
    rw [div_le_iff₀ hden]
    have hxabs : |x + y| ≤ 2 := by
      have h := abs_add_le x y
      have h' : |x| + |y| ≤ 2 := by linarith
      linarith
    have hPle1 : P ≤ 1 := by rw [hPdef]; exact Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg x])
    have hQle1 : Q ≤ 1 := by rw [hQdef]; exact Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg y])
    have hPsqle : P ^ 2 ≤ 1 := by nlinarith [hPsq, sq_nonneg x]
    have hQsqle : Q ^ 2 ≤ 1 := by nlinarith [hQsq, sq_nonneg y]
    have hPQle1 : P * Q ≤ 1 := by
      simpa using mul_le_mul hPle1 hQle1 (le_of_lt hQpos) (by norm_num : (0 : ℝ) ≤ 1)
    have hsumle : P ^ 2 + P * Q + Q ^ 2 ≤ 3 := by linarith
    have hPge : ((111 : ℝ) / 400) ≤ 1 - x ^ 2 := by nlinarith
    have hQge : ((111 : ℝ) / 400) ≤ 1 - y ^ 2 := by nlinarith
    have hPge2 : Real.sqrt ((111 : ℝ) / 400) ≤ P := by
      rw [hPdef]; exact Real.sqrt_le_sqrt hPge
    have hQge2 : Real.sqrt ((111 : ℝ) / 400) ≤ Q := by
      rw [hQdef]; exact Real.sqrt_le_sqrt hQge
    have hsq111 : Real.sqrt ((111 : ℝ) / 400) * Real.sqrt ((111 : ℝ) / 400)
        = (111 : ℝ) / 400 := by
      rw [← sq, Real.sq_sqrt (by norm_num)]
    have hPQge : ((111 : ℝ) / 400) ≤ P * Q := by
      have h := mul_le_mul hPge2 hQge2 (Real.sqrt_nonneg _) (le_of_lt hPpos)
      linarith [hsq111, h]
    have hPQ3 : ((111 : ℝ) / 400) ^ 3 ≤ P ^ 3 * Q ^ 3 := by
      have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 111 / 400) hPQge 3
      have h2 : (P * Q) ^ 3 = P ^ 3 * Q ^ 3 := by ring
      linarith [h, h2]
    have hPgehalf : (1 / 2 : ℝ) ≤ P := by
      rw [hPdef]
      exact (Real.le_sqrt (by norm_num) (le_of_lt hxpos)).mpr (by nlinarith [hx2])
    have hQgehalf : (1 / 2 : ℝ) ≤ Q := by
      rw [hQdef]
      exact (Real.le_sqrt (by norm_num) (le_of_lt hypos)).mpr (by nlinarith [hy2])
    have hPQge1 : 1 ≤ P + Q := by linarith
    have h1 : |x + y| * (P ^ 2 + P * Q + Q ^ 2) ≤ 2 * 3 :=
      mul_le_mul hxabs hsumle (by positivity) (by norm_num)
    have h2 : ((111 : ℝ) / 400) ^ 3 ≤ (P + Q) * P ^ 3 * Q ^ 3 := by
      have h := mul_le_mul hPQge1 hPQ3 (by positivity) (by positivity)
      linarith [h]
    have h3 : (6 : ℝ) ≤ 375 * ((111 : ℝ) / 400) ^ 3 := by norm_num
    nlinarith [h1, h2, h3]
  calc |x - y| * (|x + y| * (P ^ 2 + P * Q + Q ^ 2) / ((P + Q) * P ^ 3 * Q ^ 3))
      ≤ |x - y| * 375 := mul_le_mul_of_nonneg_left hfrac (abs_nonneg _)
    _ = 375 * |x - y| := by ring

theorem semicircleDeriv2Close {a u ν : ℝ} (hν : 0 ≤ ν) (hu : |u| < 4 / 5)
    (ha : |a - 1| ≤ ν) (hx : |a * u| ≤ 17 / 20) :
    |deriv (deriv Work.OddEnvelope.semicircle) (a * u) -
      deriv (deriv Work.OddEnvelope.semicircle) u| ≤ 300 * (ν + ν ^ 2) := by
  have hu17 : |u| ≤ 17 / 20 := by
    have h : (4 : ℝ) / 5 < 17 / 20 := by norm_num
    linarith
  have hkey := semicircle_deriv2_lipschitz (x := a * u) (y := u) hx hu17
  have hdiff : |a * u - u| ≤ (4 / 5) * ν := by
    have h : a * u - u = (a - 1) * u := by ring
    rw [h, abs_mul]
    have h2 := mul_le_mul ha (le_of_lt hu) (abs_nonneg u) hν
    linarith
  calc |deriv (deriv Work.OddEnvelope.semicircle) (a * u) -
        deriv (deriv Work.OddEnvelope.semicircle) u|
      ≤ 375 * |a * u - u| := hkey
    _ ≤ 375 * ((4 / 5) * ν) := mul_le_mul_of_nonneg_left hdiff (by norm_num)
    _ = 300 * ν := by ring
    _ ≤ 300 * (ν + ν ^ 2) := by nlinarith [sq_nonneg ν]

end Work.OddVolterra.Free
