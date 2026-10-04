import Mathlib
import Submission.Work.Diff.C.geoCrux.rauch_num

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! # The `c ≤ 1/4` branch of the Rauch comparison constant

`rauch_B_tiny` states that for `0 < c ≤ 1/4` and `4 ε₁ π < c`

`6 (ε₁ (1 + log (4/√c)²) + c/4) + (c/4) log (8/c) ≤ 10.05 √c`.

Self-contained route.  Put `x = √c ∈ (0, 1/2]`.  The hypothesis `4 ε₁ π < c` gives
`6 ε₁ < 3 c / (2π)` (here `π > 0`), so the left-hand side is at most

`(3/(2π)) x² (1 + log (4/x)²) + (3/2) x² + (x²/4) log (8/x²)`,

and it suffices to bound the three summands by `(9/4) x`, `(3/4) x` and `(3/4) x`.
Both logarithmic bounds come from the elementary `log t ≤ √t` (for `t ≥ 1`, proved here from
`log y ≤ y - 1`):

* `x log (4/x)² ≤ 4`  (from `log (4/x) ≤ √(4/x)`), and
* `x log (8/x²) ≤ 3`  (from `log (8/x²) ≤ √(8/x²) ≤ 3/x`).

The numerics are closed by `π > 3` and `10.05 ≥ 15/4`: `(3/(2π))·(9/2) ≤ 9/4`.
-/

set_option maxHeartbeats 1000000

namespace Work.Diff.C.geoCrux

/-- `2 log u ≤ u` for `u > 0` (elementary, from `log y ≤ y - 1` in the two ranges `u ≤ 2` and
`2 ≤ u`, splitting off `log 2 < 1` in the latter). -/
private lemma two_mul_log_le {u : ℝ} (hu : 0 < u) : 2 * Real.log u ≤ u := by
  rcases le_total u 2 with h2 | h2
  · have h := Real.log_le_sub_one_of_pos hu
    nlinarith
  · have h1 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
    have hu2 : 0 < u / 2 := by positivity
    have h2b : Real.log (u / 2) ≤ u / 2 - 1 := Real.log_le_sub_one_of_pos hu2
    have hm : Real.log u = Real.log 2 + Real.log (u / 2) := by
      rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : (u / 2) ≠ 0)]
      congr 1
      ring
    nlinarith

/-- `log t ≤ √t` for `t ≥ 1`. -/
private lemma log_le_sqrt {t : ℝ} (ht : 1 ≤ t) : Real.log t ≤ Real.sqrt t := by
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  calc Real.log t = Real.log (Real.sqrt t ^ 2) := by rw [Real.sq_sqrt ht0.le]
    _ = 2 * Real.log (Real.sqrt t) := by rw [Real.log_pow]; push_cast; ring
    _ ≤ Real.sqrt t := two_mul_log_le hs0

/-- The `x`-form of the estimate: for `0 < x ≤ 1/2`,
`(3/(2π)) x² (1 + log (4/x)²) + (3/2) x² + (x²/4) log (8/x²) ≤ 10.05 x`. -/
private lemma key_bound {x : ℝ} (hx0 : 0 < x) (hxle : x ≤ 1 / 2) :
    (3 / (2 * Real.pi)) * (x ^ 2 * (1 + (Real.log (4 / x)) ^ 2))
      + (3 / 2) * x ^ 2 + (x ^ 2 / 4) * Real.log (8 / x ^ 2) ≤ 10.05 * x := by
  have h4x : 1 ≤ 4 / x := by
    rw [le_div_iff₀ hx0]; linarith
  have h8x2 : 1 ≤ 8 / x ^ 2 := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < x ^ 2)]
    nlinarith [hxle, hx0]
  -- `log (4/x)² ≤ 4/x`
  have hLnn : 0 ≤ Real.log (4 / x) := Real.log_nonneg h4x
  have hLle : Real.log (4 / x) ≤ Real.sqrt (4 / x) := log_le_sqrt h4x
  have hsL : Real.sqrt (4 / x) ^ 2 = 4 / x := Real.sq_sqrt (by positivity)
  have hLsq : (Real.log (4 / x)) ^ 2 ≤ 4 / x :=
    by nlinarith [hsL, hLle, hLnn, Real.sqrt_nonneg (4 / x)]
  have hxL2 : x * (Real.log (4 / x)) ^ 2 ≤ 4 := by
    have h := mul_le_mul_of_nonneg_left hLsq hx0.le
    have hc : x * (4 / x) = 4 := by field_simp
    linarith [h, hc]
  have h1 : x * (1 + (Real.log (4 / x)) ^ 2) ≤ 9 / 2 := by
    nlinarith [hxL2, hxle]
  -- the middle term
  have h2 : (3 / 2) * x ^ 2 ≤ (3 / 4) * x := by
    nlinarith [hx0, hxle]
  -- `√(8/x²) ≤ 3/x`, hence `x log (8/x²) ≤ 3`
  have h8le : Real.sqrt (8 / x ^ 2) ≤ 3 / x := by
    rw [Real.sqrt_le_left (by positivity : (0 : ℝ) ≤ 3 / x)]
    have hx2p : (0 : ℝ) < x ^ 2 := by positivity
    have hsq : (3 / x) ^ 2 = 9 / x ^ 2 := by ring
    rw [hsq, div_le_div_iff₀ hx2p hx2p]
    nlinarith
  have hcore : x * Real.log (8 / x ^ 2) ≤ 3 := by
    have hlog8 : Real.log (8 / x ^ 2) ≤ Real.sqrt (8 / x ^ 2) := log_le_sqrt h8x2
    have e1 := mul_le_mul_of_nonneg_left hlog8 hx0.le
    have e2 := mul_le_mul_of_nonneg_left h8le hx0.le
    have hc : x * (3 / x) = 3 := by field_simp
    linarith [e1, e2, hc]
  have h3 : (x ^ 2 / 4) * Real.log (8 / x ^ 2) ≤ (3 / 4) * x := by
    nlinarith [hcore, hx0.le]
  -- the first term, with the numerical factor `3/(2π)`
  have hA : (3 / (2 * Real.pi)) * (x ^ 2 * (1 + (Real.log (4 / x)) ^ 2)) ≤ (9 / 4) * x := by
    have hcoef : 0 ≤ 3 / (2 * Real.pi) := by positivity
    have hxx : x ^ 2 * (1 + (Real.log (4 / x)) ^ 2)
        = x * (x * (1 + (Real.log (4 / x)) ^ 2)) := by ring
    rw [hxx]
    have s1 : (3 / (2 * Real.pi)) * (x * (x * (1 + (Real.log (4 / x)) ^ 2)))
        ≤ (3 / (2 * Real.pi)) * (x * (9 / 2)) := by
      apply mul_le_mul_of_nonneg_left _ hcoef
      exact mul_le_mul_of_nonneg_left h1 hx0.le
    have s2 : (3 / (2 * Real.pi)) * (x * (9 / 2)) = (27 / (4 * Real.pi)) * x := by ring
    have s3 : (27 / (4 * Real.pi)) * x ≤ (9 / 4) * x := by
      apply mul_le_mul_of_nonneg_right _ hx0.le
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [Real.pi_gt_three]
    linarith [s1, s2, s3]
  nlinarith [hA, h2, h3]

set_option linter.unusedVariables false in
theorem rauch_B_tiny {c ε₁ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    (hnum2 : 4 * ε₁ * Real.pi < c) :
    6 * (ε₁ * (1 + (Real.log (4 / Real.sqrt c)) ^ 2) + c / 4) + (c / 4) * Real.log (8 / c)
      ≤ 10.05 * Real.sqrt c := by
  set x : ℝ := Real.sqrt c with hxdef
  have hx0 : 0 < x := by rw [hxdef]; exact Real.sqrt_pos.mpr hc
  have hx2 : x ^ 2 = c := by rw [hxdef]; exact Real.sq_sqrt hc.le
  have hxle : x ≤ 1 / 2 := by
    rw [hxdef]
    have h : Real.sqrt c ≤ Real.sqrt (1 / 4) := Real.sqrt_le_sqrt hc1
    have h' : Real.sqrt ((1 : ℝ) / 4) = 1 / 2 := by
      rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith
  rw [← hx2]
  have h6e : 6 * ε₁ ≤ 3 * x ^ 2 / (2 * Real.pi) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)]
    nlinarith [hnum2, hx2]
  have hL2nn : 0 ≤ 1 + (Real.log (4 / x)) ^ 2 := by positivity
  have hb1 : 6 * (ε₁ * (1 + (Real.log (4 / x)) ^ 2))
      ≤ (3 / (2 * Real.pi)) * (x ^ 2 * (1 + (Real.log (4 / x)) ^ 2)) := by
    have h := mul_le_mul_of_nonneg_right h6e hL2nn
    convert h using 1 <;> ring
  have hkey := key_bound hx0 hxle
  calc 6 * (ε₁ * (1 + (Real.log (4 / x)) ^ 2) + x ^ 2 / 4)
          + (x ^ 2 / 4) * Real.log (8 / x ^ 2)
      = 6 * (ε₁ * (1 + (Real.log (4 / x)) ^ 2)) + (3 / 2) * x ^ 2
          + (x ^ 2 / 4) * Real.log (8 / x ^ 2) := by ring
    _ ≤ (3 / (2 * Real.pi)) * (x ^ 2 * (1 + (Real.log (4 / x)) ^ 2))
          + (3 / 2) * x ^ 2 + (x ^ 2 / 4) * Real.log (8 / x ^ 2) := by
        exact add_le_add (add_le_add hb1 le_rfl) le_rfl
    _ ≤ 10.05 * x := hkey

end Work.Diff.C.geoCrux
