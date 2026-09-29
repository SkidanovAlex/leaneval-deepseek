import Mathlib
import Submission.Work.C17.logPw_setup
import Submission.Work.C17.logP_bounds

/-!
# Bounds on the cusp `xs a b` for admissible pairs (area C17)

`AdmQ a b` (`Submission/Work/C17/seventeen_indep.lean`) says that `a = 2m+1` and `b = 2n+1`
are odd integers `≥ 3` with `a < b` and a small relative gap `10⁶ (b−a) ≤ b`.  Under these
hypotheses the Taylor radius `xs a b` of the unlikely series `P` is pinched between `3/4` and
`1`; this is the numerical input which makes the "stadium" continuation of
`Work.C17.logPw_continuation` fit inside the unit disc.

Writing `A = a + √(a²−1)`, `B = b + √(b²−1)`, the cusp is `xs a b = (a+√(a²−1))·(b−√(b²−1))
= A / B`.  Positivity and `xs a b < 1` are already in the library
(`Work.C17.xs_pos_and_sq_lt_one`: for `a < b` one has `A < B`).  The new content here is the
*lower* bound `3/4 ≤ xs a b`, which is the quantitative form of "the admissible gap forces the
two cusps to be numerically close": `A ≥ 2a−1`, `B ≤ 2b`, so `xs a b ≥ (2a−1)/(2b)`, and the
gap hypothesis `10⁶(b−a) ≤ b` gives `(2a−1)/(2b) ≥ 3/4` because `a ≥ 3`.
-/

namespace Work.C17

/-- The elementary lower bound `(2a−1)/(2b) ≤ xs a b` for `a, b ≥ 1`.

Indeed `xs a b = A/B` with `A = a + √(a²−1) ≥ a + (a−1) = 2a−1` (as `√(a²−1) ≥ a−1` for
`a ≥ 1`) and `B = b + √(b²−1) ≤ 2b` (as `√(b²−1) ≤ b` for `b ≥ 0`); both `A` and `B` are
positive. -/
lemma cusp_lower_bound (a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (2 * a - 1) / (2 * b) ≤ xs a b := by
  have hsa : (0 : ℝ) ≤ a ^ 2 - 1 := by nlinarith
  have hsb : (0 : ℝ) ≤ b ^ 2 - 1 := by nlinarith
  have hApos : 0 < a + Real.sqrt (a ^ 2 - 1) := by
    have := Real.sqrt_nonneg (a ^ 2 - 1); linarith
  have hBpos : 0 < b + Real.sqrt (b ^ 2 - 1) := by
    have := Real.sqrt_nonneg (b ^ 2 - 1); linarith
  have hAge : 2 * a - 1 ≤ a + Real.sqrt (a ^ 2 - 1) := by
    have h1 : a - 1 ≤ Real.sqrt (a ^ 2 - 1) := by
      rw [Real.le_sqrt (by linarith) hsa]; nlinarith
    linarith
  have hBle : b + Real.sqrt (b ^ 2 - 1) ≤ 2 * b := by
    have h1 : Real.sqrt (b ^ 2 - 1) ≤ b := by
      have h2 : Real.sqrt (b ^ 2 - 1) ≤ Real.sqrt (b ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      rwa [Real.sqrt_sq (by linarith : (0 : ℝ) ≤ b)] at h2
    linarith
  have hBmul : (b + Real.sqrt (b ^ 2 - 1)) * (b - Real.sqrt (b ^ 2 - 1)) = 1 := by
    nlinarith [Real.sq_sqrt hsb]
  have hβ : b - Real.sqrt (b ^ 2 - 1) = 1 / (b + Real.sqrt (b ^ 2 - 1)) := by
    rw [eq_div_iff (ne_of_gt hBpos), mul_comm]; exact hBmul
  have hxs : xs a b = (a + Real.sqrt (a ^ 2 - 1)) / (b + Real.sqrt (b ^ 2 - 1)) := by
    rw [xs, hβ]; ring
  rw [hxs]
  calc (2 * a - 1) / (2 * b) ≤ (a + Real.sqrt (a ^ 2 - 1)) / (2 * b) :=
        div_le_div_of_nonneg_right hAge (by linarith)
    _ ≤ (a + Real.sqrt (a ^ 2 - 1)) / (b + Real.sqrt (b ^ 2 - 1)) :=
        div_le_div_of_nonneg_left (le_of_lt hApos) hBpos hBle

/-- The arithmetic core of the lower cusp bound: for `3 ≤ a` and `10⁶(b−a) ≤ b`,
`(2a−1)/(2b) ≥ 3/4`.

The gap hypothesis rewrites as `b·(10⁶−1) ≤ a·10⁶`, i.e. `b ≤ a·10⁶/(10⁶−1)`; together with
`a ≥ 3` this gives `6b ≤ 8a − 4`, which is exactly `4(2a−1) ≥ 3·(2b)`. -/
lemma gap_arith (a b : ℝ) (ha : 3 ≤ a) (hb : 1 ≤ b) (hgap : (10 : ℝ) ^ 6 * (b - a) ≤ b) :
    (3 : ℝ) / 4 ≤ (2 * a - 1) / (2 * b) := by
  have h2b : 0 < 2 * b := by linarith
  rw [le_div_iff₀ h2b]
  have h6b : 6 * b ≤ 8 * a - 4 := by nlinarith [hgap, ha]
  linarith

/-- **Cusp bounds for admissible pairs.**  For `AdmQ a b` the cusp `xs a b` lies in
`[3/4, 1)` (and in particular is positive). -/
theorem xs_adm_bounds {a b : ℚ} (hA : AdmQ a b) :
    0 < xs (a : ℝ) (b : ℝ) ∧ xs (a : ℝ) (b : ℝ) < 1 ∧ (3 / 4 : ℝ) ≤ xs (a : ℝ) (b : ℝ) := by
  obtain ⟨ha3, hab, hgap, -⟩ := hA
  have hb3 : (3 : ℚ) ≤ b := by linarith
  obtain ⟨hpos, hsq⟩ := xs_pos_and_sq_lt_one a b ha3 hb3 hab
  have haR3 : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha3
  have hbR3 : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb3
  have hgapR : (10 : ℝ) ^ 6 * ((b : ℝ) - (a : ℝ)) ≤ (b : ℝ) := by
    have h : (((10 : ℚ) ^ 6 * (b - a) : ℚ) : ℝ) ≤ ((b : ℚ) : ℝ) := by exact_mod_cast hgap
    push_cast at h
    linarith
  refine ⟨hpos, by nlinarith, ?_⟩
  exact le_trans (gap_arith (a : ℝ) (b : ℝ) haR3 (by linarith) hgapR)
    (cusp_lower_bound (a : ℝ) (b : ℝ) (by linarith) (by linarith))

end Work.C17
