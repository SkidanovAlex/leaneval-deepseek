import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Commons.Analysis.Real

/-- Elementary algebraic bound: for `x ≥ 1` the quantity `1 + 1/x²` is at most the
square of `1 + 1/(x + x²)`. -/
private lemma one_add_inv_sq_le_sq_one_add_inv_add_sq {x : ℝ} (hx : 1 ≤ x) :
    1 + 1/x^2 ≤ (1 + 1/(x + x^2))^2 := by
  have hx2pos : (0:ℝ) < x^2 := by positivity
  have hs : (0:ℝ) < x + x^2 := by positivity
  have hA : 1/x^2 ≤ 2/(x + x^2) := by
    rw [div_le_div_iff₀ hx2pos hs]
    nlinarith
  have hexp : (1 + 1/(x + x^2))^2 = 1 + 2/(x + x^2) + (1/(x + x^2))^2 := by ring
  rw [hexp]
  have := sq_nonneg (1/(x + x^2))
  linarith

/-- Elementary algebraic bound: the square of `1 + 1/(x + x²)` is at most
`1 + 2/x²` for `x > 0`. -/
private lemma sq_one_add_inv_add_sq_le_one_add_two_div_sq {x : ℝ} (hx : 0 < x) :
    (1 + 1/(x + x^2))^2 ≤ 1 + 2/x^2 := by
  have hxs : x + x^2 ≠ 0 := by positivity
  have hx2 : x^2 ≠ 0 := by positivity
  have hmain : (0:ℝ) < 1 + 2/x^2 - (1 + 1/(x + x^2))^2 := by
    field_simp
    nlinarith [sq_nonneg x, sq_nonneg (x^2), sq_nonneg (x^3)]
  linarith

/-- Algebraic rewriting: `1 + 1/(x²/2) = 1 + 2/x²`. -/
private lemma one_add_inv_div_two_sq {x : ℝ} : (1 + 1/(x^2/2) : ℝ) = 1 + 2/x^2 := by
  field_simp

theorem log_ratio_two_sandwich {x : ℝ} (hx : 2 ≤ x) :
    Real.log (1 + 1/x^2) / Real.log (x^2)
        ≤ Real.log (1 + 1/(x + x^2)) / Real.log x ∧
      Real.log (1 + 1/(x + x^2)) / Real.log x
        ≤ Real.log (1 + 1/(x^2/2)) / Real.log (x^2/2) := by
  have hx0 : (0:ℝ) < x := by linarith
  have hx1 : (1:ℝ) < x := by linarith
  have hlogx : (0:ℝ) < Real.log x := Real.log_pos hx1
  have hlogx2 : Real.log (x^2) = 2 * Real.log x := Real.log_pow x 2
  -- twofold logarithm inequalities, coming from the algebraic bounds above
  have hlog1 : Real.log (1 + 1/x^2) ≤ 2 * Real.log (1 + 1/(x + x^2)) := by
    have hp : (0:ℝ) < 1 + 1/x^2 := by positivity
    have h := Real.log_le_log hp (one_add_inv_sq_le_sq_one_add_inv_add_sq hx1.le)
    rwa [Real.log_pow] at h
  have hlog2 : 2 * Real.log (1 + 1/(x + x^2)) ≤ Real.log (1 + 2/x^2) := by
    have hBpos : (0:ℝ) < (1 + 1/(x + x^2))^2 := by positivity
    have h := Real.log_le_log hBpos (sq_one_add_inv_add_sq_le_one_add_two_div_sq hx0)
    rwa [Real.log_pow] at h
  have hlogCnn : 0 ≤ Real.log (1 + 2/x^2) := by
    apply Real.log_nonneg
    have : (0:ℝ) < 2/x^2 := by positivity
    linarith
  have hden2 : Real.log (x^2/2) = 2 * Real.log x - Real.log 2 := by
    rw [Real.log_div (by positivity : x^2 ≠ 0) (by norm_num : (2:ℝ) ≠ 0), hlogx2]
  have hden2pos : (0:ℝ) < Real.log (x^2/2) := by
    have h4 : (4:ℝ) ≤ x^2 := by nlinarith [sq_nonneg (x - 2)]
    apply Real.log_pos
    linarith
  constructor
  · -- first inequality: `1 + 1/x² ≤ (1 + 1/(x+x²))²` and `log (x²) = 2 log x`
    rw [hlogx2, div_le_div_iff₀ (by linarith : (0:ℝ) < 2 * Real.log x) hlogx]
    have := mul_le_mul_of_nonneg_right hlog1 hlogx.le
    linarith
  · -- second inequality: `(1 + 1/(x+x²))² ≤ 1 + 2/x² = 1 + 1/(x²/2)`
    rw [one_add_inv_div_two_sq]
    have step1 : Real.log (1 + 1/(x + x^2)) / Real.log x
        ≤ Real.log (1 + 2/x^2) / (2 * Real.log x) := by
      have h : Real.log (1 + 1/(x + x^2)) ≤ Real.log (1 + 2/x^2) / 2 := by linarith
      calc Real.log (1 + 1/(x + x^2)) / Real.log x
          ≤ (Real.log (1 + 2/x^2)/2)/Real.log x := div_le_div_of_nonneg_right h hlogx.le
        _ = Real.log (1 + 2/x^2) / (2 * Real.log x) := by ring
    have step2 : Real.log (1 + 2/x^2) / (2 * Real.log x)
        ≤ Real.log (1 + 2/x^2) / Real.log (x^2/2) := by
      apply div_le_div_of_nonneg_left hlogCnn hden2pos
      rw [hden2]
      linarith [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)]
    exact le_trans step1 step2

end Commons.Analysis.Real