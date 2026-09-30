import Mathlib
import Submission.Work.BW.finitePlace_posLog_eq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A finite place takes the value `1` when `|log| < log 2`

For a nonzero `x` in a number field `K` and a finite place `v`, the value `v x` is a power
`q ^ n` where `q = N(v) ≥ 2` is the norm of the place and `n : ℤ`.  Hence if
`|log (v x)| < log 2`, then `|n| · log q < log 2 ≤ log q`, forcing `n = 0`, i.e. `v x = 1`.
-/

namespace Work.BW

open scoped nonZeroDivisors

/-- Auxiliary arithmetic fact: a power `q ^ n` (`q ≥ 2`, `n : ℤ`) whose logarithm has absolute
value `< log 2` must be `1`. -/
lemma zpow_eq_one_of_abs_log_lt {q : ℕ} (hq : 2 ≤ q) {n : ℤ}
    (h : |Real.log ((q : ℝ) ^ n)| < Real.log 2) : (q : ℝ) ^ n = 1 := by
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 1 < q)
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hlogq_pos : 0 < Real.log (q : ℝ) := Real.log_pos hq1
  have hlog2_le : Real.log 2 ≤ Real.log (q : ℝ) := Real.log_le_log (by norm_num) hq2
  rw [Real.log_zpow] at h
  have hlt := (abs_lt.mp h).2
  have hgt := (abs_lt.mp h).1
  have hn0 : n = 0 := by
    rcases lt_trichotomy n 0 with hn | hn | hn
    · have hn1 : n ≤ -1 := by omega
      have hnn : (n : ℝ) ≤ -1 := by exact_mod_cast hn1
      have hle : (n : ℝ) * Real.log (q : ℝ) ≤ -Real.log 2 := by
        have h1 : (n : ℝ) * Real.log (q : ℝ) ≤ (-1 : ℝ) * Real.log (q : ℝ) :=
          mul_le_mul_of_nonneg_right hnn hlogq_pos.le
        nlinarith [h1, hlog2_le]
      linarith
    · exact hn
    · have hn1 : 1 ≤ n := by omega
      have hnn : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      have hle : Real.log 2 ≤ (n : ℝ) * Real.log (q : ℝ) := by
        have h1 : (1 : ℝ) * Real.log (q : ℝ) ≤ (n : ℝ) * Real.log (q : ℝ) :=
          mul_le_mul_of_nonneg_right hnn hlogq_pos.le
        nlinarith [h1, hlog2_le]
      linarith
  rw [hn0, zpow_zero]

theorem finitePlace_eq_one_of_abs_log_lt_log_two {K : Type*} [Field K] [NumberField K]
    (v : NumberField.FinitePlace K) {x : K} (hx : x ≠ 0)
    (h : |Real.log (v x)| < Real.log 2) : v x = 1 := by
  have hvx : v x = ((Ideal.absNorm v.maximalIdeal.asIdeal : ℕ) : ℝ) ^
      (-(FractionalIdeal.count K v.maximalIdeal (FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers K)) x))) := by
    rw [← NumberField.FinitePlace.norm_embedding_eq v x,
      NumberField.FinitePlace.norm_embedding', valuation_eq_exp_neg_count v.maximalIdeal hx,
      toNNReal_exp, NNReal.coe_zpow, NNReal.coe_natCast]
  rw [hvx] at h ⊢
  have hq2 : 2 ≤ Ideal.absNorm v.maximalIdeal.asIdeal := by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm v.maximalIdeal
    omega
  exact zpow_eq_one_of_abs_log_lt hq2 h

end Work.BW
