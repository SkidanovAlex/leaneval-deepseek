import Mathlib

namespace Work.OffAxis.Tf72One

/-- Glue: a truncated Taylor sum is a lower bound for `exp`.

`Real.sum_le_exp_of_nonneg` says `∑_{i<n} x^i/i! ≤ exp x` for `x ≥ 0`; this lemma lets the
caller supply a rational `q` bounded above by such a sum (checked by `norm_num`), which is how
the nine grid values below are handled.  Unlike `Real.exp_bound'` there is no restriction
`x ≤ 1`, so no "raise to a power" step is needed here. -/
private lemma le_exp_of_sum {x q : ℝ} (hx : 0 ≤ x) (n : ℕ)
    (h : q ≤ ∑ i ∈ Finset.range n, x ^ i / (↑i.factorial : ℝ)) : q ≤ Real.exp x :=
  h.trans (Real.sum_le_exp_of_nonneg hx n)

/-- Rational lower bounds for `exp` at the nine grid arguments `0, 3/10, 3/5, 9/10, 6/5, 3/2, 9/5,
21/10, 17/8` (companion of `exp_bounds`, needed because the closed form's trigonometric
coefficients are large at small `σ`, so a two-sided rational enclosure of `exp (2s)` is required). -/
theorem exp_bounds_lo :
    (1:ℝ) ≤ Real.exp (0:ℝ) ∧
    (134985/100000 : ℝ) ≤ Real.exp ((3:ℝ)/10) ∧
    (182211/100000 : ℝ) ≤ Real.exp ((3:ℝ)/5) ∧
    (245960/100000 : ℝ) ≤ Real.exp ((9:ℝ)/10) ∧
    (332011/100000 : ℝ) ≤ Real.exp ((6:ℝ)/5) ∧
    (448168/100000 : ℝ) ≤ Real.exp ((3:ℝ)/2) ∧
    (604964/100000 : ℝ) ≤ Real.exp ((9:ℝ)/5) ∧
    (816616/100000 : ℝ) ≤ Real.exp ((21:ℝ)/10) ∧
    (837289/100000 : ℝ) ≤ Real.exp ((17:ℝ)/8) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Real.exp_zero]
  · -- exp(3/10), Taylor sum of order 6 at 3/10
    exact le_exp_of_sum (x := (3:ℝ)/10) (by norm_num) 6 (by norm_num [Finset.sum_range_succ])
  · -- exp(3/5), Taylor sum of order 7 at 3/5
    exact le_exp_of_sum (x := (3:ℝ)/5) (by norm_num) 7 (by norm_num [Finset.sum_range_succ])
  · -- exp(9/10), Taylor sum of order 9 at 9/10
    exact le_exp_of_sum (x := (9:ℝ)/10) (by norm_num) 9 (by norm_num [Finset.sum_range_succ])
  · -- exp(6/5), Taylor sum of order 10 at 6/5
    exact le_exp_of_sum (x := (6:ℝ)/5) (by norm_num) 10 (by norm_num [Finset.sum_range_succ])
  · -- exp(3/2), Taylor sum of order 11 at 3/2
    exact le_exp_of_sum (x := (3:ℝ)/2) (by norm_num) 11 (by norm_num [Finset.sum_range_succ])
  · -- exp(9/5), Taylor sum of order 12 at 9/5
    exact le_exp_of_sum (x := (9:ℝ)/5) (by norm_num) 12 (by norm_num [Finset.sum_range_succ])
  · -- exp(21/10), Taylor sum of order 13 at 21/10
    exact le_exp_of_sum (x := (21:ℝ)/10) (by norm_num) 13 (by norm_num [Finset.sum_range_succ])
  · -- exp(17/8), Taylor sum of order 13 at 17/8
    exact le_exp_of_sum (x := (17:ℝ)/8) (by norm_num) 13 (by norm_num [Finset.sum_range_succ])

end Work.OffAxis.Tf72One
