import Mathlib
import Submission.Work.ZeroDensity.LogFree.HB7WeightSeries

namespace Work.ZeroDensity.LogFree

/-- The weight series of Heath-Brown (1992), §7 restricted to its "undamped" doubly-exponential
factor `exp(-exp(-(j+1)η)) * exp(-2 a j η)`, is summable over `ℤ` when `1 ≤ η` and
`1 ≤ 2 a η ≤ 2`.

This is obtained by splitting the `ℤ`-indexed series into its nonnegative part `j = n`,
which is the positive-half weight `HB7P η (2 a η)`, and its negative part `j = -(n+1)`,
which is the negative-half weight `HB7N η (2 a η)`; both halves are summable by
`HB7PosBound` and `HB7NegBound`. -/
theorem HB7WeightSeriesSummable {η a : ℝ} (hη : 1 ≤ η) (hlo : 1 ≤ 2 * a * η) (hhi : 2 * a * η ≤ 2) :
    Summable (fun j : ℤ => Real.exp (-(Real.exp (-(((j : ℝ) + 1) * η))))
      * Real.exp (-(2 * a * (j : ℝ) * η))) := by
  -- The nonnegative half `j = n` is exactly `HB7P η (2 a η)`.
  have hpos : (fun n : ℕ => (fun j : ℤ => Real.exp (-(Real.exp (-(((j : ℝ) + 1) * η))))
      * Real.exp (-(2 * a * (j : ℝ) * η))) (n : ℤ)) = HB7P η (2 * a * η) := by
    funext n
    rw [HB7P_eq_exp]
    push_cast
    rw [← Real.exp_add]
    congr 1
    ring_nf
  -- The negative half `j = -(n+1)` is exactly `HB7N η (2 a η)`.
  have hneg : (fun n : ℕ => (fun j : ℤ => Real.exp (-(Real.exp (-(((j : ℝ) + 1) * η))))
      * Real.exp (-(2 * a * (j : ℝ) * η))) (-((n : ℤ) + 1))) = HB7N η (2 * a * η) := by
    funext n
    rw [HB7N_eq_exp]
    push_cast
    rw [← Real.exp_add]
    congr 1
    ring_nf
  apply Summable.of_nat_of_neg_add_one
  · rw [hpos]; exact (HB7PosBound η (2 * a * η) hlo).1
  · rw [hneg]; exact (HB7NegBound hη hlo hhi).1

end Work.ZeroDensity.LogFree
