import Mathlib

namespace Work.A7

/-- Evaluation bound for a real polynomial: `|p.eval t|` is at most the sum of the absolute
values of the coefficients of `p` times `(max 1 |t|) ^ p.natDegree`, with no hypothesis on `t`.
Route: `Polynomial.eval_eq_sum_range`, the triangle inequality, `|t| ^ i ≤ (max 1 |t|) ^ i`
(because `|t| ≤ max 1 |t|`), `(max 1 |t|) ^ i ≤ (max 1 |t|) ^ p.natDegree` for `i ≤ p.natDegree`
(because `1 ≤ max 1 |t|`), and `Finset.sum_mul`. -/
theorem poly_eval_abs_le_coeffSum (p : Polynomial ℝ) (t : ℝ) :
    |p.eval t| ≤ (Finset.sum (Finset.range (p.natDegree + 1)) (fun i => |p.coeff i|)) *
      (max 1 |t|) ^ p.natDegree := by
  set M := max 1 |t| with hM
  have hM1 : (1 : ℝ) ≤ M := le_max_left _ _
  have hMt : |t| ≤ M := le_max_right _ _
  calc |p.eval t|
      = |∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * t ^ i| := by
        rw [Polynomial.eval_eq_sum_range]
    _ ≤ ∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i| * M ^ p.natDegree := by
        refine le_trans (Finset.abs_sum_le_sum_abs (fun i => p.coeff i * t ^ i) _) ?_
        refine Finset.sum_le_sum ?_
        intro i hi
        have hi' : i ≤ p.natDegree := by
          have := Finset.mem_range.mp hi
          omega
        rw [abs_mul, abs_pow]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        exact le_trans (pow_le_pow_left₀ (abs_nonneg t) hMt i) (pow_le_pow_right₀ hM1 hi')
    _ = (∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i|) * M ^ p.natDegree := by
        rw [Finset.sum_mul]

end Work.A7
