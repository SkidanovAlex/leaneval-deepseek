import Mathlib

namespace Work.LinnikAreas.Density4

open scoped BigOperators

/-- Weighted Cauchy–Schwarz for a finite sum: for non-negative weights `u` and complex values `w`,
`(Σ u_n ‖w_n‖)² ≤ (Σ u_n)·(Σ u_n ‖w_n‖²)`. -/
lemma weighted_cauchy_schwarz {ι : Type*} (s : Finset ι) (u : ι → ℝ) (hu : ∀ n, 0 ≤ u n)
    (w : ι → ℂ) :
    (∑ n ∈ s, u n * ‖w n‖) ^ 2 ≤ (∑ n ∈ s, u n) * (∑ n ∈ s, u n * ‖w n‖ ^ 2) := by
  refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (r := fun n => u n * ‖w n‖) (f := u) (g := fun n => u n * ‖w n‖ ^ 2) s
    (fun n _ => hu n) (fun n _ => mul_nonneg (hu n) (sq_nonneg _)) (fun n _ => ?_)
  exact le_of_eq (by ring)

end Work.LinnikAreas.Density4
