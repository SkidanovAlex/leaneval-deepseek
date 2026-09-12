import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Commons.Analysis.InnerProductSpace

open scoped BigOperators

set_option autoImplicit false

/-- If every coordinate of a vector `x : EuclideanSpace ℝ (Fin n)` is bounded by `M` in
absolute value, then `‖x‖ ≤ sqrt n * M`.  (Euclidean norm versus sup norm on coordinates.) -/
theorem norm_le_sqrt_card_mul_of_abs_le {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) {M : ℝ}
    (hM : 0 ≤ M) (h : ∀ i : Fin n, |x i| ≤ M) : ‖x‖ ≤ Real.sqrt n * M := by
  have hsum : (∑ i : Fin n, (x i) ^ 2) ≤ (Real.sqrt n * M) ^ 2 := by
    calc (∑ i : Fin n, (x i) ^ 2) ≤ ∑ _i : Fin n, M ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          rw [← sq_abs (x i)]
          nlinarith [h i, abs_nonneg (x i), hM]
      _ = n * M ^ 2 := by simp
      _ = (Real.sqrt n * M) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  have hsq : ‖x‖ ^ 2 ≤ (Real.sqrt n * M) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact hsum
  have h3 : 0 ≤ Real.sqrt n * M := mul_nonneg (Real.sqrt_nonneg n) hM
  have := (sq_le_sq.mp hsq)
  rwa [abs_of_nonneg (norm_nonneg x), abs_of_nonneg h3] at this

end Commons.Analysis.InnerProductSpace