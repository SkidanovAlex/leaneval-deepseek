import Mathlib
import Submission.Work.RPCore.Saddle.saddle_test_vector
import Submission.Work.RPCore.Saddle.lower_bound_of_test_vector

/-!
# `Work.RPCore.Saddle.fderiv_coercive_lower_bound`

Lower bound for the operator norm of the derivative of a saddle function.

`F : ℝ × (E_k × E_l) → ℝ` is uniformly `C`-close (in the operator-norm sense `hC1`) to the
linear functional `w ↦ ⟨A₁ v.1, w.2.1⟩ + ⟨A₂ v.2, w.2.2)`, where `A₁` is `lam`-negative definite
and `A₂` is `lam`-positive definite on the respective Euclidean blocks.  Then

`lam * ‖z.2‖ - C ≤ ‖fderiv ℝ F z‖`

for every `z`.  The point is that the dual (test) vector produced by `saddle_test_vector` already
witnesses `lam * ‖z.2‖ ≤ L w` with `‖w‖ ≤ 1`, so `lower_bound_of_test_vector` turns the
approximation `hC1` into a lower bound for the operator norm of `fderiv ℝ F z`.
-/

namespace Work.RPCore.Saddle

theorem fderiv_coercive_lower_bound {k l : ℕ}
    (F : ℝ × (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)) → ℝ)
    (A₁ : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (A₂ : EuclideanSpace ℝ (Fin l) →L[ℝ] EuclideanSpace ℝ (Fin l))
    (lam C : ℝ) (hlam : 0 < lam) (hC : 0 ≤ C)
    (hA₁ : ∀ x, inner ℝ (A₁ x) x ≤ -lam * ‖x‖ ^ 2)
    (hA₂ : ∀ y, lam * ‖y‖ ^ 2 ≤ inner ℝ (A₂ y) y)
    (hC1 : ∀ a v w, |fderiv ℝ F (a, v) w - (inner ℝ (A₁ v.1) w.2.1 + inner ℝ (A₂ v.2) w.2.2)| ≤ C * ‖w‖) :
    ∀ (z : ℝ × (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l))),
      lam * ‖z.2‖ - C ≤ ‖fderiv ℝ F z‖ := by
  intro z
  -- The test vector witnessing `lam * ‖z.2‖ ≤ ⟨A₁ z.2.1, ·⟩ + ⟨A₂ z.2.2, ·⟩` at a unit vector.
  obtain ⟨w, hw1, hw2⟩ := saddle_test_vector A₁ A₂ lam hlam hA₁ hA₂ z.2.1 z.2.2
  refine lower_bound_of_test_vector (fderiv ℝ F z)
    (fun w => inner ℝ (A₁ z.2.1) w.2.1 + inner ℝ (A₂ z.2.2) w.2.2) hC w hw1 ?_ ?_
  · simpa using hw2
  · simpa using hC1 z.1 z.2 w

end Work.RPCore.Saddle
