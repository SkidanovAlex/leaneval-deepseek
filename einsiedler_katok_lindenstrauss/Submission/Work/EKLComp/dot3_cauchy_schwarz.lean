import Mathlib
import Submission.Work.EKLComp.EucDefs

namespace Work.EKLComp

/-- Cauchy–Schwarz inequality for the hand-rolled Euclidean dot product `dot3` and norm `enorm3`
on `Fin 3 → ℝ`. -/
theorem dot3_cauchy_schwarz (x y : Fin 3 → ℝ) :
    |Work.EKLComp.dot3 x y| ≤ Work.EKLComp.enorm3 x * Work.EKLComp.enorm3 y := by
  have h1 : |∑ i, x i * y i| ≤ ∑ i, |x i| * |y i| := by
    calc |∑ i, x i * y i| ≤ ∑ i, |x i * y i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, |x i| * |y i| := by simp [abs_mul]
  have h2 : ∑ i, |x i| * |y i| ≤ Real.sqrt (∑ i, |x i| ^ 2) * Real.sqrt (∑ i, |y i| ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  have hx : ∑ i, |x i| ^ 2 = ∑ i, x i * x i := by
    apply Finset.sum_congr rfl; intro i _; rw [sq_abs]; ring
  have hy : ∑ i, |y i| ^ 2 = ∑ i, y i * y i := by
    apply Finset.sum_congr rfl; intro i _; rw [sq_abs]; ring
  calc |Work.EKLComp.dot3 x y| = |∑ i, x i * y i| := by rw [dot3]
    _ ≤ ∑ i, |x i| * |y i| := h1
    _ ≤ Real.sqrt (∑ i, x i * x i) * Real.sqrt (∑ i, y i * y i) := by
        rw [← hx, ← hy]; exact h2
    _ = enorm3 x * enorm3 y := by simp only [enorm3, dot3]

end Work.EKLComp
