import Mathlib
import Submission.Work.HP.LsetAux.GridDefs

namespace Work.HP.LsetAux

/-- The Euclidean norm of a vector whose coordinates are bounded by `a` in absolute value is at
most `√(card ι) · a`. -/
theorem rNorm_le_sqrt_card_mul {ι : Type*} [Fintype ι] {u : ι → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ i, |u i| ≤ a) :
    Work.HP.rNorm u ≤ Real.sqrt (Fintype.card ι) * a := by
  have hsum : ∑ i, u i ^ 2 ≤ (Fintype.card ι : ℝ) * a ^ 2 := by
    calc ∑ i, u i ^ 2 ≤ ∑ _i : ι, a ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [sq_le_sq, abs_of_nonneg ha]
          exact h i
      _ = (Fintype.card ι : ℝ) * a ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (0 : ℝ) ≤ Fintype.card ι := by positivity
  calc Work.HP.rNorm u = Real.sqrt (∑ i, u i ^ 2) := rfl
    _ ≤ Real.sqrt ((Fintype.card ι : ℝ) * a ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (Fintype.card ι) * a := by
        rw [Real.sqrt_mul hcard, Real.sqrt_sq ha]

end Work.HP.LsetAux
