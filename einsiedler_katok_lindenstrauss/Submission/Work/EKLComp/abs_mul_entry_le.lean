import Mathlib

namespace Work.EKLComp

/-- Entrywise bound for the product of two `3 × 3` real matrices: if every entry of `A`
is bounded in absolute value by `C ≥ 0` and every entry of `B` by `η ≥ 0`, then every
entry of `A * B` is bounded by `3 * C * η`. -/
theorem abs_mul_entry_le {A B : Matrix (Fin 3) (Fin 3) ℝ} {C η : ℝ} (hC : 0 ≤ C) (hη : 0 ≤ η)
    (hA : ∀ i j, |A i j| ≤ C) (hB : ∀ i j, |B i j| ≤ η) (i j : Fin 3) :
    |(A * B) i j| ≤ 3 * C * η := by
  rw [Matrix.mul_apply]
  calc |∑ k : Fin 3, A i k * B k j| ≤ ∑ k : Fin 3, |A i k * B k j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin 3, |A i k| * |B k j| := by simp only [abs_mul]
    _ ≤ ∑ k : Fin 3, C * η :=
        Finset.sum_le_sum fun k _ => mul_le_mul (hA i k) (hB k j) (abs_nonneg _) hC
    _ = 3 * C * η := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring

end Work.EKLComp
