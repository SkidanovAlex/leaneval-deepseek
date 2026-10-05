import Mathlib

namespace Work.RPCore.Flow

theorem smooth_cutoff : ∃ c : ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) c ∧ (∀ t ∈ Set.Icc (-1 : ℝ) 2, c t = 1) ∧ (∀ t, 0 ≤ c t ∧ c t ≤ 1) ∧ (∀ t, t ≤ -2 → c t = 0) ∧ (∀ t, 3 ≤ t → c t = 0) := by
  refine ⟨fun t => Real.smoothTransition (t + 2) * Real.smoothTransition (3 - t),
    ?_, ?_, ?_, ?_, ?_⟩
  · fun_prop
  · intro t ht
    change Real.smoothTransition (t + 2) * Real.smoothTransition (3 - t) = 1
    simp only [Set.mem_Icc] at ht
    rw [Real.smoothTransition.one_of_one_le (by linarith : (1:ℝ) ≤ t + 2),
        Real.smoothTransition.one_of_one_le (by linarith : (1:ℝ) ≤ 3 - t), mul_one]
  · intro t
    refine ⟨mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _), ?_⟩
    calc Real.smoothTransition (t + 2) * Real.smoothTransition (3 - t)
        ≤ 1 * Real.smoothTransition (3 - t) :=
          mul_le_mul_of_nonneg_right (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
      _ = Real.smoothTransition (3 - t) := one_mul _
      _ ≤ 1 := Real.smoothTransition.le_one _
  · intro t ht
    change Real.smoothTransition (t + 2) * Real.smoothTransition (3 - t) = 0
    rw [Real.smoothTransition.zero_of_nonpos (by linarith : t + 2 ≤ 0), zero_mul]
  · intro t ht
    change Real.smoothTransition (t + 2) * Real.smoothTransition (3 - t) = 0
    rw [Real.smoothTransition.zero_of_nonpos (by linarith : 3 - t ≤ 0), mul_zero]

end Work.RPCore.Flow
