import Mathlib

namespace Work.LinnikAreas.Density4

lemma exists_bound_of_eventually_mono (F : ℕ → ℝ)
    (hmono : ∀ ⦃a b : ℕ⦄, a ≤ b → F a ≤ F b) (M : ℕ)
    (hM : ∀ N : ℕ, M ≤ N → F N ≤ (N : ℝ) * Real.log (N : ℝ) + (N : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      F N ≤ (N : ℝ) * Real.log (N : ℝ) + C * (N : ℝ) := by
  refine ⟨max 1 (|F M| + 1), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro N hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le zero_lt_one hN1
  have hlog : 0 ≤ (N : ℝ) * Real.log (N : ℝ) :=
    mul_nonneg (Nat.cast_nonneg N) (Real.log_nonneg hN1)
  have hCpos : (0 : ℝ) < max 1 (|F M| + 1) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  by_cases hNM : N < M
  · have hFN : F N ≤ F M := hmono (le_of_lt hNM)
    have hFM : F M ≤ max 1 (|F M| + 1) := by
      have h1 : F M ≤ |F M| := le_abs_self (F M)
      have h2 : |F M| ≤ |F M| + 1 := le_add_of_nonneg_right zero_le_one
      exact le_trans h1 (le_trans h2 (le_max_right _ _))
    have hCN : max 1 (|F M| + 1) ≤ (max 1 (|F M| + 1)) * (N : ℝ) := by
      have := mul_le_mul_of_nonneg_left hN1 (le_of_lt hCpos)
      simpa using this
    calc F N ≤ F M := hFN
      _ ≤ max 1 (|F M| + 1) := hFM
      _ ≤ (max 1 (|F M| + 1)) * (N : ℝ) := hCN
      _ ≤ (N : ℝ) * Real.log (N : ℝ) + (max 1 (|F M| + 1)) * (N : ℝ) := by
          linarith [hlog]
  · have hMN : M ≤ N := by omega
    have hle : (N : ℝ) ≤ (max 1 (|F M| + 1)) * (N : ℝ) := by
      have := mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) (|F M| + 1)) (le_of_lt hNpos)
      simpa using this
    have := hM N hMN
    linarith [this, hle]

end Work.LinnikAreas.Density4
