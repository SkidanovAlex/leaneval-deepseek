import Mathlib

namespace Work.Peluse.LadderP

theorem stepConstants (j n s' e₅₁ : ℕ) (hs' : 1 ≤ s') (he₅₁ : 1 ≤ e₅₁)
    {C₅₁ C_s : ℝ} (hC₅₁ : 0 < C₅₁) (hC₅₁' : C₅₁ ≤ 1) (hC_s : 0 < C_s) :
    ∃ (e : ℕ) (C cη : ℝ), 1 ≤ e ∧ 0 < C ∧ C ≤ 1 ∧ 0 < cη ∧ cη ≤ 1 ∧
      e ≥ 2^(2^(j+1) - 1 + n) * (1 + 2 * e₅₁) * e₅₁ ∧
      e ≥ 2^(2^(j+1) - 1 + n + 1) * e₅₁ + 1 ∧
      e ≥ 2^(2^(j+1) - 1 + n) * (1 + e₅₁ * 2^s') ∧
      C ≤ C₅₁ * cη ^ e₅₁ / 4 ^ ((1 + 2 * e₅₁) * e₅₁) ∧
      cη ≤ C₅₁ ∧
      C * Real.log ((j:ℝ) + 2) ≤ cη / 4 ^ (2 * e₅₁) ∧
      2 * C_s * cη ≤ C₅₁ ∧
      C ≤ 2 * C₅₁ ^ (2^s') / 4 ^ (1 + e₅₁ * 2^s') := by
  -- Step 1: choose a suitable (small, positive) cη.
  obtain ⟨cη, hcη₁, hcη₂, hcη₃, hcη₄⟩ :
      ∃ cη : ℝ, 0 < cη ∧ cη ≤ 1 ∧ cη ≤ C₅₁ ∧ 2 * C_s * cη ≤ C₅₁ := by
    refine ⟨min 1 (min C₅₁ (C₅₁ / (2 * C_s))), ?_, ?_, ?_, ?_⟩
    · exact lt_min one_pos (lt_min hC₅₁ (div_pos hC₅₁ (by linarith)))
    · exact min_le_left _ _
    · exact le_trans (min_le_right _ _) (min_le_left _ _)
    · have hle : min 1 (min C₅₁ (C₅₁ / (2 * C_s))) ≤ C₅₁ / (2 * C_s) :=
        le_trans (min_le_right _ _) (min_le_right _ _)
      have h2 : (0 : ℝ) < 2 * C_s := by linarith
      calc 2 * C_s * min 1 (min C₅₁ (C₅₁ / (2 * C_s)))
          ≤ 2 * C_s * (C₅₁ / (2 * C_s)) := mul_le_mul_of_nonneg_left hle (le_of_lt h2)
        _ = C₅₁ := by
            rw [mul_comm (2 * C_s) (C₅₁ / (2 * C_s))]
            exact div_mul_cancel₀ C₅₁ (ne_of_gt h2)
  -- Step 2: the three positive upper bounds for C, their minimum M, and C = M/2.
  let A1 : ℝ := C₅₁ * cη ^ e₅₁ / 4 ^ ((1 + 2 * e₅₁) * e₅₁)
  let A2 : ℝ := cη / (4 ^ (2 * e₅₁) * Real.log ((j : ℝ) + 2))
  let A3 : ℝ := 2 * C₅₁ ^ (2 ^ s') / 4 ^ (1 + e₅₁ * 2 ^ s')
  let M : ℝ := min 1 (min A1 (min A2 A3))
  let C : ℝ := (1 / 2) * M
  have hA1pos : 0 < A1 := by
    show (0 : ℝ) < C₅₁ * cη ^ e₅₁ / 4 ^ ((1 + 2 * e₅₁) * e₅₁)
    exact div_pos (mul_pos hC₅₁ (pow_pos hcη₁ _)) (pow_pos (by norm_num : (0:ℝ) < 4) _)
  have hlogpos : 0 < Real.log ((j : ℝ) + 2) := by
    apply Real.log_pos
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hA2pos : 0 < A2 := by
    show (0 : ℝ) < cη / (4 ^ (2 * e₅₁) * Real.log ((j : ℝ) + 2))
    exact div_pos hcη₁ (mul_pos (pow_pos (by norm_num : (0:ℝ) < 4) _) hlogpos)
  have hA3pos : 0 < A3 := by
    show (0 : ℝ) < 2 * C₅₁ ^ (2 ^ s') / 4 ^ (1 + e₅₁ * 2 ^ s')
    exact div_pos (mul_pos (by norm_num : (0:ℝ) < 2) (pow_pos hC₅₁ _))
      (pow_pos (by norm_num : (0:ℝ) < 4) _)
  have hMpos : 0 < M := by
    show (0 : ℝ) < min 1 (min A1 (min A2 A3))
    exact lt_min one_pos (lt_min hA1pos (lt_min hA2pos hA3pos))
  have hMle1 : M ≤ 1 := by
    show min 1 (min A1 (min A2 A3)) ≤ 1
    exact min_le_left _ _
  have hMleA1 : M ≤ A1 := by
    show min 1 (min A1 (min A2 A3)) ≤ A1
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hMleA2 : M ≤ A2 := by
    show min 1 (min A1 (min A2 A3)) ≤ A2
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hMleA3 : M ≤ A3 := by
    show min 1 (min A1 (min A2 A3)) ≤ A3
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hCleM : C ≤ M := by
    show (1 / 2) * M ≤ M
    linarith [hMpos]
  -- Step 3: choose e as the maximum of the three prescribed lower bounds.
  let B1 : ℕ := 2 ^ (2 ^ (j + 1) - 1 + n) * (1 + 2 * e₅₁) * e₅₁
  let B2 : ℕ := 2 ^ (2 ^ (j + 1) - 1 + n + 1) * e₅₁ + 1
  let B3 : ℕ := 2 ^ (2 ^ (j + 1) - 1 + n) * (1 + e₅₁ * 2 ^ s')
  let e : ℕ := max B1 (max B2 B3)
  have hB2ge1 : 1 ≤ B2 := by
    show 1 ≤ 2 ^ (2 ^ (j + 1) - 1 + n + 1) * e₅₁ + 1
    exact Nat.le_add_left 1 _
  refine ⟨e, C, cη, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show 1 ≤ e
    exact le_trans hB2ge1 (le_trans (le_max_left _ _) (le_max_right _ _))
  · show 0 < C
    exact mul_pos (by norm_num : (0:ℝ) < 1/2) hMpos
  · show C ≤ 1
    exact le_trans hCleM hMle1
  · exact hcη₁
  · exact hcη₂
  · show B1 ≤ e
    exact le_max_left _ _
  · show B2 ≤ e
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  · show B3 ≤ e
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  · show C ≤ C₅₁ * cη ^ e₅₁ / 4 ^ ((1 + 2 * e₅₁) * e₅₁)
    exact le_trans hCleM hMleA1
  · exact hcη₃
  · show C * Real.log ((j : ℝ) + 2) ≤ cη / 4 ^ (2 * e₅₁)
    have h1 : C ≤ A2 := le_trans hCleM hMleA2
    have h2 : C * Real.log ((j : ℝ) + 2) ≤ A2 * Real.log ((j : ℝ) + 2) :=
      mul_le_mul_of_nonneg_right h1 (le_of_lt hlogpos)
    have h3 : A2 * Real.log ((j : ℝ) + 2) = cη / 4 ^ (2 * e₅₁) := by
      show cη / (4 ^ (2 * e₅₁) * Real.log ((j : ℝ) + 2)) * Real.log ((j : ℝ) + 2)
            = cη / 4 ^ (2 * e₅₁)
      rw [div_mul_eq_mul_div]
      exact mul_div_mul_right cη (4 ^ (2 * e₅₁)) (ne_of_gt hlogpos)
    linarith [h2, h3]
  · exact hcη₄
  · show C ≤ 2 * C₅₁ ^ (2 ^ s') / 4 ^ (1 + e₅₁ * 2 ^ s')
    exact le_trans hCleM hMleA3

end Work.Peluse.LadderP
