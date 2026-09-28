import Mathlib

/-!
# `B` is at most a constant times `A log A` when `A ≥ B/log B` and `A ≤ B²`

Under the standing assumptions of the second-moment estimates (`B₀ ≤ B`, `B / log B ≤ A`,
`A ≤ B²`) we have `B ≤ C A (log A + 1)` for a constant `C` depending only on `B₀`.

Indeed `B ≤ A log B` (from `A ≥ B/log B`) and, when `log B ≥ 16` (so that `B` is large),
`log B ≤ log A + log log B ≤ log A + log B/2`, whence `log B ≤ 2 log A`.  In the remaining
case `B` is bounded and the claim is trivial.
-/

set_option autoImplicit false

namespace Work.HP.Sig2

theorem le_mul_log_of_div_log_le (B₀ : ℝ) (hB₀ : 1 < B₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ A B : ℝ, B₀ ≤ B → B / Real.log B ≤ A → A ≤ B ^ 2 →
      B ≤ C * A * (Real.log A + 1) := by
  refine ⟨max 4 (Real.exp 16), ?_, ?_⟩
  · exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4) (le_max_left 4 (Real.exp 16))
  · intro A B hB hA hAB
    have hB1 : 1 < B := lt_of_lt_of_le hB₀ hB
    have hBpos : 0 < B := lt_trans zero_lt_one hB1
    have hlogBpos : 0 < Real.log B := Real.log_pos hB1
    have h1 : B ≤ A * Real.log B := by
      have h := (div_le_iff₀ hlogBpos).mp hA
      linarith
    have hApos : 0 < A := by
      have h2 : 0 < B / Real.log B := div_pos hBpos hlogBpos
      linarith
    have hA1 : 1 ≤ A := by
      have hlogB_lt : Real.log B < B := by
        have h := Real.log_lt_sub_one_of_pos hBpos (ne_of_gt hB1)
        linarith
      have h2 : (1 : ℝ) < B / Real.log B := by
        rw [lt_div_iff₀ hlogBpos]
        linarith
      linarith
    have hlogAnn : (0 : ℝ) ≤ Real.log A := Real.log_nonneg hA1
    have hlogA1 : (0 : ℝ) ≤ Real.log A + 1 := by linarith
    have hCpos : (0 : ℝ) < max 4 (Real.exp 16) :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4) (le_max_left 4 (Real.exp 16))
    rcases lt_or_ge (Real.log B) 16 with h16 | h16
    · -- `B` is bounded
      have hBlt : B < Real.exp 16 := by
        have h := Real.exp_lt_exp.mpr h16
        rwa [Real.exp_log hBpos] at h
      have hCle : Real.exp 16 ≤ max 4 (Real.exp 16) := le_max_right _ _
      have hAlog : (1 : ℝ) ≤ A * (Real.log A + 1) := by nlinarith [hA1, hlogA1]
      calc B ≤ Real.exp 16 := le_of_lt hBlt
        _ ≤ max 4 (Real.exp 16) := hCle
        _ = max 4 (Real.exp 16) * 1 := by ring
        _ ≤ max 4 (Real.exp 16) * (A * (Real.log A + 1)) :=
            mul_le_mul_of_nonneg_left hAlog (le_of_lt hCpos)
        _ = max 4 (Real.exp 16) * A * (Real.log A + 1) := by ring
    · -- `B` is large
      have h2 : Real.log B ≤ Real.log A + Real.log (Real.log B) := by
        have h := Real.log_le_log hBpos h1
        rwa [Real.log_mul (ne_of_gt hApos) (ne_of_gt hlogBpos)] at h
      have h3 : Real.log (Real.log B) ≤ Real.log B / 2 := by
        have h := Real.log_le_rpow_div (le_of_lt hlogBpos) (by norm_num : (0 : ℝ) < 1 / 2)
        have h' : Real.log (Real.log B) ≤ Real.sqrt (Real.log B) / (1 / 2) := by
          simpa [Real.sqrt_eq_rpow] using h
        have hsq : (Real.sqrt (Real.log B)) ^ 2 = Real.log B :=
          Real.sq_sqrt (le_of_lt hlogBpos)
        have hsn : (0 : ℝ) ≤ Real.sqrt (Real.log B) := Real.sqrt_nonneg _
        have hhalf : Real.sqrt (Real.log B) / (1 / 2) ≤ Real.log B / 2 := by
          rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 2)]
          nlinarith [hsq, hsn, h16]
        exact le_trans h' hhalf
      have h5 : Real.log B ≤ 2 * Real.log A := by linarith
      have hC2 : (2 : ℝ) ≤ max 4 (Real.exp 16) := le_trans (by norm_num) (le_max_left _ _)
      have hAn : (0 : ℝ) ≤ A := le_of_lt hApos
      calc B ≤ A * Real.log B := h1
        _ ≤ A * (2 * Real.log A) := by nlinarith [hApos, h5]
        _ = (2 : ℝ) * A * Real.log A := by ring
        _ ≤ max 4 (Real.exp 16) * A * Real.log A := by
            apply mul_le_mul_of_nonneg_right _ hlogAnn
            exact mul_le_mul_of_nonneg_right hC2 hAn
        _ ≤ max 4 (Real.exp 16) * A * (Real.log A + 1) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            linarith

end Work.HP.Sig2
