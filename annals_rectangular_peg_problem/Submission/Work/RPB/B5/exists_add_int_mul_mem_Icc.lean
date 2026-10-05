import Mathlib

namespace Work.RPB.B5

/-- Reduction of an arbitrary real modulo a positive period: every `t` is `t₀ + k*T` with
`0 ≤ t₀ ≤ T` and `k : ℤ`. -/
theorem exists_add_int_mul_mem_Icc (t T : ℝ) (hT : 0 < T) :
    ∃ (t₀ : ℝ) (k : ℤ), t₀ ∈ Set.Icc (0:ℝ) T ∧ t = t₀ + k * T := by
  set m : ℤ := ⌊t / T⌋ with hm
  refine ⟨t - m * T, m, ?_, by ring⟩
  rw [Set.mem_Icc]
  have hTne : T ≠ 0 := ne_of_gt hT
  constructor
  · have h1 : (m : ℝ) ≤ t / T := by
      rw [hm]; exact Int.floor_le _
    have h2 : (m : ℝ) * T ≤ t / T * T := mul_le_mul_of_nonneg_right h1 (le_of_lt hT)
    rw [div_mul_cancel₀ t hTne] at h2
    linarith
  · have h1 : t / T < (m : ℝ) + 1 := by
      rw [hm]; exact Int.lt_floor_add_one _
    have h2 : t / T * T < ((m : ℝ) + 1) * T := mul_lt_mul_of_pos_right h1 hT
    rw [div_mul_cancel₀ t hTne] at h2
    linarith

end Work.RPB.B5
