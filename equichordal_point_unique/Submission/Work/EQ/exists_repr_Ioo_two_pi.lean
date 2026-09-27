import Mathlib

namespace Work.EQ

theorem exists_repr_Ioo_two_pi {θ : ℝ} (h : Real.sin θ ≠ 0) :
    ∃ x : ℝ, ∃ k : ℤ, 0 < x ∧ x < 2 * Real.pi ∧ θ = x + k * (2 * Real.pi) ∧
      Real.sin x = Real.sin θ := by
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have h2pi_ne : (2 : ℝ) * Real.pi ≠ 0 := ne_of_gt h2pi
  set n : ℤ := ⌊θ / (2 * Real.pi)⌋ with hn
  set x : ℝ := θ - n * (2 * Real.pi) with hx
  have hθ : θ = x + n * (2 * Real.pi) := by rw [hx]; ring
  have hsin : Real.sin x = Real.sin θ := by
    rw [hθ, Real.sin_add_int_mul_two_pi]
  have hle : (n : ℝ) ≤ θ / (2 * Real.pi) := by rw [hn]; exact Int.floor_le _
  have hlt : θ / (2 * Real.pi) < (n : ℝ) + 1 := by rw [hn]; exact Int.lt_floor_add_one _
  have hmul : θ / (2 * Real.pi) * (2 * Real.pi) = θ := div_mul_cancel₀ θ h2pi_ne
  have hb1 : (n : ℝ) * (2 * Real.pi) ≤ θ := by
    have := mul_le_mul_of_nonneg_right hle h2pi.le
    rwa [hmul] at this
  have hb2 : θ < ((n : ℝ) + 1) * (2 * Real.pi) := by
    have := mul_lt_mul_of_pos_right hlt h2pi
    rwa [hmul] at this
  have hxle : 0 ≤ x := by rw [hx]; linarith
  have hxlt : x < 2 * Real.pi := by
    rw [hx]
    have hsub : ((n : ℝ) + 1) * (2 * Real.pi) - n * (2 * Real.pi) = 2 * Real.pi := by ring
    linarith
  have hxne : x ≠ 0 := by
    intro hx0
    have hz : Real.sin x = 0 := by rw [hx0]; exact Real.sin_zero
    rw [hsin] at hz
    exact h hz
  exact ⟨x, n, lt_of_le_of_ne hxle (Ne.symm hxne), hxlt, hθ, hsin⟩

end Work.EQ
