import Mathlib

namespace Work.WilC4

theorem pb_not_eventually_zero {Y : Set (Fin 2 → ℝ)}
    (hdom : ∀ R : ℝ, ∃ x y : ℝ, R ≤ x ∧ ![x, y] ∈ Y)
    (σ C : ℝ) (hC : 1 ≤ C)
    (hσ : ∃ R : ℝ, ∀ x y : ℝ, R ≤ x → ![x, y] ∈ Y →
      C⁻¹ * x ^ σ ≤ |y| ∧ |y| ≤ C * x ^ σ) :
    ¬ (∃ R : ℝ, ∀ x y : ℝ, R ≤ x → ![x, y] ∈ Y → y = 0) := by
  rintro ⟨R₁, h₁⟩
  obtain ⟨R₂, h₂⟩ := hσ
  obtain ⟨x, y, hx, hxY⟩ := hdom (max (max R₁ R₂) 1)
  have hR₁ : R₁ ≤ x :=
    le_trans (le_trans (le_max_left R₁ R₂) (le_max_left (max R₁ R₂) 1)) hx
  have hR₂ : R₂ ≤ x :=
    le_trans (le_trans (le_max_right R₁ R₂) (le_max_left (max R₁ R₂) 1)) hx
  have hx1 : (1 : ℝ) ≤ x := le_trans (le_max_right (max R₁ R₂) 1) hx
  have hzero : y = 0 := h₁ x y hR₁ hxY
  have hbound : C⁻¹ * x ^ σ ≤ |y| := (h₂ x y hR₂ hxY).1
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hxpos : 0 < x ^ σ := Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hx1) σ
  have hpos : 0 < C⁻¹ * x ^ σ := mul_pos (inv_pos.mpr hCpos) hxpos
  have hgt : 0 < |y| := lt_of_lt_of_le hpos hbound
  rw [hzero, abs_zero] at hgt
  exact lt_irrefl 0 hgt

end Work.WilC4
