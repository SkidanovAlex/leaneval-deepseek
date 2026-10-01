import Mathlib

namespace Work.ZeroFreeTables

theorem chiMulNeFacts {q : ℕ} (χ₁ χ₂ : DirichletCharacter ℂ q)
    (hχ₁ : χ₁ * χ₁ = 1) (h₂1 : χ₂ ≠ 1) (h₂₁ : χ₂ ≠ χ₁)
    (h₂₂ : χ₂ * χ₂ ≠ 1) (h₁₂₂ : χ₁ * (χ₂ * χ₂) ≠ 1) :
    (χ₁ * χ₂ ≠ 1) ∧ (χ₁ * χ₂ ≠ χ₁) ∧ (χ₁ * χ₂ ≠ χ₁⁻¹) ∧
      (χ₂ * χ₂ ≠ χ₁) ∧ (χ₂ * χ₂ ≠ χ₁⁻¹) ∧
      (χ₁ * (χ₂ * χ₂) ≠ χ₁) ∧ (χ₁ * (χ₂ * χ₂) ≠ χ₁⁻¹) := by
  have hχ₁inv : χ₁⁻¹ = χ₁ := inv_eq_of_mul_eq_one_right hχ₁
  have hab_ne_one : χ₁ * χ₂ ≠ 1 := by
    intro h
    exact h₂₁ (by rw [← mul_eq_one_iff_inv_eq.mp h, hχ₁inv])
  have hab_ne_a : χ₁ * χ₂ ≠ χ₁ := by
    intro h
    exact h₂1 (mul_left_cancel (show χ₁ * χ₂ = χ₁ * 1 by rw [h, mul_one]))
  have hbb_ne_a : χ₂ * χ₂ ≠ χ₁ := by
    intro h
    exact h₁₂₂ (by rw [h, hχ₁])
  have habb_ne_a : χ₁ * (χ₂ * χ₂) ≠ χ₁ := by
    intro h
    exact h₂₂ (mul_left_cancel (show χ₁ * (χ₂ * χ₂) = χ₁ * 1 by rw [h, mul_one]))
  exact ⟨hab_ne_one, hab_ne_a, by rw [hχ₁inv]; exact hab_ne_a,
    hbb_ne_a, by rw [hχ₁inv]; exact hbb_ne_a,
    habb_ne_a, by rw [hχ₁inv]; exact habb_ne_a⟩

end Work.ZeroFreeTables
