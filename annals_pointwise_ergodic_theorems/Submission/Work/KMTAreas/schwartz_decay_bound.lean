import Mathlib

namespace Work.KMTAreas

/-- A Schwartz function on `ℝ` is bounded by a constant times `(1 + |t|) ^ (-2)`. -/
theorem schwartz_decay_bound (φ : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖(φ : ℝ → ℂ) t‖ ≤ C / (1 + |t|) ^ 2 := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := φ.decay 0 0
  obtain ⟨C₂, hC₂pos, hC₂⟩ := φ.decay 2 0
  simp only [norm_iteratedFDeriv_zero, pow_zero, one_mul] at hC₀
  simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at hC₂
  refine ⟨2 * (C₀ + C₂), by positivity, fun t => ?_⟩
  have hd : 0 < (1 + |t|) ^ 2 := by positivity
  rw [le_div_iff₀ hd]
  have h1 : ‖(φ : ℝ → ℂ) t‖ ≤ C₀ := hC₀ t
  have h2 : ‖(φ : ℝ → ℂ) t‖ * |t| ^ 2 ≤ C₂ := by
    have := hC₂ t
    linarith [show |t| ^ 2 * ‖(φ : ℝ → ℂ) t‖ = ‖(φ : ℝ → ℂ) t‖ * |t| ^ 2 from by ring]
  have h3 : ‖(φ : ℝ → ℂ) t‖ * (1 + |t| ^ 2) ≤ C₀ + C₂ := by
    nlinarith [h1, h2, norm_nonneg ((φ : ℝ → ℂ) t)]
  have h4 : (1 + |t|) ^ 2 ≤ 2 * (1 + |t| ^ 2) := by
    nlinarith [sq_nonneg (|t| - 1), abs_nonneg t]
  calc ‖(φ : ℝ → ℂ) t‖ * (1 + |t|) ^ 2
      ≤ ‖(φ : ℝ → ℂ) t‖ * (2 * (1 + |t| ^ 2)) :=
        mul_le_mul_of_nonneg_left h4 (norm_nonneg _)
    _ ≤ 2 * (C₀ + C₂) := by nlinarith [h3, norm_nonneg ((φ : ℝ → ℂ) t)]

end Work.KMTAreas
