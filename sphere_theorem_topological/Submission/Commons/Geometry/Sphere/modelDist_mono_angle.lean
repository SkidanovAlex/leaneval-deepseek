import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

namespace Commons.Geometry.Sphere

/-- Monotonicity of the spherical cosine expression in the angle `θ`:
`cos a cos b + sin a sin b cos θ` is antitone in `θ ∈ [0, π]` (since `sin a, sin b ≥ 0`
and `cos` is antitone there), hence so is its arccosine. -/
theorem modelDist_mono_angle {a b θ₁ θ₂ : ℝ} (ha : 0 ≤ a) (haπ : a ≤ Real.pi) (hb : 0 ≤ b)
    (hbπ : b ≤ Real.pi) (h₁ : θ₁ ∈ Set.Icc (0 : ℝ) Real.pi)
    (h₂ : θ₂ ∈ Set.Icc (0 : ℝ) Real.pi) (h : θ₁ ≤ θ₂) :
    Real.arccos (Real.cos a * Real.cos b + Real.sin a * Real.sin b * Real.cos θ₁)
      ≤ Real.arccos (Real.cos a * Real.cos b + Real.sin a * Real.sin b * Real.cos θ₂) := by
  have hsa : 0 ≤ Real.sin a := Real.sin_nonneg_of_nonneg_of_le_pi ha haπ
  have hsb : 0 ≤ Real.sin b := Real.sin_nonneg_of_nonneg_of_le_pi hb hbπ
  have hsab : 0 ≤ Real.sin a * Real.sin b := mul_nonneg hsa hsb
  have hcos : Real.cos θ₂ ≤ Real.cos θ₁ :=
    Real.cos_le_cos_of_nonneg_of_le_pi h₁.1 h₂.2 h
  have hle : Real.cos a * Real.cos b + Real.sin a * Real.sin b * Real.cos θ₂
      ≤ Real.cos a * Real.cos b + Real.sin a * Real.sin b * Real.cos θ₁ := by
    have := mul_le_mul_of_nonneg_left hcos hsab
    linarith
  exact Real.arccos_le_arccos hle

end Commons.Geometry.Sphere