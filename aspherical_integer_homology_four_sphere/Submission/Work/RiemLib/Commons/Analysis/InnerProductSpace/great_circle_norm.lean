import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Commons.Analysis.InnerProductSpace

/-- **Great-circle parametrisation is unit-speed along the sphere.**

If `P₁`, `P₂` are unit vectors in a real inner product space with
`⟪P₁, P₂⟫ = cos Φ` (so that `Φ` is the angle between them) and `0 < Φ < π`,
then for every `s` the point
`(sin ((1 - s) Φ) / sin Φ) • P₁ + (sin (s Φ) / sin Φ) • P₂`
lies on the unit sphere.  This is the geodesic (great-circle) interpolation
between `P₁` and `P₂`. -/
theorem great_circle_norm {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (P₁ P₂ : F) (Φ s : ℝ) (h1 : norm P₁ = 1) (h2 : norm P₂ = 1)
    (hΦ0 : 0 < Φ) (hΦπ : Φ < Real.pi) (hcos : inner ℝ P₁ P₂ = Real.cos Φ) :
    norm ((Real.sin ((1 - s) * Φ) / Real.sin Φ) • P₁
        + (Real.sin (s * Φ) / Real.sin Φ) • P₂) = 1 := by
  have hsinΦ : Real.sin Φ ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hΦ0 hΦπ)
  set a : ℝ := Real.sin ((1 - s) * Φ) / Real.sin Φ with ha
  set b : ℝ := Real.sin (s * Φ) / Real.sin Φ with hb
  have hsq : ‖a • P₁ + b • P₂‖ ^ 2 = 1 := by
    have hA : ‖a • P₁‖ ^ 2 = a ^ 2 := by
      rw [norm_smul, h1, mul_one, Real.norm_eq_abs, sq_abs]
    have hB : ‖b • P₂‖ ^ 2 = b ^ 2 := by
      rw [norm_smul, h2, mul_one, Real.norm_eq_abs, sq_abs]
    have hI : inner ℝ (a • P₁) (b • P₂) = a * b * Real.cos Φ := by
      rw [real_inner_smul_left, real_inner_smul_right, hcos]
      ring
    rw [norm_add_sq_real, hA, hB, hI]
    have ht : a ^ 2 + 2 * (a * b * Real.cos Φ) + b ^ 2 = 1 := by
      rw [ha, hb]
      have hu : (1 - s) * Φ + s * Φ = Φ := by ring
      have hcosΦ : Real.cos Φ = Real.cos ((1 - s) * Φ) * Real.cos (s * Φ)
          - Real.sin ((1 - s) * Φ) * Real.sin (s * Φ) := by
        conv_lhs => rw [← hu]
        rw [Real.cos_add]
      have hsinΦ' : Real.sin Φ = Real.sin ((1 - s) * Φ) * Real.cos (s * Φ)
          + Real.cos ((1 - s) * Φ) * Real.sin (s * Φ) := by
        conv_lhs => rw [← hu]
        rw [Real.sin_add]
      field_simp
      rw [hcosΦ, hsinΦ']
      nlinarith [Real.sin_sq_add_cos_sq ((1 - s) * Φ), Real.sin_sq_add_cos_sq (s * Φ)]
    linarith
  rcases sq_eq_one_iff.mp hsq with h | h
  · exact h
  · nlinarith [norm_nonneg (a • P₁ + b • P₂)]

end Commons.Analysis.InnerProductSpace