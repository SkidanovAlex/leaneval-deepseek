import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Commons.Analysis.InnerProductSpace

/-- The elementary trigonometric identity behind the great-circle norm computation:
`cos²v + cos²u - 2 cos v cos u cos(u+v) = sin²(u+v)`. -/
private lemma trig_cos_sq (u v : ℝ) :
    (Real.cos v)^2 + (Real.cos u)^2 - 2*Real.cos v*Real.cos u*Real.cos (u+v)
      = (Real.sin (u+v))^2 := by
  rw [Real.cos_add, Real.sin_add]
  nlinarith [Real.cos_sq_add_sin_sq u, Real.cos_sq_add_sin_sq v]

/-- Expansion of the squared norm of a linear combination of two vectors in a real
inner product space. -/
private lemma norm_sq_smul_add_smul {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (P Q : F) (a b : ℝ) :
    ‖a • P + b • Q‖ ^ 2 = a^2 * ‖P‖^2 + 2*a*b*inner ℝ P Q + b^2 * ‖Q‖^2 := by
  rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs]
  ring

theorem great_circle_orth_norm {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (P₁ P₂ : F) (Φ s : ℝ) (h1 : norm P₁ = 1) (h2 : norm P₂ = 1)
    (hcos : inner ℝ P₁ P₂ = Real.cos Φ) :
    norm ((-Real.cos ((1 - s) * Φ)) • P₁ + (Real.cos (s * Φ)) • P₂) = norm (Real.sin Φ) := by
  set L : F := (-Real.cos ((1 - s) * Φ)) • P₁ + (Real.cos (s * Φ)) • P₂ with hL
  have hnorm : ‖L‖ ^ 2 = (Real.sin Φ) ^ 2 := by
    rw [hL, norm_sq_smul_add_smul, h1, h2, hcos]
    have harg : s * Φ + (1 - s) * Φ = Φ := by ring
    have h := trig_cos_sq (s * Φ) ((1 - s) * Φ)
    rw [harg] at h
    linarith [h]
  have hL' : ‖L‖ = Real.sqrt (‖L‖^2) := (Real.sqrt_sq (norm_nonneg _)).symm
  have hR' : ‖Real.sin Φ‖ = Real.sqrt ((Real.sin Φ)^2) := by
    rw [Real.norm_eq_abs, Real.sqrt_sq_eq_abs]
  rw [hL, hL', hR', hnorm]

end Commons.Analysis.InnerProductSpace