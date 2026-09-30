import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Commons.Geometry.Sphere

theorem modelDist_cos {a b θ : ℝ} (ha : 0 ≤ a) (haπ : a ≤ Real.pi) (hb : 0 ≤ b)
    (hbπ : b ≤ Real.pi) (hθ : 0 ≤ θ) (hθπ : θ ≤ Real.pi) :
    Real.cos (Real.arccos (Real.cos a * Real.cos b + Real.sin a * Real.sin b * Real.cos θ))
      = Real.cos a * Real.cos b + Real.sin a * Real.sin b * Real.cos θ := by
  have hsa : 0 ≤ Real.sin a := Real.sin_nonneg_of_nonneg_of_le_pi ha haπ
  have hsb : 0 ≤ Real.sin b := Real.sin_nonneg_of_nonneg_of_le_pi hb hbπ
  have hsab : 0 ≤ Real.sin a * Real.sin b := mul_nonneg hsa hsb
  have hupper : Real.cos a * Real.cos b + Real.sin a * Real.sin b * Real.cos θ ≤ 1 := by
    have h1 : Real.sin a * Real.sin b * Real.cos θ ≤ Real.sin a * Real.sin b :=
      mul_le_of_le_one_right hsab (Real.cos_le_one θ)
    have h2 : Real.cos a * Real.cos b + Real.sin a * Real.sin b * Real.cos θ
        ≤ Real.cos a * Real.cos b + Real.sin a * Real.sin b := by linarith
    have h3 : Real.cos a * Real.cos b + Real.sin a * Real.sin b = Real.cos (a - b) := by
      rw [Real.cos_sub]
    rw [h3] at h2
    linarith [Real.cos_le_one (a - b)]
  have hlower : -1 ≤ Real.cos a * Real.cos b + Real.sin a * Real.sin b * Real.cos θ := by
    have h1 : Real.sin a * Real.sin b * (-1) ≤ Real.sin a * Real.sin b * Real.cos θ :=
      mul_le_mul_of_nonneg_left (Real.neg_one_le_cos θ) hsab
    have h2 : Real.cos a * Real.cos b - Real.sin a * Real.sin b
        ≤ Real.cos a * Real.cos b + Real.sin a * Real.sin b * Real.cos θ := by linarith
    have h3 : Real.cos a * Real.cos b - Real.sin a * Real.sin b = Real.cos (a + b) := by
      rw [Real.cos_add]
    rw [h3] at h2
    linarith [Real.neg_one_le_cos (a + b)]
  exact Real.cos_arccos hlower hupper

end Commons.Geometry.Sphere