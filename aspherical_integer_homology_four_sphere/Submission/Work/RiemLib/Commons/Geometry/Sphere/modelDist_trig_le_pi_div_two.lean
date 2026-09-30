import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Commons.Geometry.Sphere

/-- For three angles lying in `[0, π/2]` the cosine-law expression
`cos l₁ cos l₂ + sin l₁ sin l₂ cos α` is nonnegative, hence its `arccos`
is at most `π/2`. -/
theorem modelDist_trig_le_pi_div_two {l₁ l₂ α : ℝ}
    (h1 : 0 ≤ l₁) (h1' : l₁ ≤ Real.pi / 2)
    (h2 : 0 ≤ l₂) (h2' : l₂ ≤ Real.pi / 2)
    (hα : 0 ≤ α) (hα' : α ≤ Real.pi / 2) :
    Real.arccos (Real.cos l₁ * Real.cos l₂ + Real.sin l₁ * Real.sin l₂ * Real.cos α)
      ≤ Real.pi / 2 := by
  rw [Real.arccos_le_pi_div_two]
  have hcos1 : 0 ≤ Real.cos l₁ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], h1'⟩
  have hcos2 : 0 ≤ Real.cos l₂ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], h2'⟩
  have hsin1 : 0 ≤ Real.sin l₁ := Real.sin_nonneg_of_nonneg_of_le_pi h1 (by linarith [Real.pi_pos])
  have hsin2 : 0 ≤ Real.sin l₂ := Real.sin_nonneg_of_nonneg_of_le_pi h2 (by linarith [Real.pi_pos])
  have hcosα : 0 ≤ Real.cos α :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) hα'
  have hprod : 0 ≤ Real.sin l₁ * Real.sin l₂ * Real.cos α :=
    mul_nonneg (mul_nonneg hsin1 hsin2) hcosα
  exact add_nonneg (mul_nonneg hcos1 hcos2) hprod

end Commons.Geometry.Sphere