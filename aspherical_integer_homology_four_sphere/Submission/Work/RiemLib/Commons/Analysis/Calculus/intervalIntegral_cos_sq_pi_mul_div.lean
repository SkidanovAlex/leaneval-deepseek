import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Commons.Analysis.Calculus

open MeasureTheory intervalIntegral

theorem intervalIntegral_cos_sq_pi_mul_div (L : ℝ) (hL : 0 < L) :
    ∫ t in (0 : ℝ)..L, Real.cos (Real.pi * t / L) ^ 2 = L / 2 := by
  have hLne : L ≠ 0 := ne_of_gt hL
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hc : L / Real.pi ≠ 0 := div_ne_zero hLne hpi
  have harg : ∀ t : ℝ, Real.pi * t / L = t / (L / Real.pi) := by
    intro t
    field_simp
  have hLpi : L / (L / Real.pi) = Real.pi := by
    field_simp
  simp_rw [harg]
  rw [intervalIntegral.integral_comp_div (f := fun x : ℝ => Real.cos x ^ 2) hc]
  rw [zero_div, hLpi, integral_cos_sq]
  rw [Real.cos_pi, Real.sin_pi, Real.cos_zero, Real.sin_zero]
  rw [smul_eq_mul]
  field_simp
  ring

end Commons.Analysis.Calculus