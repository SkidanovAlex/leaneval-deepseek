import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Commons.Analysis.Calculus

theorem intervalIntegral_sin_sq_pi_mul_div (L : ℝ) (hL : 0 < L) :
    ∫ t in (0 : ℝ)..L, Real.sin (Real.pi * t / L) ^ 2 = L / 2 := by
  have hL0 : L ≠ 0 := ne_of_gt hL
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hc : L / Real.pi ≠ 0 := div_ne_zero hL0 hpi
  have h1 : ∀ t : ℝ, Real.sin (Real.pi * t / L) ^ 2 = Real.sin (t / (L / Real.pi)) ^ 2 := by
    intro t
    have : Real.pi * t / L = t / (L / Real.pi) := by
      field_simp
    rw [this]
  simp_rw [h1]
  rw [intervalIntegral.integral_comp_div (fun x : ℝ => Real.sin x ^ 2) hc]
  have h2 : (∫ x in (0 : ℝ)..Real.pi, Real.sin x ^ 2) = Real.pi / 2 := by
    simp
  rw [show (0 : ℝ) / (L / Real.pi) = 0 by simp,
      show L / (L / Real.pi) = Real.pi by field_simp]
  rw [h2]
  simp only [smul_eq_mul]
  field_simp

end Commons.Analysis.Calculus