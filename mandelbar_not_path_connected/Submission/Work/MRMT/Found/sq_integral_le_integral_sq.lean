import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

open MeasureTheory intervalIntegral

/-- **Cauchy–Schwarz (Jensen) inequality for the interval integral.**
For a continuous real function `g` on `[0,1]`,
`(∫₀¹ g)² ≤ ∫₀¹ g²`.  Equivalently, the variance of `g` over `[0,1]` is nonnegative. -/
theorem sq_integral_le_integral_sq {g : ℝ → ℝ} (hg : Continuous g) :
    (∫ t in (0 : ℝ)..1, g t) ^ 2 ≤ ∫ t in (0 : ℝ)..1, g t ^ 2 := by
  set m := ∫ t in (0 : ℝ)..1, g t with hm
  -- the integral of the nonnegative function `(g - m)^2`
  have hnn : 0 ≤ ∫ t in (0 : ℝ)..1, (g t - m) ^ 2 := by
    apply intervalIntegral.integral_nonneg_of_forall (by norm_num)
    intro t; exact sq_nonneg _
  have hc2 : Continuous (fun t : ℝ => g t ^ 2) := by fun_prop
  have hcl : Continuous (fun t : ℝ => (2 * m) * g t) := by fun_prop
  have hsub : Continuous (fun t : ℝ => g t ^ 2 - (2 * m) * g t) := hc2.sub hcl
  -- expand the square and integrate termwise
  have hexp : ∫ t in (0 : ℝ)..1, (g t - m) ^ 2 = (∫ t in (0 : ℝ)..1, g t ^ 2) - m ^ 2 := by
    calc ∫ t in (0 : ℝ)..1, (g t - m) ^ 2
        = ∫ t in (0 : ℝ)..1, (g t ^ 2 - (2 * m) * g t + m ^ 2) := by
          apply intervalIntegral.integral_congr
          intro t _
          ring
      _ = (∫ t in (0 : ℝ)..1, (g t ^ 2 - (2 * m) * g t)) + ∫ _t in (0 : ℝ)..1, m ^ 2 := by
          rw [intervalIntegral.integral_add (f := fun t : ℝ => g t ^ 2 - (2 * m) * g t)
            (g := fun _ : ℝ => m ^ 2) (hsub.intervalIntegrable 0 1)
            (continuous_const.intervalIntegrable 0 1)]
      _ = ((∫ t in (0 : ℝ)..1, g t ^ 2) - ∫ t in (0 : ℝ)..1, (2 * m) * g t)
            + ∫ _t in (0 : ℝ)..1, m ^ 2 := by
          rw [intervalIntegral.integral_sub (f := fun t : ℝ => g t ^ 2)
            (g := fun t : ℝ => (2 * m) * g t) (hc2.intervalIntegrable 0 1)
            (hcl.intervalIntegrable 0 1)]
      _ = ((∫ t in (0 : ℝ)..1, g t ^ 2) - (2 * m) * (∫ t in (0 : ℝ)..1, g t))
            + (1 - 0) * m ^ 2 := by
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
          simp
      _ = (∫ t in (0 : ℝ)..1, g t ^ 2) - m ^ 2 := by
          rw [hm]; ring
  linarith

end Work.MRMT.Found
