import Mathlib
import Submission.Work.Koebe.polar_ball_iterated
import Submission.Work.Koebe.inner_integral
import Submission.Work.Koebe.outer_integral

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The Cauchy transform of the disc

For `Λ > 0` and `‖ζ‖ < Λ`,
`∫ w in Metric.ball (0 : ℂ) Λ, (ζ - w)⁻¹ = π * conj ζ`.

The proof reduces the planar integral over the disc to polar coordinates
(`polar_ball_iterated`), evaluates the angular integral for each radius
(`inner_integral`: it is `2π/ζ` for `r < ‖ζ‖` and `0` for `r > ‖ζ‖`, by the
mean-value property for holomorphic functions) and integrates the resulting
function of `r` over `(0, Λ)` (`outer_integral`).
-/

namespace Work.Koebe

set_option linter.unusedVariables false

open MeasureTheory

theorem cauchyTransform_ball (Λ : ℝ) (hΛ : 0 < Λ) (ζ : ℂ) (hζ : ‖ζ‖ < Λ) :
    ∫ w in Metric.ball (0 : ℂ) Λ, (ζ - w)⁻¹ = (Real.pi : ℂ) * (starRingEnd ℂ ζ) := by
  rw [polar_ball_iterated]
  -- Pull the factor `r` out of the inner angular integral.
  have hinner : ∀ r : ℝ, (∫ θ in Set.Ioo (-Real.pi) Real.pi,
        (r : ℂ) * (ζ - (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))⁻¹)
      = (r : ℂ) * (∫ θ in Set.Ioo (-Real.pi) Real.pi,
        (ζ - (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))⁻¹) :=
    fun r => MeasureTheory.integral_const_mul (r : ℂ) _
  simp_rw [hinner]
  -- Evaluate the angular integral for almost every radius.
  have hne : ∀ᵐ r ∂(volume : MeasureTheory.Measure ℝ), r ≠ ‖ζ‖ := by
    rw [Filter.eventually_iff, MeasureTheory.mem_ae_iff]
    simp
  rw [MeasureTheory.setIntegral_congr_ae measurableSet_Ioo (by
    filter_upwards [hne] with r hrne hrIoo
    rw [inner_integral ζ r (le_of_lt hrIoo.1) hrne])]
  exact outer_integral Λ ζ hζ

end Work.Koebe
