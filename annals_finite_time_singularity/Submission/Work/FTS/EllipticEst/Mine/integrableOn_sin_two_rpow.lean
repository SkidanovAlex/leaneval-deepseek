import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Mine

/-- On `[0, π/2]` the function `sin (2θ)` is nonnegative, continuous and `≤ 1`; with `a ≥ 0`
the map `θ ↦ (sin (2θ))^a` is therefore continuous on the compact interval `[0, π/2]`, hence
integrable there.  (The singular case `a < 0` — where the integrability still holds but needs a
majorant argument — is not needed here.) -/
theorem integrableOn_sin_two_rpow {a : ℝ} (ha : 0 ≤ a) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => Real.rpow (Real.sin (2 * θ)) a)
      (Set.Icc 0 (Real.pi / 2)) := by
  have hcont : ContinuousOn (fun θ : ℝ => Real.rpow (Real.sin (2 * θ)) a)
      (Set.Icc 0 (Real.pi / 2)) := by
    apply ContinuousOn.rpow_const
    · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
    · intro θ _
      exact Or.inr ha
  exact hcont.integrableOn_compact isCompact_Icc

end Work.FTS.EllipticEst.Mine
