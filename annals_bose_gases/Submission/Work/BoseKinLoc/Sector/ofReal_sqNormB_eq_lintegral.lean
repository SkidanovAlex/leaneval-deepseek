import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseKinLoc.Sector

open MeasureTheory

/-- The box `L²`-mass of a continuous state, as an `ℝ≥0∞` Lebesgue integral:
`ofReal (∫_{abox} Φ²) = ∫⁻_{abox} ofReal (Φ²)`.  Both sides see only the box, the
integrand is a square, and a continuous function is integrable over the compact
box `abox n ℓ` (`0 < ℓ`), so Mathlib's
`ofReal_integral_eq_lintegral_ofReal` applies with the restricted measure. -/
theorem ofReal_sqNormB_eq_lintegral {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : Continuous Φ) :
    ENNReal.ofReal (Work.BoseKinLoc.sqNormB n ℓ Φ)
      = ∫⁻ z in Submission.BoseGases.abox n ℓ, ENNReal.ofReal ((Φ z) ^ 2) := by
  have hint : IntegrableOn (fun x : Submission.BoseGases.X n => (Φ x) ^ 2)
      (Submission.BoseGases.abox n ℓ) volume :=
    Submission.BoseGases.integrableOn_abox_of_continuous hℓ (hΦ.pow 2)
  have h := MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (μ := volume.restrict (Submission.BoseGases.abox n ℓ)) hint
    (Filter.Eventually.of_forall fun x => sq_nonneg (Φ x))
  simpa [Work.BoseKinLoc.sqNormB] using h

end Work.BoseKinLoc.Sector
