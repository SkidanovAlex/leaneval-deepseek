import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongEps.EpsSpace

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsSrc

/-- **`EpsSq` is the iterated `lintegral` of its (nonnegative) integrand.**

`EpsSq α f = ∫_z ∫_θ (f z θ · epsW α z θ)²` is an iterated *Bochner* set integral; the
hypothesis `EpsMem α f` is the joint integrability of the same integrand on the product set
`Iz ×ˢ Iθ`.  The bridge is the two Fubini/Tonelli theorems for set integrals:
`setIntegral_prod` identifies the iterated Bochner integral with the Bochner integral over
`Iz ×ˢ Iθ`, `ofReal_integral_eq_lintegral_ofReal` turns that into the `lintegral` of the
nonnegative integrand, and `setLIntegral_prod` (Tonelli) re-iterates it. -/
theorem ofReal_EpsSq_eq_lintegral {α : ℝ} {f : ℝ → ℝ → ℝ} (hf : EpsMem α f) :
    ENNReal.ofReal (EpsSq α f)
      = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal ((f z θ * epsW α z θ) ^ 2) := by
  -- The integrand, as a function on the product.
  have hInt : IntegrableOn (fun p : ℝ × ℝ => (f p.1 p.2 * epsW α p.1 p.2) ^ 2)
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := hf
  -- Step 1: Fubini for set integrals; the product measure on `ℝ × ℝ` is `volume.prod volume`
  -- definitionally.
  have hEpsSq : EpsSq α f
      = ∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ,
          (f p.1 p.2 * epsW α p.1 p.2) ^ 2 := by
    rw [EpsSq]
    exact (MeasureTheory.setIntegral_prod _ hInt).symm
  rw [hEpsSq]
  -- Step 2: the Bochner integral of a nonnegative function is the `lintegral` of its `ofReal`.
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt
    (Filter.Eventually.of_forall fun p => sq_nonneg _)]
  -- Step 3: Tonelli for set integrals, iterating the `lintegral`.
  exact MeasureTheory.setLIntegral_prod _
    (ENNReal.measurable_ofReal.comp_aemeasurable hInt.aestronglyMeasurable.aemeasurable)

end Work.FTS.StrongEps.EpsSrc
