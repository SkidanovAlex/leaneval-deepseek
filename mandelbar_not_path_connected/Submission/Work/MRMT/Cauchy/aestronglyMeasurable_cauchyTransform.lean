import Mathlib
import Submission.Work.MRMT.Basic
import Submission.Work.MRMT.Cauchy.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Complex Function

namespace Work.MRMT.Cauchy

/-- **The Cauchy transform is a.e. strongly measurable.** For `ω ∈ L¹(ℂ)`,
`z ↦ Work.MRMT.cauchyTransform ω z = Work.MRMT.cauchyConst * ∫ ζ, ω ζ / (ζ - z)` is
`AEStronglyMeasurable` for Lebesgue measure on `ℂ`.

Hints for the prover.  `Work.MRMT.cauchyTransform ω = fun z => Work.MRMT.cauchyConst * (∫ ζ, ω ζ / (ζ - z))`
and a constant left-multiple of an a.e. strongly measurable function is a.e. strongly measurable
(`MeasureTheory.AEStronglyMeasurable.const_mul`).  For the integral use
`MeasureTheory.AEStronglyMeasurable.integral_prod_right'` applied to
`F : ℂ × ℂ → ℂ, F p = ω p.2 / (p.2 - p.1)` (giving `AEStronglyMeasurable (fun z => ∫ ζ, F (z, ζ)) volume`):
it suffices to prove `AEStronglyMeasurable F (volume.prod volume)`.  Write
`F p = (fun p => ω p.2) p * (fun p => (p.2 - p.1)⁻¹) p`.  The first factor is a.e. strongly
measurable by `MeasureTheory.AEStronglyMeasurable.comp_snd` applied to `hω.aestronglyMeasurable`
(note: `comp_measurable` lands in `μ.map Prod.snd`, `comp_snd` is the direct one); the second factor
is measurable because `p ↦ p.2 - p.1` is continuous and `fun x : ℂ => x⁻¹` is measurable
(`Measurable.inv`), so `Measurable.aestronglyMeasurable` applies.  Combine with
`MeasureTheory.AEStronglyMeasurable.mul`. -/
theorem aestronglyMeasurable_cauchyTransform (ω : ℂ → ℂ)
    (hω : MeasureTheory.Integrable ω MeasureTheory.volume) :
    MeasureTheory.AEStronglyMeasurable (Work.MRMT.cauchyTransform ω) MeasureTheory.volume := by
  -- The two-variable integrand `F p = ω p.2 / (p.2 - p.1)` is a.e. strongly measurable.
  have h1 : MeasureTheory.AEStronglyMeasurable (fun p : ℂ × ℂ => ω p.2)
      (MeasureTheory.volume.prod MeasureTheory.volume) :=
    hω.aestronglyMeasurable.comp_snd
  have h2 : MeasureTheory.AEStronglyMeasurable (fun p : ℂ × ℂ => (p.2 - p.1)⁻¹)
      (MeasureTheory.volume.prod MeasureTheory.volume) :=
    ((measurable_snd.sub measurable_fst).inv).aestronglyMeasurable
  have hF : MeasureTheory.AEStronglyMeasurable (fun p : ℂ × ℂ => ω p.2 / (p.2 - p.1))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    exact h1.mul h2
  -- Fubini-type: the parametrized integral is a.e. strongly measurable.
  have hint : MeasureTheory.AEStronglyMeasurable (fun z : ℂ => ∫ ζ, ω ζ / (ζ - z))
      MeasureTheory.volume :=
    MeasureTheory.AEStronglyMeasurable.integral_prod_right' hF
  exact hint.const_mul Work.MRMT.cauchyConst

end Work.MRMT.Cauchy
