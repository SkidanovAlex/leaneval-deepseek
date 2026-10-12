import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.DvApriori.BandDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB2.DvApriori.MomBilDefs` — the polarised large-momentum word

The large-momentum piece of FS `eq:DefT` is the quadratic form
(`Work.BoseKinLoc.momForm`)

    `momForm ℓ d u ψ = (2π)⁻³ ∫_p 1_{(d²ℓ)⁻¹<‖p‖}·‖kinFT (θ_u·Q_uψ) p‖²`,

whose value at the fibre of a joint sector projection is what the FS §6 a-priori
estimate needs.  The *off-diagonal* piece of that estimate is the polarisation of
`momForm`, for which we record here the explicit bilinear form

    `momBil ℓ d f g = (2π)⁻³ ∫_p 1_{(d²ℓ)⁻¹<‖p‖}·⟨kinFT (θ_0·Q_0f) p, kinFT (θ_0·Q_0g) p⟩_ℝ`

at the anchored box `Λ(0)`.  The identity that makes this the polarisation of
`momForm` is delegated (and proved) separately:

    `momForm ℓ d 0 (f+g) − momForm ℓ d 0 (f−g) = 4·momBil ℓ d f g`.

This module contains *only* the definition, so that it can be imported both by the
module holding the identity and by the modules using it.
-/

noncomputable section

open scoped Real

namespace Work.BoseFixB2.DvApriori

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The polarised large-momentum word** at the anchored box `Λ(0)`: the bilinear form with
kernel `momProj ℓ d` (the high-momentum cut-off) in the `p`-convention Fourier representation
of the localised mean-free states.  Its diagonal (`g = f`) is `momForm ℓ d 0 f`, and it is the
polarisation of `momForm` (`momForm ℓ d 0 (f+g) − momForm ℓ d 0 (f−g) = 4·momBil ℓ d f g`). -/
noncomputable def momBil (ℓ d : ℝ) (f g : EuclideanSpace ℝ (Fin 3) → ℝ) : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ *
    ∫ p : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.momProj ℓ d p *
      (inner ℝ (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0 f) p)
               (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0 g) p))

end Work.BoseFixB2.DvApriori
