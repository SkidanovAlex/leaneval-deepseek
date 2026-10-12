import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB3.Defs
import Submission.Work.BoseKinLoc.Momentum.memLp_kinFT
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.HighMassAux.integrable_lowMultCoeff`

The coefficient function of the low-momentum multiplier is integrable:

`p ↦ f(‖p‖/κ) · (θ_ΛΨ)^(p)`,

where `f` is FS's low-momentum cut-off (`Work.BoseBoxFix.LowCut`), `θ_ΛΨ` is the extension by
`0` off `Λ = acube ℓ` of an `L¹`-on-`Λ` function `Ψ`, and `^(p)` is the corpus's `p`-convention
Fourier transform `kinFT`.  This is exactly the integrability hypothesis one needs to justify
the `∫_p` in `lowMult_pairing` (`Work.BoseFixB3.HighMassAux.lowMult_pairing`).

The proof is soft and rests on two facts:

* the multiplier `p ↦ f(‖p‖/κ)` is **continuous** (FS's `f` is `C^∞`) with **compact support**
  (the hypothesis `hcs`, FS's `f = 0` on `[2,∞)` after rescaling), hence so is its product
  with anything continuous;
* `kinFT` of an `L¹` function is **continuous** (`continuous_kinFT_of_integrable`); and an
  `L¹`-on-`Λ` `Ψ` gives `(θ_ΛΨ) ∈ L¹(ℝ³)` because `Λ = acube ℓ` is measurable.

A continuous function with compact support is integrable on `ℝ³` (Lebesgue measure is finite on
compacts), and the product of the compactly supported multiplier with the continuous `kinFT` is
of that shape.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB3.HighMassAux

/-- A compactly supported continuous (complex) function times the `p`-convention Fourier
transform of an `L¹` function is integrable on `ℝ³`. -/
theorem integrable_mul_kinFT_of_hasCompactSupport {m : Submission.BoseGases.kcE3 → ℂ}
    (hm : Continuous m) (hmcs : HasCompactSupport m) {G : Submission.BoseGases.kcE3 → ℂ}
    (hG : MeasureTheory.Integrable G) :
    MeasureTheory.Integrable (fun p => m p * Submission.BoseGases.kinFT G p) := by
  have hc : Continuous (m * Submission.BoseGases.kinFT G) :=
    hm.mul (Work.BoseKinLoc.Momentum.continuous_kinFT_of_integrable hG)
  have hs : HasCompactSupport (m * Submission.BoseGases.kinFT G) := hmcs.mul_right
  exact hc.integrable_of_hasCompactSupport hs

theorem integrable_lowMultCoeff {fc : Work.BoseBoxFix.LowCut} {κ ℓ : ℝ}
    {Ψ : Submission.BoseGases.kcE3 → ℝ}
    (hΨ : MeasureTheory.IntegrableOn Ψ (Submission.BoseGases.acube ℓ))
    (hcs : HasCompactSupport (fun p : Submission.BoseGases.kcE3 => fc.f (‖p‖ / κ))) :
    MeasureTheory.Integrable (fun p : Submission.BoseGases.kcE3 =>
      ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
        Submission.BoseGases.kinFT (fun z : Submission.BoseGases.kcE3 =>
          (((Submission.BoseGases.acube ℓ).indicator Ψ z : ℝ) : ℂ)) p) := by
  -- `θ_ΛΨ` is integrable: `Ψ ∈ L¹(Λ)` and `Λ = acube ℓ` is measurable.
  have hG : MeasureTheory.Integrable (fun z : Submission.BoseGases.kcE3 =>
      (((Submission.BoseGases.acube ℓ).indicator Ψ z : ℝ) : ℂ)) :=
    (IntegrableOn.integrable_indicator hΨ
      (Work.BoseKinLoc.Momentum.measurableSet_acube ℓ)).ofReal
  -- the multiplier `p ↦ f(‖p‖/κ)` is continuous (FS's `f` is smooth) …
  have hm : Continuous (fun p : Submission.BoseGases.kcE3 => ((fc.f (‖p‖ / κ) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (fc.smooth.continuous.comp (continuous_norm.div_const κ))
  -- … and compactly supported (FS's `f` vanishes on `[2,∞)`), so is its `ℂ`-valued version.
  have hmcs : HasCompactSupport (fun p : Submission.BoseGases.kcE3 =>
      ((fc.f (‖p‖ / κ) : ℝ) : ℂ)) :=
    hcs.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  exact integrable_mul_kinFT_of_hasCompactSupport hm hmcs hG

end Work.BoseFixB3.HighMassAux
