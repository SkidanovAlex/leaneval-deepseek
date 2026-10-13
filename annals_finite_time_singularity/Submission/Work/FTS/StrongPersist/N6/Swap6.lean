/-
# `Work.FTS.StrongPersist.N6.Swap6`

Tonelli for the `ℋ⁶`-integrand of an open-class datum: the verbatim level-six version of
`Work.FTS.TransportS.SupDzAux.sda_HkSqSwap_open` (there is no level-dependence in the proof,
only in the numeral `4 ↦ 6`).

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.TransportS.SupDzAux.SdaAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6

open Work.Spaces

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **Tonelli for the `ℋ⁶`-integrand of an open-class datum.**  For `f` of class `C^∞` on the
open quadrant with `HkMem α 6 f`, the iterated integral of `HkIntegrand α 6 f` in the order
`∫_θ ∫_z` equals `HkSq α 6 f`, its partially integrated function is integrable on the angles,
and for almost every angle the radial slice is integrable. -/
theorem sda_HkSqSwap_open6 (α : ℝ) (f : ℝ → ℝ → ℝ)
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : HkMem α 6 f) :
    (∫ σ in Iθ, ∫ s in Iz, HkIntegrand α 6 f s σ = HkSq α 6 f) ∧
      Integrable (fun σ : ℝ => ∫ s in Iz, HkIntegrand α 6 f s σ) (volume.restrict Iθ) ∧
      (∀ᵐ σ ∂(volume.restrict Iθ),
        IntegrableOn (fun s => HkIntegrand α 6 f s σ) Iz) := by
  have hnn : ∀ z θ : ℝ, 0 ≤ HkIntegrand α 6 f z θ :=
    fun z θ => HkIntegrand_nonneg α 6 f z θ
  have haesm : AEStronglyMeasurable
      (Function.uncurry fun z θ : ℝ => HkIntegrand α 6 f z θ)
      ((volume.restrict Iz).prod (volume.restrict Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ (hF.continuousOn_HkIntegrand α 6)
  have hslice : ∀ᵐ z ∂(volume.restrict Iz),
      Integrable (fun θ : ℝ => HkIntegrand α 6 f z θ) (volume.restrict Iθ) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => hmem.1 z hz)
  have houter : Integrable (fun z : ℝ => ∫ θ in Iθ, HkIntegrand α 6 f z θ)
      (volume.restrict Iz) := hmem.2
  obtain ⟨h1, h2, h3⟩ :=
    Work.FTS.H2.swap_iterated_integral_of_nonneg
      (μ := volume.restrict Iz) (ν := volume.restrict Iθ) hnn haesm hslice houter
  exact ⟨by rw [HkSq]; exact h1, h2, h3⟩

end Work.FTS.StrongPersist.N6
