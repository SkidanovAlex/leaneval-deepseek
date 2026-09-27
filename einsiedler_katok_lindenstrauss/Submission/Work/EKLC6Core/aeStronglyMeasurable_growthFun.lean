import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.measurable_growthFun

/-!
# `EKLC6Core.aeStronglyMeasurable_growthFun`

The entropy contribution `growthFun U ν t x = -log (ν x (conjBox U t))` (Pisa 7.6/7.18, see
`Work.EKLC6Core.Basic`) has to be integrable against `μ`, hence at least a.e. strongly
measurable.  The only obstruction is that the leaf-wise system `ν` is *only* assumed to be a
Radon family on the co-null domain `X'` of the frozen contract `IsLeafwise`: outside `X'` the
measures `ν x` are completely unconstrained, so `x ↦ ν x (conjBox U t)` need not be measurable
on the nose.

Since `μ X'ᶜ = 0` this is harmless: we correct `ν` off `X'` by the zero measure, obtaining a
family `ν'` which agrees with `ν` on `X'` and *is* finite on compacta everywhere.  For `ν'` the
weak-measurability field of `IsLeafwise` survives as honest measurability (indicator of the
measurable set `X'`), and `Work.EKLCompLeaf.measurable_apply_isCompact` applied to the compact
set `conjBox U t` (`Work.EKLC6Core.isCompact_conjBox`) gives the measurability of
`x ↦ ν' x (conjBox U t)`.  Composing with `ENNReal.toReal` and `Real.log` gives a measurable
function equal to `growthFun U ν t` on the conull set `X'`, hence a.e. strongly measurable.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

theorem aeStronglyMeasurable_growthFun {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] {U : Subgroup Work.EKLContract.SL3}
    (hU : Work.EKLContract.IsHoro U)
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' : Set Work.EKLContract.X3} (hL : Work.EKLContract.IsLeafwise μ U ν X') (t : Fin 3 → ℝ) :
    MeasureTheory.AEStronglyMeasurable (Work.EKLC6Core.growthFun U ν t) μ := by
  classical
  -- `X'` is conull
  have hmem : ∀ᵐ x ∂μ, x ∈ X' := by
    rw [MeasureTheory.ae_iff]; exact hL.conull
  -- correct `ν` off the co-null domain by the zero measure
  let ν' : X3 → Measure SL3 := fun z => if z ∈ X' then ν z else 0
  have hν'fin : ∀ z : X3, IsFiniteMeasureOnCompacts (ν' z) := by
    intro z
    by_cases hz : z ∈ X'
    · simp only [ν', hz, if_true]; exact hL.radon z hz
    · simp only [ν', hz, if_false]; exact ⟨fun K _ => by simp⟩
  have hν'meas : ∀ f : CompactlySupportedContinuousMap SL3 ℝ,
      Measurable (fun z : X3 => ∫ g, f g ∂(ν' z)) := by
    intro f
    have h1 : Measurable (fun z : X3 => ∫ g, f g ∂(ν z)) := hL.measurable f
    have h2 : (fun z : X3 => ∫ g, f g ∂(ν' z))
        = X'.indicator (fun z : X3 => ∫ g, f g ∂(ν z)) := by
      funext z
      by_cases hz : z ∈ X' <;> simp [ν', Set.indicator, hz]
    rw [h2]
    exact h1.indicator hL.meas_dom
  -- the mass of the compact conjugated box is measurable
  have hmass : Measurable (fun z : X3 => ν' z (conjBox U t)) :=
    Work.EKLCompLeaf.measurable_apply_isCompact hν'meas hν'fin (isCompact_conjBox hU t)
  have hlog : Measurable (fun z : X3 => -Real.log ((ν' z (conjBox U t)).toReal)) :=
    Real.measurable_log.comp hmass.ennreal_toReal |>.neg
  have hae : (fun z : X3 => -Real.log ((ν' z (conjBox U t)).toReal))
      =ᵐ[μ] (Work.EKLC6Core.growthFun U ν t) := by
    filter_upwards [hmem] with z hz
    simp only [growthFun, ν', hz, if_true]
  exact hlog.aestronglyMeasurable.congr hae

end Work.EKLC6Core

end
