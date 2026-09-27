import Mathlib
import Submission.Work.EKLC6Core.growth_integral_sup
import Submission.Work.EKLC6Core.measurable_growthFun
import Submission.Work.EKLContract.Interfaces

/-!
# `EKLC6Core.aestronglyMeasurable_log_prodBoxMass`

The `νH`-mass `z ↦ νH z (prodBox T U)` of the product box is measurable (after the standard
correction of `νH` off the co-null domain `XH` of the leaf-wise system), hence so is its
logarithm — this is the measurability of the coboundary that appears in
`Work.EKLC6Core.growthFun_sub_eq` and in the `A`-invariance argument of
`Work.EKLC6Core.growth_integral_sup`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal Pointwise
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- The mass of the product box `prodBox T U` with respect to a leaf-wise system `νH` for `H`
(carried on the co-null set `XH`) is measurable, hence its logarithm is almost everywhere
strongly measurable. -/
theorem aestronglyMeasurable_log_prodBoxMass {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    {H T U : Subgroup Work.EKLContract.SL3}
    (hHT : Work.EKLContract.IsHoro T) (hHU : Work.EKLContract.IsHoro U)
    {νH : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {XH : Set Work.EKLContract.X3} (hLH : Work.EKLContract.IsLeafwise μ H νH XH) :
    MeasureTheory.AEStronglyMeasurable
      (fun z : Work.EKLContract.X3 => Real.log ((νH z (Work.EKLC6Core.prodBox T U)).toReal)) μ := by
  classical
  -- `XH` is co-null
  have hmemH : ∀ᵐ x ∂μ, x ∈ XH := by
    rw [MeasureTheory.ae_iff]; exact hLH.conull
  -- correct `νH` off `XH` by the zero measure: this keeps the integrals against test functions
  -- and the compact-regularity, and gains global measurability
  let ν' : X3 → Measure SL3 := fun z => if z ∈ XH then νH z else 0
  have hν'fin : ∀ z : X3, IsFiniteMeasureOnCompacts (ν' z) := by
    intro z
    by_cases hz : z ∈ XH
    · simp only [ν', hz, if_true]; exact hLH.radon z hz
    · simp only [ν', hz, if_false]; exact ⟨fun K _ => by simp⟩
  have hν'meas : ∀ f : CompactlySupportedContinuousMap SL3 ℝ,
      Measurable (fun z : X3 => ∫ g, f g ∂(ν' z)) := by
    intro f
    have h1 : Measurable (fun z : X3 => ∫ g, f g ∂(νH z)) := hLH.measurable f
    have h2 : (fun z : X3 => ∫ g, f g ∂(ν' z))
        = XH.indicator (fun z : X3 => ∫ g, f g ∂(νH z)) := by
      funext z
      by_cases hz : z ∈ XH <;> simp [ν', Set.indicator, hz]
    rw [h2]
    exact h1.indicator hLH.meas_dom
  -- the mass of the compact product box is measurable
  have hmass : Measurable (fun z : X3 => ν' z (prodBox T U)) :=
    Work.EKLCompLeaf.measurable_apply_isCompact hν'meas hν'fin
      (isCompact_prodBox hHT hHU)
  have hlog : Measurable (fun z : X3 => Real.log ((ν' z (prodBox T U)).toReal)) :=
    Real.measurable_log.comp hmass.ennreal_toReal
  have hae : (fun z : X3 => Real.log ((ν' z (prodBox T U)).toReal))
      =ᵐ[μ] (fun z : X3 => Real.log ((νH z (prodBox T U)).toReal)) := by
    filter_upwards [hmemH] with z hz
    simp only [ν', hz, if_true]
  exact hlog.aestronglyMeasurable.congr hae

end Work.EKLC6Core

end
