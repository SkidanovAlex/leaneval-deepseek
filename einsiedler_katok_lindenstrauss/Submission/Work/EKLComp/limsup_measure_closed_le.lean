import Mathlib
import Submission.Work.EKLComp.USCBasic

/-!
# Portmanteau: `limsup` of the measures of a closed set is at most the limit measure

This is the implication (T) → (C) of the portmanteau theorem, in the form needed by the
upper semicontinuity statement `Work.EKLContract.P_USC` (EKL §9): if a sequence of Borel
probability measures `νseq` on `X₃ = SL₃(ℝ)/SL₃(ℤ)` converges weakly to a probability measure
`μ` (tested against bounded continuous real functions) then for every closed `F`

`limsupₙ νseq n F ≤ μ F`.

The proof is a direct transport to Mathlib's `MeasureTheory.ProbabilityMeasure` API, whose
topology is the weak topology, together with Mathlib's portmanteau implication
`ProbabilityMeasure.limsup_measure_closed_le_of_tendsto`.  `X₃` is Polish (hence its
`HasOuterApproxClosed` instance is available), so no regularity of `μ` has to be assumed
separately.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Work.EKLComp

theorem limsup_measure_closed_le (νseq : ℕ → MeasureTheory.Measure Work.EKLContract.X3) (μ : MeasureTheory.Measure Work.EKLContract.X3) (hprob : ∀ n, MeasureTheory.IsProbabilityMeasure (νseq n)) [MeasureTheory.IsProbabilityMeasure μ] (hweak : ∀ f : BoundedContinuousFunction Work.EKLContract.X3 ℝ, Filter.Tendsto (fun n => ∫ x, f x ∂(νseq n)) Filter.atTop (nhds (∫ x, f x ∂μ))) {F : Set Work.EKLContract.X3} (hF : IsClosed F) : Filter.limsup (fun n => νseq n F) Filter.atTop ≤ μ F := by
  let ν : ℕ → ProbabilityMeasure Work.EKLContract.X3 := fun n => ⟨νseq n, hprob n⟩
  let μ' : ProbabilityMeasure Work.EKLContract.X3 := ⟨μ, ‹MeasureTheory.IsProbabilityMeasure μ›⟩
  have hlim : Tendsto ν atTop (𝓝 μ') := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    simpa only [ν, μ', ProbabilityMeasure.coe_mk] using hweak f
  have key : (Filter.atTop.limsup fun i => (ν i : MeasureTheory.Measure Work.EKLContract.X3) F)
      ≤ (μ' : MeasureTheory.Measure Work.EKLContract.X3) F :=
    ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlim hF
  simpa only [ν, μ', ProbabilityMeasure.coe_mk] using key

end Work.EKLComp
