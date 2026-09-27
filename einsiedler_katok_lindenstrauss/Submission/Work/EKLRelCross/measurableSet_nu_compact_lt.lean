import Mathlib
import Submission.Work.EKLRelCross.LeafBasic
import Submission.Work.EKLCompLeaf.measurable_nu

/-!
# Measurability of `{x ∈ X' | ν x K < M}` for a leafwise system

Let `(μ, U, ν, X')` be a leafwise system in the sense of `Work.EKLContract.IsLeafwise`.  The field
`measurable` of that structure says that for every compactly supported continuous
`f : SL₃(ℝ) → ℝ` the function `x ↦ ∫ g, f g ∂(ν x)` is measurable, and the field `radon` says
that `ν x` is finite on compact sets for `x ∈ X'`.  Consequently (by the Urysohn /
outer-regularity argument of `Work.EKLCompLeaf.measurable_apply_isCompact`) the evaluation
`x ↦ ν x K` is measurable on `X'` for every compact `K`, and hence
`{x : X₃ | x ∈ X' ∧ ν x K < M}` is measurable.

The passage from "measurable on `X'`" to a statement about the ambient space is done by working on
the subtype `{x // x ∈ X'}`: the family `x ↦ ν x.1` is weakly measurable and everywhere finite on
compacts there, `measurable_apply_isCompact` applies verbatim, and `MeasurableSet.subtype_image`
transports the resulting measurable set back to `X₃` (using `IsLeafwise.meas_dom`).

Nothing is assumed about `ν x` for `x ∉ X'`; the intersection with `X'` is what makes this
harmless (compare `Work.EKLComp.C8Defs`, where `ν` outside `X'` is replaced by `δ₁`).
-/

open MeasureTheory

set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLRelCross

open Work.EKLContract

/-- **The bad set `{x ∈ X' | ν x K < M}` of a compact set is measurable.** -/
theorem measurableSet_nu_compact_lt {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ]
    {U : Subgroup Work.EKLContract.SL3} {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' : Set Work.EKLContract.X3} (hL : Work.EKLContract.IsLeafwise μ U ν X')
    {K : Set Work.EKLContract.SL3} (hK : IsCompact K) (M : ENNReal) :
    MeasurableSet {x : Work.EKLContract.X3 | x ∈ X' ∧ ν x K < M} := by
  classical
  -- On the subtype `X'` the leafwise system is a weakly measurable family of measures which is
  -- everywhere finite on compact sets.
  have hmeas : ∀ f : CompactlySupportedContinuousMap SL3 ℝ,
      Measurable (fun x : {x : X3 // x ∈ X'} => ∫ g, f g ∂(ν x.1)) :=
    fun f => (hL.measurable f).comp measurable_subtype_coe
  have hfin : ∀ x : {x : X3 // x ∈ X'}, IsFiniteMeasureOnCompacts (ν x.1) :=
    fun x => hL.radon x.1 x.2
  have hKmeas : Measurable (fun x : {x : X3 // x ∈ X'} => ν x.1 K) :=
    Work.EKLCompLeaf.measurable_apply_isCompact hmeas hfin hK
  have hset : MeasurableSet {x : {x : X3 // x ∈ X'} | ν x.1 K < M} :=
    measurableSet_lt hKmeas measurable_const
  have himage : MeasurableSet ((Subtype.val : {x : X3 // x ∈ X'} → X3) ''
      {x : {x : X3 // x ∈ X'} | ν x.1 K < M}) :=
    hL.meas_dom.subtype_image hset
  have heq : ((Subtype.val : {x : X3 // x ∈ X'} → X3) ''
        {x : {x : X3 // x ∈ X'} | ν x.1 K < M})
      = {x : X3 | x ∈ X' ∧ ν x K < M} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, hx⟩
    · rintro ⟨hy, hyM⟩
      exact ⟨⟨y, hy⟩, hyM, rfl⟩
  rwa [heq] at himage

end Work.EKLRelCross
