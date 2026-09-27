import Mathlib
import Submission.Work.EKLRelCross.leafwise_exists
import Submission.Work.EKLC6Core.measurable_growthFun
import Submission.Work.EKLC6Core.Assembly
import Submission.Work.EKLComp.prove_Leafwise
import Submission.Work.EKLCompLeaf.fixRadon

/-!
# `EKLC6Core.exists_leafwise_growthFun_measurable`

The leafwise-system existence theorem of component C5 (`P_Leafwise`, Pisa Theorem 6.3) supplies,
for a probability `μ` on `X₃ = SL₃(ℝ)/SL₃(ℤ)` preserved by a diagonal element `aDiag t`, a
system of leafwise measures for the *stable horospherical subgroup* `Uminus t = G⁻(t)`.

This module packages the *usable* form of that existence statement for the C6 development: it
returns the system `ν` normalised *everywhere* (so that `x ↦ ν x` is finite on compacts at every
point, `Work.EKLCompLeaf.fixRadon`), together with the measurability of the pointwise
information

`growthFun (Uminus t) ν t x = -log (ν x (conjBox (Uminus t) t))`.

The existence itself comes from `Work.EKLComp.prove_Leafwise` (the frozen component C5, proved
unconditionally in this workspace), applied at the horospherical subgroup `Uminus t` with the
contraction supplied by `Work.EKLC6Core.uminus_isHoro`; the measurability is
`Work.EKLC6Core.measurable_growthFun` (compactness of the conjugated box + weak measurability of
the leafwise system), the composition with `Real.log` using `Measurable.log`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- **Existence of a leafwise system for `Uminus t` with a globally measurable entropy
contribution.**  For any probability `μ` preserved by `x ↦ aDiag t • x` there is a system of
leafwise measures `ν` for the stable horospherical subgroup `Uminus t` (on some conull `X'`),
finite on compacts at *every* point of `X₃`, and such that
`x ↦ -log (ν x (conjBox (Uminus t) t))` is measurable.

Sketch: `Uminus t` is horospherical and contracted by `aDiag t` itself
(`Work.EKLC6Core.uminus_isHoro`), so C5 (`Work.EKLComp.prove_Leafwise`) yields
`IsLeafwise μ (Uminus t) ν X'`.  Replacing `ν` by `fixRadon ν X'` (Dirac mass at `1` off the
conull set) keeps the leafwise structure and makes it globally finite on compacts; the
measurability of the mass of the compact conjugated box is `measurable_growthFun`, and the
logarithm is measurable. -/
theorem exists_leafwise_growthFun_measurable {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ) :
    ∃ (ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3)
      (X' : Set Work.EKLContract.X3),
      Work.EKLContract.IsLeafwise μ (Work.EKLC6Core.Uminus t) ν X' ∧
      (∀ x : Work.EKLContract.X3, MeasureTheory.IsFiniteMeasureOnCompacts (ν x)) ∧
      Measurable (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t) := by
  have hHoro : IsHoro (Uminus t) := (uminus_isHoro t).1
  have hcontr : ∀ u ∈ Uminus t,
      Tendsto (fun n : ℕ => aDiag t ^ n * u * (aDiag t ^ n)⁻¹) atTop (𝓝 1) :=
    (uminus_isHoro t).2
  obtain ⟨ν, X', hL⟩ := (Work.EKLComp.prove_Leafwise μ (Uminus t) hHoro t hmp hcontr).1
  obtain ⟨hL', hfin⟩ := Work.EKLCompLeaf.fixRadon hL
  refine ⟨Work.EKLComp.fixRadon ν X', X', hL', hfin, ?_⟩
  unfold growthFun
  exact ((measurable_growthFun hL' hfin hHoro t).log).neg

end Work.EKLC6Core

end
