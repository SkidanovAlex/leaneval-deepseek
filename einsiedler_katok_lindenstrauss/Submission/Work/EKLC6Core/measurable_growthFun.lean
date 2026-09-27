import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.conjBox_measurable
import Submission.Work.EKLC6Core.conjBox_nhds
import Submission.Work.EKLCompLeaf.measurable_nu
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLProd.sl3EntryBox_compact

/-!
# `EKLC6Core.measurable_growthFun`

The pointwise information `growthFun U ν t x = -log (ν x (conjBox U t))` (Pisa 7.6/7.18) has to
be an honest function of `x` in order to be integrated.  This module proves that its argument
`x ↦ (ν x (conjBox U t)).toReal` is measurable.

`conjBox U t = aDiag t · Box1 U · (aDiag t)⁻¹` is *compact*: `Box1 U` is a closed subset of the
entrywise box `{|g i j - 1 i j| ≤ 1}`, which is a finite product of compact intervals; conjugation
by the diagonal is a homeomorphism.  Hence the result follows from the general weak-measurability
input together with finiteness on compact sets: `Z = conjBox U t` is a Borel set carrying a
finite measure, and `Work.EKLCompLeaf.measurable_apply_isCompact` (the engine behind
`EKLCompLeaf.measurable_nu`, which handles the special case `Z = A ∩ ballU 1`) gives the
measurability of `x ↦ ν x Z`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-! ## `Box1 U` is compact -/

/-- `B₁^U = Box1 U` is closed: it is the intersection of the closed subgroup `U` with the closed
sup-norm ball `{g | ∀ i j, |g i j - 1 i j| ≤ 1}` around the identity. -/
theorem isClosed_box1 {U : Subgroup SL3} (hU : IsHoro U) : IsClosed (Box1 U) := by
  have hUc : IsClosed (U : Set SL3) := hU.1
  have hB : IsClosed {g : SL3 | ∀ i j, |g i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1} := by
    rw [show {g : SL3 | ∀ i j, |g i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1}
        = ⋂ i : Fin 3, ⋂ j : Fin 3,
            {g : SL3 | |g i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1} by
      ext g; simp]
    exact isClosed_iInter (fun i => isClosed_iInter (fun j =>
      isClosed_le (by fun_prop) continuous_const))
  rw [show Box1 U = (U : Set SL3) ∩
      {g : SL3 | ∀ i j, |g i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1} by
    ext g; simp [Box1]]
  exact hUc.inter hB

/-- `B₁^U = Box1 U` is compact: it is a closed subset of the entrywise box
`{g | ∀ i j, 1 i j - 1 ≤ g i j ∧ g i j ≤ 1 i j + 1}`, which is a finite product of compact
intervals inside `SL₃(ℝ)`. -/
theorem isCompact_box1 {U : Subgroup SL3} (hU : IsHoro U) : IsCompact (Box1 U) := by
  refine (Work.EKLProd.sl3EntryBox_compact
      (fun i j => (1 : Matrix (Fin 3) (Fin 3) ℝ) i j - 1)
      (fun i j => (1 : Matrix (Fin 3) (Fin 3) ℝ) i j + 1)).of_isClosed_subset
    (isClosed_box1 hU) ?_
  intro g hg i j
  have h := hg.2 i j
  rw [abs_le] at h
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- **The conjugated box is compact.**  `conjBox U t` is the image of the compact set `Box1 U`
under the homeomorphism `g ↦ aDiag t · g · (aDiag t)⁻¹`. -/
theorem isCompact_conjBox {U : Subgroup SL3} (hU : IsHoro U) (t : Fin 3 → ℝ) :
    IsCompact (conjBox U t) := by
  rw [conjBox, conjBy]
  exact (isCompact_box1 hU).image
    ((continuous_const.mul continuous_id).mul continuous_const)

/-! ## Measurability of the mass of the conjugated box -/

theorem measurable_growthFun {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] {U : Subgroup Work.EKLContract.SL3}
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' : Set Work.EKLContract.X3} (hL : Work.EKLContract.IsLeafwise μ U ν X')
    (hν : ∀ x : Work.EKLContract.X3, MeasureTheory.IsFiniteMeasureOnCompacts (ν x))
    (hU : Work.EKLContract.IsHoro U) (t : Fin 3 → ℝ) :
    Measurable (fun x : Work.EKLContract.X3 =>
      (ν x (Work.EKLC6Core.conjBox U t)).toReal) := by
  exact (Work.EKLCompLeaf.measurable_apply_isCompact hL.measurable hν
    (isCompact_conjBox hU t)).ennreal_toReal

end Work.EKLC6Core

end
