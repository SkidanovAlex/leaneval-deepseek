import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLC6Core.uminus_isHoro
import Submission.Work.EKLC6Core.fiber_leafwise

/-!
# `Work.EKLC6Core.fiber_leafwise_thm` — Pisa 7.22 (the fibres carry the leaf-wise system)

This module is now a **thin alias** of `Work.EKLC6Core.fiber_leafwise`, which proves the very
same statement (Pisa 7.22) in a fully axiom-clean way:

`fiber_leafwise (t) (hmp) (hL) (hcov) (hX'') :  ∀ᵐ x ∂μ, IsLeafwise (κ x) (Uminus t) ν X'`.

The statement was originally delegated here as `fiber_leafwise_thm` and its prover judged *that
module's* route (transferring all nine `IsLeafwise` fields from `μ` to the ergodic component
`κ x = condExpKernel μ (invariants T) x` by hand, in particular the `condexp` field) to ask for a
uniformity in the pair (plaque algebra, test function) that the `=ᵐ`-transfers do not deliver.
The sibling development `fiber_leafwise.lean` reaches the same conclusion by a different route
(Hopf saturation `invariant_inter_plaque_ae`, the flower-based uniqueness
`leafwise_eq_of_flower_clauses` and the atom-saturation lemmas) and is `sorry`-free and
axiom-clean.  This file exists only so that the consumers
(`ent_le_growth_fiber`, `fiber_leafwise_along`, …) keep their import path; it adds no content.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- **Pisa 7.22.**  The leaf-wise system `ν` of a `T`-invariant measure `μ` (with
`T = aDiag t ·`) is also a leaf-wise system for the ergodic components
`condExpKernel μ (invariants T) x`.  Alias of `Work.EKLC6Core.fiber_leafwise`. -/
theorem fiber_leafwise_thm {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] [StandardBorelSpace Work.EKLContract.X3]
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3} (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    (hL : Work.EKLContract.IsLeafwise μ (Work.EKLC6Core.Uminus t) ν X')
    (hcov : Work.EKLC6Core.ACovariant ν X'') (hX'' : μ (X''ᶜ) = 0) :
    ∀ᵐ x ∂μ, Work.EKLContract.IsLeafwise
      (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants
        (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x)) x)
      (Work.EKLC6Core.Uminus t) ν X' :=
  fiber_leafwise t hmp hL hcov hX''

end Work.EKLC6Core

end
