import Mathlib
import Submission.Work.Mostow.KMcovol
import Submission.Work.Mostow.margulisCusp
import Submission.Work.Mostow.margulisLox
import Submission.Work.Mostow.pairStab
import Submission.Work.Mostow.classify_ge2
import Submission.Work.Mostow.multThick_ge2
import Submission.Work.Mostow.poAction_ge1
import Submission.Work.Mostow.hypIsometry_ge1

/-!
# The Kazhdan–Margulis covolume bound, unconditionally

`Work.Mostow.KMcovol` is stated with the four chapter `Prop`s (`MargulisCuspProp`,
`MargulisLoxProp`, `PairStabProp`, `ClassifyProp`) and `MultThickProp` for each lattice as
hypotheses.  All of these are now proved as lemmas of the workspace, and the action/isometry
`Prop`s are available in every dimension `≥ 1` (`Work.Mostow.poAction_ge1`,
`Work.Mostow.hypIsometry_ge1`).  Hence `CovolLB N` holds for every `N ≥ 2` with no hypotheses at
all, which is the form every caller wants.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

/-- **Kazhdan–Margulis in every dimension `≥ 2`, unconditionally.** -/
theorem covolLB_uncond (N : ℕ) (hN : 2 ≤ N) : CovolLB N := by
  have h1 : 1 ≤ N := by omega
  have hA : POActionProp N := poAction_ge1 N h1
  have hI : HypIsometryProp N := hypIsometry_ge1 N h1 hA
  have hPS : PairStabProp N := fun ξ η hξ hη hne => pairStab_pairStab N hN hA hI ξ η hξ hη hne
  exact KMcovol N hN hA hI (margulisCusp N hN hA hI) (margulisLox N hN hA hI hPS) hPS
    (classify_ge2 N hN hA hI) (fun Λ hΛ => multThick_ge2 N hN hA hI Λ hΛ)

end Work.Mostow
