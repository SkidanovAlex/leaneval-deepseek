import Mathlib
import Submission.Work.Peluse.SwapA.lemma51P_all
import Submission.Work.Peluse.SwapE.Node

/-!
# Wiring the `SwapE` endgame into the assembly

`Work.Peluse.SwapE.denseEndgame` (subproject `Peluse/SwapE`) is the linear-in-law endgame, stated
verbatim; it discharges the hypothesis `DenseEndgameP` of `SwapProps.lean`.  The remaining input of
the assembly is the concatenation `ConcatAllP` of subproject `Peluse/SwapC`, kept as a hypothesis
here: `Work.Peluse.SwapC.concatAll` currently still rests on `concatStep`
(`Submission/Work/Peluse/SwapC/concatStep.lean`), so wiring it in would make these files depend on
`sorryAx`.  As soon as that file is `sorry`-free,

```
Work.Peluse.SwapA.p3Heart_all
  : ∀ t : ℕ, 1 ≤ t → Work.Peluse.LadderP.p3Heart t
  := p3Heart_all_of (show ConcatAllP from Work.Peluse.SwapC.concatAll)
      Work.Peluse.SwapE.denseEndgame
```

and `lemma51P_all' := lemma51P_all_of (show ConcatAllP from …) Work.Peluse.SwapE.denseEndgame`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

open scoped BigOperators

namespace Work.Peluse.SwapA

noncomputable section

/-- **The heart at every level, with the endgame of `SwapE` discharged**: the only remaining
hypothesis is the concatenation node `ConcatAllP` (subproject `Peluse/SwapC`). -/
theorem p3Heart_all_of_concat (hAll : ConcatAllP) :
    ∀ t : ℕ, 1 ≤ t → Work.Peluse.LadderP.p3Heart t :=
  p3Heart_all_of hAll Work.Peluse.SwapE.denseEndgame

/-- **The heart at the window `symIcc N`, with the endgame of `SwapE` discharged.** -/
theorem p3HeartB_all_of_concat (hAll : ConcatAllP) :
    ∀ t : ℕ, 1 ≤ t → Work.Peluse.LadderP.p3HeartB t :=
  p3HeartB_all_of hAll Work.Peluse.SwapE.denseEndgame

/-- **Peluse's Lemma 5.1 at every level, with the endgame of `SwapE` discharged.** -/
theorem lemma51P_all_of_concat (hAll : ConcatAllP) :
    ∀ t : ℕ, 1 ≤ t → Work.Peluse.LadderP.lemma51P t :=
  lemma51P_all_of hAll Work.Peluse.SwapE.denseEndgame

end

end Work.Peluse.SwapA
