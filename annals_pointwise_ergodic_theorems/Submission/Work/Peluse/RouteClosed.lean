import Mathlib
import Submission.Work.Peluse.Route
import Submission.Work.Peluse.SwapA.wiring
import Submission.Work.Peluse.SwapC.concatAll
import Submission.Work.Peluse.prop36SW_of_ladderA

/-!
# `Work.Peluse.AreaA2` — the area closed

The two named hypotheses of `Work.Peluse.KMTContract_AreaA2_of_openNodes` (`Route.lean`) are now
both discharged:

* **`h51`** (`∀ t ≥ 1, LadderP.lemma51P t`): the `Swap` route.  Its tree is `sorry`-free as of
  session 24 —
  `Work.Peluse.SwapC.concatStep` is discharged by `Work.Peluse.SwapC.concatStepProved`
  (KKL Lemma 6.1, the subject of `HANDOVER_h51_concatStep.md`), so `Work.Peluse.SwapC.concatAll`
  supplies `ConcatAllP`, `Work.Peluse.SwapE.denseEndgame` supplies `DenseEndgameP`, and
  `Work.Peluse.SwapA.lemma51P_all_of_concat` assembles them;
* **`hO2`**: `Work.Peluse.prop36SW_of_ladderA` (Peluse's Prop 3.6 from her Lemma 5.7), whose two
  branches are `Work.Peluse.prop36SW_body` (the §5 chain) and `Work.Peluse.prop36SW_degenerate`
  (the extension route for degenerate data).

Consequently `Work.KMTContract.AreaA2` — the contract's frozen target — is proved unconditionally,
and with it `Work.Peluse.AreaA2` (via `Compatible.areaA2_iff`) and
`Work.Peluse.PeluseInverseKMT P` at every `P` of degree ≥ 2.
-/

set_option autoImplicit false
open scoped BigOperators
open Polynomial

namespace Work.Peluse

noncomputable section

/-- **`lemma51P` at every level, from the `Swap` route.** -/
theorem lemma51P_all' : ∀ t : ℕ, 1 ≤ t → Work.Peluse.LadderP.lemma51P t :=
  Work.Peluse.SwapA.lemma51P_all_of_concat Work.Peluse.SwapC.concatAll

/-- **O2**, in the exact hypothesis form of the route. -/
theorem O2_holds : ∀ P : Polynomial ℤ, 2 ≤ P.natDegree →
    Work.Peluse.C46.PeluseLadderA → Work.Peluse.C46.Prop36SW P :=
  fun P hd h => Work.Peluse.prop36SW_of_ladderA P hd h

/-- **`Work.KMTContract.AreaA2`** — the frozen target of area A2, unconditionally. -/
theorem kMTContract_AreaA2 : Work.KMTContract.AreaA2 :=
  Work.Peluse.KMTContract_AreaA2_of_openNodes lemma51P_all' O2_holds

/-- **`Work.Peluse.AreaA2`** — the same statement in the area's own vocabulary. -/
theorem areaA2 : Work.Peluse.AreaA2 :=
  (Work.Peluse.areaA2_iff).mp kMTContract_AreaA2

/-- **Peluse's inverse theorem** (`Work.Peluse.PeluseInverseKMT`) at every `P` of degree `≥ 2`. -/
theorem peluseInverseKMT (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) :
    Work.Peluse.PeluseInverseKMT P :=
  areaA2 P hd

end

end Work.Peluse
