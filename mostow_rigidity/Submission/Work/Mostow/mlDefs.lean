import Mathlib
import Submission.Mostow.HLDefs
import Submission.Mostow.Interfaces
import Submission.Work.Mostow.Hyper
import Submission.Work.Mostow.BaryBase
import Submission.Work.Mostow.poAux
import Submission.Work.Mostow.StabLift
import Submission.Work.Mostow.margulisPairDefs
import Submission.Work.Mostow.margulisCuspDefs

/-!
# Shared vocabulary for `Work.Mostow.margulisLox`

A single import point for the interface, the `LoxPair`/`NearIdAt`/`PairStabProp` vocabulary of
`Submission.Mostow.HLDefs`, and the auxiliary facts of `Hyper`/`BaryBase`/`poAux`.

It also defines

* `Pres2 g z w` : `g` permutes the two-point set `{z, w}` of the boundary sphere.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {n : ℕ}

/-- `g` permutes the two-point set `{z, w}` (either fixing both points or swapping them). -/
def Pres2 (g : PO n 1) (z w : E n) : Prop :=
  (bd g z = z ∧ bd g w = w) ∨ (bd g z = w ∧ bd g w = z)

end

end Work.Mostow
