import Submission.Work.Serre.EulerFibreRoot
import Submission.Work.Serre.eulerFibreRange
import Submission.Work.Serre.thomCylCellStepAlt

/-!
# The target `Work.Serre.thomIsoCylFibreRange`

The target of this module is the relative global Thom class statement of a rational spherical
fibration, `Work.Serre.ThomIsoCylFibreRange` (`Submission/Work/Serre/GysinFibreRange.lean`).

Everything this module used to prove (the definition `Work.Serre.EulerFibreRange`, the reduction
`Work.Serre.thomIsoCylFibreRange_of_eulerFibreRange`, and the elementary helpers) has been moved to
the *upstream* module `Submission.Work.Serre.EulerFibreRoot`, so that this module can eventually
import the modules that prove `EulerFibreRange`.  See
`Submission/Work/Serre/TICFR_SESSION_NOTES.md` (FINDING 1) and
`Submission/Work/Serre/ticfrAssembly.lean` (the endgame, verified with the cellular step as a
hypothesis).
-/

namespace Work.Serre

open CategoryTheory CategoryTheory.Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-! ## The target, reduced to the cellular step

**ARCHITECTURAL NOTE (session finding, now repaired).**  Until this session, this module could
*not* import `Submission.Work.Serre.eulerFibreRange`: that module (and
`Submission.Work.Serre.thomCylBaseCase`, `…eulerClass_of_thomBdd`, `…exists_cupWith_of_preimage`)
imported *this* module for the declarations `EulerFibreRange`,
`thomIsoCylFibreRange_of_eulerFibreRange`, `isZero_coh_of_ratAcyclic`, `isIso_relToAbs_succ`, …,
which made importing it back a **build cycle** (Lean: `bad import … build cycle detected`).  The
declarations have now been moved to the *upstream* module `Submission.Work.Serre.EulerFibreRoot`
(names unchanged) and those import lines point there, so the cycle is gone and this module can
import the chain.  See `Submission/Work/Serre/TICFR_SESSION_NOTES.md`, FINDING 1.

The whole remaining content of the target is the *cellular step* `Work.Serre.ThomCylCellStepAlt`
(`Submission/Work/Serre/thomCylCellStepAlt.lean`), i.e. the single step of the cell-by-cell
induction of the relative Thom class over an attachment.  Everything else is assembled:

* `Work.Serre.cwModelThomCase_of_altCellStep` (in `Submission/Work/Serre/eulerFibreRange.lean`)
  turns the cellular step into the CW-model case `Work.Serre.CWModelThomCase`;
* `Work.Serre.eulerFibreRange_of_cwModelCase` (same file, proved, axiom-clean) turns the CW-model
  case into the absolute Euler-class form `Work.Serre.EulerFibreRange`;
* `Work.Serre.thomIsoCylFibreRange_of_eulerFibreRange` (proved above) turns that into the target.

The conditional form of this reduction is recorded in
`Submission/Work/Serre/ticfrAssembly.lean` (an independent check of the same wiring).
-/

/-! ## The target -/

/-- **The global Thom class of a rational spherical fibration in the fibre range.**

The proof is the whole assembly: the cellular step `Work.Serre.thomCylCellStepAlt`
(`Submission/Work/Serre/thomCylCellStepAlt.lean`) gives the CW-model case, the CW-model case gives
the absolute Euler-class form, and the Euler-class form gives the relative statement.  The only
input is `Work.Serre.thomCylCellStepAlt`; this module therefore becomes `sorry`-free (and
`#print axioms` clean) as soon as that cellular step is completed. -/
theorem thomIsoCylFibreRange : Work.Serre.ThomIsoCylFibreRange :=
  thomIsoCylFibreRange_of_eulerFibreRange
    (eulerFibreRange_of_cwModelCase (cwModelThomCase_of_altCellStep thomCylCellStepAlt))

end

end Work.Serre
