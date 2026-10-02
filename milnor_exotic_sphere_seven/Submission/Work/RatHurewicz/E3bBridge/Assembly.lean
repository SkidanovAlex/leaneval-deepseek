import Submission.Work.RatHurewicz.E3bBridge.SerreE3bR
import Submission.Work.RatHurewicz.E3bBridge.EulerFibreRangeR
import Submission.Work.RatHurewicz.E3bBridge.EulerFibreRootR
import Submission.Work.Serre.thomCylCellStepAlt

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The island bridge: `SerreE3b` from the cellular step, on the RATHUREWICZ island

The E3(b) node of the project (`Work.Serre.SerreE3b`, the Gysin / Euler-class theorem of a rational
spherical fibration) is assembled in the SERRE area on top of the single open cellular step
`Work.Serre.thomCylCellStepAlt`:

* `Work.Serre.thomIsoCylFibreRange_of_cellStep` = `e3bR_thomIsoCylFibreRange_of_eulerFibreRange`
  applied to `e3bR_eulerFibreRange_of_cwModelCase` applied to `e3bR_cwModelThomCase_of_altCellStep`
  (`Submission/Work/Serre/ticfrAssembly.lean`, `…/thomIsoCylFibreRange.lean`),
* `Work.Serre.e3bR_serreE3b_of_thomCyl` (`Submission/Work/Serre/serreE3b.lean`) is the last step.

That assembly **cannot be imported into the RATHUREWICZ island** (which is the island of the
target `Work.RatHurewicz.sphere_stem_torsion`) because of two duplicate declarations with
*different types*: `Work.Serre.isZero_ratCoh_of_isZero_ratH` (and `isZero_dual_of_isZero`,
`isZero_ratH_of_conn`) are declared both in the SERRE E3(b) files and in
`Submission/Work/Serre/gysinCupIsoReduction.lean`, which is imported by the `C2` layer
(`Work.Stems.Engine.C2EvenRange`, …) on the RATHUREWICZ side.

This module resolves that by cloning the seven SERRE E3(b) modules involved (with the three
clashing names renamed to `e3bR_…`, and with the `sorry`-carrying declarations dropped), and then
performing the assembly here.

**Naming convention (H5, 2026-09-27).**  *Every* declaration of this clone that copies a
declaration of area SERRE's E3(b) node now carries the `e3bR_` prefix — not only the three helpers
named above — because a copy under the original name makes the clone impossible to import together
with SERRE's own files (`Work.Serre.EulerFibreRange`, `Work.Serre.CWModelThomCase`,
`Work.Serre.thomCylBaseCase`, `Work.Serre.periodicity_of_serreFibration`, … all collided).  The
prefix is what lets `Submission.Work.Serre.serreE3b` be imported alongside this island, area H5's
chain and area STEMS-B's `contractIsland`.  **Do not rename them back.**  See
`Submission/Work/Stems/INSURANCE_CHAIN_NOTES.md` and `HANDOFF.md` (addendum "H5: `e3bR_` rename of
the E3(b) clone").  Nothing else is changed; the clones are mechanical copies of

* `Submission/Work/Serre/EulerFibreRoot.lean` (`…E3bBridge.EulerFibreRootR`),
* `Submission/Work/Serre/e3bR_periodicity_of_serreFibration.lean` (`…E3bBridge.PeriodicityR`),
* `Submission/Work/Serre/e3bR_thomCylBaseCase.lean` (`…E3bBridge.ThomCylBaseCaseR`),
* `Submission/Work/Serre/e3bR_eulerClass_of_thomBdd.lean` (`…E3bBridge.EulerClassOfThomBddR`),
* `Submission/Work/Serre/e3bR_exists_cupWith_of_preimage.lean` (`…E3bBridge.ExistsCupWithOfPreimageR`),
* `Submission/Work/Serre/cwModelThomCase.lean` (`…E3bBridge.CwModelThomCaseR`, without the open
  `thomCylCellStep` and the theorem depending on it),
* `Submission/Work/Serre/eulerFibreRange.lean` (`…E3bBridge.EulerFibreRangeR`),
* `Submission/Work/Serre/serreE3b.lean` (`…E3bBridge.SerreE3bR`, without the final `serreE3b`).

The cellular step itself (`Submission/Work/Serre/thomCylCellStepAlt.lean`) is imported directly:
it is **free of clashes** with the RATHUREWICZ island, and its still-open `sorry` is harmless here
because the statements below take it as a *hypothesis*.
-/

namespace Work.RatHurewicz

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- **The global Thom class from the cellular step** (the SERRE assembly, redone on this island). -/
theorem thomIsoCylFibreRange_of_cellStep (h : Work.Serre.e3bR_CellStepProp) :
    Work.Serre.ThomIsoCylFibreRange :=
  Work.Serre.e3bR_thomIsoCylFibreRange_of_eulerFibreRange
    (Work.Serre.e3bR_eulerFibreRange_of_cwModelCase
      (Work.Serre.e3bR_cwModelThomCase_of_altCellStep h))

/-- **E3(b) (Gysin / Euler class of a rational spherical fibration) from the cellular step.**

This is the statement that the whole STEMS/SERRE endgame of the project rests on, made available
in the RATHUREWICZ island so that the target `Work.RatHurewicz.sphere_stem_torsion` can consume it. -/
theorem serreE3b_of_cellStep (h : Work.Serre.e3bR_CellStepProp) : Work.Serre.SerreE3b :=
  Work.Serre.e3bR_serreE3b_of_thomCyl (thomIsoCylFibreRange_of_cellStep h)

end

end Work.RatHurewicz
