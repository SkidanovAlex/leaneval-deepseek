/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area JacClose (Submission/Work/NOTES_LEAD_jacobian_closure.md §2.C)
-/
import Submission.Work.JacClose.Basic
import Submission.Work.JacClose.ChartsK
import Submission.Work.JacClose.Inputs
import Submission.Work.JacClose.Close
import Submission.Work.JacClose.ClosePos
import Submission.Work.JacClose.Wiring
import Submission.Work.JacClose.nonempty_symBCNaming
import Submission.Work.JacClose.symGeomFamilyData
import Submission.Work.JacClose.posSymGalBeta
import Submission.Work.JacClose.posCovOrbit
import Submission.Work.JacClose.posData
import Submission.Work.JacClose.normal_sym
import Submission.Work.JacClose.normal_sym_tensor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Area `JacClose` — the closure chapter

Import this module for the whole area.  See `Submission/Work/JacClose/NOTES.md` for the full
description of what is proved, what is assumed and what remains.

* `Basic` — the C1 naming data of `Work.BcDiv.symBC`;
* `nonempty_symBCNaming` — C1, proved;
* `ChartsK` — C2: `GalCharts.chartsK'` and its two defining equations, and TL′
  (`GalCharts.inChart_of_inChart_k`);
* `Inputs` — C3/C4: `SYData`, `ResidOld`, `gcInput`, `symQuotData`, `KLLemma`, `upInput`;
* `symGeomFamilyData` — the `SYData` of `SymQuot.symGeomFamily`, proved;
* `posSymGalBeta` — C5, proved (file `posSymGalBeta.lean`);
* `posCovOrbit` — C6, proved (file `posCovOrbit.lean`);
* `normal_sym`, `normal_sym_tensor` — the two normality fields of the corrected RESID
  interface, proved;
* `Close` — the concrete `k'`-level inputs `closeInputs`/`closeIn`, the `Data` assembly
  `closeData`/`closeData_of`, and the *statements* C5/C6 as the `Prop`s `symGalBetaProp` and
  `closeCovOrbitProp`;
* `Wiring` — C7: the wiring of the challenge's `jacPkgExists`.
-/
