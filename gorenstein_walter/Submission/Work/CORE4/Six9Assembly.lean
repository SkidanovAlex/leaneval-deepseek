/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)

# AREA CORE4 — `§4 (6)` assembled: `Case2SixImpl9` from the design-19 leaves

`Submission/Work/CORE4/Defs19.lean` (copied verbatim from `_design_gw/Core19.lean`) proves the
assembly `Work.GW2.C19.six9_of_leaves`: the target `Work.GW2.Case2SixImpl9` (Bender §4 (6)) follows
from the eight leaf propositions S1, S2, S3, `QOddCent`, S4, S5, TI, CY.

This file discharges them with the leaf theorems proved in the area:

* S1 `Submission/Work/CORE4/SixENotLeHhat.lean`,
* S2 `Submission/Work/CORE4/SixTInLayerN.lean`,
* S3 `Submission/Work/CORE4/SixELeLayerN.lean`,
* `Submission/Work/CORE4/QOddCent.lean` (the A₇/L₂(q) centralizer fact),
* S4 `Submission/Work/CORE4/SixLayerNLeM.lean` (a function of `QOddCent`),
* S5 `Submission/Work/CORE4/SixStarOfLayer.lean`,
* TI `Submission/Work/CORE4/SixTIOfStar.lean`,
* CY `Submission/Work/CORE4/SixCycOfTI.lean` (proved here, from
  `Case2Six9Aux.exists_witness_of_case2pre` and `Case2Six9Aux.isCyclic_F_of_witness_and_ti`).

The main export is `Work.CORE4.case2SixImpl9_holds`.  The older `Case2SixImpl` (no `Case2PrePlus`)
is obtained the same way via `Work.GW2.C19.six_of_leaves`.
-/
import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Defs19
import Submission.Work.CORE4.SixENotLeHhat
import Submission.Work.CORE4.SixTInLayerN
import Submission.Work.CORE4.SixELeLayerN
import Submission.Work.CORE4.QOddCent
import Submission.Work.CORE4.SixLayerNLeM
import Submission.Work.CORE4.SixStarOfLayer
import Submission.Work.CORE4.SixTIOfStar
import Submission.Work.CORE4.SixCycOfTI

namespace Work.CORE4

/-- **Bender §4 (6), fully discharged**: `Case2SixImpl9` for every `I : C4Inputs`, assembled from
the eight design-19 leaves by `Work.GW2.C19.six9_of_leaves`. -/
theorem case2SixImpl9_holds (I : Work.GW2.C4Inputs) : Work.GW2.Case2SixImpl9 I :=
  Work.GW2.C19.six9_of_leaves I (SixENotLeHhat I) (SixTInLayerN I) (SixELeLayerN I)
    (QOddCent I) (SixLayerNLeM I) (SixStarOfLayer I) (SixTIOfStar I) (SixCycOfTI I)

/-- The same leaves give the older `Case2SixImpl` (which does not mention `Case2PrePlus`). -/
theorem case2SixImpl_holds (I : Work.GW2.C4Inputs) : Work.GW2.Case2SixImpl I :=
  Work.GW2.C19.six_of_leaves I (SixENotLeHhat I) (SixTInLayerN I) (SixELeLayerN I)
    (QOddCent I) (SixLayerNLeM I) (SixStarOfLayer I) (SixTIOfStar I) (SixCycOfTI I)

end Work.CORE4
