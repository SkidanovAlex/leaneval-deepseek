/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area FUS, `Work.FUS`)

# Area FUS: the contract vocabulary and the two FUS deliverables

The build keeps the contract vocabulary (`Work.GW2.oddCore`, `Work.GW2.oddCoreIn`,
`Work.GW2.IsFourGroup`, …) and the statements of all area `Prop`s, copied verbatim from
`Submission/Work/_design_gw/Contracts2.lean`, in one canonical module:
`Submission.Work.ASM.Defs`.  Every area imports and re-exports it (this is the convention used by
`Work.DSTR.Defs`, `Work.CORE2A.Defs`, …), so that the shared names have a single definition site.

This file is area FUS's re-export.  In particular the two `Prop`s owned by area FUS are available
from here under their contract names:

* `Work.GW2.InvolutionFusionProp` (Gorenstein 7.7.3 / Bender 1.6, last sentence);
* `Work.GW2.CentralizerSplitProp` (`C(t) = O(C(t))·S`).

(Their statements in `Submission.Work.ASM.Defs` are byte-identical to the FUS section of
`Contracts2.lean`, so no copy is duplicated here and no definition-site clash can arise.)

Their *proofs* are the area's deliverables and live in the sibling files:

* `Submission/Work/FUS/Dihedral.lean`    — the reflection sign on a dihedral group, small arithmetic;
* `Submission/Work/FUS/Fusion.lean`      — `Work.FUS.involutionFusionProp`;
* `Submission/Work/FUS/Split.lean`       — `Work.FUS.centralizerSplitProp`;
* `Submission/Work/FUS/Deliverable.lean` — both, as `Work.FUS.fus_deliverable`.

`Submission/Work/FUS/NOTES_FUS.md` is the guide to the whole area.
-/
import Submission.Work.ASM.Defs
