/-
# Layer C2 (DeTurck pull-back): shared import kit for the time-derivative lemmas

This module is a pure re-export: it imports the frozen interface vocabulary
(`Submission.Diff.SMet`, `Submission.Diff.JointSmooth`, `Submission.Diff.LCSmooth`,
`Submission.Diff.lcOf`, `Submission.Diff.ricAt`, the ODE contract) together with the packaged
pull-back constructions of `Submission.Work.Diff.STE.C2.Defs`.

It exists so that lemmas about those objects can be *stated* (and delegated) in files whose only
imports are modules under `Submission/Work/`, without repeating the long import list.
-/

import Submission.Diff.ODE
import Submission.Work.Diff.STE.C2.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
