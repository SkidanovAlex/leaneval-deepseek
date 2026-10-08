/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)

# AREA CORE4 — the `A₇` fact of §4 p. 226, re-exported in `Work.GW2`

`Work.CORE4.A7S4` (in `Submission/Work/CORE4/A7S4.lean`) proves `Work.GW2.A7S4Prop`, the `a7s4`
field of `C4Inputs`.  This tiny module re-exports it under a name in the `Work.GW2` namespace, so
that a caller building a `C4Inputs` can fill that field with `Work.GW2.A7S4Prop_holds` without
depending on the internal vocabulary of `Submission.Work.CORE4.A7S4Defs`.

It is kept separate from `Assembly.lean` so that the assembly does not have to build the (large)
`A₇` computation.
-/
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.A7S4

namespace Work.GW2

/-- The `A₇` structure fact of Bender §4 p. 226 (proved in `Work.CORE4.A7S4`). -/
theorem A7S4Prop_holds : A7S4Prop := Work.CORE4.A7S4

end Work.GW2
