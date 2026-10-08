/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DSTR area (fundmath3-gorenstein_walter), `Work.DSTR.d16`

# Elementary facts about `F_{2'}(X)`, `O(X)`, `F(X)`

Supporting lemmas for `Work.DSTR.d16` (Bender 1.6).

NOTE (world compatibility).  Files of the areas `GLUE`, `RED`, `BMAX`, … each carry their own
copy of the `Work.GW2` vocabulary and therefore cannot be imported next to
`Submission.Work.DSTR.Defs` (which re-uses `Submission.Work.ASM.Defs`): Lean rejects the second
copy of names such as `Work.GW2.BenderSetup`.  This area therefore uses only `Mathlib`,
`Submission.OddOrder.*`, `Submission.Work.ASM.*` and `Submission.Work.DSTR.*`/`CORE2A.*`.
-/
import Mathlib
import Submission.Work.DSTR.Defs
import Submission.Work.DSTR.D16Aux
import Submission.Work.DSTR.fittingSelfCentralizing
import Submission.Work.ASM.oddCore_odd
import Submission.Work.CORE2A.thm26_aux

open scoped MatrixGroups

namespace Work.DSTR

open Subgroup

/-- `O_π(X)` is normal in `X`. -/
instance piCore_normal (π : Set ℕ) (G : Type*) [Group G] : (Work.GW2.piCore π G).Normal :=
  Subgroup.normalCore_normal _

/-- `F(X)` is normal in `X`. -/
instance fitting_normal (G : Type*) [Group G] : (Work.GW2.fitting G).Normal :=
  Subgroup.normalCore_normal _

/-- **Bender 1.2** in this area's vocabulary.  Alias of
`Work.DSTR.fittingSelfCentralizing`, kept here for downstream files. -/
theorem fittingSelfCentralizing' : Work.GW2.FittingSelfCentralizingProp :=
  fittingSelfCentralizing

end Work.DSTR
