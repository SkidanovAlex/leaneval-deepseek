/-
Copied from `Submission/Work/A7F/isFourGroup_V1_V2.lean` with the import list adapted to the
CORE4 world (see the note below); the `Work.A7F` content is unchanged.

**Why a copy:**  the areas of this workspace each carry their own verbatim copy of the `Work.GW2`
vocabulary (`Contracts2.lean`), and two of them cannot be imported into one environment
(`environment already contains 'Work.GW2.A7ModelProp'`).  This file therefore takes the
`Work.GW2` vocabulary from `Submission.Work.CORE4.Defs` and imports `Submission.Work.A7.Defs`
(clash-free) instead of `Submission.Work.A7F.Defs`.
-/
import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.A7.Defs
import Submission.Work.CORE4.A7M.Defs
import Submission.Work.A7F.isFourGroup_V1_V2

open scoped MatrixGroups

namespace Work.A7F

open Subgroup

/-! ## The explicit four-element subgroups -/


/-! ## The explicit subgroups are the closures of the two generators -/


/-! ## `V₁` and `V₂` are Klein four-groups -/


/-! ## The elements of `V₁` and `V₂` -/


/-! ## The requested statement -/


end Work.A7F
