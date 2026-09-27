import Mathlib
import Submission.Mostow.Interfaces
import Submission.Mostow.HLDefs

/-!
# Access module for the lead's vocabulary

`Submission.Mostow.HLDefs` (and `Submission.Mostow.Interfaces`) live outside `Submission/Work`,
so they cannot be named directly in `depends_on`.  This module re-exports them so that lemmas
stated in the lead's vocabulary (`hdist`, `NearIdAt`, `MultThickProp`, `PO n 1`, ...) can list
`Mostow.hlDefsAccess` as a dependency.

Written by the `frameThinFar` agent; safe to import.
-/
