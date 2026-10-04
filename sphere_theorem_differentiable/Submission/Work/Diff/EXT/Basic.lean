import Submission.Diff.Interfaces

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `EXT` area: re-export of the frozen interface module

Delegated lemmas of the `EXT` (continuation / Shi estimates) area are stated in the vocabulary of
`Submission.Diff.Interfaces` (`SMet`, `IsRicciFlow`, `CurvBound`, `JointSmooth`, `Extension`, ...).
This module simply re-exports it, so that a delegated statement can list `Diff/EXT/Basic` in
`depends_on` and be elaborated against the frozen definitions.
-/
