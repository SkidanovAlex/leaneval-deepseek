import Mathlib
import Submission.Diff.Alg
import Submission.Diff.Interfaces

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Shared imports for the `PP` area (curvature evolution + Hamilton's maximum principle)

This module only re-exports the frozen contract modules, so that delegated lemmas in this area can
name `Curv4`, `Q`, `Iso`, `IsInvariantFamily`, `SMet`, `IsRicciFlow`, … while importing a single
module under `Submission/Work`.
-/
