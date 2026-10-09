import Mathlib
import Submission.NK.GlobalCFT.IdeleNorm
import Submission.NK.GlobalCFT.GlobalCFT
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Import shim for the log-map section statement

This module only re-exports the idèle/place machinery used by the statements in this directory, so
that those statements can be delegated to files whose import list is derived from `depends_on`.
It makes available, in particular, `NK.GlobalCFT.Idele K`, `NK.GlobalCFT.Idele.abs`,
`NK.GlobalCFT.Place.ofInfinite`, the norm `‖·‖` on the completions `w.Completion` at infinite
places, and the weight `w.mult`.
-/

set_option autoImplicit false
