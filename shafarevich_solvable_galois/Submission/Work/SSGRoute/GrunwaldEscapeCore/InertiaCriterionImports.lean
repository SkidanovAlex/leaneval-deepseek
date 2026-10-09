import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.GrunwaldEscapeCore.escape_vocab
import Submission.Work.SSGRoute.EscapeCoreLib.charSeparation
import Submission.Work.SSGRoute.ZConstruction.localKummerDictionary
import Submission.NK.CFTLib.IdeleHasse.onePlace_localNorm
import Submission.NK.CFTLib.IdeleHasse.localFaithfulDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Import hub for the Kummer inertia criterion

Collects the vocabulary needed to *state* `onePlace_mem_gesU_of_kummerChar_eq_zero_on_inertia` in
one module path under `Submission/Work`, so that the statement can be delegated with a single
`depends_on` entry (the modules of `Submission/NK` live outside the `Submission.Work` namespace,
which the delegation harness prefixes).
-/
