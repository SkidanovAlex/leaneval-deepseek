import Mathlib
import Submission.NK.GlobalCFT.Place
import Submission.NK.GlobalCFT.Inclusion.globalCFT_localAction
import Submission.NK.Chebotarev.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Import bundle for the `HRec` node `B1`

`request_lemma`'s `depends_on` accepts only modules under `Submission.Work.*`, and the statement of
the `HRec` node `B1` (`Work.SSGRoute.HRec.exists_cyclic_level_dvd`) needs the `NK.GlobalCFT.Place`
vocabulary (`Place`, `Place.LiesOver`, `Place.ofFinite`) with its Galois `MulAction`, and the
Chebotarev development underneath.  This module bundles those imports so that the node can be
requested from the workspace.
-/
