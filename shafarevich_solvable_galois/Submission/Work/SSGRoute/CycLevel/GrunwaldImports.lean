import Mathlib
import Submission.NK.GlobalCFT.GlobalCFT
import Submission.NK.GlobalCFT.Place
import Submission.NK.HassePrinciple.IdeleCocycle
import Submission.NK.CFTLib.IdeleHasse.localGlobalArtinMap_exists
import Submission.NK.CFTLib.IdeleHasse.onePlace_localNorm
import Submission.NK.CFTLib.IdeleHasse.localNormSubgroup
import Submission.Work.SSGRoute.CFTSide.classField_exists_of_index
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Import bundle for the per-place Grünwald step

The global class field theory vocabulary (`NK.GlobalCFT`: the idèle class group `C_k`, the local
fields `k_v`, the one-place idèles, the Artin map) lives outside `Submission.Work`, and
`request_lemma`'s `depends_on` only accepts modules under `Submission.Work.*`; everything needed by
the per-place Grünwald statement
(`Submission.Work.SSGRoute.CycLevel.grunwald_odd_single_place`) is therefore re-exported here.
-/
