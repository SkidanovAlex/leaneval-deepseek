/-
Import umbrella for the `isAdmissible_of_artinKillsPrincipal` lane: it re-exports the workspace's
ideal-theoretic reciprocity vocabulary (Lang's Chapter X Theorem 2 index machinery, the idèle-ideal
dictionary map `theta`, Hilbert reciprocity for cyclic extensions, the one-place idèle dictionary,
the local norm subgroups and the cyclic norm index theorem) so that lemmas delegated inside
`Submission/Work` can state their conclusions without importing `Submission.NK` modules directly.
-/
import Mathlib
import Submission.Work.SSGRoute.ZDataMup.MyImports
import Submission.NK.CFTLib.ArtinReciprocityIdeal.langX2KernelLe
import Submission.NK.CFTLib.ArtinReciprocityIdeal.indexIdealCoprimeLeNormClassIndex
import Submission.NK.CFTLib.ArtinReciprocityIdeal.Conductor
import Submission.NK.CFTLib.hilbertReciprocity_cyclic
import Submission.NK.CFTLib.IdeleHasse.range_localNormFinite_eq_of_liesOver
import Submission.NK.CFTLib.IdeleHasse.localGlobalArtinSetup
import Submission.NK.GlobalCFTdeep.SecondInequalitySolvable
import Submission.NK.HassePrinciple.IdeleCocycle
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
