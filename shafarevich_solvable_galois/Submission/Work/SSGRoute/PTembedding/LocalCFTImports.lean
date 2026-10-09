/-
Import bundle for the local class field theory chapter as needed by
`Submission/Work/SSGRoute/PTembedding/`: the Artin reciprocity datum for a `p`-adic completion
(`NK.LocalCFT.ArtinReciprocity`, `NK.LocalReciprocityLubinTate.artinReciprocity_adicCompletion`),
the norm-indexed vocabulary of `NK.LocalReciprocity` (norm groups, maximal abelian subextension)
and the completion of the unit group (`NK.LocalReciprocity.completionUnits`).
-/
import Submission.NK.LocalReciprocity.All
import Submission.NK.LocalReciprocityLubinTate.Target
import Submission.NK.NUV2.kernelCondition_all
import Submission.NK.LocalCFT.Completion.exists_mulEquiv_unitsCompletion
import Submission.NK.LocalCFT.Functoriality.levelMulEquiv_restrict
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
