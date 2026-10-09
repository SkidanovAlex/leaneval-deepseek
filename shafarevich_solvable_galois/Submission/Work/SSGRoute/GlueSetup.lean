import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.NK.GlobalCFT.GaloisAction
import Submission.NK.GlobalCFT.Galois.exists_stabilizer_isConj_of_isReal_isComplex
import Submission.NK.GlobalCFT.Galois.globalCFT_place_smul_liesOver
import Submission.NK.GlobalCFT.Galois.globalCFT_smul_place_smul
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Shared setup for the "place glue" lemmas (`Work.SSGRoute.glue_*`)

Import carrier for the lemmas relating the subgroups of `Gal(K/k)` that arise from the local
conditions of `SSGRoute.Z1loc` (images of `decomp k A` for finite places `A` of `Ω`, images of
`Subgroup.zpowers σ` for involutions `σ` of `G_k`) to the decomposition (stabilizer) subgroups
`MulAction.stabilizer (↥K ≃ₐ[k] ↥K) w` of the places `w` of `K` (`NK.GlobalCFT.Place ↥K`).

Vocabulary used by the statements: `SSGRoute.IsFinPlace`, `SSGRoute.decomp`, `SSGRoute.res`
(`Submission.Work.SSGRoute.Interfaces`), `NK.GlobalCFT.Place` with its Galois action
(`NK.GlobalCFT.GaloisAction`).
-/

namespace Work.SSGRoute

end Work.SSGRoute
