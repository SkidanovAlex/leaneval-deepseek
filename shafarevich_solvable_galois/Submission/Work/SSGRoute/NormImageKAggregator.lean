import Submission.Work.SSGRoute.normImage_at_level_proper
import Submission.Work.SSGRoute.localUnitsEquiv_fixed_iff_ringEquiv_fixed
import Submission.Work.SSGRoute.decompK_restrict_surjective
import Submission.Work.SSGRoute.phi1_level_naturality
import Submission.Work.SSGRoute.localUnitsMap_exists
import Submission.NK.GlobalCFT.Inclusion.globalCFT_idele_smul_eq_self_iff
import Submission.NK.GlobalCFT.Galois.globalCFT_localRingEquiv_localAlgebraMapUnits
import Submission.NK.GlobalCFT.Inclusion.globalCFT_ideleClassGroup_inclusion_injective
import Submission.NK.NUV2.LC.RouteB.locUnits_tower_eq_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Aggregator: the imports of `Work.SSGRoute.normImage_at_level_proper_K`

This module carries no declarations.  It exists so that the lemma
`Work.SSGRoute.normImage_at_level_proper_K` (a `K_wˣ`-form of the proved
`Work.SSGRoute.normImage_at_level_proper`, used by the E7b base case `detect_h_trivial`)
can be requested with a `depends_on` list all of whose entries live under `Submission/Work/`.
It provides: the source lemma, the `localUnitsEquiv`↔`localRingEquiv` bridge, the surjectivity
`D_{w'} → D_w` on decomposition groups, the transitivity `localAlgebraMapUnits_comp`
(`phi1_level_naturality`), the canonical local embedding data (`localUnitsMap_exists`), the
local fixed-field theorem (`globalCFT_localFixed_mem_range`) and the injectivity of the local
algebra map (`globalCFT_localAlgebraMapUnits_injective`), and the tower equivariance
(`NK.NUV2.LC.RouteB.locUnits_tower_eq_zero`).
-/
