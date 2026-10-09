import Submission.NK.NUV2.RouteB.RayModulus.Defs
import Submission.NK.NUV2.RouteB.RayModulus.exists_modulus_le
import Submission.NK.NUV2.RouteB.RayModulus.exists_ideal_of_class
import Submission.NK.NUV2.RouteB.CongCount.finite_rayClassGroup_congSubgroup
import Submission.NK.GlobalCFT.Idele
import Submission.NK.GlobalCFT.IdeleClassGroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Import bundle: the idèle topology and the congruence subgroups

This module only collects the modules that define the idèle group `𝕀 K` with its restricted-product
topology, the congruence subgroup `U(𝔪) = NK.NUV2.RouteB.CongSubgroup K 𝔪`, the ray class group
`𝕀 K ⧸ (Kˣ · U(𝔪))` and the neighbourhood-basis machinery of the restricted product
(`NK.NUV2.RouteB.RayModulus.exists_modulus_le` and its helpers), together with the finiteness of
the ray class group of a modulus.
-/

namespace Work.SSGRoute.GrunwaldEscapeCore

end Work.SSGRoute.GrunwaldEscapeCore
