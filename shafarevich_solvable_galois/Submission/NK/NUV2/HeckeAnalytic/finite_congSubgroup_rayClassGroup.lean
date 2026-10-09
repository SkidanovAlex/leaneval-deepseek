import Mathlib
import Submission.NK.NUV2.RouteB.RayModulus.Defs
import Submission.NK.NUV2.RouteB.CongCount.finite_rayClassGroup_congSubgroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.NUV2.HeckeAnalytic

/-- Finiteness of the ray class group `𝕀 K ⧸ (Kˣ · U(𝔪))` of a modulus `𝔪`.  This is
`NK.NUV2.RouteB.CongCount.finite_rayClassGroup_congSubgroup`, which proves the classical
statement (finiteness of the class group together with the finite index of the congruence
subgroup in the integral idèles). -/
theorem finite_congSubgroup_rayClassGroup (K : Type) [Field K] [NumberField K]
    (𝔪 : NK.NUV2.RouteB.Modulus K) :
    Finite (NK.GlobalCFT.IdeleClassGroup.rayClassGroup K
      (NK.NUV2.RouteB.CongSubgroup K 𝔪)) :=
  NK.NUV2.RouteB.CongCount.finite_rayClassGroup_congSubgroup K 𝔪

end NK.NUV2.HeckeAnalytic
