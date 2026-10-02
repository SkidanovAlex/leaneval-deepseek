import Mathlib
import Submission.Work.Stems.sphereMapNull_bridge
import Submission.Work.Stems.sphereMap_null_of_lt
import Submission.Work.Stems.sphereConnected_drive

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The connectivity of spheres (`Work.Stems.SphereConnectivity`)

**Proved.**  `Work.Stems.SphereConnectivity` (every `πᵢ(Sⁿ)`, `i < n`, vanishes) follows from the
geometric lemma `Work.Stems.sphereMap_null_of_lt` (a based map `S^j → Sⁿ` with `j < n` is
null-homotopic relative to its base point, proved by the general-position/Sard route in that file)
via the cube descent of `Stems/spheresConnected.lean`.

Together with `Stems/rationalHurewiczStable_of_contract.lean` this reduces the area contract
`Work.Drive.StableStemsTorsion` to the single input `Work.Drive.RationalHurewiczStable` (the
RATHUREWICZ subproject).
-/

open scoped Topology Topology.Homotopy unitInterval

namespace Work.Stems

/-- **The connectivity of spheres**, from the geometric lemma. -/
theorem sphereConnectivity : SphereConnectivity :=
  sphereConnectivity_of_sphereMapNull
    (sphereMapNull_of_sphereMap_null_of_lt sphereMap_null_of_lt)

/-- `Sⁿ` is `(n-1)`-connected, in the RATHUREWICZ vocabulary. -/
theorem ratHurewiczSphereConnected' : Work.RatHurewicz.SphereConnected :=
  ratHurewiczSphereConnected sphereConnectivity

end Work.Stems
