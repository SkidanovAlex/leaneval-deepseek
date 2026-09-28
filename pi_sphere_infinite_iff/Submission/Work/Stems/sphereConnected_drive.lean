import Mathlib
import Submission.Work.Stems.sphereMapNull_bridge
import Submission.Work.RatHurewicz.SerreHurewicz

/-!
# The connectivity of spheres in the RATHUREWICZ vocabulary

`Work.RatHurewicz.SphereConnected` (`Submission/Work/RatHurewicz/SerreHurewicz.lean`) is the extra
input the rational-Hurewicz subproject needs for the corollary on `Sⁿ`; it is the same statement as
`Work.Stems.SphereConnectivity` (`Stems/rationalHurewiczStable_of_contract.lean`) up to the order of
arguments.  This file records the (trivial) implication, so that any proof of the connectivity of
spheres feeds both areas:

`SphereMapNull → SphereConnectivity → Work.RatHurewicz.SphereConnected`
(and, with `Stems/sphereMap_null_of_lt.lean`, the first arrow is available from the geometric
lemma).
-/

open scoped Topology

namespace Work.Stems

/-- The connectivity of spheres in the vocabulary of the rational-Hurewicz subproject. -/
theorem ratHurewiczSphereConnected (h : SphereConnectivity) : Work.RatHurewicz.SphereConnected :=
  fun n _ x₀ j hj => h n j hj x₀

end Work.Stems
