import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.LinearAlgebra.ExteriorPower

/-- If the `k`-fold wedge product of a family of vectors is non-zero, then the family is
linearly independent (over a field). -/
lemma iMulti_linearIndependent_of_ne_zero {K : Type*} [Field K] {M : Type*} [AddCommGroup M]
    [Module K M] {k : ℕ} (v : Fin k → M) (hv : exteriorPower.ιMulti K k v ≠ 0) :
    LinearIndependent K v := by
  by_contra h
  exact hv (AlternatingMap.map_linearDependent (f := exteriorPower.ιMulti K k) v h)

end Commons.LinearAlgebra.ExteriorPower