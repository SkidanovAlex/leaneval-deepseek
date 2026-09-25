import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.LinearAlgebra.Quotient

theorem finrank_quotient_le_of_le
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]
    {S T : Submodule K V} (h : S ≤ T) :
    Module.finrank K (V ⧸ T) ≤ Module.finrank K (V ⧸ S) := by
  exact LinearMap.finrank_le_finrank_of_surjective (f := Submodule.factor h)
    (Submodule.factor_surjective h)

end Commons.LinearAlgebra.Quotient