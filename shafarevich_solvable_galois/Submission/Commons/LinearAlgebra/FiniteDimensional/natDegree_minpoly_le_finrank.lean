import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.LinearAlgebra.FiniteDimensional

/-- The degree of the minimal polynomial over `F` of an element `y` of a finite-dimensional
field extension `E/F` is at most the degree `[E : F]` of the extension. -/
theorem natDegree_minpoly_le_finrank {F E : Type*} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (y : E) : (minpoly F y).natDegree ≤ Module.finrank F E :=
  minpoly.natDegree_le y

end Commons.LinearAlgebra.FiniteDimensional