import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Finiteness.Small
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Algebra.Module

/-- A field `B` that is finite-dimensional as an algebra over a small field `F` is itself small
(as a type): `B` is equivalent to `F^n` for `n = finrank F B`, and `F^n` lives in `Type 0`
when `F` does. -/
theorem small_of_finiteDimensional {F B : Type*} [Field F] [Small.{0} F] [Field B] [Algebra F B]
    [FiniteDimensional F B] : Small.{0} B :=
  Module.Finite.small F B

end Commons.Algebra.Module