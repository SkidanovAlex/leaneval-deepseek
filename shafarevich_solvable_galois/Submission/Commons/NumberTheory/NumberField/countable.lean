import Mathlib.LinearAlgebra.Countable
import Mathlib.Data.Rat.Encodable
import Mathlib.NumberTheory.NumberField.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.NumberTheory.NumberField

theorem countable {k : Type*} [Field k] [NumberField k] : Countable k :=
  Finsupp.Countable.of_moduleFinite (R := ℚ) (M := k)

end Commons.NumberTheory.NumberField