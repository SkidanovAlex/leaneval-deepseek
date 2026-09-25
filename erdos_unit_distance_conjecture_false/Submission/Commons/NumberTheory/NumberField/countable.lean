import Mathlib.Data.Rat.Encodable
import Mathlib.LinearAlgebra.Countable
import Mathlib.NumberTheory.NumberField.Basic

namespace Commons.NumberTheory.NumberField

theorem countable {k : Type*} [Field k] [NumberField k] : Countable k :=
  Finsupp.Countable.of_moduleFinite (R := ℚ) (M := k)

end Commons.NumberTheory.NumberField