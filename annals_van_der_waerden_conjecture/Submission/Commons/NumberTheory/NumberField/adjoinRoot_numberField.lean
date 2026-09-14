import Mathlib.NumberTheory.NumberField.Basic

open scoped Polynomial

namespace Commons.NumberTheory.NumberField

theorem adjoinRoot_numberField (f : ℚ[X]) [Fact (Irreducible f)] : NumberField (AdjoinRoot f) := by
  infer_instance

end Commons.NumberTheory.NumberField