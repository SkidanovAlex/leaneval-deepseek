import Mathlib

namespace NK.LocalCFT.Instance

/-- A degree-`2` field extension has no proper intermediate fields: any intermediate
field of a quadratic extension is either the base field or the whole field.

This is the `IntermediateField` instance of the classical fact that the lattice of
intermediate fields of a finite extension `E/F` has no proper elements, applied to the
prime dimension `[E : F] = 2`. -/
theorem intermediateField_eq_bot_or_top {F E : Type*} [Field F] [Field E] [Algebra F E]
    (L : IntermediateField F E) [FiniteDimensional F L] (h : Module.finrank F E = 2) :
    L = ⊥ ∨ L = ⊤ :=
  (IntermediateField.isSimpleOrder_of_finrank_prime F E (h ▸ Nat.prime_two)).eq_bot_or_eq_top L

end NK.LocalCFT.Instance
