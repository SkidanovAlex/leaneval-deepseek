import Mathlib.FieldTheory.Galois.IsGaloisGroup

open scoped NumberField

namespace Commons.NumberTheory.NumberField

theorem ringOfIntegers_isGaloisGroup (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] : IsGaloisGroup Gal(K/ℚ) ℤ (𝓞 K) := by
  infer_instance

end Commons.NumberTheory.NumberField