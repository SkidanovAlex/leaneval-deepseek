import ChallengeDeps
import Mathlib.FieldTheory.Minpoly.Field

open AlgebraicIntegers
open ComplexOrder

set_option autoImplicit false

namespace Submission.Explicit

noncomputable def toRat (P : Polynomial ℤ) : Polynomial ℚ := P.map (algebraMap ℤ ℚ)

/-- Integrality of a root of a monic integer polynomial. -/
lemma integral_of_root_of_monic_int {P : Polynomial ℤ} (hmonic : P.Monic) {α : ℂ}
    (hroot : Polynomial.aeval α P = 0) : IsIntegral ℤ α := by
  exact ⟨P, hmonic, hroot⟩

end Submission.Explicit
