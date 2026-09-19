import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_critical_poly

set_option autoImplicit false

namespace Commons.NumberTheory.DirichletCharacter

/-- A Dirichlet character takes values of modulus at most `1` at natural numbers:
it is `0` on non-units and a root of unity on units. -/
theorem norm_char_nat_le_one {N : ℕ} (χ : DirichletCharacter ℂ N) (n : ℕ) : ‖χ n‖ ≤ 1 := by
  exact χ.norm_le_one (n : ZMod N)

end Commons.NumberTheory.DirichletCharacter