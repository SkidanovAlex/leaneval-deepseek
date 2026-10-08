import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.SimpleRing.Principal

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.LinearAlgebra.Matrix

open scoped MatrixGroups

/-- The center of `SL(2, F)` is trivial when `F` is a field of characteristic two.

In characteristic two the scalar matrices in `SL(2, F)` are exactly those of the form
`r * I` with `r ^ 2 = 1`, and over a field of characteristic two `r ^ 2 = 1` forces `r = 1`
(since `-1 = 1`). -/
theorem center_SL2_eq_bot_of_charTwo {F : Type*} [Field F] [CharP F 2] :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  rw [Subgroup.mem_bot]
  rcases (Matrix.SpecialLinearGroup.mem_center_iff.mp hA) with ⟨r, hrpow, hrscalar⟩
  have hr : r = 1 := by
    have hr2 : r ^ 2 = 1 := by simpa using hrpow
    rcases (sq_eq_one_iff.mp hr2) with h | h
    · exact h
    · rw [h, CharTwo.neg_eq (1 : F)]
  have hAmat : ↑A = (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [← hrscalar, hr]
    simp
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  exact congr_fun₂ hAmat i j

end Commons.LinearAlgebra.Matrix