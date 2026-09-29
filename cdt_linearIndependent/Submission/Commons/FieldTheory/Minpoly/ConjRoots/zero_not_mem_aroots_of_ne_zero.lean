import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.FieldTheory.Minpoly.ConjRoots

/-- If `x ≠ 0` is algebraic over `ℚ`, then `0` is not a root of the minimal
polynomial of `x`: `0` would be a conjugate root of `x`, forcing `x = 0`. -/
lemma zero_not_mem_aroots_of_ne_zero {x : ℂ} (hx : IsAlgebraic ℚ x) (hx0 : x ≠ 0) :
    (0 : ℂ) ∉ (minpoly ℚ x).aroots ℂ := by
  intro hmem
  have hconj : IsConjRoot ℚ x (0 : ℂ) :=
    (isConjRoot_iff_mem_minpoly_aroots (IsAlgebraic.isIntegral hx)).mpr hmem
  exact IsConjRoot.ne_zero hx0 hconj rfl

end Commons.FieldTheory.Minpoly.ConjRoots