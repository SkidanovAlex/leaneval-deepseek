import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.zerosInStrip

namespace Commons.NumberTheory.Linnik

/-- Every zero of the completed Dirichlet L-function of a primitive non-trivial character lies
in the critical strip `0 < Re s < 1`.

This is the standard "zeros in the critical strip" theorem, proved in the commons as
`Commons.NumberTheory.DirichletCharacter.zerosInStrip`; here we instantiate it for a fixed zero
`u` of `Λ(s, χ)`. -/
lemma completedL_zero_strip {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) {u : ℂ}
    (hu : DirichletCharacter.completedLFunction χ u = 0) :
    0 < u.re ∧ u.re < 1 := by
  exact Commons.NumberTheory.DirichletCharacter.zerosInStrip χ hχ hχprim u hu

end Commons.NumberTheory.Linnik
