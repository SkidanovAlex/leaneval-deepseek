import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.completedLogDeriv_fe

namespace Commons.NumberTheory.DirichletCharacter

/-- Functional-equation transfer for the log-derivative of the completed Dirichlet
L-function of a nontrivial primitive character `χ`:
`logDeriv Λ(χ)(s) = -log N - logDeriv Λ(χ⁻¹)(1-s)`
whenever both completed L-values in question are nonzero.

This is an immediate consequence of `completedLogDeriv_fe` (which handles the
primitive case without the nontriviality assumption); the extra hypothesis
`hχ : χ ≠ 1` is unused. -/
theorem logDeriv_completedL_fe_transfer {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (s : ℂ)
    (hs : DirichletCharacter.completedLFunction χ s ≠ 0)
    (hs' : DirichletCharacter.completedLFunction (χ⁻¹) (1 - s) ≠ 0) :
    logDeriv (DirichletCharacter.completedLFunction χ) s =
      - (Real.log (N : ℝ) : ℂ) -
        logDeriv (DirichletCharacter.completedLFunction (χ⁻¹)) (1 - s) :=
  completedLogDeriv_fe χ hχprim s hs hs'

end Commons.NumberTheory.DirichletCharacter
