import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Submission.Commons.NumberTheory.DirichletCharacter.changeLevel_stable_nat

open Complex DirichletCharacter
set_option autoImplicit false

namespace Commons.NumberTheory.DirichletCharacter

/-- The rearranged functional equation for the completed Dirichlet L-function:
`Λ(s, χ) = N^(1/2 - s) · ε(χ) · Λ(1 - s, χ⁻¹)`. -/
theorem completedLFunction_eq {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (s : ℂ) :
    completedLFunction χ s = (N : ℂ) ^ (1 / 2 - s) * χ.rootNumber *
      completedLFunction (χ⁻¹) (1 - s) := by
  -- Mathlib's functional equation for primitive characters states
  --   Λ(χ, 1 - u) = N ^ (u - 1/2) · ε(χ) · Λ(χ⁻¹, u)
  -- for all `u`; substituting `u := 1 - s` and rearranging the exponents gives the claim.
  have h := hχ.completedLFunction_one_sub (1 - s)
  rw [show 1 - (1 - s) = s by ring,
      show (1 - s) - (1 / 2 : ℂ) = 1 / 2 - s by ring] at h
  exact h

end Commons.NumberTheory.DirichletCharacter