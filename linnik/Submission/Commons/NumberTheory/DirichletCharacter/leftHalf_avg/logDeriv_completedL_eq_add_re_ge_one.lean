import Mathlib.NumberTheory.LSeries.Nonvanishing
import Submission.Commons.NumberTheory.DirichletCharacter.completedLogDeriv_two_le

open Complex DirichletCharacter
set_option autoImplicit false

namespace Commons.NumberTheory.DirichletCharacter.leftHalf_avg

/-!
# Log-derivative of the completed L-function splits on `Re s ≥ 1`

For a non-trivial Dirichlet character `χ`, the completed L-function factors on
`Re s ≥ 1` as `Λ(s, χ) = L(s, χ) · gammaFactor(s, χ)` (the gamma factor is
nonzero there, and `L(s, χ)` is nonzero for `Re s ≥ 1` by Mathlib's
zero-free region `DirichletCharacter.LFunction_ne_zero_of_one_le_re`), so
taking logarithmic derivatives gives

    logDeriv Λ(χ) = logDeriv L(χ) + logDeriv gammaFactor(χ).

This is the "completed function splits" step used in the `leftHalf_avg` chain
of bounds for `logDeriv` on the right half-plane.  The factorisation identity
and the sum rule for `logDeriv` are exactly the commons lemma
`Commons.NumberTheory.DirichletCharacter.logDeriv_completedLFunction_eq_add`
(which needs `0 < s.re` and `LFunction χ s ≠ 0`); both hypotheses follow from
`1 ≤ s.re` together with non-triviality of `χ`.
-/

/-- The logarithmic derivative of the completed L-function of a non-trivial
primitive Dirichlet character is the sum of the logarithmic derivatives of the
ordinary L-function and of the gamma factor, everywhere on the closed right
half-plane `Re s ≥ 1`. -/
theorem logDeriv_completedL_eq_add_re_ge_one {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (s : ℂ)
    (hs : 1 ≤ s.re) :
    logDeriv (DirichletCharacter.completedLFunction χ) s =
      logDeriv (DirichletCharacter.LFunction χ) s +
        logDeriv (DirichletCharacter.gammaFactor χ) s := by
  have hspos : 0 < s.re := by linarith
  have hLs : DirichletCharacter.LFunction χ s ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hs
  exact Commons.NumberTheory.DirichletCharacter.logDeriv_completedLFunction_eq_add
    χ hχ s hspos hLs

end Commons.NumberTheory.DirichletCharacter.leftHalf_avg
