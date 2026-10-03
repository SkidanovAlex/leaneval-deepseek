import Mathlib.NumberTheory.LSeries.DirichletContinuation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped LSeries.notation

namespace Commons.NumberTheory.DirichletCharacter

/-- The logarithmic derivative of a Dirichlet L-function on the half-plane `re s > 1` equals
the negative of the L-series of the twist of the von Mangoldt function by the character. -/
theorem LFunction_logDeriv_eq_neg_LSeries_vonMangoldt {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    logDeriv (DirichletCharacter.LFunction χ) s =
      - LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ)) s := by
  have h1 : logDeriv (DirichletCharacter.LFunction χ) s =
      deriv (LSeries (χ ·)) s / LSeries (χ ·) s := by
    rw [logDeriv_apply, DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
      DirichletCharacter.LFunction_eq_LSeries χ hs]
  rw [h1]
  have h2 := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs
  have hD : -(LSeries (↗χ * ↗ArithmeticFunction.vonMangoldt) s) =
      deriv (LSeries (χ ·)) s / LSeries (χ ·) s := by
    rw [h2]; ring
  rw [← hD]
  congr 1
  refine LSeries_congr (fun {n} _ => ?_) s
  simp only [Pi.mul_apply]
  ring

end Commons.NumberTheory.DirichletCharacter