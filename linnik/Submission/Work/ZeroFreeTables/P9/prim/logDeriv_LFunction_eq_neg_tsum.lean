import Mathlib

namespace Work.ZeroFreeTables.P9.prim

open LSeries ArithmeticFunction
open scoped LSeries.notation

theorem logDeriv_LFunction_eq_neg_tsum {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    logDeriv (DirichletCharacter.LFunction χ) s = -∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ) * (n : ℂ) ^ (-s) := by
  have htw := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs
  have h2 : deriv (LSeries fun n : ℕ => (χ (n : ZMod N) : ℂ)) s / LSeries (fun n : ℕ => (χ (n : ZMod N) : ℂ)) s
      = - LSeries ((fun n : ℕ => (χ (n : ZMod N) : ℂ)) * fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
    have hh := congrArg Neg.neg htw.symm
    simpa only [neg_div, neg_neg] using hh
  rw [logDeriv_apply, DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
      DirichletCharacter.LFunction_eq_LSeries χ hs, h2, neg_inj]
  have hf0 : ((fun n : ℕ => (χ (n : ZMod N) : ℂ)) * fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) 0 = 0 := by
    rw [Pi.mul_apply]
    simp
  rw [LSeries]
  rw [tsum_congr (fun n => LSeries.term_def₀ hf0 s n)]
  exact tsum_congr fun n => by rw [Pi.mul_apply]; ring

end Work.ZeroFreeTables.P9.prim
