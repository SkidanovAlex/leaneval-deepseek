import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Nat.Basic

set_option linter.unusedVariables false

namespace Commons.Data.Nat

/-- The lowest `l` base-`p` digits of `c` all vanish if and only if `p ^ l` divides `c`. -/
theorem mod_pow_eq_zero_iff (p l c : ℕ) (hp : 1 ≤ p) :
    c % p ^ l = 0 ↔ ∀ j, j < l → c / p ^ j % p = 0 := by
  constructor
  · intro h j hj
    have hdvd : p ^ l ∣ c := Nat.dvd_of_mod_eq_zero h
    have hpj : p ^ j ∣ c := dvd_trans (pow_dvd_pow p (le_of_lt hj)) hdvd
    have hdiv : p ∣ c / p ^ j := by
      rw [Nat.dvd_div_iff_mul_dvd hpj, ← pow_succ]
      exact dvd_trans (pow_dvd_pow p (Nat.succ_le_of_lt hj)) hdvd
    exact Nat.mod_eq_zero_of_dvd hdiv
  · intro h
    suffices p ^ l ∣ c from Nat.mod_eq_zero_of_dvd this
    induction l with
    | zero => exact one_dvd c
    | succ l ih =>
      have h1 : p ^ l ∣ c := ih fun j hj => h j (Nat.lt_succ_of_lt hj)
      have h2 : p ∣ c / p ^ l := Nat.dvd_of_mod_eq_zero (h l (Nat.lt_succ_self l))
      have h3 : p ^ l * p ∣ c := (Nat.dvd_div_iff_mul_dvd h1).mp h2
      rw [pow_succ]
      exact h3

end Commons.Data.Nat