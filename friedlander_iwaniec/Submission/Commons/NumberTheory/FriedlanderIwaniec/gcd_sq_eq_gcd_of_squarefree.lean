import Mathlib.Algebra.Squarefree.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Nat

namespace Commons.NumberTheory.FriedlanderIwaniec

/-- For squarefree `m`, taking the square of `a` does not change `gcd` with `m`. -/
theorem gcd_sq_eq_gcd_of_squarefree {a m : ℕ} (hm : Squarefree m) :
    Nat.gcd (a ^ 2) m = Nat.gcd a m := by
  apply Nat.dvd_antisymm
  · -- `gcd (a^2) m ∣ m` is squarefree, hence `gcd (a^2) m ∣ a^2` forces `gcd (a^2) m ∣ a`.
    have h1 : Nat.gcd (a ^ 2) m ∣ m := Nat.gcd_dvd_right _ _
    have hsq : Squarefree (Nat.gcd (a ^ 2) m) := hm.squarefree_of_dvd h1
    have h2 : Nat.gcd (a ^ 2) m ∣ a ^ 2 := Nat.gcd_dvd_left _ _
    have h3 : Nat.gcd (a ^ 2) m ∣ a :=
      (hsq.dvd_pow_iff_dvd (by norm_num : (2 : ℕ) ≠ 0)).mp h2
    exact Nat.dvd_gcd h3 h1
  · -- `gcd a m ∣ a ∣ a^2` and `gcd a m ∣ m`.
    exact Nat.dvd_gcd
      (dvd_trans (Nat.gcd_dvd_left a m) (dvd_pow_self a (by norm_num : (2 : ℕ) ≠ 0)))
      (Nat.gcd_dvd_right a m)

end Commons.NumberTheory.FriedlanderIwaniec