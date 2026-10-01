import Mathlib.Data.Nat.Factorization.Defs

namespace Commons.Data.Nat

/-- For coprime `a ⊥ b` and a prime `p` dividing `a`, the exponent of `p` in
`a*b` equals the exponent in `a` (`v_p(b) = 0` because `p` cannot divide `b`). -/
theorem mul_factorization_of_dvd_left {a b p : ℕ} (hcop : Nat.Coprime a b)
    (hp : Nat.Prime p) (hpa : p ∣ a) : (a * b).factorization p = a.factorization p := by
  rw [Nat.factorization_mul_apply_of_coprime hcop]
  have hpb : ¬ p ∣ b := by
    intro hpb
    have hpg : p ∣ a.gcd b := Nat.dvd_gcd hpa hpb
    have hgcd : a.gcd b = 1 := (Nat.coprime_iff_gcd_eq_one.mp hcop)
    exact hp.not_dvd_one (by simpa [hgcd] using hpg)
  rw [Nat.factorization_eq_zero_of_not_dvd hpb]
  simp

end Commons.Data.Nat