import Mathlib.Data.Nat.Factorization.Basic

namespace Commons.NumberTheory.FriedlanderIwaniec

/-- For a prime `p` and exponent `e`, the square of `p ^ (e / 2)` divides `p ^ e`. -/
private lemma pow_div_two_sq_dvd (p e : ℕ) : (p ^ (e / 2)) ^ 2 ∣ p ^ e := by
  rw [← pow_mul]
  refine pow_dvd_pow p ?_
  calc (e / 2) * 2 = 2 * (e / 2) := Nat.mul_comm _ _
    _ ≤ e := Nat.mul_div_le e 2

/-- The integer `∏_{p | d} p ^ (v_p(d) / 2)` is the square root of the largest square divisor
of `d`: its square divides `d`. -/
theorem sqKernel_sq_dvd (d : ℕ) : ((Nat.primeFactors d).prod (fun p : ℕ => p ^ (d.factorization p / 2))) ^ 2 ∣ d := by
  rcases eq_or_ne d 0 with h0 | h0
  · subst h0
    simp
  · conv_rhs => rw [Nat.prod_primeFactors_pow_factorization h0]
    have hK : ((Nat.primeFactors d).prod (fun p : ℕ => p ^ (d.factorization p / 2))) ^ 2
        = ∏ p ∈ Nat.primeFactors d, (p ^ (d.factorization p / 2)) ^ 2 := by
      rw [← Finset.prod_pow]
    rw [hK]
    refine Finset.prod_dvd_prod_of_dvd _ _ ?_
    intro p _
    exact pow_div_two_sq_dvd p (d.factorization p)

end Commons.NumberTheory.FriedlanderIwaniec