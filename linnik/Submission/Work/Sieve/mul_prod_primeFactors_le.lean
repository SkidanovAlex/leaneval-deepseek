import Mathlib

set_option linter.unusedVariables false

namespace Work.Sieve

/-- For squarefree `d ≠ 0`, any `r ≤ R / d` and any set `t` of prime divisors of `d`
satisfy `r * ∏ p ∈ t, p ≤ R`. -/
lemma mul_prod_primeFactors_le {d R : ℕ} (hd : d ≠ 0) (hds : Squarefree d)
    {r : ℕ} (hr : r ≤ R / d) {t : Finset ℕ} (ht : t ⊆ d.primeFactors) :
    r * (∏ p ∈ t, p) ≤ R := by
  have hpos : 0 < d := Nat.pos_of_ne_zero hd
  -- the product over any subset of the prime factors divides `d`, indeed it divides
  -- the product over all prime factors, which divides `d` (the radical of `d`).
  have hdvd : (∏ p ∈ t, p) ∣ d :=
    (Finset.prod_dvd_prod_of_subset t d.primeFactors (fun p => p) ht).trans
      (Nat.prod_primeFactors_dvd d)
  have hle : ∏ p ∈ t, p ≤ d := Nat.le_of_dvd hpos hdvd
  calc r * (∏ p ∈ t, p) ≤ r * d := Nat.mul_le_mul_left r hle
    _ ≤ R := (Nat.le_div_iff_mul_le hpos).mp hr

end Work.Sieve
