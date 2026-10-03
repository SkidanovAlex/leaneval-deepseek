import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.NormNum.Basic

namespace Commons.NumberTheory.Divisors

/-- For cubefree `d`, the product `∏_{p ∣ d} p ^ (v_p(d) / 2)` is the square part
`∏_{p : p² ∣ d} p` of `d` (for cubefree `d` every exponent is `0`, `1` or `2`). -/
theorem prod_factorization_div_two_eq_sqPart (d : ℕ)
    (hcb : ∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ d) :
    ∏ p ∈ d.primeFactors, p ^ (d.factorization p / 2)
      = ∏ p ∈ d.primeFactors.filter (fun p => p ^ 2 ∣ d), p := by
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpd : p ∣ d := Nat.dvd_of_mem_primeFactors hp
  have hd0 : d ≠ 0 := (Nat.mem_primeFactors.mp hp).2.2
  have h1 : 1 ≤ d.factorization p := (hpp.dvd_iff_one_le_factorization hd0).mp hpd
  have h3 : ¬ 3 ≤ d.factorization p := by
    rw [← hpp.pow_dvd_iff_le_factorization hd0]
    exact hcb p hpp
  have hcases : d.factorization p = 1 ∨ d.factorization p = 2 := by omega
  rcases hcases with h | h
  · have hnot : ¬ p ^ 2 ∣ d := by
      rw [hpp.pow_dvd_iff_le_factorization hd0]; omega
    rw [h, if_neg hnot]
    norm_num
  · have hyes : p ^ 2 ∣ d := by
      rw [hpp.pow_dvd_iff_le_factorization hd0]; omega
    rw [h, if_pos hyes]
    norm_num

end Commons.NumberTheory.Divisors