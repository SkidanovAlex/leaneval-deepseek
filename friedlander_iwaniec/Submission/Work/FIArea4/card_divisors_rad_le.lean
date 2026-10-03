import Mathlib
import Submission.Commons.NumberTheory.Nat.radical_eq_prod_primeFactors
import Submission.Commons.NumberTheory.Nat.card_divisors_le_two_pow_card_primeFactors

namespace Work.FIArea4

open Finset

/-- The prime factors of `2 ^ e * s ^ 2` (with `s ≥ 1`) inject into `{2} ∪ s.primeFactors`:
a prime dividing the product divides `2 ^ e` (hence equals `2`) or divides `s ^ 2` (hence
divides `s`).  Consequently `ω(2 ^ e * s ^ 2) ≤ ω(s) + 1`. -/
theorem card_primeFactors_two_pow_mul_sq_le (e s : ℕ) (hs : 1 ≤ s) :
    (2 ^ e * s ^ 2).primeFactors.card ≤ s.primeFactors.card + 1 := by
  have hs0 : s ≠ 0 := by omega
  have hsub : (2 ^ e * s ^ 2).primeFactors ⊆ insert 2 s.primeFactors := by
    intro p hp
    obtain ⟨hpp, hpdvd, _⟩ := Nat.mem_primeFactors.mp hp
    rcases (hpp.dvd_mul).mp hpdvd with h | h
    · have h2 : p ∣ 2 := hpp.dvd_of_dvd_pow h
      have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp h2
      exact Finset.mem_insert.mpr (Or.inl hp2)
    · have hps : p ∣ s := hpp.dvd_of_dvd_pow h
      exact Finset.mem_insert.mpr (Or.inr (Nat.mem_primeFactors.mpr ⟨hpp, hps, hs0⟩))
  calc (2 ^ e * s ^ 2).primeFactors.card
      ≤ (insert 2 s.primeFactors).card := Finset.card_le_card hsub
    _ ≤ s.primeFactors.card + 1 := Finset.card_insert_le 2 _

/-- `2 ^ ω(s) ≤ s` for `s ≥ 1`: the product of the distinct primes dividing `s` is at least
`2 ^ ω(s)` and at most `s`. -/
theorem two_pow_card_primeFactors_le_self {s : ℕ} (hs : 1 ≤ s) :
    2 ^ s.primeFactors.card ≤ s := by
  have hs0 : s ≠ 0 := by omega
  calc 2 ^ s.primeFactors.card
      = ∏ p ∈ s.primeFactors, 2 := (Finset.prod_const (s := s.primeFactors) 2).symm
    _ ≤ ∏ p ∈ s.primeFactors, p := by
        apply Finset.prod_le_prod₀
        · intro p _
          norm_num
        · intro p hp
          exact (Nat.prime_of_mem_primeFactors hp).two_le
    _ ≤ s := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd s)

/-- **How many squarefree divisors `2 ^ e * s ^ 2` has.** The number of divisors of the radical
`∏ p ∈ n.primeFactors, p` is `2 ^ ω(n)`; here `ω(2^e s²) = ω(s) + [e ≥ 1] ≤ ω(s) + 1`, and
`2 ^ ω(s) ≤ ∏ p ∈ s.primeFactors, p ≤ s`.  Useful ingredients already in the repository:
`Submission/Commons/NumberTheory/card_divisors_le_two_pow_card_primeFactors` and `Nat.primeFactors_prod`,
`Nat.primeFactors_pow`, `Nat.primeFactors_mul`, `Nat.card_divisors`. -/
theorem card_divisors_rad_le {e s : ℕ} (hs : 1 ≤ s) :
    (∏ p ∈ (2 ^ e * s ^ 2).primeFactors, p).divisors.card ≤ 2 * s := by
  set n : ℕ := 2 ^ e * s ^ 2 with hn
  set R : ℕ := ∏ p ∈ n.primeFactors, p with hR
  have hR' : R = ∏ p ∈ n.primeFactors, p := hR
  have hpf : R.primeFactors = n.primeFactors := by
    rw [hR']
    exact Nat.primeFactors_prod_primeFactors n
  -- The radical is squarefree, so its divisor count is `2 ^ ω`.
  have hcard : R.divisors.card ≤ 2 ^ n.primeFactors.card := by
    have h := Commons.NumberTheory.Nat.card_divisors_le_two_pow_card_primeFactors R (by rw [hpf])
    rwa [hpf] at h
  have hstep : n.primeFactors.card ≤ s.primeFactors.card + 1 := by
    rw [hn]
    exact card_primeFactors_two_pow_mul_sq_le e s hs
  have hpow : 2 ^ n.primeFactors.card ≤ 2 ^ (s.primeFactors.card + 1) :=
    Nat.pow_le_pow_right (by norm_num) hstep
  calc R.divisors.card ≤ 2 ^ n.primeFactors.card := hcard
    _ ≤ 2 ^ (s.primeFactors.card + 1) := hpow
    _ = 2 * 2 ^ s.primeFactors.card := by rw [pow_succ]; ring
    _ ≤ 2 * s := Nat.mul_le_mul_left 2 (two_pow_card_primeFactors_le_self hs)

end Work.FIArea4
