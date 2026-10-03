import Mathlib
import Submission.Commons.NumberTheory.GaussianInt.two_squares_repr_count
import Submission.Commons.NumberTheory.GaussianInt.ncard_assoc_norm_mul
import Submission.Commons.NumberTheory.GaussianInt.units_classification
import Submission.Commons.NumberTheory.Diophantine.prime_three_mod_four_dvd_sq_add_sq

namespace Work.FIArea3.JointCount

open Commons.NumberTheory.GaussianInt

/-- Multiplicativity of `A` on coprime factors, with the degenerate (`0`) cases included. -/
private lemma A_mul_coprime' (x y : ℕ) (h : x.Coprime y) : A (x * y) = A x * A y := by
  rcases Nat.eq_zero_or_pos x with hx | hx
  · subst hx
    have hy : y = 1 := (Nat.coprime_zero_left y).mp h
    subst hy; simp [A_one]
  · rcases Nat.eq_zero_or_pos y with hy | hy
    · subst hy
      have hx1 : x = 1 := (Nat.coprime_zero_right x).mp h
      subst hx1; simp [A_one]
    · exact A_mul_of_coprime x y hx hy h

theorem A_le_tau_of_split_exp {M d : ℕ} (hd : 1 ≤ d) (hdvd : d ∣ M)
    (hMsub : ∀ p : ℕ, p.Prime → p ∣ M → p ∣ d)
    (hsplit : ∀ p : ℕ, p.Prime → p % 4 = 1 → M.factorization p = d.factorization p) :
    Commons.NumberTheory.GaussianInt.A M ≤ d.divisors.card := by
  have hd0 : d ≠ 0 := by omega
  -- `M ≠ 0`: otherwise every prime would divide `M = 0`, hence `d`, which is impossible.
  have hM0 : M ≠ 0 := by
    intro hM
    obtain ⟨p, hpge, hpprime⟩ := Nat.exists_infinite_primes (d + 1)
    have hpdvdM : p ∣ M := by rw [hM]; exact dvd_zero p
    have hpdvdd : p ∣ d := hMsub p hpprime hpdvdM
    have hple : p ≤ d := Nat.le_of_dvd (by omega) hpdvdd
    omega
  -- Factorization of `A M` into the prime-power values.
  have hAprod : A M = ∏ p ∈ M.primeFactors, A (p ^ M.factorization p) := by
    rw [Nat.multiplicative_factorization A A_mul_coprime' A_one hM0]
    rw [Nat.prod_factorization_eq_prod_primeFactors]
  -- The two numbers have the same prime support.
  have hpf : M.primeFactors = d.primeFactors := by
    ext p
    rw [Nat.mem_primeFactors, Nat.mem_primeFactors]
    constructor
    · rintro ⟨hp, hpdvd, -⟩
      exact ⟨hp, hMsub p hp hpdvd, hd0⟩
    · rintro ⟨hp, hpdvd, -⟩
      exact ⟨hp, hpdvd.trans hdvd, hM0⟩
  -- Each prime-power factor is bounded by the corresponding divisor-counting factor.
  have hfactor : ∀ p ∈ M.primeFactors, A (p ^ M.factorization p) ≤ d.factorization p + 1 := by
    intro p hp
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpM : p ∣ M := (Nat.mem_primeFactors.mp hp).2.1
    have hpD : p ∣ d := hMsub p hpprime hpM
    have hge : 1 ≤ d.factorization p := (hpprime.dvd_iff_one_le_factorization hd0).mp hpD
    rw [A_prime_pow p (M.factorization p) hpprime]
    by_cases h2 : p = 2
    · subst h2; rw [if_pos rfl]; omega
    · rw [if_neg h2]
      by_cases h41 : p % 4 = 1
      · rw [if_pos h41, hsplit p hpprime h41]
      · rw [if_neg h41]
        split_ifs <;> omega
  calc A M = ∏ p ∈ M.primeFactors, A (p ^ M.factorization p) := hAprod
    _ ≤ ∏ p ∈ M.primeFactors, (d.factorization p + 1) :=
        Finset.prod_le_prod₀ (fun i _ => Nat.zero_le _) hfactor
    _ = ∏ p ∈ d.primeFactors, (d.factorization p + 1) := by rw [hpf]
    _ = d.divisors.card := (Nat.card_divisors hd0).symm

end Work.FIArea3.JointCount
