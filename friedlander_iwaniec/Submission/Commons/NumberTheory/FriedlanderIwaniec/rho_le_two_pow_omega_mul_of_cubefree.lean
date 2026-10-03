import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_sieve_remainder_le
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_sum_sq_root_count_le_two_pow_omega
import Submission.Commons.NumberTheory.FriedlanderIwaniec.squarefree_sqKernel_of_cubefree
import Submission.Commons.NumberTheory.Gcd.gcd_sq_eq_gcd_of_squarefree
import Submission.Commons.NumberTheory.Divisors.prod_factorization_div_two_eq_sqPart

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.NumberTheory.FriedlanderIwaniec

/-- For squarefree `m`, `gcd c m` is the product of the primes dividing `m` that also
divide `c`. -/
private lemma gcd_eq_prod_primeFactors_filter_of_squarefree {c m : ℕ} (hm : Squarefree m) :
    Nat.gcd c m = ∏ p ∈ m.primeFactors.filter (fun p => p ∣ c), p := by
  have hgcd0 : Nat.gcd c m ≠ 0 := by
    intro h
    have h0 : 0 ∣ m := by rw [← h]; exact Nat.gcd_dvd_right c m
    exact hm.ne_zero (Nat.eq_zero_of_zero_dvd h0)
  have hsq : Squarefree (Nat.gcd c m) := Squarefree.squarefree_of_dvd (Nat.gcd_dvd_right c m) hm
  have hpf : (Nat.gcd c m).primeFactors = m.primeFactors.filter (fun p => p ∣ c) := by
    ext p
    rw [Nat.mem_primeFactors, Finset.mem_filter, Nat.mem_primeFactors]
    constructor
    · rintro ⟨hpp, hpg, _⟩
      exact ⟨⟨hpp, hpg.trans (Nat.gcd_dvd_right c m), hm.ne_zero⟩,
        hpg.trans (Nat.gcd_dvd_left c m)⟩
    · rintro ⟨⟨hpp, hpm, _⟩, hpc⟩
      exact ⟨hpp, Nat.dvd_gcd hpc hpm, hgcd0⟩
  rw [← Nat.prod_primeFactors_of_squarefree hsq, hpf]

/-- For **cubefree** `d`, the number of roots of `ν ^ 2 + c ^ 4 = 0` modulo `d` is at most
`2 ^ ω(d)` times the product of the primes `p` with `p ^ 2 ∣ d` and `p ∣ c`.

This sharpens the general bound `#{ν : ZMod d | ν ^ 2 + b ^ 2 = 0} ≤ 2 ^ ω(d) · gcd(b, ∏ p^{v_p(d)/2})`
(commons `sq_sum_sq_root_count_le_two_pow_omega`, applied with `b = c ^ 2`) by evaluating the
`gcd` for cubefree `d`: the square part is squarefree, and `gcd (c^2) m = gcd c m` for squarefree
`m`.  This is the input for the **elementary** verification of the companion-sieve hypothesis
`A_d(x) ≪ d^{-1} x^{1/2} τ(d) A(x)` (`d ≤ x^{1/2}`) for the Friedlander–Iwaniec sequence. -/
theorem rho_le_two_pow_omega_mul_of_cubefree {d c : ℕ} (hd : 0 < d)
    (hcb : ∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ d) :
    Submission.rho (c ^ 2) d ≤ 2 ^ d.primeFactors.card *
      ∏ p ∈ d.primeFactors.filter (fun p => p ^ 2 ∣ d ∧ p ∣ c), p := by
  let M : ℕ := (Nat.primeFactors d).prod (fun p => p ^ (d.factorization p / 2))
  have hMprod : M = ∏ p ∈ d.primeFactors.filter (fun p => p ^ 2 ∣ d), p :=
    Commons.NumberTheory.Divisors.prod_factorization_div_two_eq_sqPart d hcb
  have hsqM : Squarefree M := squarefree_sqKernel_of_cubefree hcb
  have hMpf : M.primeFactors = d.primeFactors.filter (fun p => p ^ 2 ∣ d) := by
    rw [hMprod]
    exact Nat.primeFactors_prod
      (fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
  have hkey : Nat.gcd (c ^ 2) M
      = ∏ p ∈ d.primeFactors.filter (fun p => p ^ 2 ∣ d ∧ p ∣ c), p := by
    rw [Commons.NumberTheory.Gcd.gcd_sq_eq_gcd_of_squarefree hsqM,
      gcd_eq_prod_primeFactors_filter_of_squarefree hsqM, hMpf, Finset.filter_filter]
  have hmain := sq_sum_sq_root_count_le_two_pow_omega (d := d) (b := c ^ 2) hd
  rw [hkey] at hmain
  simpa only [Submission.rho] using hmain

end Commons.NumberTheory.FriedlanderIwaniec
