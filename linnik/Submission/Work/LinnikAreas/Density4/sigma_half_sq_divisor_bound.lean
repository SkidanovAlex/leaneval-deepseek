import Mathlib
import Submission.Work.LinnikAreas.Density4.divisors_recip_pow_le_totient_div
import Submission.Work.LinnikAreas.Density4.divisors_sqrtrecip_mul_coprime
import Submission.Work.LinnikAreas.Density4.divisors_tau_sqrtrecip_mul_coprime
import Submission.Work.LinnikAreas.Density4.prime_local_sqrt_bound

namespace Work.LinnikAreas.Density4

open scoped BigOperators
open Finset

/-- The squarefree case of the target inequality:
`φ(n)·(Σ_{d∣n} d^{-1/2})² ≤ n·Σ_{e∣n} τ(e)·e^{-1/2}` whenever `n` is squarefree.

This is proved by strong induction on `n`.  For `n = p·m` with `p` prime and `p ∤ m`,
`Nat.totient_mul_of_prime_of_not_dvd` gives `φ(p·m) = (p-1)·φ(m)`, the two divisor
sums factor over the coprime pair `(p, m)` (via `divisors_sqrtrecip_mul_coprime` and
`divisors_tau_sqrtrecip_mul_coprime`), and the local per-prime estimate
`prime_local_sqrt_bound` closes the step. -/
private lemma squarefree_bound (n : ℕ) (hn : Squarefree n) :
    (n.totient : ℝ) * (∑ d ∈ n.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)) ^ 2
      ≤ (n : ℝ) * ∑ e ∈ n.divisors, (e.divisors.card : ℝ) / Real.sqrt (e : ℝ) := by
  have main : ∀ n : ℕ, Squarefree n →
      (n.totient : ℝ) * (∑ d ∈ n.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)) ^ 2
        ≤ (n : ℝ) * ∑ e ∈ n.divisors, (e.divisors.card : ℝ) / Real.sqrt (e : ℝ) := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih hn
    rcases eq_or_ne n 1 with rfl | hn1
    · norm_num
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn.ne_zero
      obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hn1
      set m : ℕ := n / p with hmdef
      have hn_eq : n = p * m := by
        rw [hmdef, mul_comm]
        exact (Nat.div_mul_cancel hpdvd).symm
      have hnpdvd : ¬ p ∣ m := by
        intro hpm
        have hpp : p * p ∣ n := by
          rw [hn_eq]; exact mul_dvd_mul_left p hpm
        exact (Nat.squarefree_iff_prime_squarefree.mp hn p hp) hpp
      have hmpos : 0 < m := by
        rw [hmdef]
        exact Nat.div_pos (Nat.le_of_dvd hnpos hpdvd) hp.pos
      have hm_lt : m < n := by
        rw [hn_eq, mul_comm]
        simpa using Nat.mul_lt_mul_of_pos_left hp.one_lt hmpos
      have hmsf : Squarefree m :=
        Squarefree.squarefree_of_dvd ⟨p, by rw [hn_eq, mul_comm]⟩ hn
      have hpm : p.Coprime m := (hp.coprime_iff_not_dvd).mpr hnpdvd
      have hIH := ih m hm_lt hmsf
      have hA : (∑ d ∈ n.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))
          = (1 + 1 / Real.sqrt (p : ℝ))
              * (∑ d ∈ m.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)) := by
        rw [hn_eq, divisors_sqrtrecip_mul_coprime hpm, Nat.Prime.sum_divisors hp]
        simp only [Nat.cast_one, Real.sqrt_one, div_one]
        ring
      have hB : (∑ e ∈ n.divisors, (e.divisors.card : ℝ) / Real.sqrt (e : ℝ))
          = (1 + 2 / Real.sqrt (p : ℝ))
              * (∑ e ∈ m.divisors, (e.divisors.card : ℝ) / Real.sqrt (e : ℝ)) := by
        rw [hn_eq, divisors_tau_sqrtrecip_mul_coprime hpm, Nat.Prime.sum_divisors hp]
        have hcard : p.divisors.card = 2 := by
          rw [Nat.Prime.divisors hp]
          exact Finset.card_pair (Ne.symm hp.ne_one)
        rw [Nat.divisors_one, hcard]
        simp only [Nat.cast_one, Nat.cast_ofNat, Finset.card_singleton, Real.sqrt_one, div_one]
        ring
      have hphi : (n.totient : ℝ) = ((p : ℝ) - 1) * (m.totient : ℝ) := by
        have h := Nat.totient_mul_of_prime_of_not_dvd hp hnpdvd
        rw [← hn_eq] at h
        rw [h, Nat.cast_mul, Nat.cast_sub hp.one_le, Nat.cast_one]
      have hncast : (n : ℝ) = (p : ℝ) * (m : ℝ) := by rw [hn_eq, Nat.cast_mul]
      have hCnn : 0 ≤ ((p : ℝ) - 1) * (1 + 1 / Real.sqrt (p : ℝ)) ^ 2 := by
        have hp2r : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
        exact mul_nonneg (by linarith) (sq_nonneg _)
      have hBmnn : 0 ≤ ∑ e ∈ m.divisors, (e.divisors.card : ℝ) / Real.sqrt (e : ℝ) := by
        apply Finset.sum_nonneg
        intro e _
        exact div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
      have hmn : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
      have hprime := prime_local_sqrt_bound p hp
      calc (n.totient : ℝ) * (∑ d ∈ n.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)) ^ 2
          = ((p : ℝ) - 1) * (m.totient : ℝ)
              * ((1 + 1 / Real.sqrt (p : ℝ))
                  * (∑ d ∈ m.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))) ^ 2 := by
              rw [hphi, hA]
        _ = (((p : ℝ) - 1) * (1 + 1 / Real.sqrt (p : ℝ)) ^ 2)
              * ((m.totient : ℝ)
                  * (∑ d ∈ m.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)) ^ 2) := by
              ring
        _ ≤ (((p : ℝ) - 1) * (1 + 1 / Real.sqrt (p : ℝ)) ^ 2)
              * ((m : ℝ)
                  * (∑ e ∈ m.divisors, (e.divisors.card : ℝ) / Real.sqrt (e : ℝ))) :=
              mul_le_mul_of_nonneg_left hIH hCnn
        _ = ((((p : ℝ) - 1) * (1 + 1 / Real.sqrt (p : ℝ)) ^ 2) * (m : ℝ))
              * (∑ e ∈ m.divisors, (e.divisors.card : ℝ) / Real.sqrt (e : ℝ)) := by
              ring
        _ ≤ (((p : ℝ) * (1 + 2 / Real.sqrt (p : ℝ))) * (m : ℝ))
              * (∑ e ∈ m.divisors, (e.divisors.card : ℝ) / Real.sqrt (e : ℝ)) := by
              apply mul_le_mul_of_nonneg_right _ hBmnn
              exact mul_le_mul_of_nonneg_right hprime hmn
        _ = ((p : ℝ) * (m : ℝ))
              * ((1 + 2 / Real.sqrt (p : ℝ))
                  * (∑ e ∈ m.divisors, (e.divisors.card : ℝ) / Real.sqrt (e : ℝ))) := by
              ring
        _ = (n : ℝ) * (∑ e ∈ n.divisors, (e.divisors.card : ℝ) / Real.sqrt (e : ℝ)) := by
              rw [hncast, hB]
  exact main n hn

/-- For every `n : ℕ`, the squared `σ_{-1/2}`-weight with the Euler factor is dominated by the `τ`-weighted divisor sum:
`μ²(n)·φ(n)·(Σ_{d∣n} d^{-1/2})² ≤ n·Σ_{e∣n} τ(e)·e^{-1/2}`.

If `n` is not squarefree the left side vanishes (`ArithmeticFunction.moebius_eq_zero_of_not_squarefree`), so only squarefree `n` matter. Then `φ(n) = ∏_{p∣n}(p-1)`, `Σ_{d∣n} d^{-1/2} = ∏_{p∣n}(1+p^{-1/2})` and `Σ_{e∣n} τ(e) e^{-1/2} = ∏_{p∣n}(1+2p^{-1/2})`; after dividing by `n = ∏ p` the claim is the local inequality `(1-1/p)(1+p^{-1/2})² ≤ 1+2p^{-1/2}`, which is `2x³+x⁴ ≥ 0` for `x = p^{-1/2}`.

A practical route: strong induction on `n`; for squarefree `n > 1` pick a prime `p ∣ n` (`Nat.exists_prime_and_dvd`), write `n = p*m` with `p ∤ m`, use `Nat.totient_mul_of_prime_of_not_dvd`, `Nat.divisors_mul` / `Nat.Coprime.divisors_mul` to split the divisor sums over `{d : d∣m} ⊔ {p*d : d∣m}`, and `Nat.Coprime.card_divisors_mul` for `τ(p*e) = 2*τ(e)`. Useful library lemmas already in this workspace: `Work.LinnikAreas.Density4.sum_recip_divisors_mul_coprime`, `Work.LinnikAreas.Density4.divisors_recip_pow_le_totient_div`. -/
theorem sigma_half_sq_divisor_bound (n : ℕ) :
    ((ArithmeticFunction.moebius n : ℝ) ^ 2) * (n.totient : ℝ) *
        (∑ d ∈ n.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)) ^ 2
      ≤ (n : ℝ) * ∑ e ∈ n.divisors, (e.divisors.card : ℝ) / Real.sqrt (e : ℝ) := by
  by_cases hsq : Squarefree n
  · have hmu : ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2 = 1 := by
      rw [← Int.cast_pow, ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq]
      norm_num
    rw [hmu, one_mul]
    exact squarefree_bound n hsq
  · have hmu : ((ArithmeticFunction.moebius n : ℤ) : ℝ) = 0 := by
      rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
      norm_num
    rw [hmu]
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
    apply mul_nonneg (Nat.cast_nonneg n)
    apply Finset.sum_nonneg
    intro e _
    exact div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)

end Work.LinnikAreas.Density4
