import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Nat.Totient

open scoped BigOperators

namespace Commons.NumberTheory.DuffinSchaeffer

open Finset

/-- Euler's product formula for `φ(n)/n` over the reals:
`φ(n)/n = ∏_{p | n} (1 - 1/p)` for `n ≠ 0`. -/
lemma totient_div_self_eq_prod_real (n : ℕ) (hn : n ≠ 0) :
    (n.totient : ℝ) / (n : ℝ) = ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ)) := by
  have h := Nat.totient_eq_mul_prod_factors n
  have h' := congrArg (fun z : ℚ => (z : ℝ)) h
  rw [Rat.cast_mul, Rat.cast_natCast, Rat.cast_prod] at h'
  simp only [Rat.cast_sub, Rat.cast_one, Rat.cast_inv, Rat.cast_natCast] at h'
  simp only [inv_eq_one_div] at h'
  rw [h']
  rw [mul_div_cancel_left₀ _ (by exact_mod_cast hn)]

/-- The radical (set of prime divisors) of a product of distinct primes `s` is `s`:
`(∏ p ∈ s, p).primeFactors = s` when every element of `s` is prime. -/
lemma primeFactors_prod_primes (s : Finset ℕ) :
    (∀ p ∈ s, p.Prime) → (∏ p ∈ s, p).primeFactors = s := by
  induction s using Finset.induction_on with
  | empty => intro _; simp
  | insert a s ha ih =>
      intro hs
      rw [Finset.prod_insert ha]
      have hs' : ∀ p ∈ s, p.Prime := fun p hp => hs p (Finset.mem_insert_of_mem hp)
      have hap : a.Prime := hs a (Finset.mem_insert_self a s)
      have hP : (∏ p ∈ s, p) ≠ 0 := (Finset.prod_pos (fun p hp => (hs' p hp).pos)).ne'
      rw [Nat.primeFactors_mul hap.ne_zero hP, ih hs', hap.primeFactors]
      ext x
      simp [Finset.mem_insert]

theorem shellDelta_fold (x q : ℕ) (hq : q ≠ 0) :
    let qs : ℕ := ∏ p ∈ q.primeFactors.filter (fun p : ℕ => p * p ≤ x), p
    let R : Finset ℕ := q.primeFactors.filter (fun p : ℕ => x < p * p)
    (x : ℝ) * (qs.totient : ℝ) / (qs : ℝ)
        - (∑ p ∈ R, ((x / p : ℕ) : ℝ) * (qs.totient : ℝ) / (qs : ℝ))
        - (x : ℝ) * (q.totient : ℝ) / (q : ℝ)
      = (x : ℝ) * (qs.totient : ℝ) / (qs : ℝ) * (1 - ∏ p ∈ R, (1 - (1 : ℝ) / (p : ℝ)))
        - ((∑ p ∈ R, ((x / p : ℕ) : ℝ)) * (qs.totient : ℝ) / (qs : ℝ)) := by
  dsimp only
  set F := q.primeFactors.filter (fun p : ℕ => p * p ≤ x) with hF
  set R := q.primeFactors.filter (fun p : ℕ => x < p * p) with hR
  set qs := ∏ p ∈ F, p with hqs
  -- `R` written with the complementary predicate of `F`
  have hR' : q.primeFactors.filter (fun p : ℕ => ¬ p * p ≤ x) = R := by
    rw [hR]
    apply Finset.filter_congr
    intro p _
    exact Nat.not_le
  -- every prime in `F` is a prime divisor of `q`
  have hFprime : ∀ p ∈ F, p.Prime := by
    intro p hp
    rw [hF] at hp
    exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  have hqs_ne : qs ≠ 0 := by
    rw [hqs]
    exact (Finset.prod_pos (fun p hp => (hFprime p hp).pos)).ne'
  -- Euler product for `q`
  have hq_tot : (q.totient : ℝ) / (q : ℝ)
      = ∏ p ∈ q.primeFactors, (1 - 1 / (p : ℝ)) :=
    totient_div_self_eq_prod_real q hq
  -- Euler product for `qs`
  have hqs_pf : qs.primeFactors = F := by
    rw [hqs]
    exact primeFactors_prod_primes F hFprime
  have hqs_tot : (qs.totient : ℝ) / (qs : ℝ) = ∏ p ∈ F, (1 - 1 / (p : ℝ)) := by
    rw [totient_div_self_eq_prod_real qs hqs_ne, hqs_pf]
  -- split the product over `q.primeFactors` into `F` and `R`
  have hsplit : (∏ p ∈ F, (1 - 1 / (p : ℝ))) * (∏ p ∈ R, (1 - 1 / (p : ℝ)))
      = ∏ p ∈ q.primeFactors, (1 - 1 / (p : ℝ)) := by
    rw [← Finset.prod_filter_mul_prod_filter_not q.primeFactors (fun p : ℕ => p * p ≤ x)
      (fun p => 1 - 1 / (p : ℝ))]
    rw [← hF, ← hR']
  -- key identity relating `q.totient/q` and `qs.totient/qs`
  have hkey : (q.totient : ℝ) / (q : ℝ)
      = (qs.totient : ℝ) / (qs : ℝ) * ∏ p ∈ R, (1 - 1 / (p : ℝ)) := by
    rw [hq_tot, hqs_tot, hsplit]
  -- the two sums agree
  have hS : (∑ p ∈ R, ((x / p : ℕ) : ℝ) * ((qs.totient : ℝ) / (qs : ℝ)))
      = (∑ p ∈ R, ((x / p : ℕ) : ℝ)) * ((qs.totient : ℝ) / (qs : ℝ)) :=
    (Finset.sum_mul R (fun p => ((x / p : ℕ) : ℝ)) ((qs.totient : ℝ) / (qs : ℝ))).symm
  simp_rw [mul_div_assoc]
  rw [hS, hkey]
  ring

end Commons.NumberTheory.DuffinSchaeffer