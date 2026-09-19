import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Squarefree

open scoped BigOperators
open Finset

namespace Commons.Algebra.BigOperators

/-- A (coprime-)multiplicative arithmetic function that vanishes on all prime powers
`p ^ k` with `k ≥ 2` vanishes on every non-squarefree divisor of a nonzero `n`. -/
lemma f_eq_zero_of_not_squarefree {α : Type*} [CommRing α] (f : ℕ → α) (n : ℕ)
    (hn : n ≠ 0)
    (hfm : ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a * f b)
    (hfs : ∀ p k : ℕ, p.Prime → 2 ≤ k → f (p ^ k) = 0)
    {d : ℕ} (hd : d ∈ n.divisors) (hdns : ¬ Squarefree d) : f d = 0 := by
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hn (Nat.dvd_of_mem_divisors hd)
  have hnot : ¬ ∀ x : ℕ, Nat.Prime x → ¬ x * x ∣ d :=
    (Nat.squarefree_iff_prime_squarefree.not).mp hdns
  classical
  push Not at hnot
  rcases hnot with ⟨p, hp, hppd⟩
  let e := d.factorization p
  let q := d / p ^ e
  have he2 : 2 ≤ e := by
    have hp2 : p ^ 2 ∣ d := by simpa [pow_two] using hppd
    exact (hp.pow_dvd_iff_le_factorization hd0).mp hp2
  have hdecomp : p ^ e * q = d := by
    simpa [e, q] using (Nat.ordProj_mul_ordCompl_eq_self d p)
  have hcop : Nat.Coprime (p ^ e) q := by
    simpa [q] using (Nat.Coprime.pow_left e (Nat.coprime_ordCompl hp hd0))
  calc
    f d = f (p ^ e * q) := by
      rw [← hdecomp]
    _ = f (p ^ e) * f q := hfm (p ^ e) q hcop
    _ = 0 * f q := by rw [hfs p e hp he2]
    _ = 0 := by simp

/-- A multiplicative arithmetic function with `f 1 = 1` satisfies
`f (∏ p ∈ t, p) = ∏ p ∈ t, f p` on any finite set of primes `t`. -/
lemma f_prod_prime {α : Type*} [CommRing α] (f : ℕ → α) (hf1 : f 1 = 1)
    (hfm : ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a * f b)
    (t : Finset ℕ) (ht : ∀ p ∈ t, Nat.Prime p) :
    f (∏ p ∈ t, p) = ∏ p ∈ t, f p := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [hf1]
  | insert a s ha ih =>
      have hpa : Nat.Prime a := ht a (Finset.mem_insert_self a s)
      have hcop : Nat.Coprime a (∏ p ∈ s, p) := by
        apply Nat.Coprime.prod_right
        intro p hp
        apply (Nat.coprime_primes hpa (ht p (Finset.mem_insert_of_mem hp))).2
        intro h
        apply ha
        exact h ▸ hp
      calc
        f (∏ p ∈ insert a s, p) = f (a * ∏ p ∈ s, p) := by rw [Finset.prod_insert ha]
        _ = f a * f (∏ p ∈ s, p) := hfm a (∏ p ∈ s, p) hcop
        _ = f a * ∏ p ∈ s, f p := by rw [ih (fun p hp => ht p (Finset.mem_insert_of_mem hp))]
        _ = ∏ p ∈ insert a s, f p := (Finset.prod_insert ha).symm

/-- Sum over all divisors equals product over prime factors of `1 + f p`, for a
(coprime-)multiplicative `f : ℕ → α` with `f 1 = 1` that vanishes on prime powers
`p ^ k` with exponent `k ≥ 2`. -/
theorem prod_primeFactors_one_add_eq_sum_divisors {α : Type*} [CommRing α] (f : ℕ → α) (n : ℕ)
    (hn : n ≠ 0) (hf1 : f 1 = 1)
    (hfm : ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a * f b)
    (hfs : ∀ p k : ℕ, p.Prime → 2 ≤ k → f (p ^ k) = 0) :
    (∏ p ∈ n.primeFactors, (1 + f p)) = ∑ d ∈ n.divisors, f d := by
  classical
  -- Rewrite the divisor sum: non-squarefree divisors contribute `0`, so only the
  -- squarefree divisors survive; by unique factorization those correspond exactly to
  -- the subsets of `n.primeFactors`, where `f` factors through the product.
  have hsum : (∑ d ∈ n.divisors, f d) = ∑ t ∈ n.primeFactors.powerset, (∏ p ∈ t, f p) := by
    have hzero : (∑ d ∈ n.divisors with ¬ Squarefree d, f d) = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      exact f_eq_zero_of_not_squarefree f n hn hfm hfs (Finset.mem_filter.mp hd).1
        (Finset.mem_filter.mp hd).2
    calc
      (∑ d ∈ n.divisors, f d)
          = (∑ d ∈ n.divisors with Squarefree d, f d) + (∑ d ∈ n.divisors with ¬ Squarefree d, f d) := by
            exact (Finset.sum_filter_add_sum_filter_not n.divisors (fun d : ℕ => Squarefree d) f).symm
      _ = (∑ d ∈ n.divisors with Squarefree d, f d) := by rw [hzero, add_zero]
      _ = ∑ t ∈ n.primeFactors.powerset, f (∏ p ∈ t, p) := by
            rw [Nat.sum_divisors_filter_squarefree hn]
            apply Finset.sum_congr
            · rw [Nat.factors_eq]
              rfl
            · intro i hi
              congr 1
              rw [Finset.prod_val]; rfl
      _ = ∑ t ∈ n.primeFactors.powerset, (∏ p ∈ t, f p) := by
            apply Finset.sum_congr rfl
            intro t ht
            exact f_prod_prime f hf1 hfm t (fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp ht hp))
  rw [Finset.prod_one_add]
  exact hsum.symm

end Commons.Algebra.BigOperators