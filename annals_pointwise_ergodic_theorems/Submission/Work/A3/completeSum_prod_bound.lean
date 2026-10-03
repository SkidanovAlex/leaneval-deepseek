import Mathlib
import Submission.Work.A3.coprime_factor_exists
import Submission.Work.A3.coprime_primeFactors_pow
import Submission.Work.A3.prod_factorization_rpow

/-!
# Multiplicativity of the complete exponential sum: the product bound

The complete sum `completeSum Q a q = ∑_{r<q} e(-2πi a Q(r)/q)` (`Submission/Work/A3/Circle.lean`)
is multiplicative over coprime factorisations of the modulus, by the Chinese remainder theorem
(`Submission/Work/A3/completeSum_mul_eq.lean`, `…/coprime_factor_exists.lean`).  Consequently a
power saving known at every *prime power* (the Weyl/Birch-type input of the circle method, here
hypothesis `hpp`) propagates to an arbitrary modulus, at the price of a factor `C₀` per distinct
prime divisor.

The main statement proved here is

`‖completeSum Q a q‖ ≤ C₀ ^ q.primeFactors.card * (q : ℝ) ^ (1 - η)`   (`(a,q) = 1`, `1 ≤ q`),

from the hypothesis `‖completeSum Q a (p^ν)‖ ≤ C₀ * (p^ν)^{1 - η}` for all primes `p` and `ν ≥ 1`.

The proof is an induction of the Finset of prime factors: writing
`q = ∏_{p | q} p ^ v_p(q)` (`Nat.prod_primeFactors_pow_factorization`) and splitting off the last
factor `p₀ ^ v_{p₀}(q)` from the product, the Chinese remainder factorisation
`completeSum Q a (mn) = completeSum Q (a·u) m * completeSum Q (a·v) n` (with `(u,v)` Bézout for
`(m,n)`) reduces the claim to the corresponding claim for `∏_{p ∈ t} p ^ v_p(q)`, with the
multiplier replaced by the still-admissible multiplier `a·v`.  This is the lemma
`completeSum_prod_le` below; the final bookkeeping is the arithmetic identity
`∏_{p | q} (p^{v_p(q)})^{1-η} = q^{1-η}` (`prod_factorization_rpow`).

Note that neither `1 ≤ C₀` nor `0 < η` is needed for the argument: the recursion is an exact
multiplicative identity, `(C₀ X)·(C₀^k Y) = C₀^{k+1} (X Y)`.
-/

set_option linter.unusedVariables false

namespace Work.A3

open Polynomial Finset
open scoped BigOperators

/-- The complete sum at modulus `1` is a single unit phase, hence has norm `1`. -/
lemma norm_completeSum_one (Q : Polynomial ℤ) (a : ℤ) : ‖completeSum Q a 1‖ = 1 := by
  rw [completeSum, Finset.range_one, Finset.sum_singleton, Complex.norm_exp]
  simp

/-- **The product bound for a Finset of prime powers.**

Let `s` be a finite set of primes and `e p` the exponents of a modulus `∏_{p ∈ s} p ^ e p`.  If
the complete sums at the individual prime powers are bounded by `B p`, then the complete sum at
the product is bounded by `∏_{p ∈ s} B p`, provided the prime powers are pairwise coprime (they
are `≥ 1` and coprime) and the multiplier `a` is coprime to the full modulus.

The induction splits off one prime power and applies the Chinese remainder theorem
(`coprime_factor_exists`); the two coprimality hypotheses on the new multipliers are precisely
what the inductive hypothesis needs. -/
lemma completeSum_prod_le (Q : Polynomial ℤ) :
    ∀ (s : Finset ℕ) (e : ℕ → ℕ) (B : ℕ → ℝ),
      (∀ p ∈ s, 1 ≤ p ^ e p) →
      (∀ p ∈ s, ∀ p' ∈ s, p ≠ p' → (p ^ e p).Coprime (p' ^ e p')) →
      (∀ p ∈ s, ∀ a : ℤ, IsCoprime a (((p ^ e p : ℕ) : ℤ)) →
          ‖completeSum Q a (p ^ e p)‖ ≤ B p) →
      ∀ a : ℤ, IsCoprime a (((∏ p ∈ s, p ^ e p : ℕ) : ℤ)) →
      ‖completeSum Q a (∏ p ∈ s, p ^ e p)‖ ≤ ∏ p ∈ s, B p := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro e B _ _ _ a _
      simpa using (norm_completeSum_one Q a).le
  | insert p₀ t hp₀ ih =>
      intro e B he hcop hbd a ha
      have hA1 : 1 ≤ p₀ ^ e p₀ := he p₀ (Finset.mem_insert_self p₀ t)
      have hN1 : 1 ≤ ∏ p ∈ t, p ^ e p :=
        Finset.one_le_prod₀ (fun p hp => he p (Finset.mem_insert_of_mem hp))
      -- the two factors of the split modulus are coprime
      have hco : (p₀ ^ e p₀).Coprime (∏ p ∈ t, p ^ e p) :=
        Nat.Coprime.prod_right (fun p hp =>
          hcop p₀ (Finset.mem_insert_self p₀ t) p (Finset.mem_insert_of_mem hp)
            (fun h => hp₀ (h ▸ hp)))
      have hprod : (∏ p ∈ insert p₀ t, p ^ e p) = p₀ ^ e p₀ * ∏ p ∈ t, p ^ e p :=
        Finset.prod_insert hp₀
      have ha' : IsCoprime a (((p₀ ^ e p₀ * ∏ p ∈ t, p ^ e p : ℕ) : ℤ)) := by
        rw [← hprod]; exact ha
      -- Chinese remainder: split the complete sum, keeping coprime multipliers
      obtain ⟨u, v, hu, hv, heq⟩ := coprime_factor_exists Q hA1 hN1 hco a ha'
      have hb1 : ‖completeSum Q (a * u) (p₀ ^ e p₀)‖ ≤ B p₀ :=
        hbd p₀ (Finset.mem_insert_self p₀ t) (a * u) hu
      have hb2 : ‖completeSum Q (a * v) (∏ p ∈ t, p ^ e p)‖ ≤ ∏ p ∈ t, B p :=
        ih e B
          (fun p hp => he p (Finset.mem_insert_of_mem hp))
          (fun p hp p' hp' hne =>
            hcop p (Finset.mem_insert_of_mem hp) p' (Finset.mem_insert_of_mem hp') hne)
          (fun p hp a' ha'' => hbd p (Finset.mem_insert_of_mem hp) a' ha'')
          (a * v) hv
      rw [hprod, heq, norm_mul, Finset.prod_insert hp₀]
      exact mul_le_mul hb1 hb2 (norm_nonneg _) (le_trans (norm_nonneg _) hb1)

/-- **Propagation of the power saving at prime powers to an arbitrary modulus.**

If `‖completeSum Q a (p^ν)‖ ≤ C₀ (p^ν)^{1-η}` for every prime `p` and every `ν ≥ 1` and every
`a` coprime to `p^ν`, then for every `q ≥ 1` and every `a` coprime to `q`

`‖completeSum Q a q‖ ≤ C₀ ^ q.primeFactors.card * q^{1-η}`.

The proof applies `completeSum_prod_le` to the prime factorisation
`q = ∏_{p | q} p ^ v_p(q)` with `B p = C₀ (p^{v_p(q)})^{1-η}`; the exponent identity is
`prod_factorization_rpow` and the pairwise coprimality is `coprime_primeFactors_pow`. -/
theorem completeSum_prod_bound (Q : Polynomial ℤ) (C₀ η : ℝ) (hC₀ : 1 ≤ C₀) (hη : 0 < η)
    (hpp : ∀ (p ν : ℕ) (a : ℤ), p.Prime → 1 ≤ ν → IsCoprime a ((p^ν : ℕ) : ℤ) →
      ‖Work.A3.completeSum Q a (p^ν)‖ ≤ C₀ * ((p^ν : ℕ) : ℝ) ^ (1 - η))
    (q : ℕ) (a : ℤ) (hq : 1 ≤ q) (ha : IsCoprime a (q : ℤ)) :
    ‖Work.A3.completeSum Q a q‖ ≤ C₀ ^ q.primeFactors.card * (q : ℝ) ^ (1 - η) := by
  have hq0 : q ≠ 0 := by omega
  -- the complete sum at `q` is the complete sum at its prime factorisation
  have hcs : completeSum Q a q
      = completeSum Q a (∏ p ∈ q.primeFactors, p ^ q.factorization p) := by
    congr 1
    exact Nat.prod_primeFactors_pow_factorization hq0
  -- the product bound at the prime powers
  have hmain := completeSum_prod_le Q q.primeFactors (fun p => q.factorization p)
      (fun p => C₀ * (((p ^ q.factorization p : ℕ) : ℝ) ^ (1 - η)))
      (fun p hp => Nat.one_le_pow _ _
        (lt_of_lt_of_le Nat.zero_lt_two (Nat.prime_of_mem_primeFactors hp).two_le))
      (fun p hp p' hp' hne => coprime_primeFactors_pow q p p' hp hp' hne)
      (fun p hp a' ha' => hpp p (q.factorization p) a' (Nat.prime_of_mem_primeFactors hp)
          (Nat.succ_le_of_lt (Nat.Prime.factorization_pos_of_dvd
            (Nat.prime_of_mem_primeFactors hp) hq0 (Nat.mem_primeFactors.mp hp).2.1)) ha')
      a (by rw [← Nat.prod_primeFactors_pow_factorization hq0]; exact ha)
  -- bookkeeping: `∏_{p | q} C₀ * (p^{v_p(q)})^{1-η} = C₀^{ω(q)} q^{1-η}`
  have hB : (∏ p ∈ q.primeFactors, C₀ * (((p ^ q.factorization p : ℕ) : ℝ) ^ (1 - η)))
      = C₀ ^ q.primeFactors.card * (q : ℝ) ^ (1 - η) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const]
    congr 1
    exact prod_factorization_rpow q hq η
  calc ‖completeSum Q a q‖
      = ‖completeSum Q a (∏ p ∈ q.primeFactors, p ^ q.factorization p)‖ := by rw [hcs]
    _ ≤ ∏ p ∈ q.primeFactors, C₀ * (((p ^ q.factorization p : ℕ) : ℝ) ^ (1 - η)) := hmain
    _ = C₀ ^ q.primeFactors.card * (q : ℝ) ^ (1 - η) := hB

end Work.A3
