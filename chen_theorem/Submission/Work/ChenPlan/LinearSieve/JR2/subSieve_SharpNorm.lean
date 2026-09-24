import Mathlib
import Submission.Work.ChenPlan.LinearSieve.JR2.Defs

namespace Work.ChenPlan.LinearSieve.JR2

open Finset
open scoped BigOperators

set_option autoImplicit false

-- `hK` is part of the (fixed) statement but not needed for the estimate itself.
set_option linter.unusedVariables false

/-! ## Bookkeeping for the `P/Q` sub-sieve

`Qmod A u₀ = ∏_{p ∣ P, p < u₀} p`.  Because `P` is squarefree the prime factors of `Qmod A u₀` are
exactly the primes of `P` below `u₀`, and hence the prime factors of the sub-sieve `P/Q` are exactly
the primes of `P` that are `≥ u₀`. -/

/-- `Qmod A u₀` (a product of primes `≥ 2`) is nonzero. -/
lemma Qmod_ne_zero (A : BoundingSieve) (u₀ : ℝ) : Qmod A u₀ ≠ 0 := by
  rw [Qmod]
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).ne_zero

/-- The prime factors of `Qmod A u₀` are exactly the primes of `P` below `u₀`. -/
lemma Qmod_primeFactors (A : BoundingSieve) (u₀ : ℝ) :
    (Qmod A u₀).primeFactors = A.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < u₀) := by
  rw [Qmod]
  exact Nat.primeFactors_prod
    (fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)

/-- The sifting primes of the `P/Q` sub-sieve (with `Q = Qmod A u₀`) are exactly the primes of `P`
that are `≥ u₀`. -/
lemma subSieve_Qmod_primeFactors (A : BoundingSieve) (u₀ : ℝ) :
    (subSieve A (Qmod A u₀) (Qmod_dvd A u₀)).prodPrimes.primeFactors
      = A.prodPrimes.primeFactors.filter (fun p : ℕ => u₀ ≤ (p : ℝ)) := by
  have hQnz : Qmod A u₀ ≠ 0 := Qmod_ne_zero A u₀
  have hgcd : A.prodPrimes / A.prodPrimes.gcd (Qmod A u₀) = A.prodPrimes / Qmod A u₀ := by
    rw [Nat.gcd_eq_right (Qmod_dvd A u₀)]
  rw [show (subSieve A (Qmod A u₀) (Qmod_dvd A u₀)).prodPrimes = A.prodPrimes / Qmod A u₀ from rfl]
  rw [← hgcd, Nat.primeFactors_div_gcd A.prodPrimes_squarefree hQnz, Qmod_primeFactors]
  ext p
  simp only [Finset.mem_sdiff, Finset.mem_filter]
  constructor
  · rintro ⟨hp, hp2⟩
    exact ⟨hp, not_lt.mp (fun h => hp2 ⟨hp, h⟩)⟩
  · rintro ⟨hp, hge⟩
    exact ⟨hp, fun h => not_lt_of_ge hge h.2⟩

/-- The `P/Q` sub-sieve inherits the **sharp** normalisation: if `IsLinearRange A z K`, `0 ≤ K`,
`0 ≤ ε`, `u₀ ≥ 2` and `K ≤ ε·log u₀`, then the sub-sieve `subSieve A (Qmod A u₀) _` (whose
sifting primes are exactly those of `P` above `u₀`) satisfies `SharpNorm · z ε` at *every* range
`2 ≤ w < z' ≤ z`.  Three cases: for `u₀ ≤ w` the sub-sieve product on `[w,z')` equals `P`'s, and
`K/log w ≤ K/log u₀ ≤ ε`; for `w < u₀ < z'` it equals `P`'s product on `[u₀,z')`, so `hlin` at
`(u₀,z')` gives `≤ (1+ε)log z'/log u₀ ≤ (1+ε)log z'/log w`; for `z' ≤ u₀` the product is empty.

Vocabulary: `JR2/Defs.lean` (`SharpNorm`, `Qmod`, `Qmod_dvd`, `subSieve`),
`Submission.ChenPlan.IsLinearRange` (imported transitively via `JR2/Defs`),
`Nat.mem_primeFactors`, `Nat.div_primeFactors` (to see
`(P/Q).primeFactors = P.primeFactors \ Q.primeFactors`). -/
theorem subSieve_SharpNorm (A : BoundingSieve) {z K ε u₀ : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hu₀ : 2 ≤ u₀) (hKε : K ≤ ε * Real.log u₀)
    (hlin : Submission.ChenPlan.IsLinearRange A z K) :
    Work.ChenPlan.LinearSieve.JR2.SharpNorm
      (Work.ChenPlan.LinearSieve.JR2.subSieve A (Work.ChenPlan.LinearSieve.JR2.Qmod A u₀)
        (Work.ChenPlan.LinearSieve.JR2.Qmod_dvd A u₀)) z ε := by
  intro w z' hw hwz' hz'z
  have hu₀1 : (1 : ℝ) < u₀ := by linarith
  have hw1 : (1 : ℝ) < w := by linarith
  have hlogu₀ : 0 < Real.log u₀ := Real.log_pos hu₀1
  have hlogw : 0 < Real.log w := Real.log_pos hw1
  have hlogz' : 0 < Real.log z' := Real.log_pos (by linarith)
  have hnu : ∀ p : ℕ, (subSieve A (Qmod A u₀) (Qmod_dvd A u₀)).nu p = A.nu p := fun p => rfl
  rw [subSieve_Qmod_primeFactors]
  rcases le_or_gt u₀ w with hu₀w | hw_u₀
  · -- Case A: `u₀ ≤ w`.  The sub-sieve product on `[w,z')` is `P`'s.
    have hset : (A.prodPrimes.primeFactors.filter (fun p : ℕ => u₀ ≤ (p : ℝ))).filter
        (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z')
        = A.prodPrimes.primeFactors.filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z') := by
      rw [Finset.filter_filter]
      apply Finset.filter_congr
      intro p hp
      constructor
      · rintro ⟨-, h2, h3⟩; exact ⟨h2, h3⟩
      · rintro ⟨h1, h2⟩; exact ⟨le_trans hu₀w h1, h1, h2⟩
    rw [hset]
    simp only [hnu]
    have hlogle : Real.log u₀ ≤ Real.log w := Real.log_le_log (by linarith) hu₀w
    have hKw : K / Real.log w ≤ ε := by
      rw [div_le_iff₀ hlogw]
      exact hKε.trans (mul_le_mul_of_nonneg_left hlogle hε)
    have hc : 0 ≤ Real.log z' / Real.log w := div_nonneg (le_of_lt hlogz') (le_of_lt hlogw)
    have hfin : (Real.log z' / Real.log w) * (1 + K / Real.log w)
        ≤ (1 + ε) * (Real.log z' / Real.log w) := by
      nlinarith [mul_le_mul_of_nonneg_left hKw hc]
    calc ∏ p ∈ A.prodPrimes.primeFactors.filter
            (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z'), (1 - A.nu p)⁻¹
        ≤ (Real.log z' / Real.log w) * (1 + K / Real.log w) := hlin w z' hw hwz' hz'z
      _ ≤ (1 + ε) * (Real.log z' / Real.log w) := hfin
  · rcases lt_or_ge u₀ z' with hu₀z' | hz'u₀
    · -- Case B: `w < u₀ < z'`.  The sub-sieve product on `[w,z')` is `P`'s on `[u₀,z')`.
      have hset : (A.prodPrimes.primeFactors.filter (fun p : ℕ => u₀ ≤ (p : ℝ))).filter
          (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z')
          = A.prodPrimes.primeFactors.filter (fun p : ℕ => u₀ ≤ (p : ℝ) ∧ (p : ℝ) < z') := by
        rw [Finset.filter_filter]
        apply Finset.filter_congr
        intro p hp
        constructor
        · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
        · rintro ⟨h1, h3⟩; exact ⟨h1, le_of_lt (lt_of_lt_of_le hw_u₀ h1), h3⟩
      rw [hset]
      simp only [hnu]
      have hlogle : Real.log w ≤ Real.log u₀ := Real.log_le_log (by linarith) (le_of_lt hw_u₀)
      have h1 : (1 + K / Real.log u₀) ≤ (1 + ε) := by
        have : K / Real.log u₀ ≤ ε := by rw [div_le_iff₀ hlogu₀]; exact hKε
        linarith
      have hdiv : Real.log z' / Real.log u₀ ≤ Real.log z' / Real.log w := by
        have h := one_div_le_one_div_of_le hlogw hlogle
        calc Real.log z' / Real.log u₀ = Real.log z' * (1 / Real.log u₀) := by ring
          _ ≤ Real.log z' * (1 / Real.log w) := mul_le_mul_of_nonneg_left h (le_of_lt hlogz')
          _ = Real.log z' / Real.log w := by ring
      have hc₁ : 0 ≤ Real.log z' / Real.log u₀ := div_nonneg (le_of_lt hlogz') (le_of_lt hlogu₀)
      calc ∏ p ∈ A.prodPrimes.primeFactors.filter
              (fun p : ℕ => u₀ ≤ (p : ℝ) ∧ (p : ℝ) < z'), (1 - A.nu p)⁻¹
          ≤ (Real.log z' / Real.log u₀) * (1 + K / Real.log u₀) := hlin u₀ z' hu₀ hu₀z' hz'z
        _ ≤ (1 + ε) * (Real.log z' / Real.log w) := by
            calc (Real.log z' / Real.log u₀) * (1 + K / Real.log u₀)
                ≤ (Real.log z' / Real.log u₀) * (1 + ε) := mul_le_mul_of_nonneg_left h1 hc₁
              _ ≤ (Real.log z' / Real.log w) * (1 + ε) :=
                  mul_le_mul_of_nonneg_right hdiv (by linarith)
              _ = (1 + ε) * (Real.log z' / Real.log w) := by ring
    · -- Case C: `z' ≤ u₀`.  The sub-sieve has no sifting prime below `z'`.
      have hset : (A.prodPrimes.primeFactors.filter (fun p : ℕ => u₀ ≤ (p : ℝ))).filter
          (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z') = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro p hp hpa
        rw [Finset.mem_filter] at hp
        obtain ⟨-, hle⟩ := hp
        obtain ⟨-, hlt⟩ := hpa
        exact not_lt_of_ge hle (lt_of_lt_of_le hlt hz'u₀)
      rw [hset]
      simp only [hnu, Finset.prod_empty]
      have hratio : 1 ≤ Real.log z' / Real.log w := by
        rw [le_div_iff₀ hlogw, one_mul]
        exact Real.log_le_log (by linarith) hwz'.le
      exact one_le_mul_of_one_le_of_one_le (by linarith) hratio

end Work.ChenPlan.LinearSieve.JR2
