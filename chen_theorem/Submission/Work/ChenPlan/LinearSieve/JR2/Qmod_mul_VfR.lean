import Mathlib
import Submission.Work.ChenPlan.LinearSieve.JR2.Defs
import Submission.Work.ChenPlan.LinearSieve.FrameworkR

open Finset
open scoped BigOperators

namespace Work.ChenPlan.LinearSieve.JR2

open Work.ChenPlan.LinearSieve

/-- The density factorisation of the `Q`-trick: for `u₀ ≤ Z`, the primes of `P` below `Z` split
into the primes of `Q = Qmod A u₀` and the primes of `P/Q` below `Z`, so
`∏_{p ∣ Q}(1-ν_p) · VfR(P/Q)(Z) = VfR(P)(Z)`.

Vocabulary in `JR2/Defs.lean` (`Qmod`, `Qmod_dvd`, `subSieve`); ingredients:
`Work.ChenPlan.LinearSieve.VfR`, `Finset.prod_filter_mul_prod_filter_not`,
`Nat.div_primeFactors`, `Nat.prod_primeFactors_of_squarefree`. -/
theorem Qmod_mul_VfR (A : BoundingSieve) {u₀ Z : ℝ} (hu₀Z : u₀ ≤ Z) :
    (∏ p ∈ (Work.ChenPlan.LinearSieve.JR2.Qmod A u₀).primeFactors, (1 - A.nu p))
        * Work.ChenPlan.LinearSieve.VfR
            (Work.ChenPlan.LinearSieve.JR2.subSieve A (Work.ChenPlan.LinearSieve.JR2.Qmod A u₀)
              (Work.ChenPlan.LinearSieve.JR2.Qmod_dvd A u₀)) Z
      = Work.ChenPlan.LinearSieve.VfR A Z := by
  -- `T` is the set of primes of `P` below `u₀`; `Q` is their product.
  set T : Finset ℕ := A.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < u₀) with hT
  have hTprime : ∀ p ∈ T, p.Prime := by
    intro p hp
    rw [hT] at hp
    exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  set Q : ℕ := Qmod A u₀ with hQ
  have hQprod : Q = ∏ p ∈ T, p := by rw [hQ, Qmod, hT]
  -- the prime factors of `Q` are exactly `T`
  have hQpf : Q.primeFactors = T := by rw [hQprod, Nat.primeFactors_prod hTprime]
  have hQne : Q ≠ 0 := by
    rw [hQprod]
    exact Finset.prod_ne_zero_iff.mpr (fun p hp => (hTprime p hp).ne_zero)
  have hdvd : Q ∣ A.prodPrimes := by rw [hQ]; exact Qmod_dvd A u₀
  -- the prime factors of `P/Q` are the remaining primes of `P`
  have hdiv : (A.prodPrimes / Q).primeFactors = A.prodPrimes.primeFactors \ T := by
    rw [← Nat.gcd_eq_right hdvd, Nat.primeFactors_div_gcd A.prodPrimes_squarefree hQne, hQpf]
  -- unfolding `VfR` on the sub-sieve
  have hunfold : VfR (subSieve A Q (Qmod_dvd A u₀)) Z
      = ∏ p ∈ (A.prodPrimes / Q).primeFactors.filter (fun p : ℕ => (p : ℝ) < Z),
          (1 - A.nu p) := by
    simp only [VfR, subSieve]
  -- the primes of `P` below `Z` split into `T` and the primes of `P/Q` below `Z`
  have hsplit : A.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < Z)
      = T ∪ (A.prodPrimes.primeFactors \ T).filter (fun p : ℕ => (p : ℝ) < Z) := by
    ext p
    simp only [hT, Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro ⟨hp, hpZ⟩
      by_cases hpu : (p : ℝ) < u₀
      · exact Or.inl ⟨hp, hpu⟩
      · exact Or.inr ⟨⟨hp, fun h => hpu h.2⟩, hpZ⟩
    · rintro (⟨hp, hpu⟩ | ⟨⟨hp, _⟩, hpZ⟩)
      · exact ⟨hp, lt_of_lt_of_le hpu hu₀Z⟩
      · exact ⟨hp, hpZ⟩
  have hdisj : Disjoint T ((A.prodPrimes.primeFactors \ T).filter (fun p : ℕ => (p : ℝ) < Z)) := by
    rw [Finset.disjoint_left]
    intro p hpT hpR
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hpR).1).2 hpT
  rw [hQpf, hunfold, hdiv, VfR, hsplit, Finset.prod_union hdisj]

end Work.ChenPlan.LinearSieve.JR2
