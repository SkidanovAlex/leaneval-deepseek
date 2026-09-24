import Mathlib
import Submission.Work.ChenPlan.LinearSieve.RI.identity_defs

/-!
# Splitting the Rosser–Iwaniec divisor sums at the largest prime below `z`

`Gp A z D` (resp. `Gm A z E`) is the weighted Möbius sum
`Σ_{d ∣ P(z)} [rdPlus D d] μ(d) ν(d)` over the *upper*- (resp. *lower*-) admissible divisors of
`P(z) = ∏_{p ∣ P, p < z} p`.  If `q` is the largest prime of the sieve problem strictly below the
sift limit `z` — so that the primes below `z` are exactly the primes below `q` together with `q`
itself, i.e. `P(z) = q · P(q)` — then the divisors of `P(z)` split into those of `P(q)` and those
of the form `q · d` with `d ∣ P(q)`, and the Rosser–Iwaniec recurrences
(`rdPlus_mul_prime`, `rdMinus_mul_prime` in `RI.lamMinus_sieve_lower`) turn the two sums into

* `Gp A z D = Gp A q D - ν(q) · [q³ ≤ D] · Gm A q (D/q)`,
* `Gm A z E = Gm A q E - ν(q) · Gp A q (E/q)`,

while the accompanying sieve product multiplies by the single factor `1 - ν(q)`:
`VfR A z = (1 - ν(q)) · VfR A q`.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.ChenPlan.LinearSieve.RI

noncomputable section

open Classical

/-- Splitting a sum over the divisors of `q * M` (`q` prime, coprime to `M`) into the divisors
of `M` and those of the form `q * d`. -/
private lemma Gp_Gm_split_sum (q M : ℕ) (hq : q.Prime) (hcop : q.Coprime M) (F : ℕ → ℝ) :
    ∑ d ∈ (q * M).divisors, F d = (∑ d ∈ M.divisors, F d) + ∑ d ∈ M.divisors, F (q * d) := by
  rw [Nat.divisors_mul, Finset.mul_def, Finset.sum_image hcop.mul_injOn_divisors,
    Finset.sum_product, hq.divisors, Finset.sum_pair (hq.ne_one.symm)]
  simp

theorem Gp_Gm_split (A : BoundingSieve) {z D : ℝ} {q : ℕ}
    (hq : q ∈ A.prodPrimes.primeFactors) (hqz : (q : ℝ) < z)
    (hmax : ∀ p ∈ A.prodPrimes.primeFactors, (p : ℝ) < z → p ≤ q) :
    Gp A z D = Gp A q D - A.nu q * (if (q : ℝ) ^ 3 ≤ D then Gm A q (D / q) else 0) ∧
    (∀ E : ℝ, Gm A z E = Gm A q E - A.nu q * Gp A q (E / q)) ∧
    VfR A z = (1 - A.nu q) * VfR A q := by
  have hqprime : q.Prime := (Nat.mem_primeFactors.mp hq).1
  -- the primes below `z` are the primes below `q` together with `q`
  have hS : A.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z)
      = insert q (A.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < q)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hp, hpz⟩
      rcases eq_or_ne p q with rfl | hne
      · exact Or.inl rfl
      · exact Or.inr ⟨hp, by exact_mod_cast (lt_of_le_of_ne (hmax p hp hpz) hne)⟩
    · rintro (rfl | ⟨hp, hpq⟩)
      · exact ⟨hq, hqz⟩
      · exact ⟨hp, lt_trans (by exact_mod_cast hpq) hqz⟩
  have hqnotmem : q ∉ A.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < q) :=
    fun h => lt_irrefl _ (Finset.mem_filter.mp h).2
  have hPz : Pz A z = q * Pz A q := by
    unfold Pz
    rw [hS, Finset.prod_insert hqnotmem]
  have hV : VfR A z = (1 - A.nu q) * VfR A q := by
    unfold VfR
    rw [hS, Finset.prod_insert hqnotmem]
  have hqnot : ¬ q ∣ Pz A q := by
    intro hd
    have hmem : q ∈ (Pz A q).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hqprime, hd, Pz_ne_zero A q⟩
    rw [Pz_primeFactors] at hmem
    exact absurd (Finset.mem_filter.mp hmem).2 (lt_irrefl (q : ℝ))
  have hcop : q.Coprime (Pz A q) := hqprime.coprime_iff_not_dvd.mpr hqnot
  -- the standing facts about a divisor `d` of `P(q)`
  have key : ∀ d ∈ (Pz A q).divisors,
      (¬ q ∣ d) ∧ Squarefree d ∧ (∀ p ∈ d.primeFactors, p < q) ∧ d ≠ 0 := by
    intro d hd
    obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp hd
    refine ⟨fun h => hqnot (dvd_trans h hdvd),
      Squarefree.squarefree_of_dvd hdvd (Pz_squarefree A q), ?_,
      div_ne_zero_of_dvd hdvd (Pz_ne_zero A q)⟩
    intro p hp
    have hp' : p ∈ (Pz A q).primeFactors :=
      primeFactors_subset_of_dvd hdvd (Pz_ne_zero A q) hp
    rw [Pz_primeFactors] at hp'
    exact_mod_cast (Finset.mem_filter.mp hp').2
  refine ⟨?_, ?_, hV⟩
  · rw [Gp, Gp, hPz,
      Gp_Gm_split_sum q (Pz A q) hqprime hcop
        (fun d => (if rdPlus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0) * A.nu d)]
    suffices h : (∑ d ∈ (Pz A q).divisors,
        (if rdPlus D (q * d) then ((ArithmeticFunction.moebius (q * d) : ℤ) : ℝ) else 0)
          * A.nu (q * d))
        = -(A.nu q) * (if (q : ℝ) ^ 3 ≤ D then Gm A q (D / q) else 0) by
      rw [h]; ring
    have hsummand : ∀ d ∈ (Pz A q).divisors,
        (if rdPlus D (q * d) then ((ArithmeticFunction.moebius (q * d) : ℤ) : ℝ) else 0)
          * A.nu (q * d)
        = -(A.nu q) * (if (q : ℝ) ^ 3 ≤ D then
            ((if rdMinus (D / q) d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0)
              * A.nu d)
          else 0) := by
      intro d hd
      obtain ⟨hqd, hsq, hbig, _⟩ := key d hd
      rw [moebius_mul_prime hqprime hqd,
        A.nu_mult.map_mul_of_coprime (hqprime.coprime_iff_not_dvd.mpr hqd),
        rdPlus_mul_prime hqprime hsq hqd hbig D]
      by_cases hQ : (q : ℝ) ^ 3 ≤ D
      · by_cases hM : rdMinus (D / q) d
        · rw [if_pos ⟨hQ, hM⟩, if_pos hQ, if_pos hM]; ring
        · rw [if_neg (fun h => hM h.2), if_pos hQ, if_neg hM]; ring
      · rw [if_neg (fun h => hQ h.1), if_neg hQ]; ring
    rw [Finset.sum_congr rfl hsummand, ← Finset.mul_sum]
    congr 1
    by_cases hQ : (q : ℝ) ^ 3 ≤ D
    · rw [if_pos hQ, Gm]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [if_pos hQ]
    · rw [if_neg hQ]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [if_neg hQ]
  · intro E
    rw [Gm, Gm, Gp, hPz,
      Gp_Gm_split_sum q (Pz A q) hqprime hcop
        (fun d => (if rdMinus E d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0) * A.nu d)]
    suffices h : (∑ d ∈ (Pz A q).divisors,
        (if rdMinus E (q * d) then ((ArithmeticFunction.moebius (q * d) : ℤ) : ℝ) else 0)
          * A.nu (q * d))
        = -(A.nu q) * (∑ d ∈ (Pz A q).divisors,
            (if rdPlus (E / q) d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0)
              * A.nu d) by
      rw [h]; ring
    have hsummand : ∀ d ∈ (Pz A q).divisors,
        (if rdMinus E (q * d) then ((ArithmeticFunction.moebius (q * d) : ℤ) : ℝ) else 0)
          * A.nu (q * d)
        = -(A.nu q) * ((if rdPlus (E / q) d then
            ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0) * A.nu d) := by
      intro d hd
      obtain ⟨hqd, hsq, hbig, _⟩ := key d hd
      rw [moebius_mul_prime hqprime hqd,
        A.nu_mult.map_mul_of_coprime (hqprime.coprime_iff_not_dvd.mpr hqd),
        rdMinus_mul_prime hqprime hsq hqd hbig E]
      by_cases hM : rdPlus (E / q) d
      · rw [if_pos hM, if_pos hM]; ring
      · rw [if_neg hM, if_neg hM]; ring
    rw [Finset.sum_congr rfl hsummand, ← Finset.mul_sum]

end

end Work.ChenPlan.LinearSieve.RI
