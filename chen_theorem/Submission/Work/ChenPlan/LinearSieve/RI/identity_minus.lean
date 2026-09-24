import Mathlib
import Submission.Work.ChenPlan.LinearSieve.RI.basic
import Submission.Work.ChenPlan.LinearSieve.RI.identity_defs
import Submission.Commons.NumberTheory.Sieve.Esum_rec_sieve

/-!
# The Rosser–Iwaniec `λ⁻` identity: `Gm A z D = VfR A z - Σ_{2 ≤ n, even} T_n(D,z)`

This file proves `Work.ChenPlan.LinearSieve.RI.identity_minus`.

Writing `Gm A z D = Σ_{d ∣ P(z)} [rdMinus D d] μ(d) ν(d)` for the weighted Möbius sum over the
lower-admissible divisors of `P(z)` and `T_n(D,z)` for the Rosser–Iwaniec layer sums, the identity is

`Gm A z D = VfR A z - Σ_{n even, n ≥ 2} T_n(D,z)`

(the truncation at `Nat.log 2 ⌈D⌉₊ + 3` on the right is spurious: the terms beyond it vanish).

## Proof

The two identities

* `Gm A z D = VfR A z - Σ_{n even, n ≥ 2} T_n(D,z)`
* `Gp A z D = VfR A z + Σ_{n odd, n ≥ 1} T_n(D,z)`

are proved simultaneously by induction on the number of primes of `P` below `z`, peeling the
*largest* such prime `q`:

* `Gm A z D = Gm A q D - ν(q) · Gp A q (D/q)` (the divisors of `q·P(q)` split into those not
  divisible by `q` and `q` times those of `P(q)`, and `rdMinus D (q d) ↔ rdPlus (D/q) d`),
* `Gp A z D = Gp A q D - ν(q) · [q³ ≤ D] · Gm A q (D/q)`
  (here `rdPlus D (q d) ↔ q³ ≤ D ∧ rdMinus (D/q) d`),
* `VfR A z = (1 - ν(q)) VfR A q`,
* `T_n(D,z) = T_n(D,q) + [Tcond n D q] ν(q) T_{n-1}(D/q,q)`.

The truncations are matched exactly: the even sum with cutoff `N` at level `z` is the even sum with
cutoff `N` at level `q` plus `ν(q)` times the odd sum with cutoff `N-1` at level `q`; the odd sum
with cutoff `N` at level `z` is the odd sum with cutoff `N` at level `q`, plus `ν(q)V(q)` when
`D < q³` (the `n = 1` term) and `ν(q)` times the even sum with cutoff `N-1` at level `q` when
`q³ ≤ D`.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.ChenPlan.LinearSieve.RI

noncomputable section

open Classical

attribute [local instance] Classical.propDecidable

/-! ## The truncated layer sums -/

/-- The even layer sum `Σ_{2 ≤ n < N} T_n(D,z)`. -/
private def evSum (A : BoundingSieve) (D z : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ (Finset.range N).filter (fun n : ℕ => Even n ∧ n ≠ 0), T A n D z

/-- The odd layer sum `Σ_{n < N} T_n(D,z)`. -/
private def odSum (A : BoundingSieve) (D z : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ (Finset.range N).filter (fun n : ℕ => Odd n), T A n D z

/-! ## Elementary facts about `P(z)` -/

private lemma Pz_dvd_prodPrimes (A : BoundingSieve) (z : ℝ) : Pz A z ∣ A.prodPrimes := by
  have h := Finset.prod_dvd_prod_of_subset
    (A.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z)) A.prodPrimes.primeFactors
    (fun p : ℕ => p) (Finset.filter_subset (fun p : ℕ => (p : ℝ) < z) _)
  rwa [Nat.prod_primeFactors_of_squarefree A.prodPrimes_squarefree] at h

private lemma mem_Pz_primeFactors {A : BoundingSieve} {z : ℝ} {p : ℕ}
    (hp : p ∈ (Pz A z).primeFactors) : p.Prime ∧ (p : ℝ) < z := by
  rw [Pz_primeFactors] at hp
  obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
  exact ⟨(Nat.mem_primeFactors.mp hp1).1, hp2⟩

private lemma dvd_prodPrimes_of_dvd_Pz {A : BoundingSieve} {z : ℝ} {d : ℕ} (hd : d ∣ Pz A z) :
    d ∣ A.prodPrimes := dvd_trans hd (Pz_dvd_prodPrimes A z)

private lemma lamMinus_eq (A : BoundingSieve) (D : ℝ) {d : ℕ} (hd : d ∣ A.prodPrimes) :
    lamMinus A.prodPrimes D d
      = if rdMinus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0 := by
  rw [lamMinus]
  by_cases h : rdMinus D d
  · rw [if_pos ⟨hd, h⟩, if_pos h]
  · rw [if_neg (fun hc => h hc.2), if_neg h]

private lemma lamPlus_eq (A : BoundingSieve) (D : ℝ) {d : ℕ} (hd : d ∣ A.prodPrimes) :
    lamPlus A.prodPrimes D d
      = if rdPlus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0 := by
  rw [lamPlus]
  by_cases h : rdPlus D d
  · rw [if_pos ⟨hd, h⟩, if_pos h]
  · rw [if_neg (fun hc => h hc.2), if_neg h]

/-- The weighted Möbius sum `Gm` written with `lamMinus`. -/
private lemma Gm_eq_sum (A : BoundingSieve) (z D : ℝ) :
    Gm A z D = ∑ d ∈ (Pz A z).divisors, lamMinus A.prodPrimes D d * A.nu d := by
  rw [Gm]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  rw [lamMinus_eq A D (dvd_prodPrimes_of_dvd_Pz (Nat.mem_divisors.mp hd).1)]

/-! ## Peeling the largest prime below the sift limit -/

/-- Peeling the largest prime `q` of `P` below `z` from the prime set. -/
private lemma filter_lt_max (A : BoundingSieve) {z : ℝ} {q : ℕ}
    (hqPS : q ∈ A.prodPrimes.primeFactors) (hqz : (q : ℝ) < z)
    (hmax : ∀ p ∈ A.prodPrimes.primeFactors, (p : ℝ) < z → p ≤ q) :
    A.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z)
      = insert q (A.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < q)) := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨hpPS, hpz⟩
    rcases eq_or_lt_of_le (hmax p hpPS hpz) with h | h
    · exact Or.inl h
    · exact Or.inr ⟨hpPS, by exact_mod_cast h⟩
  · rintro (rfl | ⟨hpPS, hpq⟩)
    · exact ⟨hqPS, hqz⟩
    · exact ⟨hpPS, lt_trans (by exact_mod_cast hpq) hqz⟩

/-- The same peeling, with an extra predicate `c` on the primes. -/
private lemma filter_and_lt_max (A : BoundingSieve) {z : ℝ} {q : ℕ} (c : ℕ → Prop)
    [DecidablePred c] (hqPS : q ∈ A.prodPrimes.primeFactors) (hqz : (q : ℝ) < z)
    (hmax : ∀ p ∈ A.prodPrimes.primeFactors, (p : ℝ) < z → p ≤ q) :
    A.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z ∧ c p)
      = A.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < q ∧ c p)
        ∪ (if c q then {q} else ∅) := by
  ext p
  by_cases hcq : c q
  · rw [if_pos hcq]
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton]
    constructor
    · rintro ⟨hpPS, hpz, hc⟩
      rcases eq_or_lt_of_le (hmax p hpPS hpz) with h | h
      · exact Or.inr h
      · exact Or.inl ⟨hpPS, by exact_mod_cast h, hc⟩
    · rintro (⟨hpPS, hpq, hc⟩ | hpq)
      · exact ⟨hpPS, lt_trans (by exact_mod_cast hpq) hqz, hc⟩
      · rw [hpq]
        exact ⟨hqPS, hqz, hcq⟩
  · rw [if_neg hcq]
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hpPS, hpz, hc⟩
      have hpq : p < q := lt_of_le_of_ne (hmax p hpPS hpz) (fun h => hcq (h ▸ hc))
      exact Or.inl ⟨hpPS, by exact_mod_cast hpq, hc⟩
    · rintro (h | hmem)
      · obtain ⟨hpPS, hpq, hc⟩ := h
        exact ⟨hpPS, lt_trans (by exact_mod_cast hpq) hqz, hc⟩
      · exact absurd hmem (Finset.notMem_empty p)

private lemma Pz_peel (A : BoundingSieve) {z : ℝ} {q : ℕ} (hqPS : q ∈ A.prodPrimes.primeFactors)
    (hqz : (q : ℝ) < z)
    (hmax : ∀ p ∈ A.prodPrimes.primeFactors, (p : ℝ) < z → p ≤ q) :
    Pz A z = q * Pz A q := by
  have hset := filter_lt_max A hqPS hqz hmax
  have hqmem : q ∉ A.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < q) := by
    simp only [Finset.mem_filter, not_and]
    intro _
    exact not_lt.mpr (le_refl (q : ℝ))
  calc Pz A z = ∏ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z), p := rfl
    _ = ∏ p ∈ insert q (A.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < q)), p := by
          rw [hset]
    _ = q * ∏ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < q), p :=
          Finset.prod_insert hqmem
    _ = q * Pz A q := rfl

private lemma VfR_peel (A : BoundingSieve) {z : ℝ} {q : ℕ} (hqPS : q ∈ A.prodPrimes.primeFactors)
    (hqz : (q : ℝ) < z)
    (hmax : ∀ p ∈ A.prodPrimes.primeFactors, (p : ℝ) < z → p ≤ q) :
    VfR A z = (1 - A.nu q) * VfR A q := by
  have hset := filter_lt_max A hqPS hqz hmax
  have hqmem : q ∉ A.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < q) := by
    simp only [Finset.mem_filter, not_and]
    intro _
    exact not_lt.mpr (le_refl (q : ℝ))
  calc VfR A z
      = ∏ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z), (1 - A.nu p) := rfl
    _ = ∏ p ∈ insert q (A.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < q)),
          (1 - A.nu p) := by rw [hset]
    _ = (1 - A.nu q)
          * ∏ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < q), (1 - A.nu p) :=
          Finset.prod_insert hqmem
    _ = (1 - A.nu q) * VfR A q := rfl

/-! ## The two Möbius sums split at the largest prime -/

private lemma not_dvd_Pz_self (A : BoundingSieve) {q : ℕ} (hqprime : q.Prime) :
    ¬ q ∣ Pz A q := by
  intro hd
  have hmem : q ∈ (Pz A q).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hqprime, hd, Pz_ne_zero A q⟩
  exact absurd (mem_Pz_primeFactors hmem).2 (not_lt.mpr (le_refl (q : ℝ)))

/-- The term identity behind the `Gm` peel. -/
private lemma termMinus (A : BoundingSieve) {D : ℝ} {q d : ℕ} (hqprime : q.Prime)
    (hd : d ∣ Pz A q) :
    (if rdMinus D (q * d) then ((ArithmeticFunction.moebius (q * d) : ℤ) : ℝ) else 0)
        * A.nu (q * d)
      = -(A.nu q)
        * ((if rdPlus (D / q) d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0)
            * A.nu d) := by
  have hsqd : Squarefree d :=
    Squarefree.squarefree_of_dvd (dvd_trans hd (Pz_dvd_prodPrimes A q)) A.prodPrimes_squarefree
  have hqd : ¬ q ∣ d := fun h => not_dvd_Pz_self A hqprime (dvd_trans h hd)
  have hpr : ∀ p ∈ d.primeFactors, p < q := by
    intro p hp
    exact_mod_cast (mem_Pz_primeFactors
      (primeFactors_subset_of_dvd hd (Pz_ne_zero A q) hp)).2
  have hiff := rdMinus_mul_prime hqprime hsqd hqd hpr D
  have hmu := moebius_mul_prime hqprime hqd
  have hnu : A.nu (q * d) = A.nu q * A.nu d :=
    A.nu_mult.map_mul_of_coprime (hqprime.coprime_iff_not_dvd.mpr hqd)
  by_cases h1 : rdPlus (D / q) d
  · rw [if_pos (hiff.mpr h1), if_pos h1, hmu, hnu]
    ring
  · rw [if_neg (fun hc => h1 (hiff.mp hc)), if_neg h1]
    ring

/-- The term identity behind the `Gp` peel. -/
private lemma termPlus (A : BoundingSieve) {D : ℝ} {q d : ℕ} (hqprime : q.Prime)
    (hd : d ∣ Pz A q) :
    (if rdPlus D (q * d) then ((ArithmeticFunction.moebius (q * d) : ℤ) : ℝ) else 0)
        * A.nu (q * d)
      = -(A.nu q)
        * ((if (q : ℝ) ^ 3 ≤ D then
              (if rdMinus (D / q) d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0)
            else 0) * A.nu d) := by
  have hsqd : Squarefree d :=
    Squarefree.squarefree_of_dvd (dvd_trans hd (Pz_dvd_prodPrimes A q)) A.prodPrimes_squarefree
  have hqd : ¬ q ∣ d := fun h => not_dvd_Pz_self A hqprime (dvd_trans h hd)
  have hpr : ∀ p ∈ d.primeFactors, p < q := by
    intro p hp
    exact_mod_cast (mem_Pz_primeFactors
      (primeFactors_subset_of_dvd hd (Pz_ne_zero A q) hp)).2
  have hiff := rdPlus_mul_prime hqprime hsqd hqd hpr D
  have hmu := moebius_mul_prime hqprime hqd
  have hnu : A.nu (q * d) = A.nu q * A.nu d :=
    A.nu_mult.map_mul_of_coprime (hqprime.coprime_iff_not_dvd.mpr hqd)
  by_cases h2 : (q : ℝ) ^ 3 ≤ D
  · rw [if_pos h2]
    by_cases h1 : rdMinus (D / q) d
    · rw [if_pos (hiff.mpr ⟨h2, h1⟩), if_pos h1, hmu, hnu]
      ring
    · rw [if_neg (fun hc => h1 (hiff.mp hc).2), if_neg h1]
      ring
  · rw [if_neg h2]
    rw [if_neg (fun hc => h2 (hiff.mp hc).1)]
    ring

private lemma Gm_peel (A : BoundingSieve) {z D : ℝ} {q : ℕ}
    (hqPS : q ∈ A.prodPrimes.primeFactors) (hqz : (q : ℝ) < z)
    (hmax : ∀ p ∈ A.prodPrimes.primeFactors, (p : ℝ) < z → p ≤ q) :
    Gm A z D = Gm A q D - A.nu q * Gp A q (D / q) := by
  have hqprime : q.Prime := (Nat.mem_primeFactors.mp hqPS).1
  have hPz : Pz A z = q * Pz A q := Pz_peel A hqPS hqz hmax
  have hqnd : ¬ q ∣ Pz A q := not_dvd_Pz_self A hqprime
  have h2 : (∑ d ∈ (Pz A q).divisors,
        (if rdMinus D (q * d) then ((ArithmeticFunction.moebius (q * d) : ℤ) : ℝ) else 0)
          * A.nu (q * d))
      = -(A.nu q) * Gp A q (D / q) := by
    rw [Gp, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun d hd => termMinus A hqprime (Nat.mem_divisors.mp hd).1)
  unfold Gm
  rw [hPz, Commons.NumberTheory.Sieve.sum_divisors_mul_prime
    (fun d => (if rdMinus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0) * A.nu d)
    q (Pz A q) hqprime hqnd, h2]
  ring

private lemma Gp_peel (A : BoundingSieve) {z D : ℝ} {q : ℕ}
    (hqPS : q ∈ A.prodPrimes.primeFactors) (hqz : (q : ℝ) < z)
    (hmax : ∀ p ∈ A.prodPrimes.primeFactors, (p : ℝ) < z → p ≤ q) :
    Gp A z D = Gp A q D - A.nu q * (if (q : ℝ) ^ 3 ≤ D then Gm A q (D / q) else 0) := by
  have hqprime : q.Prime := (Nat.mem_primeFactors.mp hqPS).1
  have hPz : Pz A z = q * Pz A q := Pz_peel A hqPS hqz hmax
  have hqnd : ¬ q ∣ Pz A q := not_dvd_Pz_self A hqprime
  have h2 : (∑ d ∈ (Pz A q).divisors,
        (if rdPlus D (q * d) then ((ArithmeticFunction.moebius (q * d) : ℤ) : ℝ) else 0)
          * A.nu (q * d))
      = -(A.nu q) * (if (q : ℝ) ^ 3 ≤ D then Gm A q (D / q) else 0) := by
    by_cases hc : (q : ℝ) ^ 3 ≤ D
    · rw [if_pos hc, Gm, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun d hd => ?_)
      rw [termPlus A hqprime (Nat.mem_divisors.mp hd).1, if_pos hc]
    · rw [if_neg hc, mul_zero]
      refine Finset.sum_eq_zero (fun d hd => ?_)
      rw [termPlus A hqprime (Nat.mem_divisors.mp hd).1, if_neg hc]
      simp
  unfold Gp
  rw [hPz, Commons.NumberTheory.Sieve.sum_divisors_mul_prime
    (fun d => (if rdPlus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0) * A.nu d)
    q (Pz A q) hqprime hqnd, h2]
  ring

/-! ## The layer sums peel at the largest prime -/

private lemma Tcond_of_even {n : ℕ} {D : ℝ} {q : ℕ} (h : Even n) : Tcond n D q := by
  refine ⟨?_, ?_⟩
  · intro h1
    exfalso
    obtain ⟨k, hk⟩ := h
    rw [h1] at hk
    omega
  · intro _ hodd
    exact absurd h (Nat.not_even_iff_odd.mpr hodd)

private lemma Tcond_one {D : ℝ} {q : ℕ} : (Tcond 1 D q ↔ D < (q : ℝ) ^ 3) := by
  unfold Tcond
  simp

private lemma Tcond_of_odd {n : ℕ} {D : ℝ} {q : ℕ} (hn : Odd n) (h1 : n ≠ 1) :
    (Tcond n D q ↔ (q : ℝ) ^ 3 ≤ D) := by
  obtain ⟨k, hk⟩ := hn
  have h2 : 2 ≤ n := by omega
  exact ⟨fun h => h.2 h2 ⟨k, hk⟩, fun h => ⟨fun he => absurd he h1, fun _ _ => h⟩⟩

/-- Peeling the largest prime below `z` from the layer sum recursion. -/
private lemma T_peel (A : BoundingSieve) {z : ℝ} {q : ℕ}
    (hqPS : q ∈ A.prodPrimes.primeFactors) (hqz : (q : ℝ) < z)
    (hmax : ∀ p ∈ A.prodPrimes.primeFactors, (p : ℝ) < z → p ≤ q)
    (m : ℕ) (D : ℝ) :
    T A (m + 1) D z = T A (m + 1) D q
      + (if Tcond (m + 1) D q then A.nu q * T A m (D / q) q else 0) := by
  have hset := filter_and_lt_max A (fun p : ℕ => Tcond (m + 1) D p) hqPS hqz hmax
  have hdisj : Disjoint
      (A.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < q ∧ Tcond (m + 1) D p))
      (if Tcond (m + 1) D q then {q} else ∅) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [Finset.mem_filter] at hx1
    by_cases hc : Tcond (m + 1) D q
    · rw [if_pos hc, Finset.mem_singleton] at hx2
      rw [hx2] at hx1
      exact absurd hx1.2.1 (not_lt.mpr (le_refl (q : ℝ)))
    · rw [if_neg hc] at hx2
      exact Finset.notMem_empty x hx2
  have hsmall : (∑ p ∈ A.prodPrimes.primeFactors.filter
        (fun p : ℕ => (p : ℝ) < q ∧ Tcond (m + 1) D p), A.nu p * T A m (D / p) p)
      = T A (m + 1) D q := by
    rw [T.eq_2 A D q m]
  have hq : (∑ p ∈ (if Tcond (m + 1) D q then {q} else ∅), A.nu p * T A m (D / p) p)
      = (if Tcond (m + 1) D q then A.nu q * T A m (D / q) q else 0) := by
    by_cases hc : Tcond (m + 1) D q
    · simp only [if_pos hc, Finset.sum_singleton]
    · simp only [if_neg hc, Finset.sum_empty]
  rw [T.eq_2 A D z m, hset, Finset.sum_union hdisj, hsmall, hq]

/-! ## Reindexing the layer sums -/

private lemma even_filter_image (N : ℕ) :
    (Finset.range N).filter (fun n : ℕ => Even n ∧ n ≠ 0)
      = ((Finset.range (N - 1)).filter (fun m : ℕ => Odd m)).image (fun m => m + 1) := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨hnN, hev, hne⟩
    obtain ⟨k, hk⟩ := hev
    have hk1 : 1 ≤ k := by omega
    refine ⟨n - 1, ⟨by omega, ⟨k - 1, by omega⟩⟩, by omega⟩
  · rintro ⟨m, ⟨hmN, hodd⟩, hm⟩
    obtain ⟨k, hk⟩ := hodd
    refine ⟨by omega, ⟨k + 1, by omega⟩, by omega⟩

private lemma odd_ne_one_filter_image (N : ℕ) :
    (Finset.range N).filter (fun n : ℕ => Odd n ∧ n ≠ 1)
      = ((Finset.range (N - 1)).filter (fun m : ℕ => Even m ∧ m ≠ 0)).image (fun m => m + 1) := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨hnN, hodd, hne⟩
    obtain ⟨k, hk⟩ := hodd
    refine ⟨n - 1, ⟨by omega, ⟨k, by omega⟩, by omega⟩, by omega⟩
  · rintro ⟨m, ⟨hmN, hev, hne0⟩, hm⟩
    obtain ⟨k, hk⟩ := hev
    refine ⟨by omega, ⟨k, by omega⟩, by omega⟩

private lemma erase_one_sum (N : ℕ) (f : ℕ → ℝ) :
    (∑ n ∈ ((Finset.range N).filter (fun n : ℕ => Odd n)).erase 1, f (n - 1))
      = ∑ m ∈ (Finset.range (N - 1)).filter (fun m : ℕ => Even m ∧ m ≠ 0), f m := by
  rw [← Finset.filter_ne', Finset.filter_filter, odd_ne_one_filter_image N, Finset.sum_image]
  · refine Finset.sum_congr rfl (fun m hm => ?_)
    simp
  · intro a _ b _ hab
    simpa using hab

/-- The even summand at level `z`, written at level `q`. -/
private lemma evSum_step (A : BoundingSieve) {z : ℝ} {q : ℕ}
    (hqPS : q ∈ A.prodPrimes.primeFactors) (hqz : (q : ℝ) < z)
    (hmax : ∀ p ∈ A.prodPrimes.primeFactors, (p : ℝ) < z → p ≤ q)
    (D : ℝ) :
    ∀ n : ℕ, Even n → n ≠ 0 →
      T A n D z = T A n D q + A.nu q * T A (n - 1) (D / q) q := by
  intro n hev hne
  have hn1 : n = (n - 1) + 1 := by omega
  have hcond : Tcond ((n - 1) + 1) D q := by
    rw [← hn1]
    exact Tcond_of_even hev
  conv_lhs => rw [hn1]
  rw [T_peel A hqPS hqz hmax (n - 1) D, if_pos hcond, ← hn1]

private lemma evSum_peel (A : BoundingSieve) {z : ℝ} {q : ℕ}
    (hqPS : q ∈ A.prodPrimes.primeFactors) (hqz : (q : ℝ) < z)
    (hmax : ∀ p ∈ A.prodPrimes.primeFactors, (p : ℝ) < z → p ≤ q)
    (D : ℝ) (N : ℕ) :
    evSum A D z N = evSum A D q N + A.nu q * odSum A (D / q) q (N - 1) := by
  have hstep : ∀ n ∈ (Finset.range N).filter (fun n : ℕ => Even n ∧ n ≠ 0),
      T A n D z = T A n D q + A.nu q * T A (n - 1) (D / q) q := by
    intro n hn
    obtain ⟨hnN, hev, hne⟩ := Finset.mem_filter.mp hn
    exact evSum_step A hqPS hqz hmax D n hev hne
  have hre : (∑ n ∈ (Finset.range N).filter (fun n : ℕ => Even n ∧ n ≠ 0),
        T A (n - 1) (D / q) q)
      = ∑ m ∈ (Finset.range (N - 1)).filter (fun m : ℕ => Odd m), T A m (D / q) q := by
    rw [even_filter_image N, Finset.sum_image]
    · refine Finset.sum_congr rfl (fun m hm => ?_)
      simp
    · intro a _ b _ hab
      simpa using hab
  have hL : (∑ n ∈ (Finset.range N).filter (fun n : ℕ => Even n ∧ n ≠ 0), T A n D z)
      = (∑ n ∈ (Finset.range N).filter (fun n : ℕ => Even n ∧ n ≠ 0), T A n D q)
        + A.nu q * (∑ n ∈ (Finset.range N).filter (fun n : ℕ => Even n ∧ n ≠ 0),
            T A (n - 1) (D / q) q) := by
    rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hgoal : (∑ n ∈ (Finset.range N).filter (fun n : ℕ => Even n ∧ n ≠ 0), T A n D z)
      = (∑ n ∈ (Finset.range N).filter (fun n : ℕ => Even n ∧ n ≠ 0), T A n D q)
        + A.nu q * (∑ m ∈ (Finset.range (N - 1)).filter (fun m : ℕ => Odd m),
            T A m (D / q) q) := by
    rw [hL, hre]
  unfold evSum odSum
  exact hgoal

/-- The odd summand at level `z`, written at level `q`. -/
private lemma odSum_step (A : BoundingSieve) {z : ℝ} {q : ℕ}
    (hqPS : q ∈ A.prodPrimes.primeFactors) (hqz : (q : ℝ) < z)
    (hmax : ∀ p ∈ A.prodPrimes.primeFactors, (p : ℝ) < z → p ≤ q)
    (D : ℝ) :
    ∀ n : ℕ, Odd n →
      T A n D z
        = T A n D q + (if Tcond n D q then A.nu q * T A (n - 1) (D / q) q else 0) := by
  intro n hodd
  obtain ⟨k, hk⟩ := hodd
  have hn1 : n = (n - 1) + 1 := by omega
  conv_lhs => rw [hn1]
  rw [T_peel A hqPS hqz hmax (n - 1) D, ← hn1]

private lemma odSum_peel (A : BoundingSieve) {z : ℝ} {q : ℕ}
    (hqPS : q ∈ A.prodPrimes.primeFactors) (hqz : (q : ℝ) < z)
    (hmax : ∀ p ∈ A.prodPrimes.primeFactors, (p : ℝ) < z → p ≤ q)
    (D : ℝ) (N : ℕ) (hN : 2 ≤ N) :
    odSum A D z N = odSum A D q N
      + A.nu q * (if D < (q : ℝ) ^ 3 then VfR A q else 0)
      + A.nu q * (if (q : ℝ) ^ 3 ≤ D then evSum A (D / q) q (N - 1) else 0) := by
  set F := (Finset.range N).filter (fun k : ℕ => Odd k) with hF
  have h1F : 1 ∈ F := by
    rw [hF, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, ⟨0, by norm_num⟩⟩
  have hstep : ∀ n ∈ F, T A n D z
      = T A n D q + (if Tcond n D q then A.nu q * T A (n - 1) (D / q) q else 0) := by
    intro n hn
    rw [hF, Finset.mem_filter] at hn
    obtain ⟨hnN, hodd⟩ := hn
    exact odSum_step A hqPS hqz hmax D n hodd
  have hIF : (∑ n ∈ F, (if Tcond n D q then A.nu q * T A (n - 1) (D / q) q else 0))
      = (if Tcond 1 D q then A.nu q * T A (1 - 1) (D / q) q else 0)
        + (∑ n ∈ F.erase 1,
            (if Tcond n D q then A.nu q * T A (n - 1) (D / q) q else 0)) := by
    conv_lhs => rw [← Finset.insert_erase h1F]
    rw [Finset.sum_insert (Finset.notMem_erase 1 F)]
  have hterm1 : (if Tcond 1 D q then A.nu q * T A (1 - 1) (D / q) q else 0)
      = A.nu q * (if D < (q : ℝ) ^ 3 then VfR A q else 0) := by
    rw [Tcond_one]
    by_cases hc : D < (q : ℝ) ^ 3
    · simp only [if_pos hc]
      rfl
    · rw [if_neg hc, if_neg hc]
      ring
  have hpoint : ∀ n ∈ F.erase 1,
      (if Tcond n D q then A.nu q * T A (n - 1) (D / q) q else 0)
        = (if (q : ℝ) ^ 3 ≤ D then A.nu q * T A (n - 1) (D / q) q else 0) := by
    intro n hn
    rw [Finset.mem_erase] at hn
    obtain ⟨hn1, hnF⟩ := hn
    rw [hF, Finset.mem_filter] at hnF
    obtain ⟨hnN, hodd⟩ := hnF
    rw [Tcond_of_odd hodd hn1]
  have hrest : (∑ n ∈ F.erase 1,
        (if Tcond n D q then A.nu q * T A (n - 1) (D / q) q else 0))
      = A.nu q * (if (q : ℝ) ^ 3 ≤ D then evSum A (D / q) q (N - 1) else 0) := by
    rw [Finset.sum_congr rfl hpoint]
    by_cases hc : (q : ℝ) ^ 3 ≤ D
    · rw [if_pos hc]
      simp only [if_pos hc]
      rw [hF, erase_one_sum N (fun k => A.nu q * T A k (D / q) q)]
      rw [evSum, Finset.mul_sum]
    · rw [if_neg hc]
      simp only [if_neg hc, mul_zero]
      exact Finset.sum_eq_zero (fun n hn => rfl)
  have hsum : (∑ n ∈ F, T A n D z)
      = (∑ n ∈ F, T A n D q)
        + (∑ n ∈ F, (if Tcond n D q then A.nu q * T A (n - 1) (D / q) q else 0)) := by
    rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib]
  rw [odSum, odSum, ← hF, hsum, hIF, hterm1, hrest]
  ring

/-! ## Two elementary power estimates -/

private lemma two_pow_pred_gt {D : ℝ} {N q : ℕ} (hN : 4 ≤ N) (h2 : (2 : ℝ) ^ N > D)
    (hq : 2 ≤ q) (hD : 0 < D) : D / q < (2 : ℝ) ^ (N - 1) := by
  have hqr : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hle : D / (q : ℝ) ≤ D / 2 := div_le_div_of_nonneg_left (le_of_lt hD) (by norm_num) hqr
  have hpow : (2 : ℝ) ^ N = 2 * (2 : ℝ) ^ (N - 1) := by
    conv_lhs => rw [show N = (N - 1) + 1 by omega]
    rw [pow_succ]
    ring
  have hhalf : D / 2 < (2 : ℝ) ^ (N - 1) := by
    rw [hpow] at h2
    linarith
  linarith

private lemma two_pow_max_pred_gt {D : ℝ} {N q : ℕ} (hN : 3 ≤ N) (h2 : (2 : ℝ) ^ N > D)
    (hq : 2 ≤ q) (hD : 0 < D) : D / q < (2 : ℝ) ^ (max (N - 1) 3) := by
  rcases eq_or_lt_of_le hN with h | h
  · have hmax : max (N - 1) 3 = 3 := by omega
    rw [hmax]
    have hDlt : D < 8 := by
      have h2' := h2
      rw [← h] at h2'
      norm_num at h2'
      exact h2'
    have hqr : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have hle : D / (q : ℝ) ≤ D / 2 := div_le_div_of_nonneg_left (le_of_lt hD) (by norm_num) hqr
    norm_num
    linarith
  · have hmax : max (N - 1) 3 = N - 1 := by omega
    rw [hmax]
    exact two_pow_pred_gt (by omega) h2 hq hD

/-! ## The simultaneous induction -/

private lemma main_ind (A : BoundingSieve) : ∀ n : ℕ, ∀ z : ℝ,
    (A.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z)).card = n →
    (∀ D : ℝ, ∀ N : ℕ, 3 ≤ N → (2 : ℝ) ^ N > D → 0 < D →
        Gm A z D = VfR A z - evSum A D z N) ∧
    (∀ D : ℝ, ∀ N : ℕ, 2 ≤ N → (2 : ℝ) ^ (max N 3) > D → 0 < D →
        Gp A z D = VfR A z + odSum A D z N) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro z hcard
    by_cases hne : (A.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z)).Nonempty
    · obtain ⟨q, hqmax⟩ : ∃ q : ℕ,
          q = (A.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z)).max' hne := ⟨_, rfl⟩
      have hqS : q ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z) := by
        rw [hqmax]
        exact Finset.max'_mem _ hne
      have hqPS : q ∈ A.prodPrimes.primeFactors := (Finset.mem_filter.mp hqS).1
      have hqz : (q : ℝ) < z := (Finset.mem_filter.mp hqS).2
      have hqprime : q.Prime := (Nat.mem_primeFactors.mp hqPS).1
      have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqprime.pos
      have hmax : ∀ p ∈ A.prodPrimes.primeFactors, (p : ℝ) < z → p ≤ q := by
        intro p hp hpz
        have hpmem : p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z) :=
          Finset.mem_filter.mpr ⟨hp, hpz⟩
        have hle := Finset.le_max' _ p hpmem
        rwa [← hqmax] at hle
      have hqnotmem : q ∉ A.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < q) := by
        simp only [Finset.mem_filter, not_and]
        intro _
        exact not_lt.mpr (le_refl (q : ℝ))
      have hqcard : (A.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < q)).card
          = n - 1 := by
        have hset : A.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < q)
            = (A.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z)).erase q := by
          rw [filter_lt_max A hqPS hqz hmax, Finset.erase_insert hqnotmem]
        rw [hset, Finset.card_erase_of_mem hqS, hcard]
      have hnpos : 0 < n := by
        rw [← hcard]
        exact Finset.card_pos.mpr hne
      have ihq := ih _ (by omega) q rfl
      refine ⟨fun D N hN3 h2 hDpos => ?_, fun D N hN2 h2 hDpos => ?_⟩
      · have hsplit := Gm_peel A hqPS hqz hmax (D := D)
        have hA := ihq.1 D N hN3 h2 hDpos
        have hB := ihq.2 (D / q) (N - 1) (by omega)
          (two_pow_max_pred_gt hN3 h2 hqprime.two_le hDpos) (div_pos hDpos hqpos)
        have hev := evSum_peel A hqPS hqz hmax D N
        have hV := VfR_peel A hqPS hqz hmax
        rw [hsplit, hA, hB, hV, hev]
        ring
      · have hsplit := Gp_peel A hqPS hqz hmax (D := D)
        have hB := ihq.2 D N hN2 h2 hDpos
        have hodd := odSum_peel A hqPS hqz hmax D N hN2
        have hV := VfR_peel A hqPS hqz hmax
        by_cases hc : (q : ℝ) ^ 3 ≤ D
        · have hN4 : 4 ≤ N := by
            by_contra hcon
            have h3 : N ≤ 3 := by omega
            have h8 : (2 : ℝ) ^ N ≤ 8 := by
              have h4 : (2 : ℝ) ^ N ≤ (2 : ℝ) ^ 3 := pow_le_pow_right₀ (by norm_num) h3
              have h5 : (2 : ℝ) ^ 3 = 8 := by norm_num
              rwa [h5] at h4
            have hq8 : (8 : ℝ) ≤ (q : ℝ) ^ 3 := by
              have h2q : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqprime.two_le
              have h3' : (2 : ℝ) ^ 3 ≤ (q : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) h2q 3
              norm_num at h3'
              exact h3'
            have h2three : (2 : ℝ) ^ (max N 3) = 8 := by
              rw [max_eq_right (by omega : N ≤ 3)]
              norm_num
            linarith
          have h2N : (2 : ℝ) ^ N > D := by
            have h2' := h2
            rw [max_eq_left (by omega : 3 ≤ N)] at h2'
            exact h2'
          have hA := ihq.1 (D / q) (N - 1) (by omega)
            (two_pow_pred_gt hN4 h2N hqprime.two_le hDpos) (div_pos hDpos hqpos)
          rw [hsplit, hB, hA, hV, hodd]
          simp only [if_pos hc, if_neg (not_lt.mpr hc), mul_zero, add_zero]
          ring
        · have hc' : D < (q : ℝ) ^ 3 := not_le.mp hc
          rw [hsplit, hB, hV, hodd]
          simp only [if_neg hc, if_pos hc', mul_zero, add_zero]
          ring
    · have hempty : A.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z) = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hne
      have hPz : Pz A z = 1 := by
        rw [Pz, hempty, Finset.prod_empty]
      have hVf : VfR A z = 1 := by
        rw [VfR, hempty, Finset.prod_empty]
      have hT0 : ∀ (D : ℝ) (n : ℕ), 0 < n → T A n D z = 0 := by
        intro D n hn
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
        rw [T.eq_2 A D z k]
        refine Finset.sum_eq_zero (fun p hp => ?_)
        obtain ⟨hpmem, hpz, -⟩ := Finset.mem_filter.mp hp
        have hmem : p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z) :=
          Finset.mem_filter.mpr ⟨hpmem, hpz⟩
        rw [hempty] at hmem
        exact absurd hmem (Finset.notMem_empty p)
      have hrdM : ∀ (D : ℝ), rdMinus D 1 := by
        intro D e he _ he1
        exact absurd (Nat.dvd_one.mp (Nat.mem_divisors.mp he).1) he1
      have hrdP : ∀ (D : ℝ), rdPlus D 1 := by
        intro D e he hodd
        have he1 : e = 1 := Nat.dvd_one.mp (Nat.mem_divisors.mp he).1
        rw [he1] at hodd
        simp at hodd
      refine ⟨fun D N _ _ _ => ?_, fun D N _ _ _ => ?_⟩
      · have hGm : Gm A z D = 1 := by
          rw [Gm, hPz, Nat.divisors_one, Finset.sum_singleton,
            if_pos (hrdM D), ArithmeticFunction.moebius_apply_one, A.nu_mult.map_one]
          norm_num
        have hev0 : evSum A D z N = 0 := by
          rw [evSum]
          refine Finset.sum_eq_zero (fun n hn => ?_)
          obtain ⟨hnr, hev, hne'⟩ := Finset.mem_filter.mp hn
          exact hT0 D n (Nat.pos_of_ne_zero hne')
        rw [hGm, hVf, hev0]
        ring
      · have hGp : Gp A z D = 1 := by
          rw [Gp, hPz, Nat.divisors_one, Finset.sum_singleton,
            if_pos (hrdP D), ArithmeticFunction.moebius_apply_one, A.nu_mult.map_one]
          norm_num
        have hod0 : odSum A D z N = 0 := by
          rw [odSum]
          refine Finset.sum_eq_zero (fun n hn => ?_)
          obtain ⟨hnr, hodd⟩ := Finset.mem_filter.mp hn
          obtain ⟨k, hk⟩ := hodd
          exact hT0 D n (by omega)
        rw [hGp, hVf, hod0]
        ring

theorem identity_minus (A : BoundingSieve) {D z : ℝ} (hD : 1 ≤ D) :
    ∑ d ∈ (Pz A z).divisors, lamMinus A.prodPrimes D d * A.nu d
      = VfR A z
        - ∑ n ∈ (Finset.range (Nat.log 2 ⌈D⌉₊ + 3)).filter (fun n : ℕ => Even n ∧ n ≠ 0),
            T A n D z := by
  have hDpos : 0 < D := by linarith
  have hN3 : 3 ≤ Nat.log 2 ⌈D⌉₊ + 3 := by omega
  have h2 : (2 : ℝ) ^ (Nat.log 2 ⌈D⌉₊ + 3) > D := by
    have hlt : ⌈D⌉₊ < 2 ^ (Nat.log 2 ⌈D⌉₊ + 1) := by
      simpa using Nat.lt_pow_succ_log_self (b := 2) (by norm_num) ⌈D⌉₊
    have hcast : (⌈D⌉₊ : ℝ) < (2 : ℝ) ^ (Nat.log 2 ⌈D⌉₊ + 1) := by exact_mod_cast hlt
    have hle : D ≤ (⌈D⌉₊ : ℝ) := Nat.le_ceil D
    have hpow : (2 : ℝ) ^ (Nat.log 2 ⌈D⌉₊ + 3)
        = 4 * (2 : ℝ) ^ (Nat.log 2 ⌈D⌉₊ + 1) := by
      rw [show Nat.log 2 ⌈D⌉₊ + 3 = (Nat.log 2 ⌈D⌉₊ + 1) + 2 by omega, pow_add]
      ring
    rw [hpow]
    linarith
  obtain ⟨hA, -⟩ := main_ind A _ z rfl
  rw [← Gm_eq_sum]
  exact hA D _ hN3 h2 hDpos

end

end Work.ChenPlan.LinearSieve.RI
