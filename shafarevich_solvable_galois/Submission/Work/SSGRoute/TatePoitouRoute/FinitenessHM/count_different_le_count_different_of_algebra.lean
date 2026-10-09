import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The exponent of a prime in the different grows along a field extension

For number fields `K ⊆ N` and primes `Q | P` (i.e. `Q.LiesOver P`), the exponent of `P` in the
different `𝔡_{K/ℤ}` is at most the exponent of `Q` in the different `𝔡_{N/ℤ}`.

The proof is the transitivity of the different ideal
(`differentIdeal_eq_differentIdeal_mul_differentIdeal`, `𝔡_{N/ℤ} = 𝔡_{N/K} · 𝔡_{K/ℤ}·𝒪_N`)
combined with the two elementary ideal-factoring facts proved below:
`𝔡_{N/ℤ} ≤ 𝔡_{K/ℤ}·𝒪_N`, and the exponent only grows when passing from an ideal `P^n ∣ 𝔡_{K/ℤ}`
to its extension `Q^n ∣ (P·𝒪_N)^n`, using `Q ≥ P·𝒪_N` (which is exactly `Q.LiesOver P`).
-/

open scoped NumberField

namespace Work.SSGRoute.TatePoitouRoute.FinitenessHM

open UniqueFactorizationMonoid

/-- In a Dedekind domain, `P ^ v_P(I) ∣ I` for a nonzero prime `P` and `I ≠ 0`, where `v_P`
is the exponent of `P` in the factorization of `I`. -/
lemma pow_count_dvd {T : Type*} [CommRing T] [IsDedekindDomain T]
    {P I : Ideal T} (hP : P.IsPrime) (hP0 : P ≠ ⊥) (hI : I ≠ ⊥) :
    P ^ (normalizedFactors I).count P ∣ I := by
  rw [dvd_iff_normalizedFactors_le_normalizedFactors (pow_ne_zero _ hP0) hI]
  rw [normalizedFactors_pow,
    normalizedFactors_irreducible (Ideal.prime_of_isPrime hP0 hP).irreducible,
    normalize_eq, Multiset.nsmul_singleton]
  exact Multiset.le_count_iff_replicate_le.mp le_rfl

/-- In a Dedekind domain, `Q ^ n ∣ I` for a nonzero prime `Q` and `I ≠ 0` implies
`n ≤ v_Q(I)`. -/
lemma le_count_of_pow_dvd {T : Type*} [CommRing T] [IsDedekindDomain T]
    {Q I : Ideal T} (hQ : Q.IsPrime) (hQ0 : Q ≠ ⊥) (hI : I ≠ ⊥) {n : ℕ}
    (h : Q ^ n ∣ I) : n ≤ (normalizedFactors I).count Q := by
  have hle : I ≤ Q ^ n := Ideal.dvd_iff_le.mp h
  have h1 := Ideal.count_le_of_ideal_ge (I := I) (J := Q ^ n) hle hI Q
  have h2 : (normalizedFactors (Q ^ n)).count Q = n := by
    refine Ideal.count_normalizedFactors_eq (p := Q) (x := Q ^ n) le_rfl ?_
    exact not_le_of_gt ((Ideal.pow_right_strictAnti Q hQ0 hQ.ne_top) (Nat.lt_succ_self n))
  rwa [h2] at h1

theorem count_different_le_count_different_of_algebra
    {K N : Type*} [Field K] [NumberField K] [Field N] [NumberField N] [Algebra K N]
    (P : Ideal (NumberField.RingOfIntegers K)) (Q : Ideal (NumberField.RingOfIntegers N))
    (hP : P.IsPrime) (hQ : Q.IsPrime) (hPQ : Q.LiesOver P) :
    (UniqueFactorizationMonoid.normalizedFactors
        (differentIdeal ℤ (NumberField.RingOfIntegers K))).count P ≤
      (UniqueFactorizationMonoid.normalizedFactors
        (differentIdeal ℤ (NumberField.RingOfIntegers N))).count Q := by
  by_cases hPbot : P = ⊥
  · subst hPbot
    have hzero : Multiset.count (⊥ : Ideal (𝓞 K))
        (normalizedFactors (differentIdeal ℤ (𝓞 K))) = 0 :=
      Multiset.count_eq_zero_of_notMem (zero_notMem_normalizedFactors _)
    rw [hzero]
    exact Nat.zero_le _
  · have hdK0 : differentIdeal ℤ (𝓞 K) ≠ ⊥ := differentIdeal_ne_bot
    have hdN0 : differentIdeal ℤ (𝓞 N) ≠ ⊥ := differentIdeal_ne_bot
    have hQ0 : Q ≠ ⊥ := by
      rintro rfl
      exact hPbot (by
        rw [hPQ.over, Ideal.under_def]
        exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 N)))
    have hpow : P ^ (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P ∣
        differentIdeal ℤ (𝓞 K) := pow_count_dvd hP hPbot hdK0
    have hmap : (differentIdeal ℤ (𝓞 K)).map (algebraMap (𝓞 K) (𝓞 N)) ≤
        (P.map (algebraMap (𝓞 K) (𝓞 N))) ^
          (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P := by
      rw [← Ideal.map_pow]
      exact Ideal.map_mono (Ideal.dvd_iff_le.mp hpow)
    have htrans := differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 K) (𝓞 N)
    have hle1 : differentIdeal ℤ (𝓞 N) ≤
        (differentIdeal ℤ (𝓞 K)).map (algebraMap (𝓞 K) (𝓞 N)) := by
      rw [htrans]
      exact Ideal.mul_le_right
    have hPQmap : P.map (algebraMap (𝓞 K) (𝓞 N)) ≤ Q := by
      rw [Ideal.map_le_iff_le_comap, ← Ideal.under_def, ← hPQ.over]
    have hpow2 : Q ^ (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P ∣
        differentIdeal ℤ (𝓞 N) := by
      rw [Ideal.dvd_iff_le]
      refine le_trans hle1 (le_trans hmap ?_)
      exact Ideal.dvd_iff_le.mp (pow_dvd_pow_of_dvd (Ideal.dvd_iff_le.mpr hPQmap) _)
    exact le_count_of_pow_dvd hQ hQ0 hdN0 hpow2

end Work.SSGRoute.TatePoitouRoute.FinitenessHM
