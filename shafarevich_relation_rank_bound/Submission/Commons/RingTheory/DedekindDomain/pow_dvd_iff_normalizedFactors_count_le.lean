import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

open scoped NumberField
open UniqueFactorizationMonoid

namespace Commons.RingTheory.DedekindDomain

/-- In a number field's ring of integers, the power `P ^ k` of a prime ideal `P` divides
a nonzero ideal `I` iff `k` does not exceed the multiplicity of `P` in the factorization
of `I`. -/
theorem pow_dvd_iff_normalizedFactors_count_le
    {K : Type*} [Field K] [NumberField K]
    (P : Ideal (NumberField.RingOfIntegers K)) [P.IsPrime]
    (I : Ideal (NumberField.RingOfIntegers K)) (hI : I ≠ ⊥) (k : ℕ) :
    P ^ k ∣ I ↔ k ≤ (normalizedFactors I).count P := by
  classical
  by_cases hP0 : P = ⊥
  · subst P
    have hcount : (normalizedFactors I).count (⊥ : Ideal (NumberField.RingOfIntegers K)) = 0 := by
      rw [Multiset.count_eq_zero]
      exact zero_notMem_normalizedFactors I
    rw [hcount]
    by_cases hk : k = 0
    · subst k
      simp
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      constructor
      · intro hdvd
        exfalso
        have hz : (⊥ : Ideal (NumberField.RingOfIntegers K)) ^ k = ⊥ := zero_pow hk
        rw [hz] at hdvd
        rcases hdvd with ⟨J, hJ⟩
        exact hI (by simpa using hJ)
      · intro hk'
        exfalso
        omega
  · have hPprime : Prime P := Ideal.prime_of_isPrime hP0 ‹P.IsPrime›
    have hf : FiniteMultiplicity P I := by
      apply FiniteMultiplicity.of_prime_left hPprime
      simpa using hI
    have hPirr : Irreducible P := hPprime.irreducible
    calc
      P ^ k ∣ I ↔ k ≤ multiplicity P I := hf.pow_dvd_iff_le_multiplicity
      _ ↔ k ≤ (normalizedFactors I).count (normalize P) := by
        rw [UniqueFactorizationMonoid.multiplicity_eq_count_normalizedFactors hPirr (by simpa using hI)]
      _ ↔ k ≤ (normalizedFactors I).count P := by rw [normalize_eq]

end Commons.RingTheory.DedekindDomain