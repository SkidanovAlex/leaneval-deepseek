import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_one_lower_bound_quadratic
import Submission.Commons.RingTheory.DedekindDomain.pow_dvd_iff_normalizedFactors_count_le
import Submission.Commons.NumberTheory.EulerProduct.tsum_card_expVec_mul_pow

namespace Commons.NumberTheory.NumberField

open Ideal


namespace TsumPrimePow

variable {K : Type*} [Field K] [NumberField K]

/-- The set of primes of `𝓞 K` lying over the rational prime `p`. -/
noncomputable abbrev Sset (p : ℕ) : Finset (Ideal (NumberField.RingOfIntegers K)) :=
  Commons.NumberTheory.DirichletCharacter.primesOverF (K := K) p

/-- The primes over `p`, as a type. -/
noncomputable abbrev Ty (p : ℕ) := {P : Ideal (NumberField.RingOfIntegers K) // P ∈ Sset (K := K) p}

lemma primesOver_mem (p : ℕ) [Fact p.Prime] (i : Ty (K := K) p) :
    i.1.IsPrime ∧ i.1.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  have hpne : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ :=
    (Ideal.span_singleton_eq_bot).not.mpr hp0
  haveI hmax : (Ideal.span {(p : ℤ)} : Ideal ℤ).IsMaximal :=
    ((Ideal.span_singleton_prime hp0).mpr (Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime p))).isMaximal hpne
  have h := (IsDedekindDomain.mem_primesOverFinset_iff (B := NumberField.RingOfIntegers K) hpne).mp i.2
  exact ⟨h.1, h.2⟩

lemma inertiaDeg_pos_of_mem (p : ℕ) [Fact p.Prime] (i : Ty (K := K) p) :
    0 < i.1.inertiaDeg ℤ := by
  haveI : i.1.IsPrime := (primesOver_mem (K := K) p i).1
  exact Ideal.inertiaDeg_pos i.1 ℤ

/-- The absolute norm of `∏ i, i.1 ^ c i` is `p ^ ∑ i, c i * (inertia degree)`. -/
lemma absNorm_prod_prime_pow (p : ℕ) [Fact p.Prime] (c : Ty (K := K) p → ℕ) :
    Ideal.absNorm (∏ i : Ty (K := K) p, i.1 ^ c i) =
      p ^ (∑ i : Ty (K := K) p, c i * i.1.inertiaDeg ℤ) := by
  have hnorm : ∀ i : Ty (K := K) p,
      Ideal.absNorm (i.1 : Ideal (NumberField.RingOfIntegers K)) = p ^ (i.1.inertiaDeg ℤ) := by
    intro i
    have h := primesOver_mem (K := K) p i
    haveI : i.1.IsPrime := h.1
    haveI : i.1.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := h.2
    exact (Ideal.pow_inertiaDeg p i.1).symm
  rw [Commons.NumberTheory.DirichletCharacter.absNorm_finset_prod]
  rw [show (∏ i ∈ Finset.univ, Ideal.absNorm (i.1 ^ c i)) =
      ∏ i ∈ Finset.univ, (p ^ (i.1.inertiaDeg ℤ)) ^ c i by
    apply Finset.prod_congr rfl; intro i _
    rw [Commons.NumberTheory.DirichletCharacter.absNorm_pow, hnorm i]]
  rw [show (∏ i ∈ Finset.univ, (p ^ (i.1.inertiaDeg ℤ)) ^ c i) =
      ∏ i ∈ Finset.univ, p ^ (i.1.inertiaDeg ℤ * c i) by
    apply Finset.prod_congr rfl; intro i _; rw [← pow_mul]]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  apply Finset.sum_congr rfl; intro i _; ring

/-- For a nonzero ideal `I` with `absNorm I = p ^ k`, the inertia-degree weighted sum of the
exponents of the primes over `p` equals `k`. -/
lemma sum_count_inertiaDeg_eq (p : ℕ) [Fact p.Prime] {k : ℕ}
    (I : Ideal (NumberField.RingOfIntegers K)) (hI0 : Ideal.absNorm I = p ^ k) :
    (∑ i : Ty (K := K) p, (UniqueFactorizationMonoid.normalizedFactors I).count i.1
        * i.1.inertiaDeg ℤ) = k := by
  have hpne : p ≠ 0 := (Fact.out : Nat.Prime p).ne_zero
  have hI : I ≠ ⊥ := by
    intro h
    rw [h, Ideal.absNorm_bot] at hI0
    exact (pow_ne_zero k hpne) hI0.symm
  have h := Commons.NumberTheory.DirichletCharacter.sum_count_mul_inertiaDeg_eq
    (K := K) (p := p) hI hI0
  rw [← h, Finset.univ_eq_attach]
  exact Finset.sum_attach (Sset (K := K) p)
    (fun P => (UniqueFactorizationMonoid.normalizedFactors I).count P * P.inertiaDeg ℤ)

/-- A nonzero ideal is the product of the primes over `p` raised to the exponents of its
normalized factors, expressed over the subtype of primes over `p`. -/
lemma prod_prime_pow_count_eq_self (p : ℕ) [Fact p.Prime] {k : ℕ}
    (I : Ideal (NumberField.RingOfIntegers K)) (hI0 : Ideal.absNorm I = p ^ k) (hI : I ≠ ⊥) :
    (∏ i : Ty (K := K) p, i.1 ^ (UniqueFactorizationMonoid.normalizedFactors I).count i.1) = I := by
  conv_rhs => rw [Commons.NumberTheory.DirichletCharacter.eq_prod_primesOverFinset (K := K) hI hI0]
  exact Finset.prod_attach (Sset (K := K) p)
    (fun P => P ^ (UniqueFactorizationMonoid.normalizedFactors I).count P)

/-- Bijection, for each `k`, between ideals of `𝓞 K` of absolute norm `p ^ k` and vectors of
exponents `c` on the primes over `p` with `∑ i, c i * (inertia degree) = k`. -/
noncomputable def ideals_absNorm_prime_pow_equiv (p : ℕ) [Fact p.Prime] (k : ℕ) :
    {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = p ^ k} ≃
      {c : Ty (K := K) p → ℕ // ∑ i : Ty (K := K) p, c i * i.1.inertiaDeg ℤ = k} where
  toFun I := ⟨fun i => (UniqueFactorizationMonoid.normalizedFactors I.1).count i.1,
    sum_count_inertiaDeg_eq p I.1 I.2⟩
  invFun c := ⟨∏ i : Ty (K := K) p, i.1 ^ c.1 i,
    by rw [absNorm_prod_prime_pow (K := K) p c.1, c.2]⟩
  left_inv I := by
    apply Subtype.ext
    have hpne : p ≠ 0 := (Fact.out : Nat.Prime p).ne_zero
    have hI : I.1 ≠ ⊥ := by
      intro h
      have h2 : Ideal.absNorm (⊥ : Ideal (NumberField.RingOfIntegers K)) = p ^ k := by
        rw [← h]; exact I.2
      rw [Ideal.absNorm_bot] at h2
      exact (pow_ne_zero k hpne) h2.symm
    change (∏ i : Ty (K := K) p,
      i.1 ^ (UniqueFactorizationMonoid.normalizedFactors I.1).count i.1) = I.1
    exact prod_prime_pow_count_eq_self p I.1 I.2 hI
  right_inv c := by
    apply Subtype.ext
    funext i
    have hpne : p ≠ 0 := (Fact.out : Nat.Prime p).ne_zero
    set Ip : Ideal (NumberField.RingOfIntegers K) := ∏ j : Ty (K := K) p, j.1 ^ c.1 j with hIp
    have habs : Ideal.absNorm Ip = p ^ k := by rw [hIp, absNorm_prod_prime_pow (K := K) p c.1, c.2]
    have hI : Ip ≠ ⊥ := by
      intro h
      rw [h, Ideal.absNorm_bot] at habs
      exact (pow_ne_zero k hpne) habs.symm
    have hle : ∀ j : Ty (K := K) p,
        c.1 j ≤ (UniqueFactorizationMonoid.normalizedFactors Ip).count j.1 := by
      intro j
      have hdvd : j.1 ^ c.1 j ∣ Ip := by
        rw [hIp]
        exact Finset.dvd_prod_of_mem (fun k : Ty (K := K) p => k.1 ^ c.1 k) (Finset.mem_univ j)
      exact (Commons.RingTheory.DedekindDomain.pow_dvd_iff_normalizedFactors_count_le
        j.1 Ip hI (c.1 j)).mp hdvd
    have hsum2 : (∑ j : Ty (K := K) p,
        (UniqueFactorizationMonoid.normalizedFactors Ip).count j.1 * j.1.inertiaDeg ℤ) = k :=
      sum_count_inertiaDeg_eq p Ip habs
    have heq : (∑ j : Ty (K := K) p, c.1 j * j.1.inertiaDeg ℤ) =
        (∑ j : Ty (K := K) p,
          (UniqueFactorizationMonoid.normalizedFactors Ip).count j.1 * j.1.inertiaDeg ℤ) := by
      rw [c.2, hsum2]
    have hle' : ∀ j ∈ Finset.univ, c.1 j * j.1.inertiaDeg ℤ ≤
        (UniqueFactorizationMonoid.normalizedFactors Ip).count j.1 * j.1.inertiaDeg ℤ :=
      fun j _ => Nat.mul_le_mul_right _ (hle j)
    have hterm := (Finset.sum_eq_sum_iff_of_le hle').mp heq
    have hwpos : 0 < i.1.inertiaDeg ℤ := inertiaDeg_pos_of_mem (K := K) p i
    have hi := hterm i (Finset.mem_univ i)
    exact (Nat.mul_right_cancel hwpos hi).symm

end TsumPrimePow

open TsumPrimePow in
theorem tsum_prime_pow_card_mul_pow {K : Type*} [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]
    {X : ℝ} (hX0 : 0 ≤ X) (hX1 : X < 1) :
    ∑' k : ℕ, (Nat.card {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = p ^ k} : ℝ) * X ^ k =
      ∏ P ∈ IsDedekindDomain.primesOverFinset (Ideal.span ({(p : ℤ)} : Set ℤ)) (NumberField.RingOfIntegers K),
        (1 - X ^ (P.inertiaDeg ℤ))⁻¹ := by
  have hw : ∀ i : Ty (K := K) p, 0 < i.1.inertiaDeg ℤ := inertiaDeg_pos_of_mem (K := K) p
  have hcomb := Commons.NumberTheory.EulerProduct.tsum_card_expVec_mul_pow (fun i : Ty (K := K) p => i.1.inertiaDeg ℤ) hw hX0 hX1
  calc ∑' k : ℕ, (Nat.card {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = p ^ k} : ℝ) * X ^ k
      = ∑' k : ℕ, (Nat.card {c : Ty (K := K) p → ℕ //
          ∑ i : Ty (K := K) p, c i * i.1.inertiaDeg ℤ = k} : ℝ) * X ^ k := by
        apply tsum_congr; intro k
        rw [Nat.card_congr (ideals_absNorm_prime_pow_equiv (K := K) p k)]
    _ = ∏ i : Ty (K := K) p, (1 - X ^ (i.1.inertiaDeg ℤ))⁻¹ := hcomb
    _ = ∏ P ∈ IsDedekindDomain.primesOverFinset (Ideal.span ({(p : ℤ)} : Set ℤ)) (NumberField.RingOfIntegers K),
        (1 - X ^ (P.inertiaDeg ℤ))⁻¹ := by
        rw [Finset.univ_eq_attach]
        exact Finset.prod_attach (Sset (K := K) p)
          (fun P => (1 - X ^ (P.inertiaDeg ℤ))⁻¹)

end Commons.NumberTheory.NumberField
