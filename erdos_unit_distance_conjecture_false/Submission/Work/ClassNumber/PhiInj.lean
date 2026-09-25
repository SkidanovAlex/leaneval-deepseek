import Mathlib
import Submission.Work.ClassNumber.SlotDefs

namespace Work.ClassNumber

open NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- If a rational prime `p` divides the absolute norm of a nonzero prime ideal `Q` of `𝓞 K`, then
`Q` lies over the prime ideal `span {(p : ℤ)}` of `ℤ`. -/
lemma under_eq_span_of_prime_dvd_absNorm {Q : Ideal (𝓞 K)}
    (hQ : Q.IsPrime) (hQ0 : Q ≠ ⊥) {p : ℕ} (hp : p.Prime) (hdvd : p ∣ Ideal.absNorm Q) :
    Ideal.under ℤ Q = Ideal.span {(p : ℤ)} := by
  have hQmax : Q.IsMaximal := hQ.isMaximal hQ0
  obtain ⟨P, hPmax, hPunder, hPdvd⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp Q hdvd
  rw [Ideal.dvd_iff_le] at hPdvd
  have heq : Q = P := hQmax.eq_of_le hPmax.ne_top hPdvd
  rw [heq, hPunder]

/-- `slotOf` of a nonzero prime ideal `Q` lying over `p₀` is the image of `Q` under `slotEmb`. -/
lemma slotOf_eq_slotEmb {p₀ : Ideal ℤ} [p₀.IsPrime] (h0 : p₀ ≠ ⊥)
    {Q : Ideal (𝓞 K)} (hQp : Q.IsPrime) (hQ0 : Q ≠ ⊥) (hQ : Q.LiesOver p₀) :
    slotOf K Q = slotEmb K p₀ h0 ⟨Q, hQp, hQ⟩ := by
  have hQo : p₀ = Q.under ℤ := hQ.over
  unfold slotOf
  rw [dif_pos ⟨hQp, hQ0⟩]
  subst hQo
  rfl

/-- Two nonzero prime ideals lying over the same prime of `ℤ` and carrying the same slot
coincide. -/
lemma slotOf_injective {p₀ : Ideal ℤ} [p₀.IsPrime] (h0 : p₀ ≠ ⊥)
    {A B : Ideal (𝓞 K)} (hAp : A.IsPrime) (hA0 : A ≠ ⊥) (hA : A.LiesOver p₀)
    (hBp : B.IsPrime) (hB0 : B ≠ ⊥) (hB : B.LiesOver p₀) (h : slotOf K A = slotOf K B) :
    A = B := by
  rw [slotOf_eq_slotEmb (K := K) h0 hAp hA0 hA,
    slotOf_eq_slotEmb (K := K) h0 hBp hB0 hB] at h
  exact congrArg Subtype.val ((slotEmb K p₀ h0).injective h)

/-- If `a` is a nonzero prime ideal and `Q ≠ a` a prime ideal in the same slot, then the rational
prime below `a` does not divide the norm of `Q`. -/
lemma not_dvd_absNorm_of_slotOf_eq {a Q : Ideal (𝓞 K)}
    (ha : a.IsPrime) (ha0 : a ≠ ⊥) (hQ : Q.IsPrime) (hQ0 : Q ≠ ⊥) (hne : Q ≠ a)
    (hslot : slotOf K Q = slotOf K a) {p : ℕ} (hp : p.Prime) (hpa : p ∣ Ideal.absNorm a) :
    ¬ p ∣ Ideal.absNorm Q := by
  intro hdvd
  have hua := under_eq_span_of_prime_dvd_absNorm (K := K) ha ha0 hp hpa
  have huQ := under_eq_span_of_prime_dvd_absNorm (K := K) hQ hQ0 hp hdvd
  have hQlies : Q.LiesOver (Ideal.under ℤ a) := by
    rw [← huQ.trans hua.symm]
    exact Ideal.over_under Q
  haveI : a.IsPrime := ha
  haveI : (Ideal.under ℤ a).IsPrime := Ideal.isPrime_of_liesOver a (Ideal.under ℤ a)
  exact hne (slotOf_injective (K := K) (p₀ := Ideal.under ℤ a)
    (Ideal.IsIntegral.under_ne_bot ℤ ha0) hQ hQ0 hQlies ha ha0 (Ideal.over_under a) hslot)

/-- The exponent of the rational prime `p` in `Phi K I` at the slot of a nonzero prime ideal `a`
with `absNorm a = p ^ f` equals `f` times the multiplicity of `a` in the factorization of `I`. -/
lemma factorization_Phi_slotOf (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    {a : Ideal (𝓞 K)} (ha : a.IsPrime) (ha0 : a ≠ ⊥)
    {p f : ℕ} (hp : p.Prime) (hf : 0 < f) (hnorm : Ideal.absNorm a = p ^ f) :
    (Phi K I (slotOf K a)).factorization p =
      f * (UniqueFactorizationMonoid.normalizedFactors I).count a := by
  classical
  have hpa : p ∣ Ideal.absNorm a := by rw [hnorm]; exact dvd_pow_self p hf.ne'
  have hS : ∀ Q ∈ (UniqueFactorizationMonoid.normalizedFactors I).toFinset,
      (if slotOf K Q = slotOf K a then
        (Ideal.absNorm Q) ^ ((UniqueFactorizationMonoid.normalizedFactors I).count Q)
        else 1) ≠ 0 := by
    intro Q hQ
    have hQ0 : Q ≠ ⊥ := by
      have h00 : Q ≠ 0 :=
        UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hQ)
      intro hb
      exact h00 (hb.trans Ideal.zero_eq_bot.symm)
    by_cases hsl : slotOf K Q = slotOf K a
    · rw [if_pos hsl]
      exact pow_ne_zero _ (fun hz => hQ0 (Ideal.absNorm_eq_zero_iff.mp hz))
    · rw [if_neg hsl]
      exact one_ne_zero
  have hterm_a : ((if slotOf K a = slotOf K a then
        (Ideal.absNorm a) ^ ((UniqueFactorizationMonoid.normalizedFactors I).count a)
        else 1)).factorization p =
      f * (UniqueFactorizationMonoid.normalizedFactors I).count a := by
    rw [if_pos rfl, hnorm, ← pow_mul, hp.factorization_pow, Finsupp.single_eq_same]
  have hterm_ne : ∀ Q ∈ (UniqueFactorizationMonoid.normalizedFactors I).toFinset, Q ≠ a →
      ((if slotOf K Q = slotOf K a then
        (Ideal.absNorm Q) ^ ((UniqueFactorizationMonoid.normalizedFactors I).count Q)
        else 1)).factorization p = 0 := by
    intro Q hQ hQa
    have hQ0 : Q ≠ ⊥ := by
      have h00 : Q ≠ 0 :=
        UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hQ)
      intro hb
      exact h00 (hb.trans Ideal.zero_eq_bot.symm)
    have hQp : Q.IsPrime := Ideal.isPrime_of_prime
      (UniqueFactorizationMonoid.prime_of_normalized_factor Q (Multiset.mem_toFinset.mp hQ))
    by_cases hsl : slotOf K Q = slotOf K a
    · rw [if_pos hsl, Nat.factorization_eq_zero_of_not_dvd]
      intro hdvd
      exact (not_dvd_absNorm_of_slotOf_eq (K := K) ha ha0 hQp hQ0 hQa hsl hp hpa)
        (hp.dvd_of_dvd_pow hdvd)
    · rw [if_neg hsl, Nat.factorization_one]
      simp
  simp only [Phi]
  rw [Nat.factorization_prod_apply hS]
  by_cases haIn : a ∈ (UniqueFactorizationMonoid.normalizedFactors I).toFinset
  · rw [Finset.sum_eq_single_of_mem a haIn (fun Q hQ hQa => hterm_ne Q hQ hQa)]
    exact hterm_a
  · rw [Finset.sum_eq_zero (fun Q hQ => hterm_ne Q hQ (fun hqa => haIn (hqa ▸ hQ)))]
    rw [Multiset.count_eq_zero.mpr (fun hm => haIn (Multiset.mem_toFinset.mpr hm)), mul_zero]

theorem PhiInj (K : Type*) [Field K] [NumberField K] (I I' : Ideal (NumberField.RingOfIntegers K))
    (hI : I ≠ ⊥) (hI' : I' ≠ ⊥) (h : Phi K I = Phi K I') : I = I' := by
  classical
  have hss : UniqueFactorizationMonoid.normalizedFactors I =
      UniqueFactorizationMonoid.normalizedFactors I' := by
    apply Multiset.ext'
    intro a
    by_cases ha : Irreducible a ∧ a ≠ ⊥
    · obtain ⟨hairr, ha0⟩ := ha
      have hap : Prime a := UniqueFactorizationMonoid.irreducible_iff_prime.mp hairr
      have haip : a.IsPrime := Ideal.isPrime_of_prime hap
      haveI : a.IsMaximal := haip.isMaximal ha0
      obtain ⟨p, f, hf, -, hp, hnorm⟩ := Ideal.exists_prime_and_absNorm_eq_pow a
      have k1 := factorization_Phi_slotOf (K := K) I hI haip ha0 hp hf hnorm
      have k2 := factorization_Phi_slotOf (K := K) I' hI' haip ha0 hp hf hnorm
      rw [h] at k1
      rw [k1] at k2
      exact Nat.mul_left_cancel hf k2
    · by_cases hairr : Irreducible a
      · have haeq : a = ⊥ := by
          by_contra hcontra
          exact ha ⟨hairr, hcontra⟩
        subst haeq
        have h1 : Multiset.count ⊥ (UniqueFactorizationMonoid.normalizedFactors I) = 0 := by
          apply Multiset.count_eq_zero.mpr
          intro hm
          exact UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors hm
            Ideal.zero_eq_bot.symm
        have h2 : Multiset.count ⊥ (UniqueFactorizationMonoid.normalizedFactors I') = 0 := by
          apply Multiset.count_eq_zero.mpr
          intro hm
          exact UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors hm
            Ideal.zero_eq_bot.symm
        rw [h1, h2]
      · have h1 : Multiset.count a (UniqueFactorizationMonoid.normalizedFactors I) = 0 := by
          apply Multiset.count_eq_zero.mpr
          intro hm
          exact hairr (UniqueFactorizationMonoid.irreducible_of_normalized_factor a hm)
        have h2 : Multiset.count a (UniqueFactorizationMonoid.normalizedFactors I') = 0 := by
          apply Multiset.count_eq_zero.mpr
          intro hm
          exact hairr (UniqueFactorizationMonoid.irreducible_of_normalized_factor a hm)
        rw [h1, h2]
  rw [← Ideal.prod_normalizedFactors_eq_self hI, ← Ideal.prod_normalizedFactors_eq_self hI', hss]

end Work.ClassNumber
