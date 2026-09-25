import Mathlib
import Submission.Commons.NumberTheory.NumberField.natAbs_discr_dvd_prod_pow_of_tame
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.Algebra.CharZero.Infinite

open scoped NumberField
open UniqueFactorizationMonoid

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.NumberField

/-- **Relative tame discriminant bound for the different ideal (divisibility form).**

Let `F ⊆ L` be an extension of number fields and `S` a finite set of rational primes such that

* every prime ideal `P` of `𝓞 L` dividing the relative different ideal `𝔡_{L/F}` lies over some
  `q ∈ S` (`hsup`), and
* for every `q ∈ S` and every maximal `P` over `(q)`, the `e_P`-th power of `P` does not divide
  `𝔡_{L/F}`, where `e_P` is the ramification index of `P` over `𝓞 F` (`hnot`; this is exactly
  tameness of `P` over `F`).

Then the absolute norm of the relative different ideal divides `(∏_{q ∈ S} q) ^ [L : ℚ]`. -/
theorem absNorm_differentIdeal_dvd_prod_pow_of_tame_support
    {F L : Type*} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
    [FiniteDimensional F L] (S : Finset ℕ) (hS : ∀ q ∈ S, Nat.Prime q)
    (hsup : ∀ (P : Ideal (NumberField.RingOfIntegers L)), P.IsPrime → P ≠ ⊥ →
      P ∣ differentIdeal (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers L) →
        ∃ q ∈ S, P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)))
    (hnot : ∀ q ∈ S, ∀ (P : Ideal (NumberField.RingOfIntegers L)), P.IsMaximal →
      P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) →
        ¬ P ^ P.ramificationIdx (NumberField.RingOfIntegers F) ∣
          differentIdeal (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers L)) :
    Ideal.absNorm (differentIdeal (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers L)) ∣
      (∏ q ∈ S, q) ^ Module.finrank ℚ L := by
  classical
  set 𝔡 : Ideal (𝓞 L) := differentIdeal (𝓞 F) (𝓞 L) with h𝔡
  have h𝔡ne : 𝔡 ≠ ⊥ := differentIdeal_ne_bot
  -- The `p`-adic valuation of the norm of the different is bounded by `[L : ℚ]` for `p ∈ S`.
  have hkey : ∀ (p : ℕ), Nat.Prime p → p ∈ S →
      padicValNat p (Ideal.absNorm 𝔡) ≤ Module.finrank ℚ L := by
    intro p hpprime hpS
    haveI : Fact (Nat.Prime p) := ⟨hpprime⟩
    haveI hpZprime : (Ideal.span ({(p : ℤ)} : Set ℤ)).IsPrime := by
      rw [Ideal.span_singleton_prime (by exact_mod_cast hpprime.ne_zero)]
      exact Nat.prime_iff_prime_int.mp hpprime
    haveI hpZfin : Fintype ((Ideal.span ({(p : ℤ)} : Set ℤ)).primesOver (𝓞 L)) :=
      (Algebra.QuasiFinite.finite_primesOver (Ideal.span ({(p : ℤ)} : Set ℤ))).fintype
    set U : Finset (Ideal (𝓞 L)) :=
      (normalizedFactors 𝔡).toFinset.filter
        (fun P : Ideal (𝓞 L) => P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))) with hU
    set V : Finset (Ideal (𝓞 L)) :=
      (Finset.univ : Finset ((Ideal.span ({(p : ℤ)} : Set ℤ)).primesOver (𝓞 L))).image
        Subtype.val with hV
    have hfilter : ((normalizedFactors 𝔡).toFinset.sum fun P : Ideal (𝓞 L) =>
        (normalizedFactors 𝔡).count P * padicValNat p P.absNorm)
        = ∑ P ∈ U, (normalizedFactors 𝔡).count P * P.inertiaDeg ℤ := by
      rw [hU, Finset.sum_filter]
      refine Finset.sum_congr rfl ?_
      intro P hPs
      have hPmax : P.IsMaximal :=
        isMaximal_of_mem_normalizedFactors h𝔡ne (Multiset.mem_toFinset.mp hPs)
      by_cases hqP : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))
      · rw [if_pos hqP, inertiaDeg_of_mem_normalizedFactors_liesOver p P hPmax hqP]
      · rw [if_neg hqP, padicValNat_absNorm_eq_zero_of_not_liesOver p P hPmax hqP, mul_zero]
    have hcount_le : ∀ P ∈ U, (normalizedFactors 𝔡).count P ≤
        P.ramificationIdx (𝓞 F) - 1 := by
      intro P hPU
      rw [hU, Finset.mem_filter] at hPU
      obtain ⟨hPmem0, hPq⟩ := hPU
      have hPmem : P ∈ normalizedFactors 𝔡 := Multiset.mem_toFinset.mp hPmem0
      have hPmax : P.IsMaximal := isMaximal_of_mem_normalizedFactors h𝔡ne hPmem
      have hPprime : P.IsPrime := ((Ideal.mem_normalizedFactors_iff h𝔡ne).mp hPmem).1
      haveI : P.IsPrime := hPprime
      have hnot' : ¬ P ^ P.ramificationIdx (𝓞 F) ∣ 𝔡 := hnot p hpS P hPmax hPq
      have hlt : (normalizedFactors 𝔡).count P < P.ramificationIdx (𝓞 F) := by
        by_contra hc
        rw [not_lt] at hc
        exact hnot' ((Commons.RingTheory.DedekindDomain.pow_dvd_iff_normalizedFactors_count_le
          P 𝔡 h𝔡ne _).mpr hc)
      omega
    have hle_ram : ∀ P ∈ U, P.ramificationIdx (𝓞 F) ≤ P.ramificationIdx ℤ := by
      intro P hPU
      rw [hU, Finset.mem_filter] at hPU
      have hPprime : P.IsPrime :=
        ((Ideal.mem_normalizedFactors_iff h𝔡ne).mp (Multiset.mem_toFinset.mp hPU.1)).1
      haveI : P.IsPrime := hPprime
      exact Ideal.ramificationIdx_above_le (P.under (𝓞 F)) P
    have hUV : U ⊆ V := by
      intro P hPU
      rw [hU, Finset.mem_filter] at hPU
      obtain ⟨hPmem0, hPq⟩ := hPU
      have hPprime : P.IsPrime :=
        ((Ideal.mem_normalizedFactors_iff h𝔡ne).mp (Multiset.mem_toFinset.mp hPmem0)).1
      rw [hV]
      exact Finset.mem_image.mpr ⟨⟨P, hPprime, hPq⟩, Finset.mem_univ _, rfl⟩
    have hVsum : ∑ P ∈ V, P.ramificationIdx ℤ * P.inertiaDeg ℤ = Module.finrank ℚ L := by
      rw [hV, Finset.sum_image]
      · rw [Ideal.sum_ramification_inertia_eq_finrank (R := ℤ)
            (p := Ideal.span ({(p : ℤ)} : Set ℤ)) (S := 𝓞 L),
          NumberField.RingOfIntegers.rank]
      · intro x _ y _ hxy
        exact Subtype.ext hxy
    calc padicValNat p (Ideal.absNorm 𝔡)
        = ∑ P ∈ (normalizedFactors 𝔡).toFinset,
            (normalizedFactors 𝔡).count P * padicValNat p P.absNorm :=
          padicValNat_absNorm_normalizedFactors (R := 𝓞 L) (I := 𝔡) h𝔡ne p
      _ = ∑ P ∈ U, (normalizedFactors 𝔡).count P * P.inertiaDeg ℤ := hfilter
      _ ≤ ∑ P ∈ U, (P.ramificationIdx (𝓞 F) - 1) * P.inertiaDeg ℤ :=
          Finset.sum_le_sum (fun P hP => Nat.mul_le_mul_right _ (hcount_le P hP))
      _ ≤ ∑ P ∈ U, (P.ramificationIdx ℤ - 1) * P.inertiaDeg ℤ :=
          Finset.sum_le_sum
            (fun P hP => Nat.mul_le_mul_right _ (Nat.sub_le_sub_right (hle_ram P hP) 1))
      _ ≤ ∑ P ∈ U, P.ramificationIdx ℤ * P.inertiaDeg ℤ :=
          Finset.sum_le_sum (fun P _ => Nat.mul_le_mul_right _ (Nat.sub_le _ _))
      _ ≤ ∑ P ∈ V, P.ramificationIdx ℤ * P.inertiaDeg ℤ :=
          Finset.sum_le_sum_of_subset_of_nonneg hUV (fun _ _ _ => Nat.zero_le _)
      _ = Module.finrank ℚ L := hVsum
  -- For `p ∉ S` the `p`-adic valuation vanishes.
  have hzero : ∀ (p : ℕ), Nat.Prime p → p ∉ S →
      padicValNat p (Ideal.absNorm 𝔡) = 0 := by
    intro p hpprime hpS
    haveI : Fact (Nat.Prime p) := ⟨hpprime⟩
    rw [padicValNat_absNorm_normalizedFactors (R := 𝓞 L) (I := 𝔡) h𝔡ne p]
    rw [Finset.sum_eq_zero]
    intro P hPmem
    have hPmem' : P ∈ normalizedFactors 𝔡 := Multiset.mem_toFinset.mp hPmem
    have hPif := (Ideal.mem_normalizedFactors_iff h𝔡ne).mp hPmem'
    have hPmax : P.IsMaximal := isMaximal_of_mem_normalizedFactors h𝔡ne hPmem'
    have hPne : P ≠ ⊥ := by
      intro hbot
      exact h𝔡ne (le_bot_iff.mp (by simpa [hbot] using hPif.2))
    have hdiv : P ∣ 𝔡 := Ideal.dvd_iff_le.mpr hPif.2
    have hnotlie : ¬ P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := by
      intro hPlie
      obtain ⟨q, hqS, hqlie⟩ := hsup P hPif.1 hPne hdiv
      have hpq : p = q := eq_of_liesOver_span_prime (hS q hqS) P hPlie hqlie
      exact hpS (hpq ▸ hqS)
    rw [padicValNat_absNorm_eq_zero_of_not_liesOver p P hPmax hnotlie, mul_zero]
  -- Conclude by divisibility.
  have ha : Ideal.absNorm 𝔡 ≠ 0 := (Ideal.absNorm_eq_zero_iff.not).mpr h𝔡ne
  have hb : (∏ q ∈ S, q) ^ Module.finrank ℚ L ≠ 0 :=
    pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr (fun q hq => (hS q hq).ne_zero))
  rw [← Nat.factorization_le_iff_dvd ha hb, Finsupp.le_iff]
  intro p hp
  rw [Nat.support_factorization] at hp
  have hpprime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  haveI : Fact (Nat.Prime p) := ⟨hpprime⟩
  rw [factorization_eq_padicValNat hpprime ha, factorization_eq_padicValNat hpprime hb]
  by_cases hpS : p ∈ S
  · calc padicValNat p (Ideal.absNorm 𝔡) ≤ Module.finrank ℚ L := hkey p hpprime hpS
      _ ≤ padicValNat p ((∏ q ∈ S, q) ^ Module.finrank ℚ L) :=
          finrank_le_padicValNat_prod_pow S hS p hpS
  · rw [hzero p hpprime hpS]
    exact Nat.zero_le _

/-- **Martinet's asymptotically-good totally real towers: tame norm bound for the relative
different ideal.**

Let `F ⊆ L` be an extension of number fields and `S` a finite set of rational primes such that
every prime ideal of `𝓞 L` dividing the relative different ideal `𝔡_{L/F}` lies over some `q ∈ S`
(`hsup`), and such that no maximal `P` over `q ∈ S` has `P ^ e_P` dividing `𝔡_{L/F}`, where `e_P`
is the ramification index of `P` over `𝓞 F` (`hnot`; this says precisely that `P` is tame over
`F`). Then the absolute norm of `𝔡_{L/F}` is at most `(∏_{q ∈ S} q) ^ [L : ℚ]`.

Equivalently (see `absNorm_differentIdeal_dvd_prod_pow_of_tame_support`) the absolute norm of the
relative different divides `(∏_{q ∈ S} q) ^ [L : ℚ]`: every prime dividing `𝔡_{L/F}` is tame and
lies over some `q ∈ S`, and the exponent of each such `q` is at most the degree `[L : ℚ]`. -/
theorem absNorm_differentIdeal_le_prod_pow_of_tame_support
    {F L : Type*} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
    [FiniteDimensional F L] (S : Finset ℕ) (hS : ∀ q ∈ S, Nat.Prime q)
    (hsup : ∀ (P : Ideal (NumberField.RingOfIntegers L)), P.IsPrime → P ≠ ⊥ →
      P ∣ differentIdeal (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers L) →
        ∃ q ∈ S, P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)))
    (hnot : ∀ q ∈ S, ∀ (P : Ideal (NumberField.RingOfIntegers L)), P.IsMaximal →
      P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) →
        ¬ P ^ P.ramificationIdx (NumberField.RingOfIntegers F) ∣
          differentIdeal (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers L)) :
    Ideal.absNorm (differentIdeal (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers L)) ≤
      (∏ q ∈ S, q) ^ Module.finrank ℚ L :=
  Nat.le_of_dvd (pow_pos (Finset.prod_pos (fun q hq => (hS q hq).pos)) _)
    (absNorm_differentIdeal_dvd_prod_pow_of_tame_support S hS hsup hnot)

end Commons.NumberTheory.NumberField
