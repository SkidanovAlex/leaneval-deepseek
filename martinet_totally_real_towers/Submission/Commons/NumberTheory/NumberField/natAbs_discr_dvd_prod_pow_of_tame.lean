import Mathlib
import Submission.Commons.NumberTheory.NumberField.tame_different_not_pow_dvd
import Submission.Commons.NumberTheory.NumberField.discriminant_valuation_sum
import Submission.Commons.NumberTheory.NumberField.padicValNat_absNorm_prime_eq_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.discr_padicValNat_eq_sum_over_p_count_mul_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.tame_totallyRamified_different_not_pow_dvd
import Submission.Commons.RingTheory.DedekindDomain.pow_dvd_iff_normalizedFactors_count_le
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.Algebra.CharZero.Infinite

open scoped NumberField
open UniqueFactorizationMonoid

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.NumberField

/-- For a nonzero natural number `n` and a prime `p`, the multiplicity of `p` in `n` (as given
by `Nat.factorization`) is the `p`-adic valuation of `n`. -/
lemma factorization_eq_padicValNat {p n : ℕ} (hp : Nat.Prime p) (hn : n ≠ 0) :
    n.factorization p = padicValNat p n := by
  exact Nat.factorization_def n hp

/-- A prime ideal of the ring of integers of a number field lying over two rational primes
`p` and `q` forces `p = q`. -/
lemma eq_of_liesOver_span_prime {K : Type*} [Field K] [NumberField K] {p q : ℕ}
    [Fact (Nat.Prime p)] (hq : Nat.Prime q) (P : Ideal (𝓞 K))
    (hPp : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)))
    (hPq : P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ))) : p = q := by
  have hspan : Ideal.span ({(p : ℤ)} : Set ℤ) = Ideal.span ({(q : ℤ)} : Set ℤ) := by
    rw [hPp.over, hPq.over]
  have hmem : (p : ℤ) ∈ Ideal.span ({(q : ℤ)} : Set ℤ) := by
    rw [← hspan]; exact Ideal.mem_span_singleton.mpr (dvd_refl _)
  have hdvd : q ∣ p := Int.ofNat_dvd.mp (Ideal.mem_span_singleton.mp hmem)
  exact ((Fact.out : Nat.Prime p).dvd_iff_eq hq.ne_one).mp hdvd

/-- If every maximal ideal `P` of the ring of integers lying over the rational prime `p` is
*tame* (i.e. `p` does not divide the ramification index `e_P`), then the `p`-adic valuation of the
absolute discriminant of `K` is at most the degree `[K : ℚ]`.

This is the standard discriminant-ramification inequality: the exponent of `P` in the different
ideal is bounded by `e_P` in the tame case (`tame_different_not_pow_dvd`), and the fundamental
identity `∑_{P | p} e_P f_P = [K : ℚ]` bounds the resulting sum. -/
theorem discr_padicValNat_le_finrank_of_tame {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact (Nat.Prime p)]
    (htame : ∀ (P : Ideal (NumberField.RingOfIntegers K)), P.IsMaximal →
      P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) → ¬ p ∣ P.ramificationIdx ℤ) :
    padicValNat p (NumberField.discr K).natAbs ≤ Module.finrank ℚ K := by
  classical
  haveI hpZprime : (Ideal.span ({(p : ℤ)} : Set ℤ)).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)]
    exact Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime p)
  haveI hpZfin : Fintype ((Ideal.span ({(p : ℤ)} : Set ℤ)).primesOver (𝓞 K)) :=
    (Algebra.QuasiFinite.finite_primesOver (Ideal.span ({(p : ℤ)} : Set ℤ))).fintype
  have hI : differentIdeal ℤ (𝓞 K) ≠ ⊥ := differentIdeal_ne_bot (A := ℤ) (B := 𝓞 K)
  rw [discr_padicValNat_eq_sum_over_p_count_mul_inertiaDeg (K := K) (p := p)]
  set U : Finset (Ideal (𝓞 K)) :=
    (normalizedFactors (differentIdeal ℤ (𝓞 K))).toFinset.filter
      (fun P : Ideal (𝓞 K) => P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))) with hU
  set V : Finset (Ideal (𝓞 K)) :=
    (Finset.univ : Finset ((Ideal.span ({(p : ℤ)} : Set ℤ)).primesOver (𝓞 K))).image
      Subtype.val with hV
  have hcount_le : ∀ P ∈ U,
      (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P ≤ P.ramificationIdx ℤ := by
    intro P hPU
    rw [hU, Finset.mem_filter] at hPU
    obtain ⟨hPmem0, hPq⟩ := hPU
    have hPmem : P ∈ normalizedFactors (differentIdeal ℤ (𝓞 K)) := Multiset.mem_toFinset.mp hPmem0
    have hPmax : P.IsMaximal := isMaximal_of_mem_normalizedFactors hI hPmem
    have hPprime : P.IsPrime := ((Ideal.mem_normalizedFactors_iff hI).mp hPmem).1
    haveI : P.IsPrime := hPprime
    have hnot : ¬ P ^ P.ramificationIdx ℤ ∣ differentIdeal ℤ (𝓞 K) :=
      tame_different_not_pow_dvd (K := K) p P (htame P hPmax hPq)
    have hlt : (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P < P.ramificationIdx ℤ := by
      by_contra hc
      rw [not_lt] at hc
      exact hnot ((Commons.RingTheory.DedekindDomain.pow_dvd_iff_normalizedFactors_count_le
        P (differentIdeal ℤ (𝓞 K)) hI _).mpr hc)
    omega
  have hUV : U ⊆ V := by
    intro P hPU
    rw [hU, Finset.mem_filter] at hPU
    obtain ⟨hPmem0, hPq⟩ := hPU
    have hPmem : P ∈ normalizedFactors (differentIdeal ℤ (𝓞 K)) := Multiset.mem_toFinset.mp hPmem0
    have hPprime : P.IsPrime := ((Ideal.mem_normalizedFactors_iff hI).mp hPmem).1
    rw [hV]
    exact Finset.mem_image.mpr ⟨⟨P, hPprime, hPq⟩, Finset.mem_univ _, rfl⟩
  have hVsum : ∑ P ∈ V, P.ramificationIdx ℤ * P.inertiaDeg ℤ =
      ∑ q : (Ideal.span ({(p : ℤ)} : Set ℤ)).primesOver (𝓞 K),
        q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ := by
    rw [hV, Finset.sum_image]
    intro x _ y _ hxy
    exact Subtype.ext hxy
  calc
    ∑ P ∈ U, (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P * P.inertiaDeg ℤ
        ≤ ∑ P ∈ U, P.ramificationIdx ℤ * P.inertiaDeg ℤ :=
          Finset.sum_le_sum (fun P hP => Nat.mul_le_mul_right _ (hcount_le P hP))
    _ ≤ ∑ P ∈ V, P.ramificationIdx ℤ * P.inertiaDeg ℤ :=
          Finset.sum_le_sum_of_subset_of_nonneg hUV (fun _ _ _ => Nat.zero_le _)
    _ = ∑ q : (Ideal.span ({(p : ℤ)} : Set ℤ)).primesOver (𝓞 K),
        q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ := hVsum
    _ = Module.finrank ℚ K := by
          rw [Ideal.sum_ramification_inertia_eq_finrank (Ideal.span ({(p : ℤ)} : Set ℤ)) (𝓞 K),
            NumberField.RingOfIntegers.rank]

/-- If `p` lies over none of the primes in `S`, and every prime ideal dividing the different ideal
lies over a prime in `S`, then `p` does not divide the absolute discriminant. -/
theorem discr_padicValNat_eq_zero_of_not_mem {K : Type*} [Field K] [NumberField K]
    (S : Finset ℕ) (hS : ∀ q ∈ S, Nat.Prime q)
    (hsupp : ∀ (P : Ideal (𝓞 K)), P.IsPrime → P ≠ ⊥ →
      P ∣ differentIdeal ℤ (𝓞 K) →
        ∃ q ∈ S, P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)))
    (p : ℕ) [Fact (Nat.Prime p)] (hpS : p ∉ S) :
    padicValNat p (NumberField.discr K).natAbs = 0 := by
  classical
  have hI : differentIdeal ℤ (𝓞 K) ≠ ⊥ := differentIdeal_ne_bot (A := ℤ) (B := 𝓞 K)
  rw [discr_padicValNat_eq_sum_over_p_count_mul_inertiaDeg (K := K) (p := p)]
  have hemp : (normalizedFactors (differentIdeal ℤ (𝓞 K))).toFinset.filter
      (fun P : Ideal (𝓞 K) => P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro P hPmem0 hPlie
    have hPmem : P ∈ normalizedFactors (differentIdeal ℤ (𝓞 K)) := Multiset.mem_toFinset.mp hPmem0
    have hPif := (Ideal.mem_normalizedFactors_iff hI).mp hPmem
    have hPprime : P.IsPrime := hPif.1
    have hle : differentIdeal ℤ (𝓞 K) ≤ P := hPif.2
    have hPne : P ≠ ⊥ := by
      intro hbot; exact hI (le_bot_iff.mp (by simpa [hbot] using hle))
    have hpdiv : P ∣ differentIdeal ℤ (𝓞 K) := Ideal.dvd_iff_le.mpr hle
    obtain ⟨q, hqS, hqlie⟩ := hsupp P hPprime hPne hpdiv
    have hpq : p = q := eq_of_liesOver_span_prime (hS q hqS) P hPlie hqlie
    exact hpS (hpq ▸ hqS)
  rw [hemp]
  simp

/-- The exponent of a prime `p ∈ S` in the product `∏_{q ∈ S} q` is one, so the exponent of `p`
in `(∏_{q ∈ S} q) ^ [K : ℚ]` is at least `[K : ℚ]`. -/
lemma finrank_le_padicValNat_prod_pow {K : Type*} [Field K] [NumberField K] (S : Finset ℕ)
    (hS : ∀ q ∈ S, Nat.Prime q) (p : ℕ) [Fact (Nat.Prime p)] (hpS : p ∈ S) :
    Module.finrank ℚ K ≤ padicValNat p ((∏ q ∈ S, q) ^ Module.finrank ℚ K) := by
  have hprod_ne : (∏ q ∈ S, q) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun q hq => (hS q hq).ne_zero)
  have hdvd : p ∣ ∏ q ∈ S, q := Finset.dvd_prod_of_mem (fun q => q) hpS
  have h1 : 1 ≤ padicValNat p (∏ q ∈ S, q) := by
    rcases (padicValNat_dvd_iff (p := p) 1 (∏ q ∈ S, q)).mp (by simpa using hdvd) with h | h
    · exact absurd h hprod_ne
    · exact h
  rw [padicValNat.pow]
  exact Nat.le_mul_of_pos_right _ (by omega)

/-- **Martinet's asymptotically-good totally real towers: tame discriminant bound.**

Let `K` be a number field and `S` a finite set of rational primes such that

* every maximal ideal `P` of `𝓞 K` lying over some `q ∈ S` is tame, i.e. `q ∤ e_P`
  (`htame`), and
* every prime ideal dividing the different ideal of `K` lies over some `q ∈ S` (`hsupp`).

Then the absolute discriminant of `K` divides `(∏_{q ∈ S} q) ^ [K : ℚ]`.

Equivalently, every rational prime dividing the discriminant is one of the (tamely) ramified
primes in `S`, and its exponent is at most the degree. -/
theorem natAbs_discr_dvd_prod_pow_of_tame {K : Type*} [Field K] [NumberField K] (S : Finset ℕ)
    (hS : ∀ q ∈ S, Nat.Prime q)
    (htame : ∀ q ∈ S, ∀ (P : Ideal (NumberField.RingOfIntegers K)), P.IsMaximal →
      P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) → ¬ q ∣ P.ramificationIdx ℤ)
    (hsupp : ∀ (P : Ideal (NumberField.RingOfIntegers K)), P.IsPrime → P ≠ ⊥ →
      P ∣ differentIdeal ℤ (NumberField.RingOfIntegers K) →
        ∃ q ∈ S, P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ))) :
    (NumberField.discr K).natAbs ∣ (∏ q ∈ S, q) ^ Module.finrank ℚ K := by
  classical
  have ha : (NumberField.discr K).natAbs ≠ 0 := by
    rw [← NumberField.absNorm_differentIdeal K (𝓞 K)]
    exact (Ideal.absNorm_eq_zero_iff.not).mpr (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 K))
  have hb : (∏ q ∈ S, q) ^ Module.finrank ℚ K ≠ 0 :=
    pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr (fun q hq => (hS q hq).ne_zero))
  rw [← Nat.factorization_le_iff_dvd ha hb, Finsupp.le_iff]
  intro p hp
  rw [Nat.support_factorization] at hp
  have hpprime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  haveI : Fact (Nat.Prime p) := ⟨hpprime⟩
  rw [factorization_eq_padicValNat hpprime ha, factorization_eq_padicValNat hpprime hb]
  by_cases hpS : p ∈ S
  · calc padicValNat p (NumberField.discr K).natAbs
        ≤ Module.finrank ℚ K := discr_padicValNat_le_finrank_of_tame p (htame p hpS)
      _ ≤ padicValNat p ((∏ q ∈ S, q) ^ Module.finrank ℚ K) :=
            finrank_le_padicValNat_prod_pow S hS p hpS
  · rw [discr_padicValNat_eq_zero_of_not_mem S hS hsupp p hpS]
    exact Nat.zero_le _

end Commons.NumberTheory.NumberField
