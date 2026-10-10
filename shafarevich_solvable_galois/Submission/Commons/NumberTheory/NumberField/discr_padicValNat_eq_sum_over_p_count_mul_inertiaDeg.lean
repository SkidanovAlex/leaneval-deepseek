import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Submission.Commons.NumberTheory.NumberField.discriminant_valuation_sum
import Submission.Commons.NumberTheory.NumberField.padicValNat_absNorm_prime_eq_inertiaDeg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open Classical

open scoped BigOperators NumberField
open UniqueFactorizationMonoid

namespace Commons.NumberTheory.NumberField

/-- If a rational prime `p` divides the absolute norm of a maximal ideal `P` of the ring of
integers, then `P` lies over `(p)`. -/
lemma liesOver_of_dvd_absNorm {K : Type*} [Field K] [NumberField K] (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) (hmax : P.IsMaximal) (hdiv : p ∣ P.absNorm) :
    P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := by
  obtain ⟨q, n, hn, hqmem, hqprime, hpow⟩ := Ideal.exists_prime_and_absNorm_eq_pow (S := 𝓞 K) P
  have hdivq : p ∣ q ^ n := by rwa [hpow] at hdiv
  have hpqdiv : p ∣ q := (Fact.out : Nat.Prime p).dvd_of_dvd_pow hdivq
  have hpq : q = p := (hqprime.dvd_iff_eq (Nat.Prime.ne_one (Fact.out : Nat.Prime p))).mp hpqdiv
  apply (Ideal.liesOver_span_iff (P := P) (hP := Ideal.IsMaximal.ne_top hmax)
    (hp := Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime p))).mpr
  simpa [hpq] using hqmem

/-- If a maximal ideal `P` of the ring of integers does not lie over `(p)`, then `p` does not
divide its absolute norm. -/
lemma not_dvd_absNorm_of_not_liesOver {K : Type*} [Field K] [NumberField K] (p : ℕ)
    [Fact (Nat.Prime p)] (P : Ideal (𝓞 K)) (hmax : P.IsMaximal)
    (hnot : ¬ P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))) : ¬ p ∣ P.absNorm := by
  intro hdiv
  exact hnot (liesOver_of_dvd_absNorm p P hmax hdiv)

/-- For a maximal ideal `P` of the ring of integers not lying over `(p)`, the `p`-adic valuation
of its absolute norm vanishes. -/
lemma padicValNat_absNorm_eq_zero_of_not_liesOver {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K)) (hmax : P.IsMaximal)
    (hnot : ¬ P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))) :
    padicValNat p P.absNorm = 0 := by
  exact padicValNat.eq_zero_of_not_dvd (not_dvd_absNorm_of_not_liesOver p P hmax hnot)

/-- Any prime ideal dividing a non-zero ideal of the ring of integers is maximal. -/
lemma isMaximal_of_mem_normalizedFactors {K : Type*} [Field K] [NumberField K]
    {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) {P : Ideal (𝓞 K)} (hP : P ∈ normalizedFactors I) :
    P.IsMaximal := by
  have hPif : P.IsPrime ∧ I ≤ P := (Ideal.mem_normalizedFactors_iff hI).mp hP
  have hPne : P ≠ ⊥ := by
    intro hbot
    exact hI (le_bot_iff.mp (by simpa [hbot] using hPif.2))
  haveI : P.IsPrime := hPif.1
  exact Ideal.isMaximal_of_isPrime_of_ne_bot P hPne

/-- For a prime ideal `P` dividing the different that lies over `(p)`, the `p`-adic valuation of
its absolute norm equals its inertia degree. -/
lemma inertiaDeg_of_mem_normalizedFactors_liesOver {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K)) (hmax : P.IsMaximal)
    (hq : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))) :
    padicValNat p P.absNorm = P.inertiaDeg ℤ := by
  haveI : P.IsMaximal := hmax
  haveI : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := hq
  exact padicValNat_absNorm_prime_eq_inertiaDeg (K := K) (p := p) P

theorem discr_padicValNat_eq_sum_over_p_count_mul_inertiaDeg
    {K : Type*} [Field K] [NumberField K] (p : ℕ) [Fact (Nat.Prime p)] :
    padicValNat p (NumberField.discr K).natAbs =
      (((normalizedFactors (differentIdeal ℤ (𝓞 K))).toFinset.filter
        (fun P : Ideal (𝓞 K) => P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)))).sum
        fun P : Ideal (𝓞 K) =>
          (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P * P.inertiaDeg ℤ) := by
  classical
  let m : Multiset (Ideal (𝓞 K)) := normalizedFactors (differentIdeal ℤ (𝓞 K))
  let s : Finset (Ideal (𝓞 K)) := m.toFinset
  let q : Ideal (𝓞 K) → Prop := fun P => P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))
  have hdif : differentIdeal ℤ (𝓞 K) ≠ ⊥ := differentIdeal_ne_bot (A := ℤ) (B := 𝓞 K)
  rw [discriminant_valuation_sum (K := K) (p := p)]
  change (s.sum fun P : Ideal (𝓞 K) => m.count P * padicValNat p P.absNorm) =
    (s.filter q).sum fun P : Ideal (𝓞 K) => m.count P * P.inertiaDeg ℤ
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro P hPs
  have hPm : P ∈ m := (Multiset.mem_toFinset.mp (by simpa [s] using hPs))
  by_cases hqP : q P
  · have hmax : P.IsMaximal := isMaximal_of_mem_normalizedFactors hdif (by simpa [m] using hPm)
    have h59 : padicValNat p P.absNorm = P.inertiaDeg ℤ :=
      inertiaDeg_of_mem_normalizedFactors_liesOver p P hmax hqP
    rw [if_pos hqP, h59]
  · have hmax : P.IsMaximal := isMaximal_of_mem_normalizedFactors hdif (by simpa [m] using hPm)
    have hz : padicValNat p P.absNorm = 0 :=
      padicValNat_absNorm_eq_zero_of_not_liesOver p P hmax hqP
    rw [if_neg hqP, hz]
    simp

end Commons.NumberTheory.NumberField