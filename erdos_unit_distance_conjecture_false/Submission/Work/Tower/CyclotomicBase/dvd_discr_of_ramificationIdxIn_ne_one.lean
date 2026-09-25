import Mathlib

/-!
# A prime with nontrivial ramification index divides the discriminant

If a rational prime `p` has ramification index `≠ 1` in a Galois number field `K`
(i.e. `p` ramifies in `K`), then `p` divides the discriminant of `K`.

This is the contrapositive of `NumberField.not_dvd_discr_iff_forall_liesOver`: if `p ∤ discr K`,
then every prime of `𝓞 K` above `p` is unramified, hence (since `K/ℚ` is Galois and all primes
above `p` have the same ramification index) `ramificationIdxIn p (𝓞 K) = 1`.
-/

set_option linter.style.haveILetI false

open NumberField
open scoped Classical nonZeroDivisors NumberField

namespace Work.Tower.CyclotomicBase

theorem dvd_discr_of_ramificationIdxIn_ne_one {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]
    {p : ℕ} (hp : Nat.Prime p)
    (h : (Ideal.span {(p : ℤ)}).ramificationIdxIn (NumberField.RingOfIntegers K) ≠ 1) :
    (p : ℤ) ∣ NumberField.discr K := by
  -- Prove the contrapositive: if `p ∤ discr K` then `p` has ramification index `1` in `K`.
  by_contra hnot
  apply h
  -- Structural facts for `𝓞 K` over `ℤ`, and the Galois action of `Gal(K/ℚ)` on `𝓞 K`.
  have hdom : IsDomain (𝓞 K) := (IsIntegralClosure.algebraMap_injective (𝓞 K) ℤ K).isDomain
  have hded : IsDedekindDomain (𝓞 K) := IsIntegralClosure.isDedekindDomain ℤ ℚ K (𝓞 K)
  have hfrac : IsFractionRing (𝓞 K) K :=
    IsIntegralClosure.isFractionRing_of_finite_extension ℤ ℚ K (𝓞 K)
  have hfin : Module.Finite ℤ (𝓞 K) := IsIntegralClosure.finite ℤ ℚ K (𝓞 K)
  letI : MulSemiringAction Gal(K/ℚ) (𝓞 K) := IsIntegralClosure.MulSemiringAction ℤ ℚ K (𝓞 K)
  have hgal : IsGaloisGroup Gal(K/ℚ) ℤ (𝓞 K) :=
    IsGaloisGroup.of_isFractionRing Gal(K/ℚ) ℤ (𝓞 K) ℚ K
  have hFinGal : Finite Gal(K/ℚ) := IsGaloisGroup.finite Gal(K/ℚ) ℤ (𝓞 K)
  -- `(p)` is a prime ideal of `ℤ`.
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  haveI hpprime : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime hp0).mpr hpZ
  -- Choose a prime `P` of `𝓞 K` above `(p)`.
  obtain ⟨P⟩ := (inferInstance : Nonempty ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K)))
  haveI := P.2.1
  haveI := P.2.2
  -- `P` is maximal since `𝓞 K` is a Dedekind domain and `P ≠ ⊥`.
  have hPne : P.1 ≠ ⊥ :=
    Ideal.ne_bot_of_mem_primesOver (p := Ideal.span {(p : ℤ)})
      (Ideal.span_singleton_eq_bot.not.mpr hp0) P.2
  -- Since `p ∤ discr K`, the prime `P` is unramified over `ℤ`.
  have hunr : Algebra.IsUnramifiedAt ℤ P.1 :=
    (NumberField.not_dvd_discr_iff_forall_liesOver K (𝓞 K) hpZ).mp hnot P.1
      ((Ideal.IsPrime.isMaximal P.2.1) hPne) P.2.2
  haveI : Algebra.IsUnramifiedAt ℤ P.1 := hunr
  -- Unramified means ramification index `1`, and in the Galois extension `K/ℚ` all primes above
  -- `(p)` share the ramification index `ramificationIdxIn`.
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(p : ℤ)}) P.1 Gal(K/ℚ),
    Ideal.ramificationIdx_eq_one P.1 ℤ]

end Work.Tower.CyclotomicBase
