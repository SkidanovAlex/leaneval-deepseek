import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.Work.SSGRoute.GrunwaldEscapeCore.exists_prime_mem_rayClass
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PinnedTwin

open NumberField IsDedekindDomain
open scoped NumberField nonZeroDivisors

section Basic

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K]

/-- The ring automorphism of `𝓞 K` induced by `ρ : Gal(K/k)`. -/
noncomputable abbrev rhoRing (ρ : K ≃ₐ[k] K) : 𝓞 K ≃+* 𝓞 K :=
  galRestrict (𝓞 k) k K (𝓞 K) ρ

/-- The conjugate of an ideal of `𝓞 K` under `ρ`. -/
noncomputable abbrev rhoIdeal (ρ : K ≃ₐ[k] K) (I : Ideal (𝓞 K)) : Ideal (𝓞 K) :=
  I.map (rhoRing ρ : 𝓞 K →+* 𝓞 K)

@[simp] theorem rhoIdeal_asIdeal (ρ : K ≃ₐ[k] K) (q : HeightOneSpectrum (𝓞 K)) :
    rhoIdeal ρ q.asIdeal =
      (Commons.NumberTheory.NumberField.Completion.placeSmul ρ q).asIdeal := by
  rw [Commons.NumberTheory.NumberField.Completion.placeSmul_asIdeal]
  rfl

theorem rhoIdeal_mul (ρ : K ≃ₐ[k] K) (I J : Ideal (𝓞 K)) :
    rhoIdeal ρ (I * J) = rhoIdeal ρ I * rhoIdeal ρ J := by
  rw [rhoIdeal, rhoIdeal, rhoIdeal, Ideal.map_mul]

theorem rhoIdeal_span_singleton (ρ : K ≃ₐ[k] K) (a : 𝓞 K) :
    rhoIdeal ρ (Ideal.span {a}) = Ideal.span {rhoRing ρ a} := by
  rw [rhoIdeal, Ideal.map_span, Set.image_singleton]
  congr 1

/-- `ρ` applied twice is the identity, on primes. -/
theorem placeSmul_placeSmul (ρ : K ≃ₐ[k] K) (hρ2 : ρ ^ 2 = 1)
    (q : HeightOneSpectrum (𝓞 K)) :
    Commons.NumberTheory.NumberField.Completion.placeSmul ρ
      (Commons.NumberTheory.NumberField.Completion.placeSmul ρ q) = q := by
  have hsq : ρ * ρ = 1 := by simpa [pow_two] using hρ2
  rw [← Commons.NumberTheory.NumberField.Completion.placeSmul_mul, hsq,
    Commons.NumberTheory.NumberField.Completion.placeSmul_one]

/-- `ρ` is an involution: the inverse of `ρ` acts on primes as `ρ`. -/
theorem placeSmul_inv (ρ : K ≃ₐ[k] K) (hρ2 : ρ ^ 2 = 1) (q : HeightOneSpectrum (𝓞 K)) :
    Commons.NumberTheory.NumberField.Completion.placeSmul ρ⁻¹ q
      = Commons.NumberTheory.NumberField.Completion.placeSmul ρ q := by
  have hsq : ρ * ρ = 1 := by simpa [pow_two] using hρ2
  have h : ρ⁻¹ = ρ := by
    rw [← mul_one ρ⁻¹, ← hsq, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [h]

/-- The ring automorphism of `𝓞 K` induced by `ρ` is an involution. -/
theorem rhoRing_mul_self (ρ : K ≃ₐ[k] K) (hρ2 : ρ ^ 2 = 1) :
    ∀ x : 𝓞 K, rhoRing ρ (rhoRing ρ x) = x := by
  have hsq : ρ * ρ = 1 := by simpa [pow_two] using hρ2
  intro x
  change galRestrict (𝓞 k) k K (𝓞 K) ρ (galRestrict (𝓞 k) k K (𝓞 K) ρ x) = x
  rw [← AlgEquiv.mul_apply, ← map_mul, hsq, map_one]
  rfl

end Basic

end Work.SSGRoute.PinnedTwin
