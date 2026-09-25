import Mathlib

/-!
# `Work.ShafarevichKoch.Conj` -- conjugation of ideals of `𝓞 L` by `Gal(L/F)`

The pointwise action of `Gal(L/F) = L ≃ₐ[F] L` on the ring of integers `𝓞 L` (Mathlib
`NumberField.RingOfIntegers.instMulSemiringAction`, an instance requiring
`MulSemiringAction (L ≃ₐ[F] L) L`) extends to the ideals of `𝓞 L`; the resulting `SMul` is a
*scoped* instance (`open scoped Pointwise`).  This module fixes a named, unscoped spelling of the
conjugate ideal,

  `conjIdeal σ P = σ • P`,

so that statements about conjugates of ideals can be delegated and stated without opening the
`Pointwise` scope, and records the two Mathlib facts the counting argument needs:

* `conjIdeal_isPrime` -- primality is preserved;
* `inertia_conjIdeal` -- `I_{σP} = σ I_P σ⁻¹` (Mathlib's `Ideal.inertia_smul`);
* `conjIdeal_liesOver` -- if `P` lies over `𝔮` of `𝓞 F` (identified with its image under
  `ℚ ↪ 𝓞 F`), the conjugate lies over the same `𝔮`.
-/

set_option linter.unusedVariables false

open scoped Pointwise
open scoped NumberField

noncomputable section

namespace Work.ShafarevichKoch

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-- **The conjugate of an ideal of `𝓞 L` by a Galois automorphism.**  Named spelling of the
pointwise action `σ • P`, so that it can be referred to without `open scoped Pointwise`. -/
def conjIdeal (σ : L ≃ₐ[F] L) (P : Ideal (NumberField.RingOfIntegers L)) :
    Ideal (NumberField.RingOfIntegers L) :=
  σ • P

/-- The conjugate of an ideal is prime iff the ideal is. -/
theorem conjIdeal_isPrime (σ : L ≃ₐ[F] L) (P : Ideal (NumberField.RingOfIntegers L)) :
    (conjIdeal σ P).IsPrime ↔ P.IsPrime :=
  Ideal.IsPrime.smul_iff σ

/-- `conjIdeal` is the pointwise action. -/
@[simp]
theorem conjIdeal_eq_smul (σ : L ≃ₐ[F] L) (P : Ideal (NumberField.RingOfIntegers L)) :
    conjIdeal σ P = σ • P := rfl

/-- **Conjugation of inertia groups**: `I_{σ P} = σ I_P σ⁻¹`. -/
theorem inertia_conjIdeal [NumberField L] (σ : L ≃ₐ[F] L)
    (P : Ideal (NumberField.RingOfIntegers L)) :
    Ideal.inertia (L ≃ₐ[F] L) (conjIdeal σ P) =
      (Ideal.inertia (L ≃ₐ[F] L) P).map (MulAut.conj σ) :=
  Ideal.inertia_smul σ P

/-- Two conjugates by `σ` and `σ⁻¹` cancel. -/
@[simp]
theorem conjIdeal_inv_conjIdeal (σ : L ≃ₐ[F] L) (P : Ideal (NumberField.RingOfIntegers L)) :
    conjIdeal σ⁻¹ (conjIdeal σ P) = P := by
  simp [conjIdeal]

/-- `conjIdeal` is multiplicative in the automorphism. -/
@[simp]
theorem conjIdeal_mul (σ τ : L ≃ₐ[F] L) (P : Ideal (NumberField.RingOfIntegers L)) :
    conjIdeal (σ * τ) P = conjIdeal σ (conjIdeal τ P) := by
  simp [conjIdeal, mul_smul]

/-- **Transitivity of the Galois action on the primes over a prime.**  For `L/F` finite Galois and
`P₀, P` primes of `𝓞 L` over the same prime `𝔮` of `𝓞 F`, `P` is a Galois conjugate of `P₀`.
This is Mathlib's `Ideal.exists_smul_eq_of_isGaloisGroup` in the spelling of `conjIdeal`. -/
theorem exists_conjIdeal_eq_of_liesOver {F L : Type} [Field F] [Field L] [Algebra F L]
    [NumberField F] [NumberField L] [FiniteDimensional F L] [IsGalois F L]
    (𝔮 : Ideal (NumberField.RingOfIntegers F)) [𝔮.IsPrime]
    (P₀ : Ideal (NumberField.RingOfIntegers L)) [P₀.IsPrime] [P₀.LiesOver 𝔮]
    (P : Ideal (NumberField.RingOfIntegers L)) [P.IsPrime] [P.LiesOver 𝔮] :
    ∃ σ : L ≃ₐ[F] L, P = conjIdeal σ P₀ := by
  haveI : IsGaloisGroup (L ≃ₐ[F] L) (NumberField.RingOfIntegers F)
      (NumberField.RingOfIntegers L) := inferInstance
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup 𝔮 P₀ P (L ≃ₐ[F] L)
  exact ⟨σ, by rw [← hσ]; rfl⟩

end Work.ShafarevichKoch
