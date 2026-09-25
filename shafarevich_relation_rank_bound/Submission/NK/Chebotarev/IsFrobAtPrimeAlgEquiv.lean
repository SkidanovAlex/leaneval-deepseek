import Mathlib
import Submission.NK.Chebotarev.Basic

/-!
# Frobenius elements are compatible with isomorphisms of number fields

Let `L` and `E` be number fields (finite Galois over `ℚ`) and let `e : L ≃ₐ[ℚ] E` be an
isomorphism of `ℚ`-algebras.  Then `e` transports Frobenius elements: `σ : Gal(L/ℚ)` is a
Frobenius at a prime `p` of `ℚ` if and only if the conjugate `e⁻¹ σ e` is a Frobenius at `p`.

The proof transports primes along the induced isomorphism `𝓞 L ≃+* 𝓞 E` of rings of integers
and uses that this isomorphism intertwines the actions of `Gal(L/ℚ)` and `Gal(E/ℚ)` on the
rings of integers.
-/

set_option linter.unusedSectionVars false

open scoped NumberField
open NumberField

namespace NK.Chebotarev

section Core

variable {L E : Type*} [Field L] [NumberField L] [Field E] [NumberField E]
  [FiniteDimensional ℚ L] [FiniteDimensional ℚ E] [IsGalois ℚ L] [IsGalois ℚ E]

/-- The restriction of a `ℚ`-algebra isomorphism of number fields to the rings of integers,
evaluated in the ambient fields. -/
lemma algebraMap_mapAlgEquiv (e : L ≃ₐ[ℚ] E) (z : 𝓞 L) :
    (algebraMap (𝓞 E) E) (RingOfIntegers.mapAlgEquiv e z) = e ((algebraMap (𝓞 L) L) z) :=
  RingOfIntegers.mapRingHom_apply _ z

/-- The inverse of the restricted isomorphism of rings of integers, evaluated in the ambient
fields. -/
lemma algebraMap_mapAlgEquiv_symm (e : L ≃ₐ[ℚ] E) (z : 𝓞 E) :
    (algebraMap (𝓞 L) L) ((RingOfIntegers.mapAlgEquiv e).symm z)
      = e.symm ((algebraMap (𝓞 E) E) z) :=
  algebraMap_mapAlgEquiv e.symm z

/-- **Conjugation by an isomorphism of fields intertwines the actions of the Galois groups on the
rings of integers.** -/
lemma galRestrict_trans_conj_apply (e : L ≃ₐ[ℚ] E) (σ : Gal(L/ℚ)) (y : 𝓞 E) :
    galRestrict (𝓞 ℚ) ℚ E (𝓞 E) (e.symm.trans (σ.trans e)) y
      = (RingOfIntegers.mapAlgEquiv e)
          ((galRestrict (𝓞 ℚ) ℚ L (𝓞 L) σ) ((RingOfIntegers.mapAlgEquiv e).symm y)) := by
  apply RingOfIntegers.coe_injective
  simp only [algebraMap_galRestrict_apply, AlgEquiv.trans_apply,
    algebraMap_mapAlgEquiv, algebraMap_mapAlgEquiv_symm]

/-- Membership in the image of an ideal under the isomorphism of rings of integers induced by a
`ℚ`-algebra isomorphism of number fields. -/
lemma mem_map_mapAlgEquiv_iff (e : L ≃ₐ[ℚ] E) (I : Ideal (𝓞 L)) (z : 𝓞 E) :
    z ∈ Ideal.map (RingOfIntegers.mapAlgEquiv e) I ↔
      (RingOfIntegers.mapAlgEquiv e).symm z ∈ I := by
  rw [Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨x, hx, hxz⟩
    rw [← hxz, AlgEquiv.symm_apply_apply]
    exact hx
  · rintro hz
    exact ⟨_, hz, (RingOfIntegers.mapAlgEquiv e).apply_symm_apply z⟩

/-- The conjugation action of `Gal(E/ℚ)` on itself, transported along `e`, is inverted by
swapping the roles of `L` and `E`. -/
lemma trans_conj_trans_symm (e : L ≃ₐ[ℚ] E) (σ : Gal(L/ℚ)) :
    e.trans ((e.symm.trans (σ.trans e)).trans e.symm) = σ := by
  ext x
  simp only [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]

end Core

section Main

variable {L E : Type*} [Field L] [NumberField L] [Field E] [NumberField E]
  [FiniteDimensional ℚ L] [FiniteDimensional ℚ E] [IsGalois ℚ L] [IsGalois ℚ E]

/-- **Frobenius elements are carried by field isomorphisms.**  If `σ` is a Frobenius at `p` in
`L`, then the conjugate of `σ` by an isomorphism `e : L ≃ₐ[ℚ] E` is a Frobenius at `p` in `E`. -/
lemma isFrobAtPrime_of_algEquiv (e : L ≃ₐ[ℚ] E) (σ : Gal(L/ℚ))
    (p : PrimeIdeal ℚ) (hσ : IsFrobAtPrime (K := ℚ) (L := L) p σ) :
    IsFrobAtPrime (K := ℚ) (L := E) p (e.symm.trans (σ.trans e)) := by
  obtain ⟨P, hP, hPσ⟩ := hσ
  have hprime : (Ideal.map (RingOfIntegers.mapAlgEquiv e) P.asIdeal).IsPrime :=
    Ideal.map_isPrime_of_equiv _
  have hne : Ideal.map (RingOfIntegers.mapAlgEquiv e) P.asIdeal ≠ ⊥ :=
    fun h => P.ne_bot ((Ideal.map_eq_bot_iff_of_injective
      (RingOfIntegers.mapAlgEquiv e).injective).mp h)
  have hlies : (Ideal.map (RingOfIntegers.mapAlgEquiv e) P.asIdeal).LiesOver p.asIdeal :=
    Ideal.map_equiv_liesOver P.asIdeal p.asIdeal (RingOfIntegers.mapAlgEquiv e)
  refine ⟨⟨_, hprime, hne⟩, hlies, ?_⟩
  intro y
  show galRestrict (𝓞 ℚ) ℚ E (𝓞 E) (e.symm.trans (σ.trans e)) y -
      y ^ Nat.card (𝓞 ℚ ⧸ (Ideal.map (RingOfIntegers.mapAlgEquiv e)
        P.asIdeal).under (𝓞 ℚ)) ∈ Ideal.map (RingOfIntegers.mapAlgEquiv e) P.asIdeal
  have hq : Nat.card (𝓞 ℚ ⧸ (Ideal.map (RingOfIntegers.mapAlgEquiv e)
        P.asIdeal).under (𝓞 ℚ)) = Nat.card (𝓞 ℚ ⧸ p.asIdeal) := by
    rw [show (Ideal.map (RingOfIntegers.mapAlgEquiv e)
        P.asIdeal).under (𝓞 ℚ) = p.asIdeal from hlies.over.symm]
  have h := hPσ ((RingOfIntegers.mapAlgEquiv e).symm y)
  rw [show P.asIdeal.under (𝓞 ℚ) = p.asIdeal from hP.over.symm] at h
  rw [hq, mem_map_mapAlgEquiv_iff, map_sub, map_pow, galRestrict_trans_conj_apply,
    AlgEquiv.symm_apply_apply]
  exact h

end Main

theorem IsFrobAtPrimeAlgEquiv {L E : Type*} [Field L] [NumberField L] [Field E] [NumberField E]
    [FiniteDimensional ℚ L] [FiniteDimensional ℚ E]
    [IsGalois ℚ L] [IsGalois ℚ E] (e : L ≃ₐ[ℚ] E) (σ : Gal(L/ℚ))
    (p : NK.Chebotarev.PrimeIdeal ℚ) :
    NK.Chebotarev.IsFrobAtPrime (K := ℚ) (L := L) p σ ↔
      NK.Chebotarev.IsFrobAtPrime (K := ℚ) (L := E) p (e.symm.trans (σ.trans e)) := by
  refine ⟨fun h => isFrobAtPrime_of_algEquiv e σ p h, fun h => ?_⟩
  have h' := isFrobAtPrime_of_algEquiv (e := e.symm) (σ := e.symm.trans (σ.trans e)) p h
  simp only [AlgEquiv.symm_symm] at h'
  rwa [trans_conj_trans_symm e σ] at h'

end NK.Chebotarev
