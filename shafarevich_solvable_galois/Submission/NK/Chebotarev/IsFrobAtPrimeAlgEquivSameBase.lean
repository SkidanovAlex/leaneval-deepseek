import Mathlib
import Submission.NK.Chebotarev.Basic
import Submission.NK.Chebotarev.IsFrobAtPrimeAlgEquiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Frobenius elements are compatible with isomorphisms over a common base

Let `L₁` and `L₂` be finite Galois extensions of the *same* number field `K`, and let
`e : L₁ ≃ₐ[K] L₂` be a `K`-algebra isomorphism.  Then `e` transports Frobenius elements:
`σ : Gal(L₁/K)` is a Frobenius at a prime `p` of `K` if and only if the conjugate
`e⁻¹ σ e` is a Frobenius at `p` in `L₂`.

This is the common-base version of `NK.Chebotarev.IsFrobAtPrimeAlgEquiv` (which treats
`K = ℚ`).  The proof transports primes along the induced isomorphism `𝓞 L₁ ≃+* 𝓞 L₂` of rings
of integers, intertwining the actions of the two Galois groups on the rings of integers.
-/

set_option linter.unusedSectionVars false

open scoped NumberField
open NumberField
open IsDedekindDomain

namespace NK.Chebotarev

section Core

variable {K L E : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Field E]
  [NumberField E] [Algebra K L] [Algebra K E]

/-- The restriction of a `K`-algebra isomorphism of number fields to the rings of integers,
evaluated in the ambient fields. -/
lemma algebraMap_mapAlgEquiv_gen (e : L ≃ₐ[K] E) (z : 𝓞 L) :
    (algebraMap (𝓞 E) E) (RingOfIntegers.mapAlgEquiv e z) = e ((algebraMap (𝓞 L) L) z) :=
  RingOfIntegers.mapRingHom_apply _ z

/-- The inverse of the restricted isomorphism of rings of integers, evaluated in the ambient
fields. -/
lemma algebraMap_mapAlgEquiv_symm_gen (e : L ≃ₐ[K] E) (z : 𝓞 E) :
    (algebraMap (𝓞 L) L) ((RingOfIntegers.mapAlgEquiv e).symm z)
      = e.symm ((algebraMap (𝓞 E) E) z) := by
  rw [show (RingOfIntegers.mapAlgEquiv e).symm = RingOfIntegers.mapAlgEquiv e.symm from rfl,
    algebraMap_mapAlgEquiv_gen e.symm z]

/-- **Conjugation by an isomorphism of fields intertwines the actions of the Galois groups on the
rings of integers.** -/
lemma galRestrict_trans_conj_apply_gen (e : L ≃ₐ[K] E) (σ : Gal(L/K)) (y : 𝓞 E) :
    galRestrict (𝓞 K) K E (𝓞 E) (e.symm.trans (σ.trans e)) y
      = (RingOfIntegers.mapAlgEquiv e)
          ((galRestrict (𝓞 K) K L (𝓞 L) σ) ((RingOfIntegers.mapAlgEquiv e).symm y)) := by
  apply RingOfIntegers.coe_injective
  simp only [algebraMap_galRestrict_apply, AlgEquiv.trans_apply, algebraMap_mapAlgEquiv_gen,
    algebraMap_mapAlgEquiv_symm_gen]

/-- Membership in the image of an ideal under the isomorphism of rings of integers induced by a
`K`-algebra isomorphism of number fields. -/
lemma mem_map_mapAlgEquiv_iff_gen (e : L ≃ₐ[K] E) (I : Ideal (𝓞 L)) (z : 𝓞 E) :
    z ∈ Ideal.map (RingOfIntegers.mapAlgEquiv e) I ↔
      (RingOfIntegers.mapAlgEquiv e).symm z ∈ I := by
  rw [Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨x, hx, hxz⟩
    rw [← hxz, AlgEquiv.symm_apply_apply]
    exact hx
  · rintro hz
    exact ⟨_, hz, (RingOfIntegers.mapAlgEquiv e).apply_symm_apply z⟩

/-- The conjugation action of `Gal(E/K)` on itself, transported along `e`, is inverted by
swapping the roles of `L` and `E`. -/
lemma trans_conj_trans_symm_gen (e : L ≃ₐ[K] E) (σ : Gal(L/K)) :
    e.trans ((e.symm.trans (σ.trans e)).trans e.symm) = σ := by
  ext x
  simp only [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]

end Core

section Main

variable {K L E : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Field E]
  [NumberField E] [Algebra K L] [Algebra K E] [FiniteDimensional K L]
  [FiniteDimensional K E] [IsGalois K L] [IsGalois K E]

/-- **Frobenius elements are carried by field isomorphisms.**  If `σ` is a Frobenius at `p` in
`L`, then the conjugate of `σ` by a `K`-algebra isomorphism `e : L ≃ₐ[K] E` is a Frobenius at `p`
in `E`. -/
lemma isFrobAtPrime_of_algEquiv_gen (e : L ≃ₐ[K] E) (σ : Gal(L/K))
    (p : PrimeIdeal K) (hσ : IsFrobAtPrime (K := K) (L := L) p σ) :
    IsFrobAtPrime (K := K) (L := E) p (e.symm.trans (σ.trans e)) := by
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
  show galRestrict (𝓞 K) K E (𝓞 E) (e.symm.trans (σ.trans e)) y -
      y ^ Nat.card (𝓞 K ⧸ (Ideal.map (RingOfIntegers.mapAlgEquiv e)
        P.asIdeal).under (𝓞 K)) ∈ Ideal.map (RingOfIntegers.mapAlgEquiv e) P.asIdeal
  have hq : Nat.card (𝓞 K ⧸ (Ideal.map (RingOfIntegers.mapAlgEquiv e)
        P.asIdeal).under (𝓞 K)) = Nat.card (𝓞 K ⧸ p.asIdeal) := by
    rw [show (Ideal.map (RingOfIntegers.mapAlgEquiv e)
        P.asIdeal).under (𝓞 K) = p.asIdeal from hlies.over.symm]
  have h := hPσ ((RingOfIntegers.mapAlgEquiv e).symm y)
  rw [show P.asIdeal.under (𝓞 K) = p.asIdeal from hP.over.symm] at h
  rw [hq, mem_map_mapAlgEquiv_iff_gen, map_sub, map_pow, galRestrict_trans_conj_apply_gen,
    AlgEquiv.symm_apply_apply]
  exact h

end Main

/-- **Frobenius elements are compatible with isomorphisms of Galois extensions of a common base
field.** -/
theorem IsFrobAtPrimeAlgEquivSameBase {K L₁ L₂ : Type*} [Field K] [NumberField K] [Field L₁]
    [NumberField L₁] [Field L₂] [NumberField L₂] [Algebra K L₁] [Algebra K L₂]
    [FiniteDimensional K L₁] [FiniteDimensional K L₂] [IsGalois K L₁] [IsGalois K L₂]
    (e : L₁ ≃ₐ[K] L₂) (σ : Gal(L₁/K)) (p : NK.Chebotarev.PrimeIdeal K) :
    NK.Chebotarev.IsFrobAtPrime (K := K) (L := L₁) p σ ↔
      NK.Chebotarev.IsFrobAtPrime (K := K) (L := L₂) p (e.symm.trans (σ.trans e)) := by
  refine ⟨fun h => isFrobAtPrime_of_algEquiv_gen e σ p h, fun h => ?_⟩
  have h' := isFrobAtPrime_of_algEquiv_gen (e := e.symm)
    (σ := e.symm.trans (σ.trans e)) p h
  simp only [AlgEquiv.symm_symm] at h'
  rwa [trans_conj_trans_symm_gen e σ] at h'

end NK.Chebotarev
