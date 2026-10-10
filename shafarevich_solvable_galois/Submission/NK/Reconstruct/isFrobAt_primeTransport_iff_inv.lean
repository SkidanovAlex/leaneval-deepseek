import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.NK.Reconstruct.Transport
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Frobenius elements are preserved by the correspondence of primes (inverse direction)

This file proves `NK.Reconstruct.isFrobAt_primeTransport_iff_inv`: for a ring isomorphism
`τ : ↥L₁ ≃+* ↥L₂` of finite levels which is compatible with the base fields
(`MapsBaseLevel L₁ L₂ τ`), and for a prime `P` of `𝓞 L₁`, an element `u` of `Gal(↥L₂/K₂)` is a
Frobenius element at the transported prime `primeTransport τ P` if and only if its conjugate
`conjAlgEquiv τ.symm h.symm u` under `τ⁻¹` is a Frobenius element at `P`.

The proof rests on the following two facts, proved here in the auxiliary namespace
`NK.Reconstruct.PrimeTransportInv`:

* `MapsBaseLevel L₁ L₂ τ` induces a ring isomorphism `K₁ ≃+* K₂` of the base fields, hence an
  isomorphism `𝓞 K₁ ≃+* 𝓞 K₂` of their rings of integers, compatible with the isomorphism
  `𝓞 L₁ ≃+* 𝓞 L₂` induced by `τ` (`ringOfIntegersEquiv_map_transportBase`).  Consequently the
  prime of `𝓞 K₂` below `primeTransport τ P` is the transport of the prime of `𝓞 K₁` below `P`
  (`under_primeTransport_eq_map`), so the two residue cardinalities defining the Frobenius
  condition coincide (`natCard_under_primeTransport`).
* The two Galois actions on the rings of integers are intertwined by `τ`
  (`galRestrict_conjAlgEquiv`).

The Frobenius condition `NK.Chebotarev.IsFrobAt P σ` is then literally transported across
`𝓞 L₁ ≃+* 𝓞 L₂` element by element.
-/

set_option linter.unusedSectionVars false

namespace NK.Reconstruct

open scoped NumberField Pointwise
open NumberField

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
  {L₁ : IntermediateField K₁ K₁'} {L₂ : IntermediateField K₂ K₂'}
  [FiniteDimensional K₁ ↥L₁] [NumberField ↥L₁]
  [FiniteDimensional K₂ ↥L₂] [NumberField ↥L₂]
  {τ : ↥L₁ ≃+* ↥L₂}

/-! ## Elementwise description of `Ideal.map` for a ring equivalence -/

namespace PrimeTransportInv

lemma mem_map_iff {R S : Type*} [Ring R] [Ring S] (e : R ≃+* S) (I : Ideal R) (z : R) :
    e z ∈ Ideal.map e I ↔ z ∈ I := by
  rw [Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨w, hw, hwz⟩
    rwa [e.injective hwz] at hw
  · intro hz
    exact ⟨z, hz, rfl⟩

lemma mem_map_iff_symm_mem {R S : Type*} [Ring R] [Ring S] (e : R ≃+* S) (I : Ideal R)
    (y : S) : y ∈ Ideal.map e I ↔ e.symm y ∈ I := by
  rw [Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨x, hx, hxy⟩
    rwa [← hxy, RingEquiv.symm_apply_apply]
  · intro hy
    exact ⟨e.symm y, hy, e.apply_symm_apply y⟩

/-! ## The isomorphism of base fields induced by a level isomorphism -/

/-- The map `K₁ → K₂` induced by a level isomorphism compatible with the base fields. -/
noncomputable def transportBaseFun (h : MapsBaseLevel L₁ L₂ τ) (a : K₁) : K₂ :=
  Classical.choose (h.1 a)

/-- The inverse of `transportBaseFun`. -/
noncomputable def transportBaseInvFun (h : MapsBaseLevel L₁ L₂ τ) (b : K₂) : K₁ :=
  Classical.choose (h.2 b)

lemma transportBaseFun_spec (h : MapsBaseLevel L₁ L₂ τ) (a : K₁) :
    τ (algebraMap K₁ ↥L₁ a) = algebraMap K₂ ↥L₂ (transportBaseFun h a) :=
  Classical.choose_spec (h.1 a)

lemma transportBaseInvFun_spec (h : MapsBaseLevel L₁ L₂ τ) (b : K₂) :
    τ.symm (algebraMap K₂ ↥L₂ b) = algebraMap K₁ ↥L₁ (transportBaseInvFun h b) :=
  Classical.choose_spec (h.2 b)

lemma transportBaseInvFun_transportBaseFun (h : MapsBaseLevel L₁ L₂ τ) (a : K₁) :
    transportBaseInvFun h (transportBaseFun h a) = a := by
  apply (algebraMap K₁ ↥L₁).injective
  rw [← transportBaseInvFun_spec h (transportBaseFun h a), ← transportBaseFun_spec h a,
    RingEquiv.symm_apply_apply]

lemma transportBaseFun_transportBaseInvFun (h : MapsBaseLevel L₁ L₂ τ) (b : K₂) :
    transportBaseFun h (transportBaseInvFun h b) = b := by
  apply (algebraMap K₂ ↥L₂).injective
  rw [← transportBaseFun_spec h (transportBaseInvFun h b), ← transportBaseInvFun_spec h b,
    RingEquiv.apply_symm_apply]

lemma transportBaseFun_add (h : MapsBaseLevel L₁ L₂ τ) (a b : K₁) :
    transportBaseFun h (a + b) = transportBaseFun h a + transportBaseFun h b := by
  apply (algebraMap K₂ ↥L₂).injective
  rw [map_add, ← transportBaseFun_spec h (a + b)]
  simp only [map_add, transportBaseFun_spec h a, transportBaseFun_spec h b]

lemma transportBaseFun_mul (h : MapsBaseLevel L₁ L₂ τ) (a b : K₁) :
    transportBaseFun h (a * b) = transportBaseFun h a * transportBaseFun h b := by
  apply (algebraMap K₂ ↥L₂).injective
  rw [map_mul, ← transportBaseFun_spec h (a * b)]
  simp only [map_mul, transportBaseFun_spec h a, transportBaseFun_spec h b]

lemma transportBaseFun_one (h : MapsBaseLevel L₁ L₂ τ) : transportBaseFun h 1 = 1 := by
  apply (algebraMap K₂ ↥L₂).injective
  rw [map_one, ← transportBaseFun_spec h 1]
  simp

lemma transportBaseFun_zero (h : MapsBaseLevel L₁ L₂ τ) : transportBaseFun h 0 = 0 := by
  apply (algebraMap K₂ ↥L₂).injective
  rw [map_zero, ← transportBaseFun_spec h 0]
  simp

/-- **The isomorphism of base fields induced by a level isomorphism compatible with the base
fields.** -/
noncomputable def transportBaseEquiv (h : MapsBaseLevel L₁ L₂ τ) : K₁ ≃+* K₂ where
  toFun := transportBaseFun h
  invFun := transportBaseInvFun h
  left_inv := transportBaseInvFun_transportBaseFun h
  right_inv := transportBaseFun_transportBaseInvFun h
  map_mul' := transportBaseFun_mul h
  map_add' := transportBaseFun_add h

lemma transportBaseEquiv_spec (h : MapsBaseLevel L₁ L₂ τ) (a : K₁) :
    τ (algebraMap K₁ ↥L₁ a) = algebraMap K₂ ↥L₂ (transportBaseEquiv h a) :=
  transportBaseFun_spec h a

lemma transportBaseEquiv_symm_spec (h : MapsBaseLevel L₁ L₂ τ) (b : K₂) :
    τ.symm (algebraMap K₂ ↥L₂ b) = algebraMap K₁ ↥L₁ ((transportBaseEquiv h).symm b) :=
  transportBaseInvFun_spec h b

/-! ## Compatibility at the level of rings of integers -/

lemma ringOfIntegersEquiv_eq_mapRingEquiv (e : ↥L₁ ≃+* ↥L₂) :
    ringOfIntegersEquiv e = RingOfIntegers.mapRingEquiv e := by
  ext x
  rw [ringOfIntegersEquiv_apply, RingOfIntegers.mapRingEquiv_apply]

lemma base_coe_apply₁ (x : 𝓞 K₁) :
    ((algebraMap (𝓞 K₁) (𝓞 ↥L₁) x : 𝓞 ↥L₁) : ↥L₁) = algebraMap K₁ ↥L₁ (x : K₁) := rfl

lemma base_coe_apply₂ (y : 𝓞 K₂) :
    ((algebraMap (𝓞 K₂) (𝓞 ↥L₂) y : 𝓞 ↥L₂) : ↥L₂) = algebraMap K₂ ↥L₂ (y : K₂) := rfl

/-- **The isomorphism of rings of integers induced by `τ` is compatible with the induced
isomorphism of the base rings of integers.** -/
lemma ringOfIntegersEquiv_map_transportBase (h : MapsBaseLevel L₁ L₂ τ) (x : 𝓞 K₁) :
    ringOfIntegersEquiv τ (algebraMap (𝓞 K₁) (𝓞 ↥L₁) x) =
      algebraMap (𝓞 K₂) (𝓞 ↥L₂) (RingOfIntegers.mapRingEquiv (transportBaseEquiv h) x) := by
  apply RingOfIntegers.ext
  rw [ringOfIntegersEquiv_apply, base_coe_apply₁, base_coe_apply₂,
    RingOfIntegers.mapRingEquiv_apply, ← transportBaseEquiv_spec h (x : K₁)]

lemma ringOfIntegersEquiv_symm_map_transportBase (h : MapsBaseLevel L₁ L₂ τ) (x : 𝓞 K₂) :
    (ringOfIntegersEquiv τ).symm (algebraMap (𝓞 K₂) (𝓞 ↥L₂) x) =
      algebraMap (𝓞 K₁) (𝓞 ↥L₁)
        ((RingOfIntegers.mapRingEquiv (transportBaseEquiv h)).symm x) := by
  have hkey := ringOfIntegersEquiv_map_transportBase h
    ((RingOfIntegers.mapRingEquiv (transportBaseEquiv h)).symm x)
  rw [RingEquiv.apply_symm_apply] at hkey
  rw [← hkey, RingEquiv.symm_apply_apply]

/-! ## The prime correspondence -/

lemma primeTransport_asIdeal (P : NK.Chebotarev.PrimeIdeal ↥L₁) :
    (primeTransport τ P).asIdeal = Ideal.map (ringOfIntegersEquiv τ) P.asIdeal := rfl

/-- **The prime of `𝓞 K₂` below the transported prime is the transport of the prime of `𝓞 K₁`
below `P`.** -/
lemma under_primeTransport_eq_map (h : MapsBaseLevel L₁ L₂ τ)
    (P : NK.Chebotarev.PrimeIdeal ↥L₁) :
    (primeTransport τ P).asIdeal.under (𝓞 K₂) =
      Ideal.map (RingOfIntegers.mapRingEquiv (transportBaseEquiv h)) (P.asIdeal.under (𝓞 K₁)) := by
  ext x
  rw [Ideal.under_def, Ideal.mem_comap, primeTransport_asIdeal, mem_map_iff_symm_mem,
    ringOfIntegersEquiv_symm_map_transportBase h x]
  exact (mem_map_iff_symm_mem (RingOfIntegers.mapRingEquiv (transportBaseEquiv h))
    (P.asIdeal.under (𝓞 K₁)) x).symm

/-- **The residue cardinality defining the Frobenius condition is preserved by the transport of
primes.** -/
lemma natCard_under_primeTransport (h : MapsBaseLevel L₁ L₂ τ)
    (P : NK.Chebotarev.PrimeIdeal ↥L₁) :
    Nat.card (𝓞 K₂ ⧸ (primeTransport τ P).asIdeal.under (𝓞 K₂)) =
      Nat.card (𝓞 K₁ ⧸ P.asIdeal.under (𝓞 K₁)) := by
  rw [under_primeTransport_eq_map h P]
  exact (Nat.card_congr (Ideal.quotientEquiv (P.asIdeal.under (𝓞 K₁))
    (Ideal.map (RingOfIntegers.mapRingEquiv (transportBaseEquiv h)) (P.asIdeal.under (𝓞 K₁)))
    (RingOfIntegers.mapRingEquiv (transportBaseEquiv h)) rfl)).symm

/-! ## The intertwining of the Galois actions on the rings of integers -/

/-- **Conjugation by `τ` intertwines the two Galois actions on the rings of integers.** -/
lemma galRestrict_conjAlgEquiv (h : MapsBaseLevel L₁ L₂ τ) (u : Gal(↥L₂/K₂)) (x : 𝓞 ↥L₁) :
    ringOfIntegersEquiv τ
        (galRestrict (𝓞 K₁) K₁ (↥L₁) (𝓞 ↥L₁) (conjAlgEquiv τ.symm h.symm u) x) =
      galRestrict (𝓞 K₂) K₂ (↥L₂) (𝓞 ↥L₂) u (ringOfIntegersEquiv τ x) := by
  apply RingOfIntegers.ext
  simp only [ringOfIntegersEquiv_apply, algebraMap_galRestrict_apply, conjAlgEquiv_apply,
    RingEquiv.symm_symm, RingEquiv.apply_symm_apply]

end PrimeTransportInv

/-- **Frobenius elements and the correspondence of primes, inverse direction.**  For a ring
isomorphism `τ : ↥L₁ ≃+* ↥L₂` of finite levels compatible with the base fields, an element `u`
of `Gal(↥L₂/K₂)` is a Frobenius element at the prime `primeTransport τ P` transported from `P` if
and only if its conjugate `τ⁻¹ u τ` is a Frobenius element at `P`. -/
theorem isFrobAt_primeTransport_iff_inv {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂]
    [Field K₁'] [Field K₂'] [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂'] {L₁ : IntermediateField K₁ K₁'}
    {L₂ : IntermediateField K₂ K₂'} [FiniteDimensional K₁ ↥L₁] [NumberField ↥L₁]
    [FiniteDimensional K₂ ↥L₂] [NumberField ↥L₂] {τ : ↥L₁ ≃+* ↥L₂}
    (h : NK.Reconstruct.MapsBaseLevel L₁ L₂ τ) (u : Gal(↥L₂/K₂))
    (P : NK.Chebotarev.PrimeIdeal ↥L₁) :
    NK.Chebotarev.IsFrobAt (NK.Reconstruct.primeTransport τ P) u ↔
      NK.Chebotarev.IsFrobAt P (NK.Reconstruct.conjAlgEquiv τ.symm h.symm u) := by
  rw [NK.Chebotarev.isFrobAt_def, NK.Chebotarev.isFrobAt_def]
  constructor
  · intro hL x
    have hx := hL (ringOfIntegersEquiv τ x)
    rw [PrimeTransportInv.primeTransport_asIdeal] at hx
    refine (PrimeTransportInv.mem_map_iff (ringOfIntegersEquiv τ) P.asIdeal
      (galRestrict (𝓞 K₁) K₁ (↥L₁) (𝓞 ↥L₁) (conjAlgEquiv τ.symm h.symm u) x -
        x ^ Nat.card (𝓞 K₁ ⧸ P.asIdeal.under (𝓞 K₁)))).mp ?_
    rw [map_sub, map_pow, PrimeTransportInv.galRestrict_conjAlgEquiv h u x,
      ← PrimeTransportInv.natCard_under_primeTransport h P]
    exact hx
  · intro hR y
    have hx := hR ((ringOfIntegersEquiv τ).symm y)
    have key : ringOfIntegersEquiv τ
          (galRestrict (𝓞 K₁) K₁ (↥L₁) (𝓞 ↥L₁) (conjAlgEquiv τ.symm h.symm u)
              ((ringOfIntegersEquiv τ).symm y) -
            ((ringOfIntegersEquiv τ).symm y) ^
              Nat.card (𝓞 K₁ ⧸ P.asIdeal.under (𝓞 K₁))) =
        galRestrict (𝓞 K₂) K₂ (↥L₂) (𝓞 ↥L₂) u y -
          y ^ Nat.card (𝓞 K₂ ⧸ (primeTransport τ P).asIdeal.under (𝓞 K₂)) := by
      rw [map_sub, map_pow, PrimeTransportInv.galRestrict_conjAlgEquiv h u
          ((ringOfIntegersEquiv τ).symm y), RingEquiv.apply_symm_apply,
        PrimeTransportInv.natCard_under_primeTransport h P]
    rw [← key, PrimeTransportInv.primeTransport_asIdeal]
    exact (PrimeTransportInv.mem_map_iff (ringOfIntegersEquiv τ) P.asIdeal
      (galRestrict (𝓞 K₁) K₁ (↥L₁) (𝓞 ↥L₁) (conjAlgEquiv τ.symm h.symm u)
          ((ringOfIntegersEquiv τ).symm y) -
        ((ringOfIntegersEquiv τ).symm y) ^
          Nat.card (𝓞 K₁ ⧸ P.asIdeal.under (𝓞 K₁)))).mpr hx

end NK.Reconstruct
