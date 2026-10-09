import Mathlib
import Submission.NK.Reconstruct.Transport
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Frobenius elements are preserved by the transport of primes along a level isomorphism

This file proves `NK.Reconstruct.isFrobAt_primeTransport_iff`: for a ring isomorphism
`τ : ↥L₁ ≃+* ↥L₂` of two finite levels of the separable closures `K₁'`/`K₁` and `K₂'`/`K₂`
which is compatible with the base fields (`MapsBaseLevel L₁ L₂ τ`), an element
`d : Gal(↥L₁/K₁)` is an arithmetic Frobenius at a prime `P` of `𝓞 L₁` if and only if its
conjugate `τ d τ⁻¹` is an arithmetic Frobenius at the transported prime
`primeTransport τ P` of `𝓞 L₂`.

The mathematical content is the residue-field computation: `τ` identifies the residue field
`𝓞 L₁ ⧸ P` with `𝓞 L₂ ⧸ τP` and, by compatibility with the base fields, the residue field of
the prime `P ∩ 𝓞 K₁` below `P` with that of its counterpart below `τP`; hence the Frobenius
congruence `σ x ≡ x ^ #(𝓞 K₁ ⧸ P ∩ 𝓞 K₁) (mod P)` is transported verbatim.

The base-field compatibility `MapsBaseLevel L₁ L₂ τ` is used twice: once to conjugate the Galois
automorphism (`NK.Reconstruct.conjAlgEquiv`, already in `Transport.lean`) and once to build the
ring isomorphism `𝓞 K₁ ≃+* 𝓞 K₂` of the two *base* rings of integers which matches the two
Frobenius exponents.

Everything below is proved from scratch; nothing is assumed.
-/

set_option linter.unusedSectionVars false

namespace NK.Reconstruct

open NumberField

section Aux

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
  {L₁ : IntermediateField K₁ K₁'} {L₂ : IntermediateField K₂ K₂'}
  [FiniteDimensional K₁ ↥L₁] [NumberField ↥L₁]
  [FiniteDimensional K₂ ↥L₂] [NumberField ↥L₂]

/-! ## The isomorphism of base fields induced by a level isomorphism

`MapsBaseLevel L₁ L₂ τ` says that `τ` carries the embedded copy of `K₁` into the embedded copy
of `K₂` and vice versa.  Because both embeddings are injective we may define the induced ring
homomorphism, and (using the reverse direction) it is a ring isomorphism. -/

/-- **The ring homomorphism `K₁ →+* K₂` induced by a base-level-compatible isomorphism of
levels.**  It is defined by transporting along `τ`: `baseHom h a` is the (unique) element whose
image in `↥L₂` is the image of `algebraMap K₁ ↥L₁ a` under `τ`. -/
private noncomputable def baseHom {τ : ↥L₁ ≃+* ↥L₂} (h : MapsBaseLevel L₁ L₂ τ) : K₁ →+* K₂ where
  toFun a := Classical.choose (h.1 a)
  map_one' := by
    refine FaithfulSMul.algebraMap_injective K₂ ↥L₂ ?_
    rw [← Classical.choose_spec (h.1 1)]
    simp
  map_zero' := by
    refine FaithfulSMul.algebraMap_injective K₂ ↥L₂ ?_
    rw [← Classical.choose_spec (h.1 0)]
    simp
  map_add' a b := by
    refine FaithfulSMul.algebraMap_injective K₂ ↥L₂ ?_
    calc (algebraMap K₂ ↥L₂) (Classical.choose (h.1 (a + b)))
        = τ ((algebraMap K₁ ↥L₁) (a + b)) := (Classical.choose_spec (h.1 (a + b))).symm
      _ = τ ((algebraMap K₁ ↥L₁) a + (algebraMap K₁ ↥L₁) b) := by rw [map_add]
      _ = τ ((algebraMap K₁ ↥L₁) a) + τ ((algebraMap K₁ ↥L₁) b) := by rw [map_add]
      _ = (algebraMap K₂ ↥L₂) (Classical.choose (h.1 a))
            + (algebraMap K₂ ↥L₂) (Classical.choose (h.1 b)) := by
            rw [← Classical.choose_spec (h.1 a), ← Classical.choose_spec (h.1 b)]
      _ = (algebraMap K₂ ↥L₂) (Classical.choose (h.1 a) + Classical.choose (h.1 b)) := by
            rw [map_add]
  map_mul' a b := by
    refine FaithfulSMul.algebraMap_injective K₂ ↥L₂ ?_
    calc (algebraMap K₂ ↥L₂) (Classical.choose (h.1 (a * b)))
        = τ ((algebraMap K₁ ↥L₁) (a * b)) := (Classical.choose_spec (h.1 (a * b))).symm
      _ = τ ((algebraMap K₁ ↥L₁) a * (algebraMap K₁ ↥L₁) b) := by rw [map_mul]
      _ = τ ((algebraMap K₁ ↥L₁) a) * τ ((algebraMap K₁ ↥L₁) b) := by rw [map_mul]
      _ = (algebraMap K₂ ↥L₂) (Classical.choose (h.1 a))
            * (algebraMap K₂ ↥L₂) (Classical.choose (h.1 b)) := by
            rw [← Classical.choose_spec (h.1 a), ← Classical.choose_spec (h.1 b)]
      _ = (algebraMap K₂ ↥L₂) (Classical.choose (h.1 a) * Classical.choose (h.1 b)) := by
            rw [map_mul]

/-- The defining property of `baseHom`: it is intertwined by `τ` with the two embeddings of the
base fields. -/
private lemma baseHom_spec {τ : ↥L₁ ≃+* ↥L₂} (h : MapsBaseLevel L₁ L₂ τ) (a : K₁) :
    τ (algebraMap K₁ ↥L₁ a) = algebraMap K₂ ↥L₂ (baseHom h a) :=
  Classical.choose_spec (h.1 a)

/-- **The inverse direction** of the induced base-field map, from the second half of
`MapsBaseLevel`. -/
private noncomputable def baseHomSymm {τ : ↥L₁ ≃+* ↥L₂} (h : MapsBaseLevel L₁ L₂ τ) : K₂ →+* K₁ where
  toFun b := Classical.choose (h.2 b)
  map_one' := by
    refine FaithfulSMul.algebraMap_injective K₁ ↥L₁ ?_
    rw [← Classical.choose_spec (h.2 1)]
    simp
  map_zero' := by
    refine FaithfulSMul.algebraMap_injective K₁ ↥L₁ ?_
    rw [← Classical.choose_spec (h.2 0)]
    simp
  map_add' a b := by
    refine FaithfulSMul.algebraMap_injective K₁ ↥L₁ ?_
    calc (algebraMap K₁ ↥L₁) (Classical.choose (h.2 (a + b)))
        = τ.symm ((algebraMap K₂ ↥L₂) (a + b)) := (Classical.choose_spec (h.2 (a + b))).symm
      _ = τ.symm ((algebraMap K₂ ↥L₂) a + (algebraMap K₂ ↥L₂) b) := by rw [map_add]
      _ = τ.symm ((algebraMap K₂ ↥L₂) a) + τ.symm ((algebraMap K₂ ↥L₂) b) := by rw [map_add]
      _ = (algebraMap K₁ ↥L₁) (Classical.choose (h.2 a))
            + (algebraMap K₁ ↥L₁) (Classical.choose (h.2 b)) := by
            rw [← Classical.choose_spec (h.2 a), ← Classical.choose_spec (h.2 b)]
      _ = (algebraMap K₁ ↥L₁) (Classical.choose (h.2 a) + Classical.choose (h.2 b)) := by
            rw [map_add]
  map_mul' a b := by
    refine FaithfulSMul.algebraMap_injective K₁ ↥L₁ ?_
    calc (algebraMap K₁ ↥L₁) (Classical.choose (h.2 (a * b)))
        = τ.symm ((algebraMap K₂ ↥L₂) (a * b)) := (Classical.choose_spec (h.2 (a * b))).symm
      _ = τ.symm ((algebraMap K₂ ↥L₂) a * (algebraMap K₂ ↥L₂) b) := by rw [map_mul]
      _ = τ.symm ((algebraMap K₂ ↥L₂) a) * τ.symm ((algebraMap K₂ ↥L₂) b) := by rw [map_mul]
      _ = (algebraMap K₁ ↥L₁) (Classical.choose (h.2 a))
            * (algebraMap K₁ ↥L₁) (Classical.choose (h.2 b)) := by
            rw [← Classical.choose_spec (h.2 a), ← Classical.choose_spec (h.2 b)]
      _ = (algebraMap K₁ ↥L₁) (Classical.choose (h.2 a) * Classical.choose (h.2 b)) := by
            rw [map_mul]

/-- The defining property of `baseHomSymm`. -/
private lemma baseHomSymm_spec {τ : ↥L₁ ≃+* ↥L₂} (h : MapsBaseLevel L₁ L₂ τ) (b : K₂) :
    τ.symm (algebraMap K₂ ↥L₂ b) = algebraMap K₁ ↥L₁ (baseHomSymm h b) :=
  Classical.choose_spec (h.2 b)

/-- **The ring isomorphism `K₁ ≃+* K₂` of base fields induced by a base-level-compatible
isomorphism of levels.** -/
private noncomputable def baseEquiv {τ : ↥L₁ ≃+* ↥L₂} (h : MapsBaseLevel L₁ L₂ τ) : K₁ ≃+* K₂ where
  toFun := baseHom h
  invFun := baseHomSymm h
  left_inv a := by
    refine FaithfulSMul.algebraMap_injective K₁ ↥L₁ ?_
    calc (algebraMap K₁ ↥L₁) (baseHomSymm h (baseHom h a))
        = τ.symm ((algebraMap K₂ ↥L₂) (baseHom h a)) := (baseHomSymm_spec h (baseHom h a)).symm
      _ = τ.symm (τ ((algebraMap K₁ ↥L₁) a)) := by rw [baseHom_spec h a]
      _ = (algebraMap K₁ ↥L₁) a := by rw [RingEquiv.symm_apply_apply]
  right_inv b := by
    refine FaithfulSMul.algebraMap_injective K₂ ↥L₂ ?_
    calc (algebraMap K₂ ↥L₂) (baseHom h (baseHomSymm h b))
        = τ ((algebraMap K₁ ↥L₁) (baseHomSymm h b)) := (baseHom_spec h (baseHomSymm h b)).symm
      _ = τ (τ.symm ((algebraMap K₂ ↥L₂) b)) := by rw [baseHomSymm_spec h b]
      _ = (algebraMap K₂ ↥L₂) b := by rw [RingEquiv.apply_symm_apply]
  map_mul' := (baseHom h).map_mul
  map_add' := (baseHom h).map_add

/-! ## The induced isomorphism of the two base rings of integers -/

/-- The coercion of `algebraMap (𝓞 K) (𝓞 L) x` back to `L` is `algebraMap K L (x : K)`. -/
private lemma coe_algebraMap_ringOfIntegers {K L : Type*} [Field K] [Field L] [Algebra K L]
    (x : 𝓞 K) : ((algebraMap (𝓞 K) (𝓞 L) x : 𝓞 L) : L) = algebraMap K L (x : K) := by
  change ((RingOfIntegers.mapRingHom (algebraMap K L) x : 𝓞 L) : L) = _
  rw [RingOfIntegers.mapRingHom_apply]

/-- **Compatibility of the two induced maps**: the isomorphism `𝓞 L₁ ≃+* 𝓞 L₂` induced by `τ`
intertwines the two embeddings of the base rings of integers coming from the base-field
isomorphism `baseEquiv h`. -/
private lemma ringOfIntegersEquiv_algebraMap_baseEquiv {τ : ↥L₁ ≃+* ↥L₂} (h : MapsBaseLevel L₁ L₂ τ)
    (x : 𝓞 K₁) :
    ringOfIntegersEquiv τ (algebraMap (𝓞 K₁) (𝓞 ↥L₁) x)
      = algebraMap (𝓞 K₂) (𝓞 ↥L₂) (RingOfIntegers.mapRingEquiv (baseEquiv h) x) := by
  apply RingOfIntegers.ext
  rw [ringOfIntegersEquiv_apply]
  rw [coe_algebraMap_ringOfIntegers x]
  rw [coe_algebraMap_ringOfIntegers (RingOfIntegers.mapRingEquiv (baseEquiv h) x)]
  rw [RingOfIntegers.mapRingEquiv_apply]
  exact baseHom_spec h (x : K₁)

/-! ## Transport of primes and of Frobenius elements -/

/-- **Membership in the transported prime.**  For a level isomorphism `τ : ↥L₁ ≃+* ↥L₂`, the
prime `primeTransport τ P` of `𝓞 L₂` is the image of `P` under the induced isomorphism of rings
of integers, so `z` lies in `P` exactly when `τ z` lies in `primeTransport τ P`. -/
private lemma mem_primeTransport_iff {τ : ↥L₁ ≃+* ↥L₂} (P : NK.Chebotarev.PrimeIdeal ↥L₁)
    (z : 𝓞 ↥L₁) :
    ringOfIntegersEquiv τ z ∈ (primeTransport τ P).asIdeal ↔ z ∈ P.asIdeal := by
  show ringOfIntegersEquiv τ z ∈ Ideal.map (ringOfIntegersEquiv τ) P.asIdeal ↔ z ∈ P.asIdeal
  rw [Ideal.mem_map_iff_of_surjective _ (ringOfIntegersEquiv τ).surjective]
  constructor
  · rintro ⟨w, hw, hwz⟩
    rw [(ringOfIntegersEquiv τ).injective hwz] at hw
    exact hw
  · intro hz; exact ⟨z, hz, rfl⟩

/-- **The prime below the transported prime is the transport of the prime below.**  The base
rings of integers correspond through `baseEquiv h`, hence so do their prime ideals. -/
private lemma map_baseEquiv_under {τ : ↥L₁ ≃+* ↥L₂} (h : MapsBaseLevel L₁ L₂ τ)
    (P : NK.Chebotarev.PrimeIdeal ↥L₁) :
    Ideal.map (RingOfIntegers.mapRingEquiv (baseEquiv h)) (P.asIdeal.under (𝓞 K₁))
      = (primeTransport τ P).asIdeal.under (𝓞 K₂) := by
  let e₀ : 𝓞 K₁ ≃+* 𝓞 K₂ := RingOfIntegers.mapRingEquiv (baseEquiv h)
  have hkey : ∀ z : 𝓞 K₁,
      algebraMap (𝓞 K₂) (𝓞 ↥L₂) (e₀ z) ∈ (primeTransport τ P).asIdeal
        ↔ algebraMap (𝓞 K₁) (𝓞 ↥L₁) z ∈ P.asIdeal := by
    intro z
    rw [← ringOfIntegersEquiv_algebraMap_baseEquiv h z]
    exact mem_primeTransport_iff P _
  have hmem : ∀ y : 𝓞 K₂,
      (∃ x ∈ P.asIdeal.under (𝓞 K₁), e₀ x = y) ↔ (e₀.symm y ∈ P.asIdeal.under (𝓞 K₁)) := by
    intro y; constructor
    · rintro ⟨x, hx, hxeq⟩
      have hxy : x = e₀.symm y := by rw [← hxeq]; simp
      rwa [hxy] at hx
    · intro hy; exact ⟨e₀.symm y, hy, e₀.apply_symm_apply y⟩
  refine Ideal.ext fun y => ?_
  rw [Ideal.mem_map_iff_of_surjective _ e₀.surjective, hmem y, Ideal.mem_under, Ideal.mem_under,
    ← hkey (e₀.symm y)]
  simp

/-- **The two Frobenius exponents agree.**  The cardinality of the residue field of `P` over the
base field `K₁` equals that of the residue field of the transported prime over `K₂`. -/
private lemma natCard_residue_eq {τ : ↥L₁ ≃+* ↥L₂} (h : MapsBaseLevel L₁ L₂ τ)
    (P : NK.Chebotarev.PrimeIdeal ↥L₁) :
    Nat.card (𝓞 K₁ ⧸ P.asIdeal.under (𝓞 K₁))
      = Nat.card (𝓞 K₂ ⧸ (primeTransport τ P).asIdeal.under (𝓞 K₂)) := by
  refine Nat.card_congr ?_
  exact (Ideal.quotientEquiv (P.asIdeal.under (𝓞 K₁)) ((primeTransport τ P).asIdeal.under (𝓞 K₂))
    (RingOfIntegers.mapRingEquiv (baseEquiv h)) (map_baseEquiv_under h P).symm).toEquiv

/-- **Transport of the Galois action on rings of integers.**  The isomorphism of rings of integers
induced by `τ` intertwines `galRestrict d` with `galRestrict (τ d τ⁻¹)`. -/
private lemma galRestrict_ringOfIntegersEquiv {τ : ↥L₁ ≃+* ↥L₂} (h : MapsBaseLevel L₁ L₂ τ)
    (d : Gal(↥L₁/K₁)) (x : 𝓞 ↥L₁) :
    ringOfIntegersEquiv τ (galRestrict (𝓞 K₁) K₁ ↥L₁ (𝓞 ↥L₁) d x)
      = galRestrict (𝓞 K₂) K₂ ↥L₂ (𝓞 ↥L₂) (conjAlgEquiv τ h d) (ringOfIntegersEquiv τ x) := by
  apply RingOfIntegers.ext
  rw [ringOfIntegersEquiv_apply]
  change τ (algebraMap (𝓞 ↥L₁) ↥L₁ ((galRestrict (𝓞 K₁) K₁ ↥L₁ (𝓞 ↥L₁)) d x))
      = algebraMap (𝓞 ↥L₂) ↥L₂ ((galRestrict (𝓞 K₂) K₂ ↥L₂ (𝓞 ↥L₂))
          (conjAlgEquiv τ h d) ((ringOfIntegersEquiv τ) x))
  rw [algebraMap_galRestrict_apply, algebraMap_galRestrict_apply]
  rw [conjAlgEquiv_apply]
  rw [← RingOfIntegers.coe_eq_algebraMap (ringOfIntegersEquiv τ x)]
  rw [ringOfIntegersEquiv_apply]
  rw [RingEquiv.symm_apply_apply]

end Aux

/-! ## The main statement -/

theorem isFrobAt_primeTransport_iff {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁']
    [Field K₂'] [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂'] {L₁ : IntermediateField K₁ K₁'}
    {L₂ : IntermediateField K₂ K₂'} [FiniteDimensional K₁ ↥L₁] [NumberField ↥L₁]
    [FiniteDimensional K₂ ↥L₂] [NumberField ↥L₂] {τ : ↥L₁ ≃+* ↥L₂}
    (h : NK.Reconstruct.MapsBaseLevel L₁ L₂ τ) (d : Gal(↥L₁/K₁))
    (P : NK.Chebotarev.PrimeIdeal ↥L₁) :
    NK.Chebotarev.IsFrobAt P d ↔
      NK.Chebotarev.IsFrobAt (NK.Reconstruct.primeTransport τ P)
        (NK.Reconstruct.conjAlgEquiv τ h d) := by
  rw [NK.Chebotarev.isFrobAt_def, NK.Chebotarev.isFrobAt_def]
  have hcard := natCard_residue_eq h P
  constructor
  · intro hd y
    have h3 := (mem_primeTransport_iff (τ := τ) P _).mpr (hd ((ringOfIntegersEquiv τ).symm y))
    rw [← hcard]
    simpa only [map_sub, map_pow, galRestrict_ringOfIntegersEquiv h d,
      RingEquiv.apply_symm_apply] using h3
  · intro hd x
    have h3 : ringOfIntegersEquiv τ
        (galRestrict (𝓞 K₁) K₁ ↥L₁ (𝓞 ↥L₁) d x
          - x ^ Nat.card (𝓞 K₂ ⧸ (primeTransport τ P).asIdeal.under (𝓞 K₂)))
        ∈ (primeTransport τ P).asIdeal := by
      simpa only [map_sub, map_pow, galRestrict_ringOfIntegersEquiv h d]
        using hd (ringOfIntegersEquiv τ x)
    have h4 := (mem_primeTransport_iff (τ := τ) P _).mp h3
    rw [← hcard] at h4
    exact h4

end NK.Reconstruct
