/-
Transport of places and local fields along an isomorphism of number fields.

For `e : L ≃ₐ[K] L'` (an isomorphism of `K`-algebras) we construct the induced
equivalence `Place.congr e : Place L ≃ Place L'` of places, and record its
compatibility with the Galois actions: the transport of places is equivariant
for the isomorphism `AlgEquiv.autCongr e : Gal(L/K) ≃* Gal(L'/K)`.
-/
import Mathlib
import Submission.NK.GlobalCFT.GaloisIdelesAction
import Submission.NK.GlobalCFT.GaloisIdeles

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFT

namespace Place

variable {K L L' : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Field L']
  [NumberField L'] [Algebra K L] [Algebra K L']

/-- The equivalence of infinite places attached to a `K`-algebra isomorphism `e : L ≃ₐ[K] L'`:
the place `w` is sent to the place `x ↦ w (e⁻¹ x)` of `L'`. -/
noncomputable def congrInf (e : L ≃ₐ[K] L') : InfinitePlace L ≃ InfinitePlace L' where
  toFun w := w.comap e.symm.toRingHom
  invFun w := w.comap e.toRingHom
  left_inv w := by
    show InfinitePlace.comap (InfinitePlace.comap w e.symm.toRingEquiv.toRingHom)
      e.toRingEquiv.toRingHom = w
    rw [← InfinitePlace.mk_embedding w]
    simp only [InfinitePlace.comap_mk]
    congr 1
    ext x
    simp
  right_inv w := by
    show InfinitePlace.comap (InfinitePlace.comap w e.toRingEquiv.toRingHom)
      e.symm.toRingEquiv.toRingHom = w
    rw [← InfinitePlace.mk_embedding w]
    simp only [InfinitePlace.comap_mk]
    congr 1
    ext x
    simp

@[simp] theorem congrInf_apply (e : L ≃ₐ[K] L') (w : InfinitePlace L) :
    congrInf e w = w.comap e.symm.toRingHom := rfl

@[simp] theorem congrInf_symm_apply (e : L ≃ₐ[K] L') (w : InfinitePlace L') :
    (congrInf e).symm w = w.comap e.toRingHom := rfl

/-- The ring isomorphism `𝓞 L ≃+* 𝓞 L'` attached to `e : L ≃ₐ[K] L'`. -/
noncomputable def ringOfIntegersCongr (e : L ≃ₐ[K] L') : (𝓞 L) ≃+* (𝓞 L') :=
  NumberField.RingOfIntegers.mapRingEquiv e.toRingEquiv

theorem ringOfIntegersCongr_apply (e : L ≃ₐ[K] L') (x : 𝓞 L) :
    ((ringOfIntegersCongr e x : 𝓞 L') : L') = e (x : L) :=
  NumberField.RingOfIntegers.mapRingEquiv_apply e.toRingEquiv x

/-- The equivalence of nonarchimedean places attached to a `K`-algebra isomorphism
`e : L ≃ₐ[K] L'`, induced by the map on nonzero primes. -/
noncomputable def congrFin (e : L ≃ₐ[K] L') :
    HeightOneSpectrum (𝓞 L) ≃ HeightOneSpectrum (𝓞 L') where
  toFun q := ⟨Ideal.map (ringOfIntegersCongr e : 𝓞 L →+* 𝓞 L') q.asIdeal,
    Ideal.map_isPrime_of_equiv (ringOfIntegersCongr e),
    fun h => q.ne_bot ((Ideal.map_eq_bot_iff_of_injective (ringOfIntegersCongr e).injective).mp h)⟩
  invFun q := ⟨Ideal.map ((ringOfIntegersCongr e).symm : 𝓞 L' →+* 𝓞 L) q.asIdeal,
    Ideal.map_isPrime_of_equiv (ringOfIntegersCongr e).symm,
    fun h => q.ne_bot
      ((Ideal.map_eq_bot_iff_of_injective (ringOfIntegersCongr e).symm.injective).mp h)⟩
  left_inv q := by
    ext x
    simp only [Ideal.map_map]
    rw [show ((ringOfIntegersCongr e).symm : 𝓞 L' →+* 𝓞 L).comp
        (ringOfIntegersCongr e : 𝓞 L →+* 𝓞 L') = RingHom.id _ from by ext x; simp]
    simp
  right_inv q := by
    ext x
    simp only [Ideal.map_map]
    rw [show (ringOfIntegersCongr e : 𝓞 L →+* 𝓞 L').comp
        ((ringOfIntegersCongr e).symm : 𝓞 L' →+* 𝓞 L) = RingHom.id _ from by ext x; simp]
    simp

@[simp] theorem congrFin_asIdeal (e : L ≃ₐ[K] L') (q : HeightOneSpectrum (𝓞 L)) :
    (congrFin e q).asIdeal
      = Ideal.map (ringOfIntegersCongr e : 𝓞 L →+* 𝓞 L') q.asIdeal := rfl

/-- The equivalence of places attached to a `K`-algebra isomorphism `e : L ≃ₐ[K] L'`. -/
noncomputable def congr (e : L ≃ₐ[K] L') : Place L ≃ Place L' :=
  (congrInf e).sumCongr (congrFin e)

@[simp] theorem congr_ofInfinite (e : L ≃ₐ[K] L') (w : InfinitePlace L) :
    congr e (ofInfinite w) = ofInfinite (congrInf e w) := rfl

@[simp] theorem congr_ofFinite (e : L ≃ₐ[K] L') (q : HeightOneSpectrum (𝓞 L)) :
    congr e (ofFinite q) = ofFinite (congrFin e q) := rfl

@[simp] theorem congr_symm_ofInfinite (e : L ≃ₐ[K] L') (w : InfinitePlace L') :
    (congr e).symm (ofInfinite w) = ofInfinite ((congrInf e).symm w) := rfl

@[simp] theorem congr_symm_ofFinite (e : L ≃ₐ[K] L') (q : HeightOneSpectrum (𝓞 L')) :
    (congr e).symm (ofFinite q) = ofFinite ((congrFin e).symm q) := rfl

/-- The transport of infinite places is equivariant for `AlgEquiv.autCongr`. -/
theorem congrInf_smul (e : L ≃ₐ[K] L') (σ : L ≃ₐ[K] L) (w : InfinitePlace L) :
    congrInf e (σ • w) = (AlgEquiv.autCongr e σ) • congrInf e w := by
  rw [← InfinitePlace.mk_embedding w]
  simp only [InfinitePlace.smul_mk, congrInf_apply, InfinitePlace.comap_mk]
  congr 1
  ext x
  simp [AlgEquiv.autCongr_apply]

/-- The transport of nonarchimedean places is equivariant for `AlgEquiv.autCongr`. -/
theorem congrFin_smul (e : L ≃ₐ[K] L') (σ : L ≃ₐ[K] L) (q : HeightOneSpectrum (𝓞 L)) :
    congrFin e (smulHeightOneSpectrum σ q)
      = smulHeightOneSpectrum (AlgEquiv.autCongr e σ) (congrFin e q) := by
  refine HeightOneSpectrum.ext ?_
  show Ideal.map (ringOfIntegersCongr e : 𝓞 L →+* 𝓞 L')
      (Ideal.map (ringOfIntegersEquiv σ : 𝓞 L →+* 𝓞 L) q.asIdeal)
    = Ideal.map (ringOfIntegersEquiv (AlgEquiv.autCongr e σ) : 𝓞 L' →+* 𝓞 L')
      (Ideal.map (ringOfIntegersCongr e : 𝓞 L →+* 𝓞 L') q.asIdeal)
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  ext x
  simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom]
  simp only [ringOfIntegersCongr_apply, Place.ringOfIntegersEquiv_apply, AlgEquiv.autCongr_apply,
    AlgEquiv.trans_apply]
  simp

/-- The transport of places is equivariant for `AlgEquiv.autCongr`. -/
theorem congr_smul (e : L ≃ₐ[K] L') (σ : L ≃ₐ[K] L) (v : Place L) :
    congr e (σ • v) = (AlgEquiv.autCongr e σ) • congr e v := by
  cases v with
  | inl w => simp only [smul_ofInfinite, congr_ofInfinite, congrInf_smul]
  | inr q => simp only [smul_ofFinite, congr_ofFinite, congrFin_smul]

end Place

end NK.GlobalCFT
