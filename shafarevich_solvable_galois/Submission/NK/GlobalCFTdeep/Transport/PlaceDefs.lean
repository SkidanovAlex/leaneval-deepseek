import Mathlib
import Submission.NK.GlobalCFT.NormGroup
import Submission.NK.GlobalCFT.NormGroup.Basic
import Submission.NK.GlobalCFT.GlobalCFT
import Submission.NK.UniverseUnify.heightOneSpectrumULift
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Transport of the places of a number field along a ring equivalence

Given a ring equivalence `e : K ≃+* K'` of number fields, we transport

* the archimedean places: `w ↦ w.comap e.symm`,
* the nonarchimedean places: the nonzero prime `Q` of `𝓞 K` goes to its image under
  `NumberField.RingOfIntegers.mapRingEquiv e`,

giving a bijection `NK.GlobalCFTdeep.Transport.placeEquiv e : Place K ≃ Place K'` of the
places.  This is the index set on which the idèle group `𝕀 K` is built, so this is the first
ingredient in the transport of the norm subgroup `N_{L/K}C_L`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep.Transport

open NK.GlobalCFT

variable {K K' : Type*} [Field K] [NumberField K] [Field K'] [NumberField K']

/-- **Transport of archimedean places along a ring equivalence.**  The place `w` of `K` is sent
to the place `w ∘ e.symm` of `K'`. -/
noncomputable def infinitePlaceEquiv (e : K ≃+* K') :
    NumberField.InfinitePlace K ≃ NumberField.InfinitePlace K' where
  toFun w := w.comap (e.symm : K' →+* K)
  invFun v := v.comap (e : K →+* K')
  left_inv w := by
    show (w.comap (e.symm : K' →+* K)).comap (e : K →+* K') = w
    rw [← NumberField.InfinitePlace.comap_comp]
    have h : (e.symm : K' →+* K).comp (e : K →+* K') = RingHom.id K := by
      ext x; simp
    rw [h, NumberField.InfinitePlace.comap_id]
  right_inv v := by
    show (v.comap (e : K →+* K')).comap (e.symm : K' →+* K) = v
    rw [← NumberField.InfinitePlace.comap_comp]
    have h : (e : K →+* K').comp (e.symm : K' →+* K) = RingHom.id K' := by
      ext x; simp
    rw [h, NumberField.InfinitePlace.comap_id]

@[simp] theorem infinitePlaceEquiv_apply (e : K ≃+* K') (w : NumberField.InfinitePlace K) :
    infinitePlaceEquiv e w = w.comap (e.symm : K' →+* K) := rfl

/-- **Transport of nonarchimedean places along a ring equivalence.**  The nonzero prime `Q` of
`𝓞 K` is sent to the image `Ideal.map (RingOfIntegers.mapRingEquiv e) Q`. -/
noncomputable def finitePlaceEquiv (e : K ≃+* K') :
    HeightOneSpectrum (𝓞 K) ≃ HeightOneSpectrum (𝓞 K') :=
  NK.UniverseUnify.heightOneSpectrumCongr (NumberField.RingOfIntegers.mapRingEquiv e)

@[simp] theorem finitePlaceEquiv_asIdeal (e : K ≃+* K')
    (Q : HeightOneSpectrum (𝓞 K)) :
    (finitePlaceEquiv e Q).asIdeal =
      Q.asIdeal.map (NumberField.RingOfIntegers.mapRingEquiv e : 𝓞 K →+* 𝓞 K') :=
  NK.UniverseUnify.heightOneSpectrumMapRingEquiv_asIdeal _ Q

/-- **Transport of places along a ring equivalence**, as a bijection `Place K ≃ Place K'`. -/
noncomputable def placeEquiv (e : K ≃+* K') : Place K ≃ Place K' :=
  Equiv.sumCongr (infinitePlaceEquiv e) (finitePlaceEquiv e)

@[simp] theorem placeEquiv_ofInfinite (e : K ≃+* K') (w : NumberField.InfinitePlace K) :
    placeEquiv e (Place.ofInfinite w) = Place.ofInfinite (infinitePlaceEquiv e w) := rfl

@[simp] theorem placeEquiv_ofFinite (e : K ≃+* K') (Q : HeightOneSpectrum (𝓞 K)) :
    placeEquiv e (Place.ofFinite Q) = Place.ofFinite (finitePlaceEquiv e Q) := rfl

@[simp] theorem placeEquiv_symm_ofInfinite (e : K ≃+* K') (w : NumberField.InfinitePlace K) :
    (placeEquiv e).symm (Place.ofInfinite (infinitePlaceEquiv e w)) = Place.ofInfinite w := by
  rw [← placeEquiv_ofInfinite]; exact (placeEquiv e).symm_apply_apply _

@[simp] theorem placeEquiv_symm_ofFinite (e : K ≃+* K') (Q : HeightOneSpectrum (𝓞 K)) :
    (placeEquiv e).symm (Place.ofFinite (finitePlaceEquiv e Q)) = Place.ofFinite Q := by
  rw [← placeEquiv_ofFinite]; exact (placeEquiv e).symm_apply_apply _

end NK.GlobalCFTdeep.Transport
