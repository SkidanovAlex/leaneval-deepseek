import Mathlib
import Submission.NK.GlobalCFTdeep.Transport.IdeleClassEquiv
import Submission.NK.GlobalCFT.Galois.globalCFT_localRingEquiv_comp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.Sha2Lib

open NumberField IsDedekindDomain
open scoped NumberField RestrictedProduct
open NK.GlobalCFT NK.GlobalCFTdeep.Transport

variable {K : Type*} [Field K] [NumberField K]

/-! ### The transport `placeEquiv` of places along the identity ring equivalence -/

lemma ssgr_infinitePlaceEquiv_refl (w : NumberField.InfinitePlace K) :
    infinitePlaceEquiv (RingEquiv.refl K) w = w := by
  rw [infinitePlaceEquiv_apply]
  simp [NumberField.InfinitePlace.comap_id]

lemma ssgr_mapRingEquiv_refl :
    (NumberField.RingOfIntegers.mapRingEquiv (RingEquiv.refl K) : 𝓞 K →+* 𝓞 K) =
      RingHom.id (𝓞 K) := by
  ext x
  change (NumberField.RingOfIntegers.mapRingEquiv (RingEquiv.refl K) x : K) = (x : K)
  rw [NumberField.RingOfIntegers.mapRingEquiv_apply]
  exact RingEquiv.refl_apply K (x : K)

lemma ssgr_finitePlaceEquiv_refl (Q : HeightOneSpectrum (𝓞 K)) :
    finitePlaceEquiv (RingEquiv.refl K) Q = Q := by
  apply HeightOneSpectrum.ext
  rw [finitePlaceEquiv_asIdeal, ssgr_mapRingEquiv_refl, Ideal.map_id]

lemma ssgr_placeEquiv_refl (v : Place K) : placeEquiv (RingEquiv.refl K) v = v := by
  cases v with
  | inl w => rw [placeEquiv_ofInfinite, ssgr_infinitePlaceEquiv_refl]
  | inr Q => rw [placeEquiv_ofFinite, ssgr_finitePlaceEquiv_refl]

/-! ### The local field transport along the identity is the identity

The local field `K_v` is a family of types indexed by the places, so the identity statement has to
be transported along the equality `placeEquiv (refl K) v = v` of places.  The proof is the density
argument: both sides are continuous and agree on the dense image of `K` in `K_v`. -/

lemma ssgr_localFieldIso_refl (v : Place K) (h : placeEquiv (RingEquiv.refl K) v = v)
    (y : Place.localField K v) :
    NormTransport.localFieldIso (RingEquiv.refl K) v y = h.symm ▸ y := by
  have hdense : DenseRange (algebraMap K (Place.localField K v)) :=
    NK.GlobalCFT.Galois.denseRange_algebraMap_localField v
  have hcont₁ : Continuous (fun y : Place.localField K v =>
      NormTransport.localFieldIso (RingEquiv.refl K) v y) :=
    NormTransport.localFieldIso_continuous (RingEquiv.refl K) v
  have hcont₂ : Continuous (fun y : Place.localField K v => h.symm ▸ y) :=
    NK.GlobalCFT.Galois.continuous_localField_cast h.symm continuous_id
  have hfun : (fun y : Place.localField K v =>
        NormTransport.localFieldIso (RingEquiv.refl K) v y) =
      fun y : Place.localField K v => h.symm ▸ y := by
    refine DenseRange.equalizer hdense hcont₁ hcont₂ ?_
    funext x
    simp only [Function.comp_apply]
    rw [NormTransport.localFieldIso_algebraMap (RingEquiv.refl K) v x,
      NK.GlobalCFT.Galois.localField_cast_algebraMap h.symm x]
    rfl
  exact congrFun hfun y

/-! ### Elementary facts about the transport `h ▸ ·` along an equality of places -/

lemma ssgr_idele_congr_apply {a b : Place K} (h : a = b) (x : Idele K) :
    h ▸ x a = x b := by
  cases h; rfl

lemma ssgr_units_cast_val {a b : Place K} (h : a = b) (u : (Place.localField K a)ˣ) :
    ((h ▸ u : (Place.localField K b)ˣ) : Place.localField K b) =
      h ▸ ((u : Place.localField K a)) := by
  cases h; rfl

lemma ssgr_units_map_localFieldEquiv_refl (v : Place K)
    (h : placeEquiv (RingEquiv.refl K) v = v) (u : (Place.localField K v)ˣ) :
    Units.map (NormTransport.localFieldIso (RingEquiv.refl K) v).toMonoidHom u = h.symm ▸ u := by
  apply Units.ext
  rw [Units.coe_map, ssgr_units_cast_val h.symm u]
  exact ssgr_localFieldIso_refl v h u

/-! ### The idèle transport along the identity is the identity -/

lemma ssgr_ideleEquiv_refl_apply (x : Idele K) :
    ideleEquiv (RingEquiv.refl K) x = x := by
  apply NK.GlobalCFT.Idele.ext
  intro v
  have hplace := ssgr_placeEquiv_refl (K := K) v
  rw [← hplace]
  rw [ideleEquiv_apply_placeEquiv (RingEquiv.refl K) x v]
  change Units.map (NormTransport.localFieldIso (RingEquiv.refl K) v).toMonoidHom (x v)
      = x (placeEquiv (RingEquiv.refl K) v)
  rw [ssgr_units_map_localFieldEquiv_refl v hplace (x v)]
  exact ssgr_idele_congr_apply hplace.symm x

/-! ### The idèle class group transport along the identity is the identity -/

lemma ssgr_ideleClassEquiv_refl_apply (x : IdeleClassGroup K) :
    ideleClassEquiv (RingEquiv.refl K) x = x := by
  refine QuotientGroup.induction_on x (fun a => ?_)
  change ideleClassEquiv (RingEquiv.refl K) (IdeleClassGroup.mk K a) = IdeleClassGroup.mk K a
  rw [ideleClassEquiv_mk, ssgr_ideleEquiv_refl_apply a]

theorem ideleClassEquiv_refl (K : Type) [Field K] [NumberField K]
    (x : NK.GlobalCFT.IdeleClassGroup K) :
    NK.GlobalCFTdeep.Transport.ideleClassEquiv (RingEquiv.refl K) x = x :=
  ssgr_ideleClassEquiv_refl_apply x

end Work.SSGRoute.Sha2Lib
