import Mathlib
import Submission.NK.GlobalCFT.Inclusion
import Submission.NK.GlobalCFT.GaloisIdelesAction
import Submission.NK.GlobalCFT.LocalInputs
import Submission.NK.GlobalCFT.Galois.globalCFT_smul_place_smul
import Submission.NK.GlobalCFT.Galois.globalCFT_one_smul_place
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct NumberField.LiesOver
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFT.Inclusion

open NK.GlobalCFT

/-! ### Elementary transport lemmas

The local field `L_w` of a place is a `match` on the place, so equalities of places have to be
transported along.  The following lemmas record the basic compatibility of this transport with
functions, with units and with the ring operations. -/

/-- Transporting the value of a dependent function along an equality of the arguments. -/
theorem globalCFT_eqRec_apply {α : Type*} {β : α → Type*} (f : (i : α) → β i) {a b : α}
    (h : a = b) : h ▸ f a = f b := by cases h; rfl

/-- Transporting in the other direction. -/
theorem globalCFT_eqRec_apply_symm {α : Type*} {β : α → Type*} (f : (i : α) → β i) {a b : α}
    (h : a = b) : h.symm ▸ f b = f a := by cases h; rfl

/-- Two successive transports cancel. -/
theorem globalCFT_eqRec_transport_transport {α : Type*} {β : α → Type*} {a b : α} (h : a = b)
    (z : β a) : h.symm ▸ (h ▸ z) = z := by cases h; rfl

/-- Two successive transports cancel, in the other direction. -/
theorem globalCFT_eqRec_transport_transport' {α : Type*} {β : α → Type*} {a b : α} (h : a = b)
    (z : β b) : h ▸ (h.symm ▸ z) = z := by cases h; rfl

namespace Place

/-- Transport along an equality of places commutes with multiplication in the local field. -/
theorem globalCFT_localField_cast_mul {L : Type*} [Field L] [NumberField L] {a b : Place L}
    (h : a = b) (x y : Place.localField L a) :
    h ▸ (x * y) = (h ▸ x) * (h ▸ y) := by cases h; rfl

/-- Transport along an equality of places commutes with addition in the local field. -/
theorem globalCFT_localField_cast_add {L : Type*} [Field L] [NumberField L] {a b : Place L}
    (h : a = b) (x y : Place.localField L a) :
    h ▸ (x + y) = (h ▸ x) + (h ▸ y) := by cases h; rfl

end Place

/-! ### The two actions of `Gal(L/K)` on the finite places agree

The commons develop the decomposition group of a finite place `q` of `L` using their own action
`Commons.NumberTheory.NumberField.Completion.placeSmul`, while the `NK.GlobalCFT` development uses
`NK.GlobalCFT.Place.smulHeightOneSpectrum`.  Both are `HeightOneSpectrum.mapRingEquiv` of the
automorphism of `𝓞 L` induced by `σ ∈ Gal(L/K)`, so they coincide. -/

theorem globalCFT_placeSmul_eq_smulHeightOneSpectrum {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (q : HeightOneSpectrum (𝓞 L)) :
    Commons.NumberTheory.NumberField.Completion.placeSmul σ q =
      Place.smulHeightOneSpectrum σ q := by
  have hval : ∀ x : 𝓞 L,
      ((galRestrict (𝓞 K) K L (𝓞 L) σ : 𝓞 L ≃+* 𝓞 L)) x = Place.ringOfIntegersEquiv σ x := by
    intro x
    refine NumberField.RingOfIntegers.coe_injective ?_
    show (algebraMap (𝓞 L) L) (((galRestrict (𝓞 K) K L (𝓞 L) σ)) x)
      = (algebraMap (𝓞 L) L) (Place.ringOfIntegersEquiv σ x)
    rw [algebraMap_galRestrict_apply (𝓞 K) σ x]
    rfl
  have hhom : (↑((galRestrict (𝓞 K) K L (𝓞 L) σ) : 𝓞 L →+* 𝓞 L))
      = (↑(Place.ringOfIntegersEquiv σ) : 𝓞 L →+* 𝓞 L) := RingHom.ext hval
  refine HeightOneSpectrum.ext ?_
  rw [Commons.NumberTheory.NumberField.Completion.placeSmul_asIdeal,
    Place.smulHeightOneSpectrum_asIdeal, hhom]
  congr 1

/-- Membership in the commons' decomposition group, in terms of the `NK.GlobalCFT` action on
the finite places of `L`. -/
theorem globalCFT_mem_decompositionSubgroup_iff {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (q : HeightOneSpectrum (𝓞 L)) :
    σ ∈ Commons.NumberTheory.NumberField.Completion.decompositionSubgroup q ↔
      Place.smulHeightOneSpectrum σ q = q := by
  rw [Commons.NumberTheory.NumberField.Completion.mem_decompositionSubgroup,
    globalCFT_placeSmul_eq_smulHeightOneSpectrum]

/-! ### The local action of a stabiliser of a place -/

/-- The canonical local isomorphism `L_w ≃+* L_{σ w}` transported to an automorphism of `L_w`
for an element `σ` of `Gal(L/K)` stabilising the place `w`. -/
noncomputable def Place.localAction {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L) (w : Place L) (h : σ • w = w) :
    (Place.localField L w) ≃+* (Place.localField L w) where
  toFun y := h ▸ (Place.localRingEquiv σ w y)
  invFun y := (Place.localRingEquiv σ w).symm (h.symm ▸ y)
  left_inv y := by
    show (Place.localRingEquiv σ w).symm (h.symm ▸ (h ▸ (Place.localRingEquiv σ w y))) = y
    rw [globalCFT_eqRec_transport_transport h (Place.localRingEquiv σ w y)]
    exact (Place.localRingEquiv σ w).symm_apply_apply y
  right_inv y := by
    show h ▸ (Place.localRingEquiv σ w ((Place.localRingEquiv σ w).symm (h.symm ▸ y))) = y
    rw [(Place.localRingEquiv σ w).apply_symm_apply]
    exact globalCFT_eqRec_transport_transport' h y
  map_mul' y z := by
    show h ▸ (Place.localRingEquiv σ w (y * z))
      = (h ▸ (Place.localRingEquiv σ w y)) * (h ▸ (Place.localRingEquiv σ w z))
    rw [map_mul, Place.globalCFT_localField_cast_mul]
  map_add' y z := by
    show h ▸ (Place.localRingEquiv σ w (y + z))
      = (h ▸ (Place.localRingEquiv σ w y)) + (h ▸ (Place.localRingEquiv σ w z))
    rw [map_add, Place.globalCFT_localField_cast_add]

@[simp] theorem Place.localAction_apply {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L) (w : Place L) (h : σ • w = w)
    (y : Place.localField L w) :
    Place.localAction σ w h y = h ▸ (Place.localRingEquiv σ w y) := rfl

@[simp] theorem Place.localAction_symm_apply {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L) (w : Place L) (h : σ • w = w)
    (y : Place.localField L w) :
    (Place.localAction σ w h).symm y =
      (Place.localRingEquiv σ w).symm (h.symm ▸ y) := rfl

/-- The local action is compatible with the canonical embeddings of `L`. -/
theorem Place.localAction_algebraMap {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L) (w : Place L) (h : σ • w = w) (y : L) :
    Place.localAction σ w h (algebraMap L (Place.localField L w) y)
      = h ▸ (algebraMap L (Place.localField L (σ • w)) (σ y)) := by
  rw [Place.localAction_apply, Place.localRingEquiv_algebraMap]

/-- **The component at a stabilised place of a Galois-fixed idèle is fixed by the local action.**
If `x` is an idèle fixed by all of `Gal(L/K)` and `σ` stabilises the place `w`, then the `w`
component `x w` is fixed by the automorphism `Place.localAction σ w` of `L_w`. -/
theorem globalCFT_fixed_component {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (x : Idele L) (hx : ∀ σ : L ≃ₐ[K] L, σ • x = x)
    (σ : L ≃ₐ[K] L) (w : Place L) (hσ : σ • w = w) :
    Units.map ((Place.localAction σ w hσ).symm).toMonoidHom (x w) = x w := by
  have h1 : Units.map (Place.localRingEquiv σ w).symm.toMonoidHom (x (σ • w)) = x w := by
    have h2 : (σ⁻¹ • x) w = x w := congrArg (fun y : Idele L => y w) (hx σ⁻¹)
    simp only [Idele.smul_apply] at h2
    exact h2
  apply Units.ext
  show ((Place.localRingEquiv σ w).symm (hσ.symm ▸ ((x w : (Place.localField L w)ˣ) :
      Place.localField L w))) = ((x w : (Place.localField L w)ˣ) : Place.localField L w)
  rw [globalCFT_eqRec_apply (fun p : Place L =>
    ((x p : (Place.localField L p)ˣ) : Place.localField L p)) hσ.symm]
  exact congrArg (fun u : (Place.localField L w)ˣ => (u : Place.localField L w)) h1


/-! ### Unfolding the local embeddings

The definition of `Place.localAlgebraMapUnits` is a case distinction which never uses its third
argument; the following lemmas compute it in the two nontrivial cases. -/

private theorem globalCFT_localAlgebraMapUnits_congr {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] (w : Place L) (v : Place K)
    (h h' : Place.LiesOver w v) :
    Place.localAlgebraMapUnits w v h = Place.localAlgebraMapUnits w v h' := rfl

theorem globalCFT_localAlgebraMapUnits_ofFinite {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] (q : HeightOneSpectrum (𝓞 L))
    (Q : HeightOneSpectrum (𝓞 K)) [hqQ : q.asIdeal.LiesOver Q.asIdeal]
    (h : Place.LiesOver (Place.ofFinite q) (Place.ofFinite Q)) :
    Place.localAlgebraMapUnits (Place.ofFinite q) (Place.ofFinite Q) h =
      Units.map (Commons.RingTheory.Henselian.adicCompletionMap Q q hqQ).toMonoidHom := by
  rw [globalCFT_localAlgebraMapUnits_congr (Place.ofFinite q) (Place.ofFinite Q) h
    (Place.liesOver_ofFinite hqQ)]
  unfold Place.localAlgebraMapUnits
  simp only [dif_pos hqQ]

theorem globalCFT_localAlgebraMapUnits_ofInfinite {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] (w : InfinitePlace L) (v : InfinitePlace K)
    [hwv : w.LiesOver v] (h : Place.LiesOver (Place.ofInfinite w) (Place.ofInfinite v)) :
    Place.localAlgebraMapUnits (Place.ofInfinite w) (Place.ofInfinite v) h =
      Units.map (NumberField.LiesOver.completionMap (v := v) (w := w)).toMonoidHom := by
  rw [globalCFT_localAlgebraMapUnits_congr (Place.ofInfinite w) (Place.ofInfinite v) h
    (Place.liesOver_ofInfinite hwv)]
  unfold Place.localAlgebraMapUnits
  simp only [dif_pos hwv]

/-- The local action of a stabiliser is continuous. -/
theorem Place.continuous_localAction {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L) (w : Place L) (h : σ • w = w) :
    Continuous (Place.localAction σ w h) := by
  have hfun : (⇑(Place.localAction σ w h)) = fun y : Place.localField L w =>
      h ▸ (Place.localRingEquiv σ w y) := by
    funext y
    rw [Place.localAction_apply]
  rw [hfun]
  exact Galois.continuous_localField_cast h (Galois.continuous_localRingEquiv σ w)

/-- **The component at a stabilised place of a Galois-fixed idèle is fixed by the local action**
(field-element form). -/
theorem globalCFT_fixed_component_field {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (x : Idele L) (hx : ∀ σ : L ≃ₐ[K] L, σ • x = x)
    (σ : L ≃ₐ[K] L) (w : Place L) (hσ : σ • w = w) :
    Place.localAction σ w hσ ((x w : (Place.localField L w)ˣ) : Place.localField L w)
      = ((x w : (Place.localField L w)ˣ) : Place.localField L w) := by
  have h1 : Units.map (Place.localRingEquiv σ w).symm.toMonoidHom (x (σ • w)) = x w := by
    have h2 : (σ⁻¹ • x) w = x w := congrArg (fun y : Idele L => y w) (hx σ⁻¹)
    simp only [Idele.smul_apply] at h2
    exact h2
  have h1' : (Place.localRingEquiv σ w).symm
      ((x (σ • w) : (Place.localField L (σ • w))ˣ) : Place.localField L (σ • w))
      = ((x w : (Place.localField L w)ˣ) : Place.localField L w) := by
    simpa using congrArg (fun u : (Place.localField L w)ˣ => (u : Place.localField L w)) h1
  have h2 : (Place.localAction σ w hσ).symm ((x w : (Place.localField L w)ˣ) :
      Place.localField L w) = ((x w : (Place.localField L w)ˣ) : Place.localField L w) := by
    show (Place.localRingEquiv σ w).symm (hσ.symm ▸ ((x w : (Place.localField L w)ˣ) :
      Place.localField L w)) = ((x w : (Place.localField L w)ˣ) : Place.localField L w)
    rw [globalCFT_eqRec_apply (fun p : Place L =>
      ((x p : (Place.localField L p)ˣ) : Place.localField L p)) hσ.symm]
    exact h1'
  have h3 := congrArg (⇑(Place.localAction σ w hσ)) h2
  rw [RingEquiv.apply_symm_apply] at h3
  exact h3.symm


/-! ### The image of `L` in the adic completion -/

/-- The `toCompletion` presentation of the image of an element of `L` in the `q`-adic
completion, which is the form in which the commons' lemmas compute. -/
theorem globalCFT_adicCompletion_coe_eq {L : Type*} [Field L] [NumberField L]
    (q : HeightOneSpectrum (𝓞 L)) (y : L) :
    (algebraMap L (q.adicCompletion L) y)
      = ({toCompletion :=
          ↑((WithVal.equiv (IsDedekindDomain.HeightOneSpectrum.valuation L q)).symm y)} :
          q.adicCompletion L) := by
  rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
  rfl

/-- **The local action of a stabiliser of a finite place is the commons' action of the
decomposition group on the completion.** -/
theorem globalCFT_localAction_eq_decompositionToAdicCompletion {K L : Type*} [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] (q : HeightOneSpectrum (𝓞 L)) (σ : L ≃ₐ[K] L)
    (hσ' : Place.smulHeightOneSpectrum σ q = q)
    (hσ : σ • Place.ofFinite q = Place.ofFinite q) (y : q.adicCompletion L) :
    Place.localAction σ (Place.ofFinite q) hσ y
      = Commons.NumberTheory.NumberField.Completion.decompositionToAdicCompletion (K := K) q
          ⟨σ, (globalCFT_mem_decompositionSubgroup_iff σ q).mpr hσ'⟩ y := by
  have hdense : DenseRange (algebraMap L (Place.localField L (Place.ofFinite q))) :=
    Galois.denseRange_algebraMap_localField (Place.ofFinite q)
  have hcont1 : Continuous (fun z : Place.localField L (Place.ofFinite q) =>
      Place.localAction σ (Place.ofFinite q) hσ z) :=
    Place.continuous_localAction σ (Place.ofFinite q) hσ
  have hcont2 : Continuous (fun z : Place.localField L (Place.ofFinite q) =>
      Commons.NumberTheory.NumberField.Completion.decompositionToAdicCompletion (K := K) q
        ⟨σ, (globalCFT_mem_decompositionSubgroup_iff σ q).mpr hσ'⟩ z) :=
    Commons.NumberTheory.NumberField.Completion.continuous_decompositionToAdicCompletion q _
  have hfun : (fun z : Place.localField L (Place.ofFinite q) =>
        Place.localAction σ (Place.ofFinite q) hσ z)
      = fun z => Commons.NumberTheory.NumberField.Completion.decompositionToAdicCompletion
          (K := K) q ⟨σ, (globalCFT_mem_decompositionSubgroup_iff σ q).mpr hσ'⟩ z := by
    refine DenseRange.equalizer hdense hcont1 hcont2 ?_
    funext z
    simp only [Function.comp_apply]
    rw [Place.localAction_algebraMap]
    rw [globalCFT_eqRec_apply (fun p : Place L => algebraMap L (Place.localField L p) (σ z)) hσ]
    rw [globalCFT_adicCompletion_coe_eq q (σ z)]
    rw [globalCFT_adicCompletion_coe_eq q z]
    rw [Commons.NumberTheory.NumberField.Completion.decompositionToAdicCompletion_coe]
    try rfl
  exact congrFun hfun y


/-! ### The embedding of the archimedean local field into `ℂ` -/

/-- The canonical embedding of the completion at an infinite place, evaluated on the image of
`L`. -/
theorem globalCFT_extensionEmbedding_algebraMap {L : Type*} [Field L] [NumberField L]
    (w : InfinitePlace L) (z : L) :
    NumberField.InfinitePlace.Completion.extensionEmbedding w
        (algebraMap L (Place.localField L (Place.ofInfinite w)) z) = w.embedding z := by
  rw [show (algebraMap L (Place.localField L (Place.ofInfinite w)) z)
      = ({toCompletion := ↑(WithAbs.toAbs w.1 z)} : w.Completion) from
        NumberField.InfinitePlace.Completion.algebraMap_apply w z]
  rw [NumberField.InfinitePlace.Completion.extensionEmbedding_coe]
  simp [WithAbs.equiv_apply]

/-- **The local action of a complex conjugation is complex conjugation on the local field.**  If
`σ ∈ Gal(L/K)` stabilises the infinite place `w` and acts as the complex conjugation with respect
to the embedding `w.embedding`, then the local action of `σ` on `L_w` is complex conjugation
under the canonical identification `L_w ≅ ℂ`. -/
theorem globalCFT_localAction_extensionEmbedding_conj {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (w : InfinitePlace L) (σ : L ≃ₐ[K] L) (hσ : σ • Place.ofInfinite w = Place.ofInfinite w)
    (hconj : NumberField.ComplexEmbedding.IsConj w.embedding σ) (y : w.Completion) :
    NumberField.InfinitePlace.Completion.extensionEmbedding w
        (Place.localAction σ (Place.ofInfinite w) hσ y)
      = starRingEnd ℂ (NumberField.InfinitePlace.Completion.extensionEmbedding w y) := by
  have hdense : DenseRange (algebraMap L (Place.localField L (Place.ofInfinite w))) :=
    Galois.denseRange_algebraMap_localField (Place.ofInfinite w)
  have hcont1 : Continuous (fun y : Place.localField L (Place.ofInfinite w) =>
      NumberField.InfinitePlace.Completion.extensionEmbedding w
        (Place.localAction σ (Place.ofInfinite w) hσ y)) :=
    (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
      (Place.continuous_localAction σ (Place.ofInfinite w) hσ)
  have hcont2 : Continuous (fun y : Place.localField L (Place.ofInfinite w) =>
      starRingEnd ℂ (NumberField.InfinitePlace.Completion.extensionEmbedding w y)) :=
    Complex.continuous_conj.comp
      (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding w).continuous
  have hfun : (fun y : Place.localField L (Place.ofInfinite w) =>
        NumberField.InfinitePlace.Completion.extensionEmbedding w
          (Place.localAction σ (Place.ofInfinite w) hσ y))
      = fun y => starRingEnd ℂ
          (NumberField.InfinitePlace.Completion.extensionEmbedding w y) := by
    refine DenseRange.equalizer hdense hcont1 hcont2 ?_
    funext z
    simp only [Function.comp_apply]
    rw [Place.localAction_algebraMap]
    rw [globalCFT_eqRec_apply (fun p : Place L => algebraMap L (Place.localField L p) (σ z)) hσ]
    rw [globalCFT_extensionEmbedding_algebraMap w (σ z),
      globalCFT_extensionEmbedding_algebraMap w z, hconj.eq z]
    rfl
  exact congrFun hfun y


/-- A unit in the range of a ring homomorphism between fields has a preimage unit. -/
theorem globalCFT_exists_unit_of_mem_range {A B : Type*} [Field A] [Field B] (f : A →+* B)
    (u : Bˣ) (h : (u : B) ∈ Set.range f) :
    ∃ z : Aˣ, Units.map f.toMonoidHom z = u := by
  obtain ⟨b, hb⟩ := h
  refine ⟨Units.mk0 b ?_, ?_⟩
  · intro hb0
    have h0 : (u : B) = 0 := by rw [← hb, hb0, map_zero]
    exact Units.ne_zero u h0
  · apply Units.ext
    simp only [Units.coe_map, Units.val_mk0]
    exact hb

end NK.GlobalCFT.Inclusion
