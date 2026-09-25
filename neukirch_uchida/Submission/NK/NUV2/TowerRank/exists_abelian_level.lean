import Mathlib
import Submission.NK.GlobalCFT.NormGroup.Basic
import Submission.NK.GlobalCFTdeep.FundamentalClassReduction
import Submission.NK.Reconstruct.Gamma
import Submission.NK.NUV2.ArtinBridge.index_eq_card_abelianization_of_fundamentalClassElement
import Submission.NK.NUV2.TowerRank.normClassSubgroup_fixedField_commutator
import Submission.NK.GlobalCFTdeep.hasseNorm_index_eq_universe
import Submission.NK.NUV2.ShrinkTransport
import Submission.NK.GlobalCFT.Galois.globalCFT_localRingEquiv_comp

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

open scoped RestrictedProduct Topology
open Filter NumberField IsDedekindDomain

namespace NK.NUV2.TowerRank

open NK.GlobalCFT NK.GlobalCFTdeep.Transport

variable {K K' : Type*} [Field K] [NumberField K] [Field K'] [NumberField K']

/-! ## Elementary transports along an equality of places -/

private lemma ringEquiv_cast_apply {ι : Type*} {R : ι → Type*} [∀ i, Mul (R i)] [∀ i, Add (R i)]
    {i j : ι} (h : i = j) (x : R i) : RingEquiv.cast h x = h ▸ x := by cases h; rfl

/-! ## The transport of places is compatible with inversion -/

/-- The transport of places along `e.symm` is the inverse transport of the places along `e`. -/
private theorem placeEquiv_symm_apply_placeEquiv_aux {K K' : Type*} [Field K] [NumberField K] [Field K']
    [NumberField K'] (e : K ≃+* K') (v : Place K) :
    placeEquiv e.symm (placeEquiv e v) = v := by
  have hin : ∀ w : NumberField.InfinitePlace K,
      infinitePlaceEquiv e.symm (infinitePlaceEquiv e w) = w := by
    intro w
    rw [infinitePlaceEquiv_apply, infinitePlaceEquiv_apply, ← NumberField.InfinitePlace.comap_comp]
    simp only [RingEquiv.symm_symm]
    have h : (e.symm : K' →+* K).comp (e : K →+* K') = RingHom.id K := by ext x; simp
    rw [h, NumberField.InfinitePlace.comap_id]
  have hfin : ∀ Q : HeightOneSpectrum (𝓞 K), finitePlaceEquiv e.symm (finitePlaceEquiv e Q) = Q := by
    intro Q
    have hsymm : RingOfIntegers.mapRingEquiv e.symm = (RingOfIntegers.mapRingEquiv e).symm := by
      ext x; simp
    show NK.UniverseUnify.heightOneSpectrumMapRingEquiv (RingOfIntegers.mapRingEquiv e.symm)
        (NK.UniverseUnify.heightOneSpectrumMapRingEquiv (RingOfIntegers.mapRingEquiv e) Q) = Q
    apply HeightOneSpectrum.ext
    rw [NK.UniverseUnify.heightOneSpectrumMapRingEquiv_asIdeal,
      NK.UniverseUnify.heightOneSpectrumMapRingEquiv_asIdeal, Ideal.map_map, hsymm]
    have hcomp : (((RingOfIntegers.mapRingEquiv e).symm : 𝓞 K' →+* 𝓞 K).comp
        ((RingOfIntegers.mapRingEquiv e) : 𝓞 K →+* 𝓞 K')) = RingHom.id (𝓞 K) := by
      ext x; simp
    rw [hcomp, Ideal.map_id]
  cases v with
  | inl w =>
    simp only [placeEquiv, Equiv.sumCongr_apply, Sum.map_inl]
    exact congrArg Sum.inl (hin w)
  | inr Q =>
    simp only [placeEquiv, Equiv.sumCongr_apply, Sum.map_inr]
    exact congrArg Sum.inr (hfin Q)

/-! ## Openness of the local field transport -/

/-- **The transport of a local field is an open map** (it is a homeomorphism for the local
topologies).  Its inverse is the transport along `e.symm` at the transported place, composed with
the transport along the equality of places `placeEquiv e.symm (placeEquiv e v) = v`; the identity is
checked by a density argument for the dense image of `K` (resp. `K'`). -/
private theorem isOpenMap_localFieldEquiv_aux {K K' : Type*} [Field K] [NumberField K] [Field K']
    [NumberField K'] (e : K ≃+* K') (v : Place K) :
    IsOpenMap ⇑(localFieldEquiv e v) := by
  have hplace : placeEquiv e.symm (placeEquiv e v) = v := placeEquiv_symm_apply_placeEquiv_aux e v
  have hcastcont : Continuous fun y : Place.localField K' (placeEquiv e v) =>
      RingEquiv.cast (R := fun u : Place K => Place.localField K u) hplace
        (localFieldEquiv e.symm (placeEquiv e v) y) := by
    have h1 : (fun y : Place.localField K' (placeEquiv e v) =>
        RingEquiv.cast (R := fun u : Place K => Place.localField K u) hplace
          (localFieldEquiv e.symm (placeEquiv e v) y)) =
        fun y => hplace ▸ (localFieldEquiv e.symm (placeEquiv e v) y) := by
      funext y; exact ringEquiv_cast_apply hplace _
    rw [h1]
    exact Galois.continuous_localField_cast hplace
      (NormTransport.localFieldIso_continuous e.symm _)
  have hB : ∀ y : Place.localField K' (placeEquiv e v),
      localFieldEquiv e v (RingEquiv.cast (R := fun u : Place K => Place.localField K u) hplace
        (localFieldEquiv e.symm (placeEquiv e v) y)) = y := by
    have hdense' : DenseRange (algebraMap K' (Place.localField K' (placeEquiv e v))) :=
      Galois.denseRange_algebraMap_localField _
    have hcont : Continuous fun y : Place.localField K' (placeEquiv e v) =>
        localFieldEquiv e v (RingEquiv.cast (R := fun u : Place K => Place.localField K u) hplace
          (localFieldEquiv e.symm (placeEquiv e v) y)) :=
      (NormTransport.localFieldIso_continuous e v).comp hcastcont
    have heq : (fun y : Place.localField K' (placeEquiv e v) =>
        localFieldEquiv e v (RingEquiv.cast (R := fun u : Place K => Place.localField K u) hplace
          (localFieldEquiv e.symm (placeEquiv e v) y))) = id := by
      refine DenseRange.equalizer hdense' hcont continuous_id ?_
      funext y
      simp only [Function.comp_apply, id_eq]
      rw [ringEquiv_cast_apply, localFieldEquiv_algebraMap e.symm (placeEquiv e v) y,
        Galois.localField_cast_algebraMap hplace, localFieldEquiv_algebraMap e v]
      simp
    intro y
    exact congrFun heq y
  have key : ∀ y : Place.localField K' (placeEquiv e v),
      (localFieldEquiv e v).symm y = RingEquiv.cast
        (R := fun u : Place K => Place.localField K u) hplace
        (localFieldEquiv e.symm (placeEquiv e v) y) := by
    intro y
    refine RingEquiv.injective (localFieldEquiv e v) ?_
    rw [RingEquiv.apply_symm_apply]
    exact (hB y).symm
  change IsOpenMap ⇑(localFieldEquiv e v).toEquiv
  rw [← Equiv.continuous_symm_iff (localFieldEquiv e v).toEquiv]
  change Continuous ⇑(localFieldEquiv e v).symm
  rw [show ⇑(localFieldEquiv e v).symm = (fun y : Place.localField K' (placeEquiv e v) =>
      RingEquiv.cast (R := fun u : Place K => Place.localField K u) hplace
        (localFieldEquiv e.symm (placeEquiv e v) y)) from funext key]
  exact hcastcont

/-- The idèle transport is continuous. -/
private theorem continuous_ideleEquiv_aux (e : K ≃+* K') :
    Continuous (NK.GlobalCFTdeep.Transport.ideleEquiv e) := by
  classical
  refine (RestrictedProduct.continuous_dom (R := fun v : Place K => (Place.localField K v)ˣ)
    (A := fun v : Place K => Place.localUnits K v) (𝓕 := Filter.cofinite)
    (f := ⇑(NK.GlobalCFTdeep.Transport.ideleEquiv e))).mpr ?_
  intro S hS
  set T : Set (Place K') := NK.GlobalCFTdeep.Transport.placeEquiv e '' S with hT
  have hTle : Filter.cofinite ≤ Filter.principal T := by
    rw [Filter.le_principal_iff, Filter.mem_cofinite]
    have hSfin : Sᶜ.Finite := Filter.mem_cofinite.mp (Filter.le_principal_iff.mp hS)
    refine (hSfin.image (NK.GlobalCFTdeep.Transport.placeEquiv e)).subset ?_
    rintro j hj1
    refine ⟨(NK.GlobalCFTdeep.Transport.placeEquiv e).symm j, ?_,
      (NK.GlobalCFTdeep.Transport.placeEquiv e).apply_symm_apply j⟩
    intro hmem
    exact hj1 (by rw [hT]; exact ⟨(NK.GlobalCFTdeep.Transport.placeEquiv e).symm j, hmem,
      (NK.GlobalCFTdeep.Transport.placeEquiv e).apply_symm_apply j⟩)
  set G : (Πʳ v, [(Place.localField K v)ˣ, Place.localUnits K v]_[Filter.principal S]) →
      (Πʳ j, [(Place.localField K' j)ˣ, Place.localUnits K' j]_[Filter.principal T]) :=
    fun x => ⟨fun j => ((NK.GlobalCFTdeep.Transport.ideleEquiv e
      (RestrictedProduct.inclusion (fun v : Place K => (Place.localField K v)ˣ)
        (fun v : Place K => Place.localUnits K v) hS x : NK.GlobalCFT.Idele K)) :
          (j : Place K') → (Place.localField K' j)ˣ) j, by
        rw [Filter.eventually_principal]
        intro j hj
        obtain ⟨v, hv, rfl⟩ := hj
        show ((NK.GlobalCFTdeep.Transport.ideleEquiv e)
            (RestrictedProduct.inclusion (fun v : Place K => (Place.localField K v)ˣ)
              (fun v : Place K => Place.localUnits K v) hS x : NK.GlobalCFT.Idele K))
            ((NK.GlobalCFTdeep.Transport.placeEquiv e) v) ∈
          Place.localUnits K' ((NK.GlobalCFTdeep.Transport.placeEquiv e) v)
        rw [NK.GlobalCFTdeep.Transport.ideleEquiv_apply_placeEquiv]
        exact (NK.GlobalCFTdeep.Transport.localFieldEquiv_localUnits e v _).mp
          (Filter.eventually_principal.mp x.2 v hv)⟩ with hG
  have hGcont : Continuous G := by
    rw [RestrictedProduct.continuous_rng_of_principal_iff_forall]
    refine (NK.GlobalCFTdeep.Transport.placeEquiv e).forall_congr_right.mp fun v => ?_
    show Continuous (fun x : (Πʳ v, [(Place.localField K v)ˣ, Place.localUnits K v]_[Filter.principal S]) =>
      (G x) (NK.GlobalCFTdeep.Transport.placeEquiv e v))
    have hfun : (fun x : (Πʳ v, [(Place.localField K v)ˣ, Place.localUnits K v]_[Filter.principal S]) =>
          (G x) (NK.GlobalCFTdeep.Transport.placeEquiv e v)) =
        fun x => Units.map (NK.GlobalCFTdeep.Transport.localFieldEquiv e v).toMonoidHom
          ((RestrictedProduct.inclusion (fun v : Place K => (Place.localField K v)ˣ)
            (fun v : Place K => Place.localUnits K v) hS x) v) := by
      funext x
      exact NK.GlobalCFTdeep.Transport.ideleEquiv_apply_placeEquiv e _ v
    rw [hfun]
    refine (Continuous.units_map _
      (NK.GlobalCFTdeep.Transport.NormTransport.localFieldIso_continuous e v)).comp ?_
    exact (RestrictedProduct.continuous_eval v).congr (fun x => rfl)
  have hpiece : Continuous (fun x : (Πʳ v, [(Place.localField K v)ˣ, Place.localUnits K v]_[Filter.principal S]) =>
      RestrictedProduct.inclusion (fun j : Place K' => (Place.localField K' j)ˣ)
        (fun j : Place K' => Place.localUnits K' j) hTle (G x)) :=
    (RestrictedProduct.continuous_inclusion hTle).comp hGcont
  exact hpiece.congr (fun x => Subtype.ext (by funext j; rfl))

/-- The inverse local transport preserves the local units. -/
private theorem localFieldEquiv_localUnits_symm_aux (e : K ≃+* K') (v : Place K)
    (u : (Place.localField K' (NK.GlobalCFTdeep.Transport.placeEquiv e v))ˣ)
    (hu : u ∈ Place.localUnits K' (NK.GlobalCFTdeep.Transport.placeEquiv e v)) :
    Units.map ((NK.GlobalCFTdeep.Transport.localFieldEquiv e v).symm.toMonoidHom) u ∈
      Place.localUnits K v := by
  refine (NK.GlobalCFTdeep.Transport.localFieldEquiv_localUnits e v _).mpr ?_
  have key : Units.map ((NK.GlobalCFTdeep.Transport.localFieldEquiv e v).toMonoidHom)
      (Units.map ((NK.GlobalCFTdeep.Transport.localFieldEquiv e v).symm.toMonoidHom) u) = u := by
    ext
    simp [Units.coe_map]
  rwa [key]

/-- Evaluation of the inverse transport at a place. -/
private theorem ideleEquiv_symm_apply_place_aux (e : K ≃+* K') (y : NK.GlobalCFT.Idele K')
    (v : Place K) :
    ((NK.GlobalCFTdeep.Transport.ideleEquiv e).symm y) v =
      Units.map ((NK.GlobalCFTdeep.Transport.localFieldEquiv e v).symm.toMonoidHom)
        (y ((NK.GlobalCFTdeep.Transport.placeEquiv e) v)) :=
  NK.GlobalCFTdeep.Transport.IdeleTransport.ideleEquiv_symm_apply_placeEquiv
    (NK.GlobalCFTdeep.Transport.placeEquiv e) (NK.GlobalCFTdeep.Transport.localFieldEquiv e)
    (fun v u => NK.GlobalCFTdeep.Transport.localFieldEquiv_localUnits e v u) y v

/-- The inverse of the local field transport is continuous. -/
private theorem continuous_localFieldEquiv_symm_aux {K K' : Type*} [Field K] [NumberField K] [Field K']
    [NumberField K'] (e : K ≃+* K') (v : Place K) :
    Continuous ⇑(NK.GlobalCFTdeep.Transport.localFieldEquiv e v).symm :=
  (Equiv.continuous_symm_iff (NK.GlobalCFTdeep.Transport.localFieldEquiv e v).toEquiv).mpr
    (isOpenMap_localFieldEquiv_aux e v)

/-- The inverse idèle transport is continuous. -/
private theorem continuous_ideleEquiv_symm_aux (e : K ≃+* K') :
    Continuous (NK.GlobalCFTdeep.Transport.ideleEquiv e).symm := by
  classical
  refine (RestrictedProduct.continuous_dom (R := fun j : Place K' => (Place.localField K' j)ˣ)
    (A := fun j : Place K' => Place.localUnits K' j) (𝓕 := Filter.cofinite)
    (f := ⇑(NK.GlobalCFTdeep.Transport.ideleEquiv e).symm)).mpr ?_
  intro S hS
  set T : Set (Place K) := (NK.GlobalCFTdeep.Transport.placeEquiv e).symm '' S with hT
  have hTle : Filter.cofinite ≤ Filter.principal T := by
    rw [Filter.le_principal_iff, Filter.mem_cofinite]
    have hSfin : Sᶜ.Finite := Filter.mem_cofinite.mp (Filter.le_principal_iff.mp hS)
    refine (hSfin.image (NK.GlobalCFTdeep.Transport.placeEquiv e).symm).subset ?_
    rintro j hj1
    refine ⟨(NK.GlobalCFTdeep.Transport.placeEquiv e) j, ?_,
      (NK.GlobalCFTdeep.Transport.placeEquiv e).symm_apply_apply j⟩
    intro hmem
    exact hj1 (by rw [hT]; exact ⟨(NK.GlobalCFTdeep.Transport.placeEquiv e) j, hmem,
      (NK.GlobalCFTdeep.Transport.placeEquiv e).symm_apply_apply j⟩)
  set G : (Πʳ j, [(Place.localField K' j)ˣ, Place.localUnits K' j]_[Filter.principal S]) →
      (Πʳ v, [(Place.localField K v)ˣ, Place.localUnits K v]_[Filter.principal T]) :=
    fun x => ⟨fun v => ((NK.GlobalCFTdeep.Transport.ideleEquiv e).symm
      (RestrictedProduct.inclusion (fun j : Place K' => (Place.localField K' j)ˣ)
        (fun j : Place K' => Place.localUnits K' j) hS x : NK.GlobalCFT.Idele K')) v, by
        rw [Filter.eventually_principal]
        intro v hv
        obtain ⟨j, hj, rfl⟩ := hv
        have hmem : (RestrictedProduct.inclusion (fun j : Place K' => (Place.localField K' j)ˣ)
            (fun j : Place K' => Place.localUnits K' j) hS x) j ∈ Place.localUnits K' j :=
          Filter.eventually_principal.mp x.2 j hj
        rw [← (NK.GlobalCFTdeep.Transport.placeEquiv e).apply_symm_apply j] at hmem
        show ((NK.GlobalCFTdeep.Transport.ideleEquiv e).symm
            (RestrictedProduct.inclusion (fun j : Place K' => (Place.localField K' j)ˣ)
              (fun j : Place K' => Place.localUnits K' j) hS x : NK.GlobalCFT.Idele K'))
            ((NK.GlobalCFTdeep.Transport.placeEquiv e).symm j) ∈
          Place.localUnits K ((NK.GlobalCFTdeep.Transport.placeEquiv e).symm j)
        rw [ideleEquiv_symm_apply_place_aux]
        exact localFieldEquiv_localUnits_symm_aux e ((NK.GlobalCFTdeep.Transport.placeEquiv e).symm j) _ hmem⟩ with hG
  have hGcont : Continuous G := by
    rw [RestrictedProduct.continuous_rng_of_principal_iff_forall]
    intro v
    show Continuous (fun x : (Πʳ j, [(Place.localField K' j)ˣ, Place.localUnits K' j]_[Filter.principal S]) =>
      (G x) v)
    have hfun : (fun x : (Πʳ j, [(Place.localField K' j)ˣ, Place.localUnits K' j]_[Filter.principal S]) =>
          (G x) v) =
        fun x => Units.map ((NK.GlobalCFTdeep.Transport.localFieldEquiv e v).symm.toMonoidHom)
          ((RestrictedProduct.inclusion (fun j : Place K' => (Place.localField K' j)ˣ)
            (fun j : Place K' => Place.localUnits K' j) hS x)
              ((NK.GlobalCFTdeep.Transport.placeEquiv e) v)) := by
      funext x
      exact ideleEquiv_symm_apply_place_aux e _ v
    rw [hfun]
    refine (Continuous.units_map _
      (continuous_localFieldEquiv_symm_aux e v)).comp ?_
    exact (RestrictedProduct.continuous_eval ((NK.GlobalCFTdeep.Transport.placeEquiv e) v)).congr (fun x => rfl)
  have hpiece : Continuous (fun x : (Πʳ j, [(Place.localField K' j)ˣ, Place.localUnits K' j]_[Filter.principal S]) =>
      RestrictedProduct.inclusion (fun v : Place K => (Place.localField K v)ˣ)
        (fun v : Place K => Place.localUnits K v) hTle (G x)) :=
    (RestrictedProduct.continuous_inclusion hTle).comp hGcont
  exact hpiece.congr (fun x => Subtype.ext (by funext v; rfl))

/-- The transport of the idèle class group is continuous. -/
private theorem continuous_ideleClassEquiv_aux {K K' : Type*} [Field K] [NumberField K] [Field K']
    [NumberField K'] (e : K ≃+* K') :
    Continuous (NK.GlobalCFTdeep.Transport.ideleClassEquiv e) := by
  have hcomp : (⇑(NK.GlobalCFTdeep.Transport.ideleClassEquiv e) ∘
      (QuotientGroup.mk : NK.GlobalCFT.Idele K → NK.GlobalCFT.IdeleClassGroup K)) =
      ((QuotientGroup.mk : NK.GlobalCFT.Idele K' → NK.GlobalCFT.IdeleClassGroup K')) ∘
        ⇑(NK.GlobalCFTdeep.Transport.ideleEquiv e) := by
    funext x
    exact NK.GlobalCFTdeep.Transport.ideleClassEquiv_mk e x
  refine (QuotientGroup.isOpenQuotientMap_mk (N := NK.GlobalCFT.Idele.principalSubgroup K)
    ).continuous_comp_iff (g := ⇑(NK.GlobalCFTdeep.Transport.ideleClassEquiv e)).mp ?_
  rw [hcomp]
  exact QuotientGroup.continuous_mk.comp (continuous_ideleEquiv_aux e)

/-- The inverse of the transport of the idèle class group is continuous. -/
private theorem continuous_ideleClassEquiv_symm_aux {K K' : Type*} [Field K] [NumberField K] [Field K']
    [NumberField K'] (e : K ≃+* K') :
    Continuous ⇑(NK.GlobalCFTdeep.Transport.ideleClassEquiv e).symm := by
  have hcomp : (⇑(NK.GlobalCFTdeep.Transport.ideleClassEquiv e).symm ∘
      (QuotientGroup.mk : NK.GlobalCFT.Idele K' → NK.GlobalCFT.IdeleClassGroup K')) =
      ((QuotientGroup.mk : NK.GlobalCFT.Idele K → NK.GlobalCFT.IdeleClassGroup K)) ∘
        ⇑(NK.GlobalCFTdeep.Transport.ideleEquiv e).symm := by
    funext y
    simp only [Function.comp_apply]
    refine (NK.GlobalCFTdeep.Transport.ideleClassEquiv e).injective ?_
    have h1 : (NK.GlobalCFTdeep.Transport.ideleClassEquiv e)
        (NK.GlobalCFT.IdeleClassGroup.mk K ((NK.GlobalCFTdeep.Transport.ideleEquiv e).symm y)) =
        NK.GlobalCFT.IdeleClassGroup.mk K' y := by
      rw [NK.GlobalCFTdeep.Transport.ideleClassEquiv_mk, MulEquiv.apply_symm_apply]
    rw [MulEquiv.apply_symm_apply]
    exact h1.symm
  refine (QuotientGroup.isOpenQuotientMap_mk (N := NK.GlobalCFT.Idele.principalSubgroup K')
    ).continuous_comp_iff (g := ⇑(NK.GlobalCFTdeep.Transport.ideleClassEquiv e).symm).mp ?_
  rw [hcomp]
  exact QuotientGroup.continuous_mk.comp (continuous_ideleEquiv_symm_aux e)

/-- **The transport of an open subgroup of the idèle class group is open.** -/
private theorem isOpen_map_ideleClassEquiv_aux {K K' : Type*} [Field K] [NumberField K] [Field K']
    [NumberField K'] (e : K ≃+* K') {V : Subgroup (NK.GlobalCFT.IdeleClassGroup K)}
    (hV : IsOpen (V : Set (NK.GlobalCFT.IdeleClassGroup K))) :
    IsOpen ((V.map (NK.GlobalCFTdeep.Transport.ideleClassEquiv e) :
      Subgroup (NK.GlobalCFT.IdeleClassGroup K')) :
      Set (NK.GlobalCFT.IdeleClassGroup K')) := by
  have h : V.map (NK.GlobalCFTdeep.Transport.ideleClassEquiv e) =
      V.comap ((NK.GlobalCFTdeep.Transport.ideleClassEquiv e).symm : C[K'] →* C[K]) :=
    Subgroup.map_equiv_eq_comap_symm _ _
  rw [h]
  exact hV.preimage (continuous_ideleClassEquiv_symm_aux e)


open scoped IsMulCommutative

/-- Commutativity of the multiplication transports along a multiplicative equivalence. -/
private theorem isMulCommutative_of_mulEquiv {G H : Type*} [Group G] [Group H]
    [IsMulCommutative G] (e : G ≃* H) : IsMulCommutative H := by
  refine IsMulCommutative.of_comm (fun a b => ?_)
  have h : e.symm (a * b) = e.symm (b * a) := by
    rw [map_mul, map_mul]
    exact IsMulCommutative.is_comm.comm _ _
  calc a * b = e (e.symm (a * b)) := (e.apply_symm_apply _).symm
    _ = e (e.symm (b * a)) := by rw [h]
    _ = b * a := e.apply_symm_apply _

theorem exists_abelian_level (hFC : NK.GlobalCFTdeep.FundamentalClassElement)
    (hEx : ∀ (K : Type) [Field K] [NumberField K], NK.GlobalCFT.ExistenceTheorem K)
    {K Ω : Type*} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    [IsSepClosure K Ω]
    (V : Subgroup (NK.GlobalCFT.IdeleClassGroup K)) (hV : V.FiniteIndex)
    (hVo : IsOpen (V : Set (NK.GlobalCFT.IdeleClassGroup K))) :
    ∃ F : NK.Reconstruct.FrobLevel K Ω, IsMulCommutative (↥F.L ≃ₐ[K] ↥F.L) ∧
      NK.GlobalCFT.Idele.normClassSubgroup K ↥F.L = V := by
  classical
  -- ## Step 0: shrink `K` to universe zero, so that the existence theorem applies
  haveI hKsmall : Small.{0} K := NK.NUV2.ShrinkModels.small_of_numberField K
  let E : K ≃+* Shrink.{0} K := (Shrink.ringEquiv K).symm
  let V' : Subgroup (NK.GlobalCFT.IdeleClassGroup (Shrink.{0} K)) :=
    V.map (NK.GlobalCFTdeep.Transport.ideleClassEquiv E)
  have hV'fin : V'.FiniteIndex := by
    rw [Subgroup.finiteIndex_iff] at hV ⊢
    rw [Subgroup.index_map_equiv]
    exact hV
  have hV'open : IsOpen (V' : Set (NK.GlobalCFT.IdeleClassGroup (Shrink.{0} K))) :=
    isOpen_map_ideleClassEquiv_aux E hVo
  -- ## Step 1: the class field of `V` given by the existence theorem, over the shrunk model
  obtain ⟨L₀, hFldL₀, hNfL₀, hAlgL₀, hFdL₀, hGalL₀, hN₀⟩ :=
    (hEx (Shrink.{0} K)).exists_normSubgroup V' hV'fin hV'open
  letI : Field L₀ := hFldL₀
  letI : NumberField L₀ := hNfL₀
  letI : Algebra (Shrink.{0} K) L₀ := hAlgL₀
  letI : FiniteDimensional (Shrink.{0} K) L₀ := hFdL₀
  letI : IsGalois (Shrink.{0} K) L₀ := hGalL₀
  -- ## Step 2: transport the structure to `K`
  letI : Algebra K (Shrink.{0} K) := Algebra.compHom (Shrink.{0} K) E.toRingHom
  letI : Algebra K L₀ := Algebra.compHom L₀ E.toRingHom
  have hcompat : (algebraMap K L₀).comp E.symm.toRingHom
      = (RingEquiv.refl L₀ : L₀ →+* L₀).comp (algebraMap (Shrink.{0} K) L₀) := by
    refine RingHom.ext fun y => ?_
    show algebraMap (Shrink.{0} K) L₀ (E (E.symm y)) = algebraMap (Shrink.{0} K) L₀ y
    rw [E.apply_symm_apply]
  haveI hfdK : FiniteDimensional K L₀ :=
    Module.Finite.of_equiv_equiv E.symm (RingEquiv.refl L₀) hcompat
  haveI hgalK : IsGalois K L₀ :=
    IsGalois.of_equiv_equiv (f := E.symm) (g := RingEquiv.refl L₀) hcompat
  have hnormK : NK.GlobalCFT.Idele.normClassSubgroup K L₀ = V := by
    have hmap := NK.GlobalCFTdeep.Transport.normClassSubgroup_map_ideleClassEquiv
      (K := K) (L := L₀) (K' := Shrink.{0} K) (L' := L₀) E (RingEquiv.refl L₀)
      (fun _ => rfl)
    refine Subgroup.map_injective
      (f := (NK.GlobalCFTdeep.Transport.ideleClassEquiv E).toMonoidHom)
      (NK.GlobalCFTdeep.Transport.ideleClassEquiv E).injective ?_
    rw [hmap, hN₀]
    rfl
  -- ## Step 3: replace `L₀` by its maximal abelian subextension
  let H : Subgroup (L₀ ≃ₐ[K] L₀) := commutator (L₀ ≃ₐ[K] L₀)
  haveI hHn : H.Normal := Subgroup.commutator_normal (⊤ : Subgroup (L₀ ≃ₐ[K] L₀)) ⊤
  let M₀ : IntermediateField K L₀ := IntermediateField.fixedField H
  haveI hgalM₀ : IsGalois K ↥M₀ := IsGalois.of_fixedField_normal_subgroup H
  haveI hfdM₀ : FiniteDimensional K ↥M₀ := IntermediateField.finiteDimensional_left M₀
  haveI hfdM₀L₀ : FiniteDimensional ↥M₀ L₀ := IntermediateField.finiteDimensional_right M₀
  haveI hnfM₀ : NumberField ↥M₀ :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField M₀
  haveI hcommM₀ : IsMulCommutative (↥M₀ ≃ₐ[K] ↥M₀) := by
    have eG : (↥M₀ ≃ₐ[K] ↥M₀) ≃* Abelianization (L₀ ≃ₐ[K] L₀) :=
      (IsGalois.normalAutEquivQuotient (K := K) (L := L₀) H).symm
    exact isMulCommutative_of_mulEquiv eG.symm
  have hnormM₀ : NK.GlobalCFT.Idele.normClassSubgroup K ↥M₀ = V :=
    (NK.NUV2.TowerRank.normClassSubgroup_fixedField_commutator hFC (K := K)
      (F := L₀)).trans hnormK
  -- ## Step 4: realise `M₀` as a level of `Ω`
  haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
  let φ : ↥M₀ →ₐ[K] Ω := IsSepClosed.lift
  let ψ : IntermediateField K Ω := φ.fieldRange
  let e : ↥M₀ ≃ₐ[K] ↥ψ := AlgEquiv.ofInjectiveField φ
  haveI hfinψ : FiniteDimensional K ↥ψ := LinearEquiv.finiteDimensional e.toLinearEquiv
  have hnormψ : Normal K ↥ψ := Normal.of_algEquiv e
  haveI : Normal K ↥ψ := hnormψ
  haveI hnfψ : NumberField ↥ψ :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField ψ
  have hT : V.map (NK.GlobalCFTdeep.Transport.ideleClassEquiv
      (RingEquiv.refl K)).toMonoidHom = V := by
    rw [← hnormM₀]
    exact NK.GlobalCFTdeep.Transport.normClassSubgroup_map_ideleClassEquiv
      (RingEquiv.refl K) (RingEquiv.refl ↥M₀) (fun _ => rfl)
  have hNψ : NK.GlobalCFT.Idele.normClassSubgroup K ↥ψ = V := by
    have hmap := NK.GlobalCFTdeep.Transport.normClassSubgroup_map_ideleClassEquiv
      (K := K) (L := ↥M₀) (K' := K) (L' := ↥ψ) (RingEquiv.refl K) (e : ↥M₀ ≃+* ↥ψ)
      (fun x => e.commutes x)
    rw [← hmap, hnormM₀, hT]
  refine ⟨{ L := ψ, finite := hfinψ, normal := hnormψ, numberField := hnfψ }, ?_, ?_⟩
  · exact isMulCommutative_of_mulEquiv (AlgEquiv.autCongr e)
  · exact hNψ

end NK.NUV2.TowerRank
