import Mathlib
import Submission.Work.SSS.serreE1Transport

/-!
# Auxiliary material for the concatenation coherence of the canonical fibre transport

This file collects the vocabulary used in the proof of `Work.SSS.transportIsoPath_trans`, the
compatibility of the canonical fibre transport `Work.SSS.transportIsoPath` with concatenation of
paths.

For a Serre fibration `p : E → B` and a path `γ : Path b b'`, the canonical transport
`transportIsoPath p hp γ j` is the composite

`HZ (p⁻¹b) ≅ HZ (q_γ⁻¹{0}) → HZ (Pullback p γ) → HZ (q_γ⁻¹{1}) ≅ HZ (p⁻¹b')`

of the fibre homeomorphisms of the pullback with the two homology isomorphisms induced by the
inclusions of the fibres of `q_γ = pullbackSnd p γ : Pullback p γ → I` over `0` and `1`.  For the
concatenation `γ.trans δ` the pullback `Pullback p (γ.trans δ)` is neither `Pullback p γ` nor
`Pullback p δ`; the three are compared through the reparametrisation maps

* `phiMap : (e,t) ↦ (e, t/2) : Pullback p γ → Pullback p (γ.trans δ)`,
* `psiMap : (e,t) ↦ (e, t/2+1/2) : Pullback p δ → Pullback p (γ.trans δ)`,

and the naturality squares of the fibre inclusions along them.  This file provides:

* `HZmap`, `inclHZ` — the homology maps induced by a continuous map and by an inclusion;
* the reparametrisations `halfIcc`, `halfShiftIcc` of the interval, the midpoint `midI`, and the
  evaluation lemmas `trans_half_apply`, `trans_halfShift_apply` at the concatenation;
* `inclIso`, `pbTrans` — the inclusion of the fibre of a pullback as an isomorphism and the
  transport of a fibration over the interval between the fibres over two points, together with the
  identification `pullbackTransportIso_eq_pbTrans` with the transport of `serreE1Transport`;
* `phiMap`, `psiMap` and the homeomorphisms `phiZeroHomeo`, `phiTwelfthHomeo`,
  `psiTwelfthHomeo`, `psiOneHomeo` induced by them on the relevant fibres;
* the naturality squares `inclHZ_phiMap_zero`, `inclHZ_phiMap_mid`, `inclHZ_psiMap_mid`,
  `inclHZ_psiMap_one` for these homeomorphisms;
* the endpoint identifications `pathSrc`, `pathTgt`, `pathCore` of `transportIsoPath` and their
  compatibility with concatenation.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.SSS

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-! ## The homology map induced by a continuous map -/

/-- The map induced on integral singular homology by a continuous map. -/
def HZmap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (j : ℕ) :
    Work.PiS.HZ X j ⟶ Work.PiS.HZ Y j :=
  HomologicalComplex.homologyMap
    (Work.Cohomology.chainMap ℤ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f)) j

/-- The map induced on integral singular homology by the inclusion of a subspace. -/
def inclHZ (X : Type) [TopologicalSpace X] (A : Set X) (j : ℕ) :
    Work.PiS.HZ ↥A j ⟶ Work.PiS.HZ X j :=
  HomologicalComplex.homologyMap (Work.Cohomology.inclChains (TopCat.of X) A) j

/-- Functoriality of the singular chain complex under composition. -/
theorem chainMap_comp_chains {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Work.Cohomology.chainMap ℤ X Y f ≫ Work.Cohomology.chainMap ℤ Y Z g =
      Work.Cohomology.chainMap ℤ X Z (f ≫ g) :=
  (CategoryTheory.Functor.map_comp _ f g).symm

theorem HZmap_id {X : Type} [TopologicalSpace X] (j : ℕ) :
    HZmap (ContinuousMap.id X) j = 𝟙 (Work.PiS.HZ X j) := by
  rw [HZmap]
  rw [show Work.Cohomology.chainMap ℤ (TopCat.of X) (TopCat.of X) (TopCat.ofHom (ContinuousMap.id X))
      = 𝟙 _ from by
    show _ = 𝟙 (Cohomology.singularChains ℤ (TopCat.of X))
    rw [Work.Cohomology.chainMap, show TopCat.ofHom (ContinuousMap.id X) = 𝟙 (TopCat.of X) from rfl]
    exact CategoryTheory.Functor.map_id _ _]
  rw [HomologicalComplex.homologyMap_id]

theorem HZmap_comp {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) (j : ℕ) :
    HZmap (g.comp f) j = HZmap f j ≫ HZmap g j := by
  rw [HZmap, HZmap, HZmap]
  rw [Work.Cohomology.chainMap, Work.Cohomology.chainMap, Work.Cohomology.chainMap]
  rw [show TopCat.ofHom (g.comp f) = TopCat.ofHom f ≫ TopCat.ofHom g from TopCat.ofHom_comp f g]
  rw [CategoryTheory.Functor.map_comp]
  rw [HomologicalComplex.homologyMap_comp]

theorem HZmap_congr {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (h : f = g) (j : ℕ) : HZmap f j = HZmap g j := by
  rw [h]

/-- The forward map of `HZHomeoIso` is the homology map of the underlying continuous map. -/
theorem HZHomeoIso_hom_HZmap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (j : ℕ) : (HZHomeoIso e j).hom = HZmap (e : C(X, Y)) j := by
  rw [HZHomeoIso, HZmap]
  rw [Functor.mapIso_hom, Functor.mapIso_hom, TopCat.isoOfHomeo_hom]
  rfl

theorem HZHomeoIso_refl' {X : Type} [TopologicalSpace X] (j : ℕ) :
    HZHomeoIso (Homeomorph.refl X) j = Iso.refl (Work.PiS.HZ X j) := by
  have h1 : (TopCat.isoOfHomeo (Homeomorph.refl X) : TopCat.of X ≅ TopCat.of X) = Iso.refl _ := by
    refine Iso.ext ?_
    show TopCat.ofHom (↑(Homeomorph.refl X) : C(X, X)) = 𝟙 (TopCat.of X)
    rfl
  simp only [HZHomeoIso, h1, CategoryTheory.Functor.mapIso_refl]
  rfl

theorem HZHomeoIso_trans' {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (e₁ : X ≃ₜ Y) (e₂ : Y ≃ₜ Z) (j : ℕ) :
    HZHomeoIso (e₁.trans e₂) j = HZHomeoIso e₁ j ≪≫ HZHomeoIso e₂ j := by
  have h1 : (TopCat.isoOfHomeo (e₁.trans e₂ : TopCat.of X ≃ₜ TopCat.of Z) :
        TopCat.of X ≅ TopCat.of Z) =
      (TopCat.isoOfHomeo (e₁ : TopCat.of X ≃ₜ TopCat.of Y) : TopCat.of X ≅ TopCat.of Y) ≪≫
        (TopCat.isoOfHomeo (e₂ : TopCat.of Y ≃ₜ TopCat.of Z) : TopCat.of Y ≅ TopCat.of Z) := by
    refine Iso.ext ?_
    show TopCat.ofHom (↑(e₁.trans e₂) : C(X, Z)) =
      TopCat.ofHom (↑e₁ : C(X, Y)) ≫ TopCat.ofHom (↑e₂ : C(Y, Z))
    rfl
  simp only [HZHomeoIso, h1, CategoryTheory.Functor.mapIso_trans]
  rfl

theorem HZHomeoIso_symm' {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (j : ℕ) : (HZHomeoIso e j).symm = HZHomeoIso e.symm j := by
  have h1 : (TopCat.isoOfHomeo (e.symm : TopCat.of Y ≃ₜ TopCat.of X) :
        TopCat.of Y ≅ TopCat.of X) =
      (TopCat.isoOfHomeo (e : TopCat.of X ≃ₜ TopCat.of Y) : TopCat.of X ≅ TopCat.of Y).symm := by
    refine Iso.ext ?_
    show TopCat.ofHom (↑(e.symm) : C(Y, X)) = TopCat.ofHom (↑(e.symm) : C(Y, X))
    rfl
  simp only [HZHomeoIso, h1, CategoryTheory.Functor.mapIso_symm]
  rfl

/-- The canonical homeomorphism between the fibres of `p` over equal base points. -/
def fibrePointHomeo (p : C(E, B)) {b b' : B} (h : b = b') :
    Work.StemsB.fibre p b ≃ₜ Work.StemsB.fibre p b' where
  toFun y := ⟨y.1, h ▸ y.2⟩
  invFun y := ⟨y.1, h.symm ▸ y.2⟩
  left_inv y := by cases h; rfl
  right_inv y := by cases h; rfl
  continuous_toFun := continuous_subtype_val.subtype_mk (fun y => h ▸ y.2)
  continuous_invFun := continuous_subtype_val.subtype_mk (fun y => h.symm ▸ y.2)

theorem fibrePointHomeo_symm (p : C(E, B)) {b b' : B} (h : b = b') :
    (fibrePointHomeo p h).symm = fibrePointHomeo p h.symm := by
  cases h
  exact Homeomorph.ext (fun y => rfl)

/-- The endpoint correction of `Work.SSS.transportIsoPath` is the homology isomorphism induced by
the canonical homeomorphism of the fibres. -/
theorem eqToIso_fibre_eq' (p : C(E, B)) {b b' : B} (h : b = b') (j : ℕ) :
    eqToIso (congrArg (fun x => Work.PiS.HZ (Work.StemsB.fibre p x) j) h) =
      HZHomeoIso (fibrePointHomeo p h) j := by
  cases h
  rw [show fibrePointHomeo p rfl = Homeomorph.refl (Work.StemsB.fibre p b) from
    Homeomorph.ext (fun y => rfl), HZHomeoIso_refl',
    show congrArg (fun x => Work.PiS.HZ (Work.StemsB.fibre p x) j) (rfl : b = b) = rfl from rfl,
    eqToIso_refl]

/-- **Naturality of the fibre inclusions** along a continuous map of spaces over the interval. -/
theorem inclHZ_comp_HZmap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (qX : C(X, unitInterval)) (qY : C(Y, unitInterval)) (f : C(X, Y))
    {t s : unitInterval} (g : C(↥{x : X | qX x = t}, ↥{y : Y | qY y = s}))
    (hg : ∀ x, (g x : Y) = f x) (j : ℕ) :
    inclHZ X {x : X | qX x = t} j ≫ HZmap f j
      = HZmap g j ≫ inclHZ Y {y : Y | qY y = s} j := by
  have hsq : (Work.Cohomology.subtypeIncl (TopCat.of X) {x : X | qX x = t}) ≫ TopCat.ofHom f
      = TopCat.ofHom g ≫ (Work.Cohomology.subtypeIncl (TopCat.of Y) {y : Y | qY y = s}) := by
    ext x
    exact (hg x).symm
  rw [inclHZ, inclHZ, HZmap, HZmap]
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
  congr 1
  rw [chainMap_comp_chains, chainMap_comp_chains, hsq]

/-! ## The reparametrisations of the unit interval -/

/-- The midpoint of the unit interval. -/
def midI : unitInterval := ⟨1/2, by norm_num⟩

/-- The reparametrisation `t ↦ t/2` of the unit interval. -/
def halfIcc : C(unitInterval, unitInterval) where
  toFun t := ⟨(t : ℝ) / 2, by
    constructor
    · linarith [t.2.1]
    · linarith [t.2.2]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk (f := fun t : unitInterval => (t : ℝ) / 2)
    fun_prop

/-- The reparametrisation `t ↦ t/2 + 1/2` of the unit interval. -/
def halfShiftIcc : C(unitInterval, unitInterval) where
  toFun t := ⟨(t : ℝ) / 2 + 1 / 2, by
    constructor
    · linarith [t.2.1]
    · linarith [t.2.2]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk (f := fun t : unitInterval => (t : ℝ) / 2 + 1 / 2)
    fun_prop

theorem halfIcc_one : halfIcc 1 = midI := by ext; norm_num [halfIcc, midI]

theorem halfShiftIcc_zero : halfShiftIcc 0 = midI := by ext; norm_num [halfShiftIcc, midI]

theorem halfIcc_zero : halfIcc 0 = (0 : unitInterval) := by ext; norm_num [halfIcc]

theorem halfShiftIcc_one : halfShiftIcc 1 = (1 : unitInterval) := by
  ext; norm_num [halfShiftIcc]

theorem trans_half_apply {b b' b'' : B} (γ : Path b b') (δ : Path b' b'') (t : unitInterval) :
    (γ.trans δ) (halfIcc t) = γ t := by
  rw [Path.trans_apply]
  rw [dif_pos (show ((halfIcc t : unitInterval) : ℝ) ≤ 1 / 2 by
    show (t : ℝ) / 2 ≤ 1 / 2
    linarith [t.2.2])]
  congr 1
  ext
  show 2 * ((halfIcc t : unitInterval) : ℝ) = (t : ℝ)
  norm_num [halfIcc]
  ring

theorem trans_halfShift_apply {b b' b'' : B} (γ : Path b b') (δ : Path b' b'')
    (t : unitInterval) : (γ.trans δ) (halfShiftIcc t) = δ t := by
  rw [Path.trans_apply]
  rcases eq_or_ne t 0 with rfl | ht
  · rw [dif_pos (show ((halfShiftIcc 0 : unitInterval) : ℝ) ≤ 1 / 2 by
      norm_num [halfShiftIcc])]
    rw [show (⟨2 * (halfShiftIcc 0 : unitInterval), _⟩ : unitInterval) = 1 from by
      ext; norm_num [halfShiftIcc]]
    rw [Path.target, Path.source]
  · rw [dif_neg (show ¬ ((halfShiftIcc t : unitInterval) : ℝ) ≤ 1 / 2 by
      have ht' : (0 : ℝ) < (t : ℝ) :=
        lt_of_le_of_ne t.2.1 (fun h => ht (Subtype.ext h.symm))
      rw [show ((halfShiftIcc t : unitInterval) : ℝ) = (t : ℝ) / 2 + 1 / 2 from rfl]
      linarith)]
    congr 1
    ext
    show 2 * ((halfShiftIcc t : unitInterval) : ℝ) - 1 = (t : ℝ)
    rw [show ((halfShiftIcc t : unitInterval) : ℝ) = (t : ℝ) / 2 + 1 / 2 from rfl]
    ring

theorem trans_zero_apply {b b' b'' : B} (γ : Path b b') (δ : Path b' b'') :
    (γ.trans δ) 0 = γ 0 := by
  conv_lhs => rw [← halfIcc_zero]
  exact trans_half_apply γ δ 0

theorem trans_one_apply {b b' b'' : B} (γ : Path b b') (δ : Path b' b'') :
    (γ.trans δ) 1 = δ 1 := by
  conv_lhs => rw [← halfShiftIcc_one]
  exact trans_halfShift_apply γ δ 1

theorem trans_mid_left {b b' b'' : B} (γ : Path b b') (δ : Path b' b'') :
    (γ.trans δ) midI = γ 1 := by
  conv_lhs => rw [← halfIcc_one]
  exact trans_half_apply γ δ 1

theorem trans_mid_right {b b' b'' : B} (γ : Path b b') (δ : Path b' b'') :
    (γ.trans δ) midI = δ 0 := by
  conv_lhs => rw [← halfShiftIcc_zero]
  exact trans_halfShift_apply γ δ 0

/-! ## The contraction of the interval onto an arbitrary point -/

/-- The contraction of the unit interval onto the point `t`, fixing `t`. -/
def unitContrTo (t : unitInterval) : C(unitInterval × unitInterval, unitInterval) where
  toFun q := ⟨(1 - (q.2 : ℝ)) * (q.1 : ℝ) + (q.2 : ℝ) * (t : ℝ), by
    constructor
    · have h1 : 0 ≤ (q.2 : ℝ) * (t : ℝ) := mul_nonneg q.2.2.1 t.2.1
      have h2 : 0 ≤ (1 - (q.2 : ℝ)) * (q.1 : ℝ) :=
        mul_nonneg (by linarith [q.2.2.2]) q.1.2.1
      linarith
    · have h1 : (q.2 : ℝ) * (t : ℝ) ≤ (q.2 : ℝ) :=
        mul_le_of_le_one_right q.2.2.1 t.2.2
      have h2 : (1 - (q.2 : ℝ)) * (q.1 : ℝ) ≤ (1 - (q.2 : ℝ)) :=
        mul_le_of_le_one_right (by linarith [q.2.2.2]) q.1.2.2
      have h3 : (1 - (q.2 : ℝ)) + (q.2 : ℝ) = 1 := by ring
      nlinarith [h1, h2]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk (f := fun q : unitInterval × unitInterval =>
      (1 - (q.2 : ℝ)) * (q.1 : ℝ) + (q.2 : ℝ) * (t : ℝ))
    fun_prop

theorem unitContrTo_zero (t x : unitInterval) : unitContrTo t (x, 0) = x := by
  ext
  show (1 - (0 : ℝ)) * (x : ℝ) + (0 : ℝ) * (t : ℝ) = (x : ℝ)
  ring

theorem unitContrTo_one (t x : unitInterval) : unitContrTo t (x, 1) = t := by
  ext
  show (1 - (1 : ℝ)) * (x : ℝ) + (1 : ℝ) * (t : ℝ) = (t : ℝ)
  ring

theorem unitContrTo_fixes (t s : unitInterval) : unitContrTo t (t, s) = t := by
  ext
  show (1 - (s : ℝ)) * (t : ℝ) + (s : ℝ) * (t : ℝ) = (t : ℝ)
  ring

/-! ## Vanishing of the relative homology of the fibres of a pullback over the interval -/

theorem isZero_relChains_fibre_pb_any (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    (δ : C(unitInterval, B)) (t : unitInterval) (m : ℕ) :
    IsZero ((Work.Cohomology.relChains (TopCat.of (Work.StemsB.Pullback p δ))
      {x : Work.StemsB.Pullback p δ | Work.StemsB.pullbackSnd p δ x = t}).homology m) :=
  Work.Serre.isZero_relChains_fibre_of_contraction (Work.StemsB.pullbackSnd p δ)
    (fun i => Work.StemsB.hasHLP_pullback p δ (hp i)) t (unitContrTo t) (unitContrTo_zero t)
    (unitContrTo_one t) (unitContrTo_fixes t) m

/-- The inclusion of the fibre of the pullback over any point is a homology isomorphism. -/
theorem isIso_inclHZ_pb_any (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    (δ : C(unitInterval, B)) (t : unitInterval) (j : ℕ) :
    IsIso (inclHZ (Work.StemsB.Pullback p δ)
      {x : Work.StemsB.Pullback p δ | Work.StemsB.pullbackSnd p δ x = t} j) :=
  Work.Serre.isIso_inclChains_homologyMap_of_isZero_relChains _
    (fun m => isZero_relChains_fibre_pb_any p hp δ t m) j

/-- **The inclusion of the fibre of the pullback over `t`**, packaged as an isomorphism. -/
def inclIso (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (δ : C(unitInterval, B))
    (t : unitInterval) (j : ℕ) :
    Work.PiS.HZ ↥{x : Work.StemsB.Pullback p δ | Work.StemsB.pullbackSnd p δ x = t} j ≅
      Work.PiS.HZ (Work.StemsB.Pullback p δ) j := by
  haveI : IsIso (inclHZ (Work.StemsB.Pullback p δ)
      {x : Work.StemsB.Pullback p δ | Work.StemsB.pullbackSnd p δ x = t} j) :=
    isIso_inclHZ_pb_any p hp δ t j
  exact asIso (inclHZ (Work.StemsB.Pullback p δ)
      {x : Work.StemsB.Pullback p δ | Work.StemsB.pullbackSnd p δ x = t} j)

/-- **The transport of the pullback of `p` along `δ`** between the fibres over `t₀` and `t₁`,
namely the inclusion of the fibre over `t₀` followed by the inverse of the inclusion of the fibre
over `t₁`. -/
def pbTrans (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (δ : C(unitInterval, B))
    (t₀ t₁ : unitInterval) (j : ℕ) :
    Work.PiS.HZ ↥{x : Work.StemsB.Pullback p δ | Work.StemsB.pullbackSnd p δ x = t₀} j ≅
      Work.PiS.HZ ↥{x : Work.StemsB.Pullback p δ | Work.StemsB.pullbackSnd p δ x = t₁} j :=
  inclIso p hp δ t₀ j ≪≫ (inclIso p hp δ t₁ j).symm

/-- **Unfolding of the pullback transport** of `serreE1Transport` into the two fibre inclusions. -/
theorem pullbackTransportIso_eq_pbTrans (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    (δ : C(unitInterval, B)) (j : ℕ) :
    pullbackTransportIso p hp δ j = pbTrans p hp δ 0 1 j := by
  rw [pullbackTransportIso, pbTrans, inclIso, inclIso]
  rfl

/-- The transport of the pullback is transitive. -/
theorem pbTrans_trans (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (δ : C(unitInterval, B))
    (s t u : unitInterval) (j : ℕ) :
    pbTrans p hp δ s t j ≪≫ pbTrans p hp δ t u j = pbTrans p hp δ s u j := by
  rw [pbTrans, pbTrans, pbTrans, Iso.trans_assoc, Iso.symm_self_id_assoc]

/-- The transport of the pullback of `γ : Path b b'` between the fibres over `0` and `1`. -/
def pathTrans (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) {b b' : B} (γ : Path b b')
    (j : ℕ) :
    Work.PiS.HZ ↥{x : Work.StemsB.Pullback p γ.toContinuousMap |
        Work.StemsB.pullbackSnd p γ.toContinuousMap x = 0} j ≅
      Work.PiS.HZ ↥{x : Work.StemsB.Pullback p γ.toContinuousMap |
        Work.StemsB.pullbackSnd p γ.toContinuousMap x = 1} j :=
  pbTrans p hp γ.toContinuousMap 0 1 j

theorem pullbackTransportIso_eq_pathTrans (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    {b b' : B} (γ : Path b b') (j : ℕ) :
    pullbackTransportIso p hp γ.toContinuousMap j = pathTrans p hp γ j :=
  pullbackTransportIso_eq_pbTrans p hp γ.toContinuousMap j

/-! ## The reparametrisations of the pullback along a concatenation -/

/-- The map `φ : (e,t) ↦ (e, t/2)` from the pullback of `p` along `γ` to the pullback along the
concatenation `γ.trans δ`. -/
def phiMap (p : C(E, B)) {b b' b'' : B} (γ : Path b b') (δ : Path b' b'') :
    C(Work.StemsB.Pullback p γ.toContinuousMap,
      Work.StemsB.Pullback p (γ.trans δ).toContinuousMap) where
  toFun x := ⟨(x.1.1, halfIcc x.1.2), by
    show p x.1.1 = (γ.trans δ) (halfIcc x.1.2)
    rw [trans_half_apply]
    exact x.2⟩
  continuous_toFun :=
    ((continuous_fst.comp continuous_subtype_val).prodMk
        (halfIcc.continuous.comp (continuous_snd.comp continuous_subtype_val))).subtype_mk
      (fun x => by
        show p x.1.1 = (γ.trans δ) (halfIcc x.1.2)
        rw [trans_half_apply]
        exact x.2)

/-- The map `ψ : (e,t) ↦ (e, t/2+1/2)` from the pullback of `p` along `δ` to the pullback along
the concatenation `γ.trans δ`. -/
def psiMap (p : C(E, B)) {b b' b'' : B} (γ : Path b b') (δ : Path b' b'') :
    C(Work.StemsB.Pullback p δ.toContinuousMap,
      Work.StemsB.Pullback p (γ.trans δ).toContinuousMap) where
  toFun x := ⟨(x.1.1, halfShiftIcc x.1.2), by
    show p x.1.1 = (γ.trans δ) (halfShiftIcc x.1.2)
    rw [trans_halfShift_apply]
    exact x.2⟩
  continuous_toFun :=
    ((continuous_fst.comp continuous_subtype_val).prodMk
        (halfShiftIcc.continuous.comp (continuous_snd.comp continuous_subtype_val))).subtype_mk
      (fun x => by
        show p x.1.1 = (γ.trans δ) (halfShiftIcc x.1.2)
        rw [trans_halfShift_apply]
        exact x.2)

/-- The homeomorphism induced by `φ` on the fibres over `0`. -/
def phiZeroHomeo (p : C(E, B)) {b b' b'' : B} (γ : Path b b') (δ : Path b' b'') :
    ↥{x : Work.StemsB.Pullback p γ.toContinuousMap |
        Work.StemsB.pullbackSnd p γ.toContinuousMap x = 0} ≃ₜ
      ↥{x : Work.StemsB.Pullback p (γ.trans δ).toContinuousMap |
        Work.StemsB.pullbackSnd p (γ.trans δ).toContinuousMap x = 0} :=
  (pullbackFibreHomeo p γ.toContinuousMap 0).trans
    ((fibrePointHomeo p (trans_zero_apply γ δ).symm).trans
      (pullbackFibreHomeo p (γ.trans δ).toContinuousMap 0).symm)

/-- The homeomorphism induced by `φ` on the fibre over `1` (which lands over `1/2`). -/
def phiTwelfthHomeo (p : C(E, B)) {b b' b'' : B} (γ : Path b b') (δ : Path b' b'') :
    ↥{x : Work.StemsB.Pullback p γ.toContinuousMap |
        Work.StemsB.pullbackSnd p γ.toContinuousMap x = 1} ≃ₜ
      ↥{x : Work.StemsB.Pullback p (γ.trans δ).toContinuousMap |
        Work.StemsB.pullbackSnd p (γ.trans δ).toContinuousMap x = midI} :=
  (pullbackFibreHomeo p γ.toContinuousMap 1).trans
    ((fibrePointHomeo p (trans_mid_left γ δ).symm).trans
      (pullbackFibreHomeo p (γ.trans δ).toContinuousMap midI).symm)

/-- The homeomorphism induced by `ψ` on the fibre over `0` (which lands over `1/2`). -/
def psiTwelfthHomeo (p : C(E, B)) {b b' b'' : B} (γ : Path b b') (δ : Path b' b'') :
    ↥{x : Work.StemsB.Pullback p δ.toContinuousMap |
        Work.StemsB.pullbackSnd p δ.toContinuousMap x = 0} ≃ₜ
      ↥{x : Work.StemsB.Pullback p (γ.trans δ).toContinuousMap |
        Work.StemsB.pullbackSnd p (γ.trans δ).toContinuousMap x = midI} :=
  (pullbackFibreHomeo p δ.toContinuousMap 0).trans
    ((fibrePointHomeo p (trans_mid_right γ δ).symm).trans
      (pullbackFibreHomeo p (γ.trans δ).toContinuousMap midI).symm)

/-- The homeomorphism induced by `ψ` on the fibres over `1`. -/
def psiOneHomeo (p : C(E, B)) {b b' b'' : B} (γ : Path b b') (δ : Path b' b'') :
    ↥{x : Work.StemsB.Pullback p δ.toContinuousMap |
        Work.StemsB.pullbackSnd p δ.toContinuousMap x = 1} ≃ₜ
      ↥{x : Work.StemsB.Pullback p (γ.trans δ).toContinuousMap |
        Work.StemsB.pullbackSnd p (γ.trans δ).toContinuousMap x = 1} :=
  (pullbackFibreHomeo p δ.toContinuousMap 1).trans
    ((fibrePointHomeo p (trans_one_apply γ δ).symm).trans
      (pullbackFibreHomeo p (γ.trans δ).toContinuousMap 1).symm)

/-! ## The fibres of a pullback and the endpoint identifications of `transportIsoPath` -/

/-- The fibre of the pullback of `p` along `δ` over the point `t`. -/
abbrev PbF (p : C(E, B)) (δ : C(unitInterval, B)) (t : unitInterval) : Type :=
  ↥{x : Work.StemsB.Pullback p δ | Work.StemsB.pullbackSnd p δ x = t}

/-- The source identification of `transportIsoPath`, from the fibre over the source of the path. -/
def pathSrc (p : C(E, B)) {b b' : B} (γ : Path b b') (j : ℕ) :
    Work.PiS.HZ (Work.StemsB.fibre p b) j ≅ Work.PiS.HZ (Work.StemsB.fibre p (γ 0)) j :=
  eqToIso (congrArg (fun x => Work.PiS.HZ (Work.StemsB.fibre p x) j) γ.source'.symm)

/-- The target identification of `transportIsoPath`, to the fibre over the target of the path. -/
def pathTgt (p : C(E, B)) {b b' : B} (γ : Path b b') (j : ℕ) :
    Work.PiS.HZ (Work.StemsB.fibre p (γ 1)) j ≅ Work.PiS.HZ (Work.StemsB.fibre p b') j :=
  eqToIso (congrArg (fun x => Work.PiS.HZ (Work.StemsB.fibre p x) j) γ.target')

/-- The core transport of `transportIsoPath`, between the fibres over the declared endpoints. -/
def pathCore (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) {b b' : B} (γ : Path b b')
    (j : ℕ) :
    Work.PiS.HZ (Work.StemsB.fibre p (γ 0)) j ≅ Work.PiS.HZ (Work.StemsB.fibre p (γ 1)) j :=
  (HZHomeoIso (pullbackFibreHomeo p γ.toContinuousMap 0) j).symm ≪≫
    pathTrans p hp γ j ≪≫
    HZHomeoIso (pullbackFibreHomeo p γ.toContinuousMap 1) j

/-- The core transport in terms of the transport of `serreE1Transport`. -/
theorem pathCore_eq (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) {b b' : B}
    (γ : Path b b') (j : ℕ) :
    pathCore p hp γ j =
      (HZHomeoIso (pullbackFibreHomeo p γ.toContinuousMap 0) j).symm ≪≫
        pullbackTransportIso p hp γ.toContinuousMap j ≪≫
        HZHomeoIso (pullbackFibreHomeo p γ.toContinuousMap 1) j := by
  rw [pathCore, pullbackTransportIso_eq_pathTrans]

/-- `transportIsoPath` unfolds into the source identification, the core transport and the target
identification. -/
theorem transportIsoPath_eq (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) {b b' : B}
    (γ : Path b b') (j : ℕ) :
    transportIsoPath p hp γ j = pathSrc p γ j ≪≫ pathCore p hp γ j ≪≫ pathTgt p γ j := by
  rw [transportIsoPath, pathCore, pathSrc, pathTgt, pathTrans, pullbackTransportIso_eq_pbTrans]
  simp only [CategoryTheory.Iso.trans_assoc]

/-- The identification of the fibres of the pullbacks of `γ` and of the concatenation at the
source of `γ`. -/
def pcSrc (p : C(E, B)) {b b' b'' : B} (γ : Path b b') (δ : Path b' b'') (j : ℕ) :
    Work.PiS.HZ (Work.StemsB.fibre p (γ 0)) j ≅
      Work.PiS.HZ (Work.StemsB.fibre p ((γ.trans δ) 0)) j :=
  eqToIso (congrArg (fun x => Work.PiS.HZ (Work.StemsB.fibre p x) j)
    (trans_zero_apply γ δ).symm)

/-- The identification of the fibres of the pullbacks of `δ` and of the concatenation at the
target of `δ`. -/
def pcTgt (p : C(E, B)) {b b' b'' : B} (γ : Path b b') (δ : Path b' b'') (j : ℕ) :
    Work.PiS.HZ (Work.StemsB.fibre p ((γ.trans δ) 1)) j ≅
      Work.PiS.HZ (Work.StemsB.fibre p (δ 1)) j :=
  eqToIso (congrArg (fun x => Work.PiS.HZ (Work.StemsB.fibre p x) j)
    (trans_one_apply γ δ))

/-- The identification of the fibres of `p` over the two endpoints of the junction of `γ` and
`δ`. -/
def pcMid (p : C(E, B)) {b b' b'' : B} (γ : Path b b') (δ : Path b' b'') (j : ℕ) :
    Work.PiS.HZ (Work.StemsB.fibre p (γ 1)) j ≅
      Work.PiS.HZ (Work.StemsB.fibre p (δ 0)) j :=
  eqToIso (congrArg (fun x => Work.PiS.HZ (Work.StemsB.fibre p x) j)
    ((Path.target γ).trans (Path.source δ).symm))

/-- The source identifications are compatible with concatenation. -/
theorem pathSrc_trans (p : C(E, B)) {b b' b'' : B} (γ : Path b b') (δ : Path b' b'') (j : ℕ) :
    pathSrc p (γ.trans δ) j = pathSrc p γ j ≪≫ pcSrc p γ δ j := by
  rw [pathSrc, pathSrc, pcSrc, eqToIso_trans]

/-- The target identifications are compatible with concatenation. -/
theorem pathTgt_trans (p : C(E, B)) {b b' b'' : B} (γ : Path b b') (δ : Path b' b'') (j : ℕ) :
    pathTgt p (γ.trans δ) j = pcTgt p γ δ j ≪≫ pathTgt p δ j := by
  rw [pathTgt, pathTgt, pcTgt, eqToIso_trans]

/-- The junction identification is the composite of the target identification of `γ` and the
source identification of `δ`. -/
theorem pathTgt_pathSrc (p : C(E, B)) {b b' b'' : B} (γ : Path b b') (δ : Path b' b'') (j : ℕ) :
    pathTgt p γ j ≪≫ pathSrc p δ j = pcMid p γ δ j := by
  rw [pathTgt, pathSrc, pcMid, eqToIso_trans]

/-! ## A generic cancellation lemma for transports through two ambient objects -/

/-- **Two transports computed through different ambient objects agree.**  If `i₀, i₁, h₀, h₁, k₀,
k₁` are isomorphisms and the morphisms `i₀ ≫ j` and `h₀ ≫ k₀` (resp. `i₁ ≫ j` and `h₁ ≫ k₁`) agree
for a common morphism `j`, then the transport `i₀ ≫ i₁⁻¹` between the two sources agrees with the
one computed through the factorisation `h₀ ≫ k₀ ≫ k₁⁻¹ ≫ h₁⁻¹`. -/
theorem iso_cancel_hom {C : Type*} [Category C] {A B D C' E : C}
    (i₀ : A ≅ D) (i₁ : B ≅ D) (h₀ : A ≅ C') (h₁ : B ≅ C') (k₀ : C' ≅ E) (k₁ : C' ≅ E)
    (j : D ⟶ E) (e₀ : i₀.hom ≫ j = h₀.hom ≫ k₀.hom) (e₁ : i₁.hom ≫ j = h₁.hom ≫ k₁.hom) :
    i₀.hom ≫ i₁.inv = ((h₀.hom ≫ k₀.hom) ≫ k₁.inv) ≫ h₁.inv := by
  have h2 : i₁.inv ≫ (h₁.hom ≫ k₁.hom) = j := by
    rw [← e₁]
    simp only [Iso.inv_hom_id_assoc]
  refine (Iso.eq_comp_inv h₁).mpr ?_
  refine (Iso.eq_comp_inv k₁).mpr ?_
  rw [Category.assoc, Category.assoc]
  rw [h2, e₀]

/-! ## The reparametrisations of the pullbacks -/

/-- The value of `φ` on the fibres over `0`, identified with `phiMap`. -/
theorem phiZeroHomeo_apply (p : C(E, B)) {b b' b'' : B} (γ : Path b b') (δ : Path b' b'')
    (x : PbF p γ.toContinuousMap 0) :
    ((phiZeroHomeo p γ δ) x : Work.StemsB.Pullback p (γ.trans δ).toContinuousMap)
      = phiMap p γ δ x := by
  refine Subtype.ext (Prod.ext rfl ?_)
  show (0 : unitInterval) = halfIcc x.1.1.2
  rw [show x.1.1.2 = 0 from x.2]
  exact halfIcc_zero.symm

/-- The value of `φ` on the fibres over `1`, identified with `phiMap`. -/
theorem phiTwelfthHomeo_apply (p : C(E, B)) {b b' b'' : B} (γ : Path b b') (δ : Path b' b'')
    (x : PbF p γ.toContinuousMap 1) :
    ((phiTwelfthHomeo p γ δ) x : Work.StemsB.Pullback p (γ.trans δ).toContinuousMap)
      = phiMap p γ δ x := by
  refine Subtype.ext (Prod.ext rfl ?_)
  show midI = halfIcc x.1.1.2
  rw [show x.1.1.2 = 1 from x.2]
  exact halfIcc_one.symm

/-- The value of `ψ` on the fibres over `0`, identified with `psiMap`. -/
theorem psiTwelfthHomeo_apply (p : C(E, B)) {b b' b'' : B} (γ : Path b b') (δ : Path b' b'')
    (x : PbF p δ.toContinuousMap 0) :
    ((psiTwelfthHomeo p γ δ) x : Work.StemsB.Pullback p (γ.trans δ).toContinuousMap)
      = psiMap p γ δ x := by
  refine Subtype.ext (Prod.ext rfl ?_)
  show midI = halfShiftIcc x.1.1.2
  rw [show x.1.1.2 = 0 from x.2]
  exact halfShiftIcc_zero.symm

/-- The value of `ψ` on the fibres over `1`, identified with `psiMap`. -/
theorem psiOneHomeo_apply (p : C(E, B)) {b b' b'' : B} (γ : Path b b') (δ : Path b' b'')
    (x : PbF p δ.toContinuousMap 1) :
    ((psiOneHomeo p γ δ) x : Work.StemsB.Pullback p (γ.trans δ).toContinuousMap)
      = psiMap p γ δ x := by
  refine Subtype.ext (Prod.ext rfl ?_)
  show (1 : unitInterval) = halfShiftIcc x.1.1.2
  rw [show x.1.1.2 = 1 from x.2]
  exact halfShiftIcc_one.symm

/-! ## The naturality squares for the reparametrisations -/

/-- Naturality of the fibre inclusions over `0` along `φ`. -/
theorem inclHZ_phiMap_zero (p : C(E, B)) {b b' b'' : B}
    (γ : Path b b') (δ : Path b' b'') (j : ℕ) :
    inclHZ (Work.StemsB.Pullback p γ.toContinuousMap)
        {x : Work.StemsB.Pullback p γ.toContinuousMap |
          Work.StemsB.pullbackSnd p γ.toContinuousMap x = 0} j ≫ HZmap (phiMap p γ δ) j
      = HZmap ((↑(phiZeroHomeo p γ δ)) :
          C(PbF p γ.toContinuousMap 0, PbF p (γ.trans δ).toContinuousMap 0)) j ≫
        inclHZ (Work.StemsB.Pullback p (γ.trans δ).toContinuousMap)
          {x : Work.StemsB.Pullback p (γ.trans δ).toContinuousMap |
            Work.StemsB.pullbackSnd p (γ.trans δ).toContinuousMap x = 0} j :=
  inclHZ_comp_HZmap _ _ _ _
    (fun x => phiZeroHomeo_apply p γ δ x) j

/-- Naturality of the fibre inclusions over `1` along `φ`. -/
theorem inclHZ_phiMap_mid (p : C(E, B)) {b b' b'' : B}
    (γ : Path b b') (δ : Path b' b'') (j : ℕ) :
    inclHZ (Work.StemsB.Pullback p γ.toContinuousMap)
        {x : Work.StemsB.Pullback p γ.toContinuousMap |
          Work.StemsB.pullbackSnd p γ.toContinuousMap x = 1} j ≫ HZmap (phiMap p γ δ) j
      = HZmap ((↑(phiTwelfthHomeo p γ δ)) :
          C(PbF p γ.toContinuousMap 1, PbF p (γ.trans δ).toContinuousMap midI)) j ≫
        inclHZ (Work.StemsB.Pullback p (γ.trans δ).toContinuousMap)
          {x : Work.StemsB.Pullback p (γ.trans δ).toContinuousMap |
            Work.StemsB.pullbackSnd p (γ.trans δ).toContinuousMap x = midI} j :=
  inclHZ_comp_HZmap _ _ _ _
    (fun x => phiTwelfthHomeo_apply p γ δ x) j

/-- Naturality of the fibre inclusions over `0` along `ψ`. -/
theorem inclHZ_psiMap_mid (p : C(E, B)) {b b' b'' : B}
    (γ : Path b b') (δ : Path b' b'') (j : ℕ) :
    inclHZ (Work.StemsB.Pullback p δ.toContinuousMap)
        {x : Work.StemsB.Pullback p δ.toContinuousMap |
          Work.StemsB.pullbackSnd p δ.toContinuousMap x = 0} j ≫ HZmap (psiMap p γ δ) j
      = HZmap ((↑(psiTwelfthHomeo p γ δ)) :
          C(PbF p δ.toContinuousMap 0, PbF p (γ.trans δ).toContinuousMap midI)) j ≫
        inclHZ (Work.StemsB.Pullback p (γ.trans δ).toContinuousMap)
          {x : Work.StemsB.Pullback p (γ.trans δ).toContinuousMap |
            Work.StemsB.pullbackSnd p (γ.trans δ).toContinuousMap x = midI} j :=
  inclHZ_comp_HZmap _ _ _ _
    (fun x => psiTwelfthHomeo_apply p γ δ x) j

/-- Naturality of the fibre inclusions over `1` along `ψ`. -/
theorem inclHZ_psiMap_one (p : C(E, B)) {b b' b'' : B}
    (γ : Path b b') (δ : Path b' b'') (j : ℕ) :
    inclHZ (Work.StemsB.Pullback p δ.toContinuousMap)
        {x : Work.StemsB.Pullback p δ.toContinuousMap |
          Work.StemsB.pullbackSnd p δ.toContinuousMap x = 1} j ≫ HZmap (psiMap p γ δ) j
      = HZmap ((↑(psiOneHomeo p γ δ)) :
          C(PbF p δ.toContinuousMap 1, PbF p (γ.trans δ).toContinuousMap 1)) j ≫
        inclHZ (Work.StemsB.Pullback p (γ.trans δ).toContinuousMap)
          {x : Work.StemsB.Pullback p (γ.trans δ).toContinuousMap |
            Work.StemsB.pullbackSnd p (γ.trans δ).toContinuousMap x = 1} j :=
  inclHZ_comp_HZmap _ _ _ _
    (fun x => psiOneHomeo_apply p γ δ x) j

/-- **The two transports computed through two different ambient objects agree.**  Version of
`iso_cancel_hom` as an equality of isomorphisms. -/
theorem iso_cancel_iso_aux {C : Type*} [Category C] {A B D C' E : C}
    (i₀ : A ≅ D) (i₁ : B ≅ D) (h₀ : A ≅ C') (h₁ : B ≅ C') (k₀ : C' ≅ E) (k₁ : C' ≅ E)
    (j : D ⟶ E) (e₀ : i₀.hom ≫ j = h₀.hom ≫ k₀.hom) (e₁ : i₁.hom ≫ j = h₁.hom ≫ k₁.hom) :
    i₀ ≪≫ i₁.symm = (h₀ ≪≫ k₀) ≪≫ (h₁ ≪≫ k₁).symm := by
  have h := iso_cancel_hom i₀ i₁ h₀ h₁ k₀ k₁ j e₀ e₁
  apply Iso.ext
  change i₀.hom ≫ i₁.inv = (h₀.hom ≫ k₀.hom) ≫ (k₁.inv ≫ h₁.inv)
  rw [h, Category.assoc]

/-! ## The two halves of the transport along a concatenation -/

/-- The first half of the transport of the pullback of `p` along the concatenation, from the fibre
over `0` to the fibre over the junction point `1/2`. -/
def halfLeft (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) {b b' b'' : B}
    (γ : Path b b') (δ : Path b' b'') (j : ℕ) :
    Work.PiS.HZ (PbF p (γ.trans δ).toContinuousMap 0) j ≅
      Work.PiS.HZ (PbF p (γ.trans δ).toContinuousMap midI) j :=
  pbTrans p hp (γ.trans δ).toContinuousMap 0 midI j

/-- The second half of the transport of the pullback of `p` along the concatenation, from the fibre
over the junction point `1/2` to the fibre over `1`. -/
def halfRight (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) {b b' b'' : B}
    (γ : Path b b') (δ : Path b' b'') (j : ℕ) :
    Work.PiS.HZ (PbF p (γ.trans δ).toContinuousMap midI) j ≅
      Work.PiS.HZ (PbF p (γ.trans δ).toContinuousMap 1) j :=
  pbTrans p hp (γ.trans δ).toContinuousMap midI 1 j

/-- The transport along the concatenation is the composite of its two halves. -/
theorem pathTrans_trans_eq (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) {b b' b'' : B}
    (γ : Path b b') (δ : Path b' b'') (j : ℕ) :
    pathTrans p hp (γ.trans δ) j = halfLeft p hp γ δ j ≪≫ halfRight p hp γ δ j :=
  (pbTrans_trans p hp (γ.trans δ).toContinuousMap 0 midI 1 j).symm

/-! ## The reparametrisation homeomorphisms, evaluated on homology -/

theorem phiZeroHomeo_HZ (p : C(E, B)) {b b' b'' : B} (γ : Path b b') (δ : Path b' b'')
    (j : ℕ) :
    HZHomeoIso (phiZeroHomeo p γ δ) j =
      HZHomeoIso (pullbackFibreHomeo p γ.toContinuousMap 0) j ≪≫
        HZHomeoIso (fibrePointHomeo p ((trans_zero_apply γ δ).symm)) j ≪≫
        (HZHomeoIso (pullbackFibreHomeo p (γ.trans δ).toContinuousMap 0) j).symm := by
  rw [phiZeroHomeo, HZHomeoIso_trans', HZHomeoIso_trans', ← HZHomeoIso_symm']

theorem phiTwelfthHomeo_HZ (p : C(E, B)) {b b' b'' : B} (γ : Path b b') (δ : Path b' b'')
    (j : ℕ) :
    HZHomeoIso (phiTwelfthHomeo p γ δ) j =
      HZHomeoIso (pullbackFibreHomeo p γ.toContinuousMap 1) j ≪≫
        HZHomeoIso (fibrePointHomeo p ((trans_mid_left γ δ).symm)) j ≪≫
        (HZHomeoIso (pullbackFibreHomeo p (γ.trans δ).toContinuousMap midI) j).symm := by
  rw [phiTwelfthHomeo, HZHomeoIso_trans', HZHomeoIso_trans', ← HZHomeoIso_symm']

theorem psiTwelfthHomeo_HZ (p : C(E, B)) {b b' b'' : B} (γ : Path b b') (δ : Path b' b'')
    (j : ℕ) :
    HZHomeoIso (psiTwelfthHomeo p γ δ) j =
      HZHomeoIso (pullbackFibreHomeo p δ.toContinuousMap 0) j ≪≫
        HZHomeoIso (fibrePointHomeo p ((trans_mid_right γ δ).symm)) j ≪≫
        (HZHomeoIso (pullbackFibreHomeo p (γ.trans δ).toContinuousMap midI) j).symm := by
  rw [psiTwelfthHomeo, HZHomeoIso_trans', HZHomeoIso_trans', ← HZHomeoIso_symm']

theorem psiOneHomeo_HZ (p : C(E, B)) {b b' b'' : B} (γ : Path b b') (δ : Path b' b'')
    (j : ℕ) :
    HZHomeoIso (psiOneHomeo p γ δ) j =
      HZHomeoIso (pullbackFibreHomeo p δ.toContinuousMap 1) j ≪≫
        HZHomeoIso (fibrePointHomeo p ((trans_one_apply γ δ).symm)) j ≪≫
        (HZHomeoIso (pullbackFibreHomeo p (γ.trans δ).toContinuousMap 1) j).symm := by
  rw [psiOneHomeo, HZHomeoIso_trans', HZHomeoIso_trans', ← HZHomeoIso_symm']

/-! ## The point-change identifications as homology isomorphisms -/

theorem pcSrc_eq_homeo (p : C(E, B)) {b b' b'' : B} (γ : Path b b') (δ : Path b' b'') (j : ℕ) :
    pcSrc p γ δ j = HZHomeoIso (fibrePointHomeo p ((trans_zero_apply γ δ).symm)) j := by
  rw [pcSrc, eqToIso_fibre_eq']

theorem pcTgt_eq_homeo (p : C(E, B)) {b b' b'' : B} (γ : Path b b') (δ : Path b' b'') (j : ℕ) :
    pcTgt p γ δ j = HZHomeoIso (fibrePointHomeo p (trans_one_apply γ δ)) j := by
  rw [pcTgt, eqToIso_fibre_eq']

theorem pcMid_eq_homeo (p : C(E, B)) {b b' b'' : B} (γ : Path b b') (δ : Path b' b'') (j : ℕ) :
    pcMid p γ δ j =
      HZHomeoIso (fibrePointHomeo p ((Path.target γ).trans (Path.source δ).symm)) j := by
  rw [pcMid, eqToIso_fibre_eq']

theorem fibrePointHomeo_comp (p : C(E, B)) {a b c : B} (h : a = b) (h' : b = c) :
    (fibrePointHomeo p h).trans (fibrePointHomeo p h') = fibrePointHomeo p (h.trans h') := by
  cases h
  cases h'
  exact Homeomorph.ext (fun y => rfl)

theorem fibrePointHomeo_congr (p : C(E, B)) {a b : B} (h h' : a = b) :
    fibrePointHomeo p h = fibrePointHomeo p h' :=
  Homeomorph.ext (fun _y => Subtype.ext rfl)

theorem HZHomeoIso_fibrePointHomeo_symm (p : C(E, B)) {a b : B} (h : a = b) (j : ℕ) :
    HZHomeoIso (fibrePointHomeo p h) j =
      (HZHomeoIso (fibrePointHomeo p h.symm) j).symm := by
  rw [← fibrePointHomeo_symm, ← HZHomeoIso_symm']

/-! ## The blocks of the assembly, with a variable tail -/

/-- **Source block.** -/
theorem leaf_zero_tail (p : C(E, B)) {b b' b'' : B} (γ : Path b b') (δ : Path b' b'') (j : ℕ)
    {Z : Type} [TopologicalSpace Z]
    (X : Work.PiS.HZ (PbF p γ.toContinuousMap 0) j ≅ Work.PiS.HZ Z j) :
    pcSrc p γ δ j ≪≫
        (HZHomeoIso (pullbackFibreHomeo p (γ.trans δ).toContinuousMap 0) j).symm ≪≫
        (HZHomeoIso (phiZeroHomeo p γ δ) j).symm ≪≫ X
      = (HZHomeoIso (pullbackFibreHomeo p γ.toContinuousMap 0) j).symm ≪≫ X := by
  rw [pcSrc_eq_homeo, phiZeroHomeo_HZ, Iso.trans_symm, Iso.trans_symm]
  simp only [Iso.trans_assoc, Iso.symm_symm_eq, Iso.symm_self_id_assoc, Iso.self_symm_id_assoc]

/-- Point-change identifications compose. -/
theorem eqToIso_fibre_eq_comp (p : C(E, B)) {b b' b'' : B} (h : b = b') (h' : b' = b'')
    (j : ℕ) :
    eqToIso (congrArg (fun x => Work.PiS.HZ (Work.StemsB.fibre p x) j) h) ≪≫
        eqToIso (congrArg (fun x => Work.PiS.HZ (Work.StemsB.fibre p x) j) h')
      = eqToIso (congrArg (fun x => Work.PiS.HZ (Work.StemsB.fibre p x) j) (h.trans h')) := by
  rw [eqToIso_trans]

/-- The inverse of a point-change identification. -/
theorem eqToIso_fibre_eq_symm (p : C(E, B)) {b b' : B} (h : b = b') (j : ℕ) :
    (eqToIso (congrArg (fun x => Work.PiS.HZ (Work.StemsB.fibre p x) j) h)).symm
      = eqToIso (congrArg (fun x => Work.PiS.HZ (Work.StemsB.fibre p x) j) h.symm) :=
  Iso.ext rfl

/-- The identification of the fibres over the junction point as a conjugate of the two
homeomorphisms at the junction. -/
theorem pcMid_eq (p : C(E, B)) {b b' b'' : B} (γ : Path b b') (δ : Path b' b'') (j : ℕ) :
    HZHomeoIso (fibrePointHomeo p ((trans_mid_left γ δ).symm)) j ≪≫
        (HZHomeoIso (fibrePointHomeo p ((trans_mid_right γ δ).symm)) j).symm
      = pcMid p γ δ j := by
  rw [← eqToIso_fibre_eq', ← eqToIso_fibre_eq', pcMid, eqToIso_fibre_eq_symm,
    eqToIso_fibre_eq_comp]
  · exact (trans_mid_left γ δ).symm
  · exact trans_mid_right γ δ
  · exact (trans_mid_right γ δ).symm

/-- The identification of the fibres over the junction point, in the form needed for a composite
with a variable tail. -/
theorem pcMid_eq_tail (p : C(E, B)) {b b' b'' : B} (γ : Path b b') (δ : Path b' b'') (j : ℕ)
    {Z : Type} [TopologicalSpace Z]
    (Y : Work.PiS.HZ (Work.StemsB.fibre p (δ 0)) j ≅ Work.PiS.HZ Z j) :
    HZHomeoIso (fibrePointHomeo p ((trans_mid_left γ δ).symm)) j ≪≫
        (HZHomeoIso (fibrePointHomeo p ((trans_mid_right γ δ).symm)) j).symm ≪≫ Y
      = pcMid p γ δ j ≪≫ Y := by
  rw [← Iso.trans_assoc, pcMid_eq]

/-- **Junction block.** -/
theorem leaf_mid_tail (p : C(E, B)) {b b' b'' : B} (γ : Path b b') (δ : Path b' b'') (j : ℕ)
    {Z : Type} [TopologicalSpace Z]
    (X : Work.PiS.HZ (PbF p δ.toContinuousMap 0) j ≅ Work.PiS.HZ Z j) :
    HZHomeoIso (phiTwelfthHomeo p γ δ) j ≪≫
        (HZHomeoIso (psiTwelfthHomeo p γ δ) j).symm ≪≫ X
      = HZHomeoIso (pullbackFibreHomeo p γ.toContinuousMap 1) j ≪≫ pcMid p γ δ j ≪≫
        (HZHomeoIso (pullbackFibreHomeo p δ.toContinuousMap 0) j).symm ≪≫ X := by
  rw [phiTwelfthHomeo_HZ, psiTwelfthHomeo_HZ, Iso.trans_symm, Iso.trans_symm,
    Iso.symm_symm_eq]
  simp only [Iso.trans_assoc, Iso.symm_self_id_assoc]
  rw [pcMid_eq_tail p γ δ j ((HZHomeoIso (pullbackFibreHomeo p δ.toContinuousMap 0) j).symm ≪≫ X)]

/-- **Target block.** -/
theorem leaf_one_tail (p : C(E, B)) {b b' b'' : B} (γ : Path b b') (δ : Path b' b'') (j : ℕ)
    {Z : Type} [TopologicalSpace Z]
    (X : Work.PiS.HZ (Work.StemsB.fibre p (δ 1)) j ≅ Work.PiS.HZ Z j) :
    HZHomeoIso (psiOneHomeo p γ δ) j ≪≫
        HZHomeoIso (pullbackFibreHomeo p (γ.trans δ).toContinuousMap 1) j ≪≫ pcTgt p γ δ j ≪≫ X
      = HZHomeoIso (pullbackFibreHomeo p δ.toContinuousMap 1) j ≪≫ X := by
  rw [psiOneHomeo_HZ, pcTgt_eq_homeo, HZHomeoIso_fibrePointHomeo_symm]
  simp only [Iso.trans_assoc, Iso.symm_self_id_assoc]

/-- **Junction identification with a variable tail.** -/
theorem pathTgt_pathSrc_tail (p : C(E, B)) {b b' b'' : B} (γ : Path b b') (δ : Path b' b'')
    (j : ℕ) {Z : Type} [TopologicalSpace Z]
    (X : Work.PiS.HZ (Work.StemsB.fibre p (δ 0)) j ≅ Work.PiS.HZ Z j) :
    pathTgt p γ j ≪≫ pathSrc p δ j ≪≫ X = pcMid p γ δ j ≪≫ X := by
  rw [← Iso.trans_assoc, pathTgt_pathSrc]

end

end Work.SSS
