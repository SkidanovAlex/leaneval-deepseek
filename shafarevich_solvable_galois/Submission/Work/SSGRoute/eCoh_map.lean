import Mathlib
import Submission.Work.SSGRoute.E0bDefs
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.E0bBarChange
import Submission.Work.SSGRoute.cochainsMap_inhomogeneousCochainsIso_comm
import Submission.Work.SSGRoute.MapExtAuxDefs
import Submission.Work.SSGRoute.mapExtAddHom_extMk_gen
import Submission.Commons.RepresentationTheory.GroupCohomology.inhomogeneousCochainsIso_apply
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Naturality of the `E0b` bridge `eCoh`

`Work.SSGRoute.eCoh_map`: `eCoh n H B ((groupCohomology.map f φ n) y) = extHMap f φ (eCoh n G A y)`.
-/

namespace Work.SSGRoute

open CategoryTheory Limits
open SSGRoute.PTExt

noncomputable section

universe u v u' v'

/-! ## 0. The "L–M" step: `Ext` commutes with an exact functor along a lift of the resolution -/

/-- **L–M.**  For an exact additive functor `F : C ⥤ D`, a projective resolution `R` of `X`, a
cocycle `g : R.complex.X n ⟶ Y`, a projective resolution `R'` of `X'`, a morphism
`g' : X' ⟶ F.obj X`, and a chain map `φ : R'.complex ⟶ F(R.complex)` compatible with the
augmentations (`hφ`), `mk₀ g'` composed with the image of `R.extMk g` under `F` is computed by
`R'.extMk` of `φ.f n ≫ F.map g`. -/
theorem mapExtAddHom_extMk_aux {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C]
    {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{v'} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {X Y : C} (R : ProjectiveResolution X) {n : ℕ} (g : R.complex.X n ⟶ Y)
    (hg : R.complex.d (n + 1) n ≫ g = 0)
    {X' : D} (R' : ProjectiveResolution X') (g' : X' ⟶ F.obj X)
    (φ : R'.complex ⟶ (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj R.complex)
    (hφ : φ ≫ (F.mapHomologicalComplex (ComplexShape.down ℕ)).map R.π ≫
        (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.down ℕ) 0).hom.app X
        = R'.π ≫ (ChainComplex.single₀ D).map g')
    (hg' : R'.complex.d (n + 1) n ≫ (φ.f n ≫ F.map g) = 0) :
    (Abelian.Ext.mk₀ g').comp ((R.extMk g (n + 1) rfl hg).mapExactFunctor F) (zero_add n)
      = R'.extMk (φ.f n ≫ F.map g) (n + 1) rfl hg' :=
  Work.SSGRoute.mapExtAddHom_extMk_gen F R g hg R' g' φ hφ hg'

/-! ## 1. The chosen comparison `Φ` of `eCoh` and its computation rule -/

/-- The additive equivalence `Hⁿ(Hom(barComplex, A)) ≃+ Extⁿ_G(ℤ, A)` chosen by
`Classical.choose` in the definition of `eCoh`. -/
abbrev eCohPhi (n : ℕ) (G : Type) [Group G] (A : Rep.{0} Coeff G) :
    ((Rep.barResolution Coeff G).complex.linearYonedaObj Coeff A).homology n ≃+ extH A n :=
  Classical.choose (Work.SSGRoute.projRes_homologyAddEquiv_extMk
    (X := unitRep G) (Y := A) (Rep.barResolution Coeff G) n)

/-- The computation rule of `eCohPhi` on the class of a cocycle of the `Hom`-complex. -/
lemma eCohPhi_spec (n : ℕ) (G : Type) [Group G] (A : Rep.{0} Coeff G)
    (f : (Rep.barResolution Coeff G).complex.X n ⟶ A)
    (hf : (Rep.barResolution Coeff G).complex.d (n + 1) n ≫ f = 0) :
    eCohPhi n G A
        ((HomologicalComplex.homologyπ
            ((Rep.barResolution Coeff G).complex.linearYonedaObj Coeff A) n)
          ((HomologicalComplex.cyclesMk
            ((Rep.barResolution Coeff G).complex.linearYonedaObj Coeff A)) f (n + 1) (by simp) (by
            change (Rep.barResolution Coeff G).complex.d (n + 1) n ≫ f = 0
            exact hf))) =
      (Rep.barResolution Coeff G).extMk f (n + 1) rfl hf :=
  Classical.choose_spec (Work.SSGRoute.projRes_homologyAddEquiv_extMk
    (X := unitRep G) (Y := A) (Rep.barResolution Coeff G) n) f hf

set_option backward.isDefEq.respectTransparency false in
/-- `groupCohomologyIso` for the bar resolution is `homologyMap` of `inhomogeneousCochainsIso`. -/
lemma groupCohomologyIso_bar_hom (n : ℕ) (G : Type) [Group G] (A : Rep.{0} Coeff G) :
    (groupCohomologyIso A n (Rep.barResolution Coeff G)).hom =
      HomologicalComplex.homologyMap (groupCohomology.inhomogeneousCochainsIso A).hom n := by
  rw [groupCohomologyIso, groupCohomologyIsoExt]
  rw [Rep.barResolution.extIso]
  rw [Iso.trans_hom, Iso.trans_hom, Category.assoc, Iso.symm_hom, Iso.inv_hom_id, Category.comp_id,
    isoOfQuasiIsoAt_hom]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Unfolding of `eCoh` on the homology of `Hom(barComplex, A)`. -/
lemma eCoh_apply (n : ℕ) (G : Type) [Group G] (A : Rep.{0} Coeff G)
    (x : groupCohomology A n) :
    eCoh n G A x = eCohPhi n G A
      (HomologicalComplex.homologyMap (groupCohomology.inhomogeneousCochainsIso A).hom n x) := by
  have h3 : ((groupCohomologyIso A n (Rep.barResolution Coeff G)).toLinearEquiv.toAddEquiv) x =
      (groupCohomologyIso A n (Rep.barResolution Coeff G)).hom x := rfl
  rw [SSGRoute.PTExt.eCoh, AddEquiv.trans_apply, h3, groupCohomologyIso_bar_hom]
  rfl

/-! ## 2. `homologyMap` on the class of a cocycle -/

set_option backward.isDefEq.respectTransparency false in
/-- For a morphism of cochain complexes of `k`-modules, the induced map on `n`-cycles sends the
cycle of a cocycle `x` to the cycle of `φ.f n x`. -/
lemma cyclesMap_cyclesMk {k : Type*} [Ring k] {K L : CochainComplex (ModuleCat k) ℕ}
    (φ : K ⟶ L) (n : ℕ) (x : K.X n)
    (hx : (forget₂ (ModuleCat k) Ab).map (K.d n (n + 1)) x = 0)
    (hx' : (forget₂ (ModuleCat k) Ab).map (L.d n (n + 1))
      ((forget₂ (ModuleCat k) Ab).map (φ.f n) x) = 0) :
    (forget₂ (ModuleCat k) Ab).map (HomologicalComplex.cyclesMap φ n)
        (HomologicalComplex.cyclesMk K x (n + 1) (by simp) hx) =
      HomologicalComplex.cyclesMk L ((forget₂ (ModuleCat k) Ab).map (φ.f n) x) (n + 1) (by simp)
        hx' := by
  apply (Preadditive.mono_iff_injective (L.iCycles n)).1 inferInstance
  conv_lhs =>
    rw [← ConcreteCategory.forget₂_comp_apply, HomologicalComplex.cyclesMap_i,
      ConcreteCategory.forget₂_comp_apply, HomologicalComplex.i_cyclesMk K x (n + 1) (by simp) hx]
  exact (HomologicalComplex.i_cyclesMk L ((forget₂ (ModuleCat k) Ab).map (φ.f n) x) (n + 1)
    (by simp) hx').symm

set_option backward.isDefEq.respectTransparency false in
/-- `homologyMap` on the homology class of a cocycle. -/
lemma homologyMap_homologyπ_cyclesMk {k : Type*} [Ring k]
    {K L : CochainComplex (ModuleCat k) ℕ} (φ : K ⟶ L) (n : ℕ) (x : K.X n)
    (hx : (forget₂ (ModuleCat k) Ab).map (K.d n (n + 1)) x = 0)
    (hx' : (forget₂ (ModuleCat k) Ab).map (L.d n (n + 1))
      ((forget₂ (ModuleCat k) Ab).map (φ.f n) x) = 0) :
    HomologicalComplex.homologyMap φ n
        (HomologicalComplex.homologyπ K n
          (HomologicalComplex.cyclesMk K x (n + 1) (by simp) hx)) =
      HomologicalComplex.homologyπ L n
        (HomologicalComplex.cyclesMk L ((forget₂ (ModuleCat k) Ab).map (φ.f n) x) (n + 1)
          (by simp) hx') := by
  have h := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality φ n)
  simp only [ConcreteCategory.comp_apply] at h
  refine (h (HomologicalComplex.cyclesMk K x (n + 1) (by simp) hx)).trans ?_
  exact congrArg (fun z => (ConcreteCategory.hom (HomologicalComplex.homologyπ L n)) z)
    (cyclesMap_cyclesMk φ n x hx hx')

/-! ## 3. Cocycle conditions -/

set_option backward.isDefEq.respectTransparency false in
/-- The cocycle condition for the `Hom`-complex cycle attached to an inhomogeneous cocycle. -/
lemma freeLift_cocycle (G : Type) [Group G] (A : Rep.{0} Coeff G) (n : ℕ)
    (z : (Fin n → G) → A) (hz : inhomogeneousCochains.d A n z = 0) :
    (Rep.barComplex Coeff G).d (n + 1) n ≫ Rep.freeLift Coeff G A z = 0 := by
  have hcomm := ConcreteCategory.congr_hom (HomologicalComplex.Hom.comm
    (groupCohomology.inhomogeneousCochainsIso A).hom n (n + 1))
  simp only [ConcreteCategory.comp_apply] at hcomm
  have h0 := hcomm z
  have hzA : (ConcreteCategory.hom
      ((groupCohomology.inhomogeneousCochains A).d n (n + 1))) z = 0 := by
    rw [groupCohomology.inhomogeneousCochains.d_def]
    exact hz
  rw [hzA, map_zero] at h0
  rw [linearYonedaObj_d_apply (Rep.barComplex Coeff G) A (i := n) (j := n + 1) rfl] at h0
  have hfe : (ConcreteCategory.hom
      ((groupCohomology.inhomogeneousCochainsIso A).hom.f n)) z = Rep.freeLift Coeff G A z := rfl
  rw [hfe] at h0
  exact h0

set_option backward.isDefEq.respectTransparency false in
/-- The cocycle condition is preserved by `cochainsMap`. -/
lemma cochainsMap_cocycle (G H : Type) [Group G] [Group H] (f : H →* G)
    (A : Rep.{0} Coeff G) (B : Rep.{0} Coeff H) (φ : Rep.res f A ⟶ B) (n : ℕ)
    (z : (Fin n → G) → A) (hz : inhomogeneousCochains.d A n z = 0) :
    inhomogeneousCochains.d B n (fun y : Fin n → H => φ (z (f ∘ y))) = 0 := by
  have hcomm := ConcreteCategory.congr_hom (HomologicalComplex.Hom.comm
    (groupCohomology.cochainsMap f φ) n (n + 1))
  simp only [ConcreteCategory.comp_apply] at hcomm
  have h0 := hcomm z
  have hzA : (ConcreteCategory.hom
      ((groupCohomology.inhomogeneousCochains A).d n (n + 1))) z = 0 := by
    rw [groupCohomology.inhomogeneousCochains.d_def]
    exact hz
  rw [hzA, map_zero] at h0
  simp only [CochainComplex.of_d] at h0
  rw [show (fun y : Fin n → H => φ (z (f ∘ y))) = ⇑((groupCohomology.cochainsMap f φ).f n) z
      from (Work.SSGRoute.cochainsMap_f_hom_apply G H f A B φ n z).symm]
  exact h0

set_option backward.isDefEq.respectTransparency false in
/-- The cocycle condition preserved by `cochainsMap`, in the form in which it is needed as an
argument of `cyclesMk`. -/
lemma cochainsMap_cocycle_wrapped (G H : Type) [Group G] [Group H] (f : H →* G)
    (A : Rep.{0} Coeff G) (B : Rep.{0} Coeff H) (φ : Rep.res f A ⟶ B) (n : ℕ)
    (z : (Fin n → G) → A) (hz : inhomogeneousCochains.d A n z = 0) :
    (ConcreteCategory.hom ((forget₂ (ModuleCat Coeff) Ab).map
      ((groupCohomology.inhomogeneousCochains B).d n (n + 1))))
      ((ConcreteCategory.hom ((forget₂ (ModuleCat Coeff) Ab).map
        ((groupCohomology.cochainsMap f φ).f n))) z) = 0 := by
  rw [groupCohomology.inhomogeneousCochains.d_def]
  exact cochainsMap_cocycle G H f A B φ n z hz

set_option backward.isDefEq.respectTransparency false in
/-- Every cycle of the inhomogeneous cochain complex is of the form `cocyclesMk z hz`. -/
lemma exists_cocyclesMk (n : ℕ) (G : Type) [Group G] (A : Rep.{0} Coeff G)
    (x : groupCohomology.cocycles A n) :
    ∃ (z : (Fin n → G) → A) (hz : inhomogeneousCochains.d A n z = 0),
      groupCohomology.cocyclesMk z hz = x := by
  refine ⟨(forget₂ (ModuleCat Coeff) Ab).map
    (HomologicalComplex.iCycles (groupCohomology.inhomogeneousCochains A) n) x, ?_, ?_⟩
  · have h := ConcreteCategory.congr_hom (HomologicalComplex.iCycles_d
      (groupCohomology.inhomogeneousCochains A) n (n + 1))
    simp only [ConcreteCategory.comp_apply] at h
    simpa [CochainComplex.of_d] using h x
  · apply (Preadditive.mono_iff_injective
      (HomologicalComplex.iCycles (groupCohomology.inhomogeneousCochains A) n)).1 inferInstance
    rw [HomologicalComplex.i_cyclesMk]

/-! ## 4. The two computation rules -/

set_option backward.isDefEq.respectTransparency false in
/-- **`eCoh` on the class of an inhomogeneous cocycle.** -/
lemma eCoh_cocyclesMk (n : ℕ) (G : Type) [Group G] (A : Rep.{0} Coeff G)
    (z : (Fin n → G) → A) (hz : inhomogeneousCochains.d A n z = 0) :
    eCoh n G A (groupCohomology.π A n (groupCohomology.cocyclesMk z hz)) =
      (Rep.barResolution Coeff G).extMk (Rep.freeLift Coeff G A z) (n + 1) rfl
        (freeLift_cocycle G A n z hz) := by
  rw [eCoh_apply]
  unfold groupCohomology groupCohomology.π groupCohomology.cocycles groupCohomology.cocyclesMk
  have hstep : HomologicalComplex.homologyMap (groupCohomology.inhomogeneousCochainsIso A).hom n
      (HomologicalComplex.homologyπ (groupCohomology.inhomogeneousCochains A) n
        (HomologicalComplex.cyclesMk (groupCohomology.inhomogeneousCochains A) z (n + 1) (by simp)
          (by
            rw [groupCohomology.inhomogeneousCochains.d_def]
            exact hz))) =
      HomologicalComplex.homologyπ
          (((Rep.barResolution Coeff G).complex).linearYonedaObj Coeff A) n
        (HomologicalComplex.cyclesMk (((Rep.barResolution Coeff G).complex).linearYonedaObj Coeff A)
          (Rep.freeLift Coeff G A z) (n + 1) (by simp) (freeLift_cocycle G A n z hz)) := by
    refine homologyMap_homologyπ_cyclesMk (groupCohomology.inhomogeneousCochainsIso A).hom n z
      (by rw [groupCohomology.inhomogeneousCochains.d_def]; exact hz)
      (freeLift_cocycle G A n z hz)
  rw [hstep]
  exact eCohPhi_spec n G A (Rep.freeLift Coeff G A z) (freeLift_cocycle G A n z hz)

set_option backward.isDefEq.respectTransparency false in
/-- **`map` on the class of an inhomogeneous cocycle.** -/
lemma map_cocyclesMk (n : ℕ) (G H : Type) [Group G] [Group H] (f : H →* G)
    (A : Rep.{0} Coeff G) (B : Rep.{0} Coeff H) (φ : Rep.res f A ⟶ B)
    (z : (Fin n → G) → A) (hz : inhomogeneousCochains.d A n z = 0) :
    groupCohomology.map f φ n (groupCohomology.π A n (groupCohomology.cocyclesMk z hz)) =
      groupCohomology.π B n (groupCohomology.cocyclesMk (fun y : Fin n → H => φ (z (f ∘ y)))
        (cochainsMap_cocycle G H f A B φ n z hz)) := by
  rw [groupCohomology.π_map_apply]
  unfold groupCohomology.cocyclesMap groupCohomology.cocyclesMk
  congr 1
  exact cyclesMap_cyclesMk (groupCohomology.cochainsMap f φ) n z
    (by rw [groupCohomology.inhomogeneousCochains.d_def]; exact hz)
    (cochainsMap_cocycle_wrapped G H f A B φ n z hz)

/-! ## 5. The group-change identity for `freeLift` -/

set_option backward.isDefEq.respectTransparency false in
/-- The group-change map on the bar complex computes the group-change of an inhomogeneous
cochain. -/
lemma freeLift_barChange (G H : Type) [Group G] [Group H] (f : H →* G)
    (A : Rep.{0} Coeff G) (B : Rep.{0} Coeff H) (φ : Rep.res f A ⟶ B) (n : ℕ)
    (z : (Fin n → G) → A) :
    Rep.freeLift Coeff H B (fun y : Fin n → H => φ (z (f ∘ y))) =
      barChange Coeff G H f n ≫ (Rep.resFunctor f).map (Rep.freeLift Coeff G A z) ≫ φ := by
  apply Rep.free_ext
  intro y
  change (Rep.Hom.hom (Rep.freeLift Coeff H B (fun y : Fin n → H => φ (z (f ∘ y)))))
      (Finsupp.single y (MonoidAlgebra.single (1 : H) (1 : Coeff))) =
    (Rep.Hom.hom (barChange Coeff G H f n ≫
      (Rep.resFunctor f).map (Rep.freeLift Coeff G A z) ≫ φ))
      (Finsupp.single y (MonoidAlgebra.single (1 : H) (1 : Coeff)))
  rw [Rep.hom_comp, Rep.hom_comp]
  simp only [Representation.IntertwiningMap.comp_apply]
  rw [barChange_apply]
  simp only [map_one]
  rw [Rep.resMap_hom_apply]
  simp [Rep.freeLift, Rep.hom_ofHom, Representation.freeLift_single_single]
  rfl

/-! ## 6. The `Ext` half -/

set_option backward.isDefEq.respectTransparency false in
/-- The cocycle condition for the group-changed cocycle (without a coefficient map). -/
lemma barChange_cocycle' (G H : Type) [Group G] [Group H] (f : H →* G)
    (A : Rep.{0} Coeff G) (n : ℕ) (g : Rep.free Coeff G (Fin n → G) ⟶ A)
    (hg : (Rep.barComplex Coeff G).d (n + 1) n ≫ g = 0) :
    (Rep.barComplex Coeff H).d (n + 1) n ≫
      (barChange Coeff G H f n ≫ (Rep.resFunctor f).map g) = 0 := by
  have h := barChange_chain (k := Coeff) G H f n
  rw [← Rep.barComplex.d_def, ← Rep.barComplex.d_def] at h
  rw [← Category.assoc, ← h, Category.assoc, ← Functor.map_comp, hg, Functor.map_zero,
    Limits.comp_zero]

set_option backward.isDefEq.respectTransparency false in
/-- The cocycle condition for the group-changed cocycle. -/
lemma barChange_cocycle (G H : Type) [Group G] [Group H] (f : H →* G)
    (A : Rep.{0} Coeff G) (B : Rep.{0} Coeff H) (φ : Rep.res f A ⟶ B) (n : ℕ)
    (g : Rep.free Coeff G (Fin n → G) ⟶ A)
    (hg : (Rep.barComplex Coeff G).d (n + 1) n ≫ g = 0) :
    (Rep.barComplex Coeff H).d (n + 1) n ≫
      (barChange Coeff G H f n ≫ (Rep.resFunctor f).map g ≫ φ) = 0 := by
  rw [← Category.assoc (barChange Coeff G H f n) ((Rep.resFunctor f).map g) φ,
    ← Category.assoc ((Rep.barComplex Coeff H).d (n + 1) n)
      (barChange Coeff G H f n ≫ (Rep.resFunctor f).map g) φ,
    barChange_cocycle' G H f A n g hg, Limits.zero_comp]

set_option backward.isDefEq.respectTransparency false in
/-- **The `Ext` computation rule** ("L–M"): `mk₀ (unitRes f)` composed with the image under
`Rep.resFunctor f` of `extMk` is computed by the group-change map of the bar complex. -/
lemma extHMap_extMk_bar (G H : Type) [Group G] [Group H] (f : H →* G)
    (A : Rep.{0} Coeff G) (B : Rep.{0} Coeff H) (φ : Rep.res f A ⟶ B) (n : ℕ)
    (g : Rep.free Coeff G (Fin n → G) ⟶ A)
    (hg : (Rep.barComplex Coeff G).d (n + 1) n ≫ g = 0)
    (hg' : (Rep.barComplex Coeff H).d (n + 1) n ≫
      (barChange Coeff G H f n ≫ (Rep.resFunctor f).map g ≫ φ) = 0) :
    extHMap f φ ((Rep.barResolution Coeff G).extMk g (n + 1) rfl hg) =
      (Rep.barResolution Coeff H).extMk
        (barChange Coeff G H f n ≫ (Rep.resFunctor f).map g ≫ φ) (n + 1) rfl hg' := by
  have h1 := mapExtAddHom_extMk_aux (C := Rep.{0} Coeff G) (D := Rep.{0} Coeff H)
    (F := Rep.resFunctor f) (X := unitRep G) (Y := A)
    (R := Rep.barResolution Coeff G) (n := n) (g := g)
    (hg := hg) (X' := unitRep H) (R' := Rep.barResolution Coeff H)
    (g' := unitRes f) (φ := barHom Coeff G H f) (hφ := barHom_augmentation Coeff G H f)
    (hg' := barChange_cocycle' G H f A n g hg)
  simp only [SSGRoute.PTExt.extHMap, SSGRoute.PTExt.extRes]
  rw [← Abelian.Ext.comp_assoc_of_third_deg_zero (Abelian.Ext.mk₀ (unitRes f))
    (((Rep.barResolution Coeff G).extMk g (n + 1) rfl hg).mapExactFunctor (Rep.resFunctor f))
    (Abelian.Ext.mk₀ φ) (zero_add n)]
  rw [h1]
  rw [ProjectiveResolution.extMk_comp_mk₀]
  rfl

/-! ## 7. The main theorem -/

set_option backward.isDefEq.respectTransparency false in
open CategoryTheory Limits in
theorem eCoh_map (n : ℕ) (G H : Type) [Group G] [Group H] (f : H →* G)
    (A : Rep SSGRoute.PTExt.Coeff G) (B : Rep SSGRoute.PTExt.Coeff H)
    (φ : Rep.res f A ⟶ B) (y : groupCohomology A n) :
    SSGRoute.PTExt.eCoh n H B ((groupCohomology.map f φ n).hom y) =
      SSGRoute.PTExt.extHMap f φ (SSGRoute.PTExt.eCoh n G A y) := by
  refine groupCohomology_induction_on y fun x => ?_
  obtain ⟨z, hz, rfl⟩ := exists_cocyclesMk n G A x
  rw [map_cocyclesMk n G H f A B φ z hz]
  rw [eCoh_cocyclesMk n G A z hz]
  rw [extHMap_extMk_bar G H f A B φ n (Rep.freeLift Coeff G A z) (freeLift_cocycle G A n z hz)
    (barChange_cocycle G H f A B φ n (Rep.freeLift Coeff G A z) (freeLift_cocycle G A n z hz))]
  rw [eCoh_cocyclesMk n H B (fun y : Fin n → H => φ (z (f ∘ y)))
    (cochainsMap_cocycle G H f A B φ n z hz)]
  exact extMk_congr _ (freeLift_barChange G H f A B φ n z) _ _

end

end Work.SSGRoute
