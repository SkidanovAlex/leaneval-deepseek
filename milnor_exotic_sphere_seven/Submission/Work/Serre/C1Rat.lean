import Submission.Work.StemsB.sphRatHomology

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The `ℤ → ℚ` transfer of homology isomorphisms

Changing coefficients from `ℤ` to `ℚ` (the flat base change `- ⊗[ℤ] ℚ`) carries isomorphisms of
integral homology to isomorphisms of rational homology.  The chapter built here proves this by
providing the *naturality* of the comparison isomorphism

`Φ_X : (C_*(X;ℤ) ⊗[ℤ] ℚ) ≅ C_*(X;ℚ)`

of `Submission/Work/StemsB/sphRatHomology.lean` in the space `X` (the missing ingredient recorded in
`Submission/Work/Serre/serreC1.lean`).

The comparison is assembled from

* `eqToIso (map_alternatingFaceMapComplex F)`, a transport along an equality of functors, and
* `(alternatingFaceMapComplex ℚ).mapIso (isoWhiskerLeft X (sigmaConstObjCompIso F ℤ))`,

so its naturality is `eqToHom_congrArg_map` (coherence of the transport) together with
`isoWhiskerLeft_naturality` (naturality of the whiskering); the coefficient change is handled by
`coeffIso_naturality`.  Finally, `isIso_homologyMap_mapHomologicalComplex` says that `- ⊗[ℤ] ℚ` on
chain complexes preserves quasi-isomorphisms, via the naturality of `ShortComplex.mapHomologyIso`.
-/

open CategoryTheory Limits AlgebraicTopology Simplicial
open scoped Simplicial TensorProduct

namespace Work.Serre

noncomputable section

noncomputable abbrev IntRat : ModuleCat.{0} ℤ ⥤ ModuleCat.{0} ℚ :=
  ModuleCat.extendScalars (Int.castRingHom ℚ)
abbrev ZMod : ModuleCat.{0} ℤ := ModuleCat.of ℤ ℤ
abbrev QMod : ModuleCat.{0} ℚ := ModuleCat.of ℚ ℚ

/-! ## The complexes, in unfolded form -/

abbrev ChZ (X : SSet.{0}) : ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  (alternatingFaceMapComplex (ModuleCat.{0} ℤ)).obj (X ⋙ Limits.sigmaConst.obj ZMod)

abbrev ChQZ (X : SSet.{0}) : ChainComplex (ModuleCat.{0} ℚ) ℕ :=
  (alternatingFaceMapComplex (ModuleCat.{0} ℚ)).obj (X ⋙ Limits.sigmaConst.obj (IntRat.obj ZMod))

abbrev ChQ (X : SSet.{0}) : ChainComplex (ModuleCat.{0} ℚ) ℕ :=
  (alternatingFaceMapComplex (ModuleCat.{0} ℚ)).obj (X ⋙ Limits.sigmaConst.obj QMod)

abbrev FC (X : SSet.{0}) : ChainComplex (ModuleCat.{0} ℚ) ℕ :=
  (IntRat.mapHomologicalComplex (ComplexShape.down ℕ)).obj (ChZ X)

abbrev cmZ {X Y : SSet.{0}} (σ : X ⟶ Y) : ChZ X ⟶ ChZ Y :=
  (alternatingFaceMapComplex (ModuleCat.{0} ℤ)).map
    (Functor.whiskerRight σ (Limits.sigmaConst.obj ZMod))

abbrev cmQZ {X Y : SSet.{0}} (σ : X ⟶ Y) : ChQZ X ⟶ ChQZ Y :=
  (alternatingFaceMapComplex (ModuleCat.{0} ℚ)).map
    (Functor.whiskerRight σ (Limits.sigmaConst.obj (IntRat.obj ZMod)))

abbrev cmQ {X Y : SSet.{0}} (σ : X ⟶ Y) : ChQ X ⟶ ChQ Y :=
  (alternatingFaceMapComplex (ModuleCat.{0} ℚ)).map
    (Functor.whiskerRight σ (Limits.sigmaConst.obj QMod))

abbrev FCmap {X Y : SSet.{0}} (σ : X ⟶ Y) : FC X ⟶ FC Y :=
  (IntRat.mapHomologicalComplex (ComplexShape.down ℕ)).map (cmZ σ)

abbrev G2map {X Y : SSet.{0}} (σ : X ⟶ Y) :
    (alternatingFaceMapComplex (ModuleCat.{0} ℚ)).obj
        ((X ⋙ Limits.sigmaConst.obj ZMod) ⋙ IntRat) ⟶
      (alternatingFaceMapComplex (ModuleCat.{0} ℚ)).obj
        ((Y ⋙ Limits.sigmaConst.obj ZMod) ⋙ IntRat) :=
  ((SimplicialObject.whiskering (ModuleCat.{0} ℤ) (ModuleCat.{0} ℚ)).obj IntRat ⋙
      alternatingFaceMapComplex (ModuleCat.{0} ℚ)).map
        (Functor.whiskerRight σ (Limits.sigmaConst.obj ZMod))

/-! ## Coherence and whiskering -/

/-- **Coherence of the transport along an equality of functors.** -/
theorem eqToHom_congrArg_map {D D' : Type*} [Category* D] [Category* D']
    {G₁ G₂ : D ⥤ D'} (E : G₁ = G₂) {Y Y' : D} (τ : Y ⟶ Y') :
    eqToHom (congrArg (fun G : D ⥤ D' => G.obj Y) E) ≫ G₂.map τ
      = G₁.map τ ≫ eqToHom (congrArg (fun G : D ⥤ D' => G.obj Y') E) := by
  cases E
  simp

/-- **Naturality of `Functor.isoWhiskerLeft`**. -/
theorem isoWhiskerLeft_naturality {B C D : Type*} [Category* B] [Category* C] [Category* D]
    {F G : C ⥤ D} (e : F ≅ G) {X Y : B ⥤ C} (σ : X ⟶ Y) :
    (Functor.isoWhiskerLeft X e).hom ≫ Functor.whiskerRight σ G =
      Functor.whiskerRight σ F ≫ (Functor.isoWhiskerLeft Y e).hom := by
  ext Δ
  exact (e.hom.naturality (σ.app Δ)).symm

/-! ## The comparison isomorphism and its two factors -/

/-- The equality of chain-complex functors coming from `map_alternatingFaceMapComplex`. -/
abbrev AE : ((alternatingFaceMapComplex (ModuleCat.{0} ℤ)) ⋙
      IntRat.mapHomologicalComplex (ComplexShape.down ℕ))
    = ((SimplicialObject.whiskering (ModuleCat.{0} ℤ) (ModuleCat.{0} ℚ)).obj IntRat ⋙
      alternatingFaceMapComplex (ModuleCat.{0} ℚ)) :=
  AlgebraicTopology.map_alternatingFaceMapComplex IntRat

/-- The transport of the source complex, at a simplicial set `X`. -/
abbrev h1 (X : SSet.{0}) : FC X = (alternatingFaceMapComplex (ModuleCat.{0} ℚ)).obj
    ((X ⋙ Limits.sigmaConst.obj ZMod) ⋙ IntRat) :=
  congrArg (fun G : SimplicialObject (ModuleCat.{0} ℤ) ⥤ ChainComplex (ModuleCat.{0} ℚ) ℕ =>
    G.obj (X ⋙ Limits.sigmaConst.obj ZMod)) AE

/-- The "nice" isomorphism between the two models of the rational chains. -/
abbrev β (X : SSet.{0}) : (X ⋙ Limits.sigmaConst.obj ZMod) ⋙ IntRat ≅
    X ⋙ Limits.sigmaConst.obj (IntRat.obj ZMod) :=
  Iso.refl ((X ⋙ Limits.sigmaConst.obj ZMod) ⋙ IntRat) ≪≫
    Functor.isoWhiskerLeft X (Work.StemsB.SphRat.sigmaConstObjCompIso IntRat ZMod)

/-- The "nice" factor of the comparison, as a morphism of chain complexes. -/
abbrev Ψ (X : SSet.{0}) : (alternatingFaceMapComplex (ModuleCat.{0} ℚ)).obj
    ((X ⋙ Limits.sigmaConst.obj ZMod) ⋙ IntRat) ⟶ ChQZ X :=
  (alternatingFaceMapComplex (ModuleCat.{0} ℚ)).map (β X).hom

/-- `β` is, up to the identity, the whiskering of `sigmaConstObjCompIso`. -/
theorem β_hom (X : SSet.{0}) : (β X).hom = (Functor.isoWhiskerLeft X
    (Work.StemsB.SphRat.sigmaConstObjCompIso IntRat ZMod)).hom := by
  rw [β, Iso.trans_hom, Iso.refl_hom, Category.id_comp]

/-- Naturality of the "nice" isomorphism of simplicial objects. -/
theorem β_naturality {X Y : SSet.{0}} (σ : X ⟶ Y) :
    (β X).hom ≫ Functor.whiskerRight σ (Limits.sigmaConst.obj (IntRat.obj ZMod))
      = Functor.whiskerRight σ (Limits.sigmaConst.obj ZMod ⋙ IntRat) ≫ (β Y).hom := by
  rw [β_hom, β_hom]
  exact isoWhiskerLeft_naturality (Work.StemsB.SphRat.sigmaConstObjCompIso IntRat ZMod) σ

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the "nice" factor of the comparison in the simplicial set. -/
theorem Ψ_naturality {X Y : SSet.{0}} (σ : X ⟶ Y) :
    (Ψ X) ≫ cmQZ σ = G2map σ ≫ (Ψ Y) := by
  have hsrc : ((Functor.isoWhiskerLeft X (Work.StemsB.SphRat.sigmaConstObjCompIso IntRat ZMod)).hom
        ≫ Functor.whiskerRight σ (Limits.sigmaConst.obj (IntRat.obj ZMod)) :
      ((X ⋙ Limits.sigmaConst.obj ZMod) ⋙ IntRat) ⟶
        (Y ⋙ Limits.sigmaConst.obj (IntRat.obj ZMod)))
      = ((((SimplicialObject.whiskering (ModuleCat.{0} ℤ) (ModuleCat.{0} ℚ)).obj IntRat).map
            (Functor.whiskerRight σ (Limits.sigmaConst.obj ZMod)) ≫
          (Functor.isoWhiskerLeft Y (Work.StemsB.SphRat.sigmaConstObjCompIso IntRat ZMod)).hom) :
      ((X ⋙ Limits.sigmaConst.obj ZMod) ⋙ IntRat) ⟶
        (Y ⋙ Limits.sigmaConst.obj (IntRat.obj ZMod))) :=
    isoWhiskerLeft_naturality (Work.StemsB.SphRat.sigmaConstObjCompIso IntRat ZMod) σ
  have hmap := congrArg (fun k : ((X ⋙ Limits.sigmaConst.obj ZMod) ⋙ IntRat) ⟶
      (Y ⋙ Limits.sigmaConst.obj (IntRat.obj ZMod)) =>
        (alternatingFaceMapComplex (ModuleCat.{0} ℚ)).map k) hsrc
  simp only [Functor.map_comp] at hmap
  show (alternatingFaceMapComplex (ModuleCat.{0} ℚ)).map (β X).hom ≫ cmQZ σ
    = G2map σ ≫ (alternatingFaceMapComplex (ModuleCat.{0} ℚ)).map (β Y).hom
  rw [β_hom X, β_hom Y]
  exact hmap

/-- The comparison `C_*(X;ℤ) ⊗[ℤ] ℚ ≅ C_*(X;ℚ)` (as `Work.StemsB.SphRat.chainComplexBaseChange`,
rewritten with `eqToIso`). -/
noncomputable def rawIso (X : SSet.{0}) : FC X ≅ ChQZ X :=
  eqToIso (h1 X) ≪≫ (alternatingFaceMapComplex (ModuleCat.{0} ℚ)).mapIso (β X)

theorem rawIso_hom (X : SSet.{0}) : (rawIso X).hom = eqToHom (h1 X) ≫ (Ψ X) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the comparison in the simplicial set. -/
theorem rawIso_naturality {X Y : SSet.{0}} (σ : X ⟶ Y) :
    (rawIso X).hom ≫ cmQZ σ = FCmap σ ≫ (rawIso Y).hom := by
  have hΨ := Ψ_naturality σ
  have hcoh : eqToHom (h1 X) ≫ G2map σ
      = (((alternatingFaceMapComplex (ModuleCat.{0} ℤ) ⋙
          IntRat.mapHomologicalComplex (ComplexShape.down ℕ)).map
            (Functor.whiskerRight σ (Limits.sigmaConst.obj ZMod))) ≫ eqToHom (h1 Y)) :=
    eqToHom_congrArg_map AE (Functor.whiskerRight σ (Limits.sigmaConst.obj ZMod))
  calc (rawIso X).hom ≫ cmQZ σ
      = (eqToHom (h1 X) ≫ (Ψ X)) ≫ cmQZ σ := by rw [rawIso_hom]
    _ = eqToHom (h1 X) ≫ ((Ψ X) ≫ cmQZ σ) := Category.assoc _ _ _
    _ = eqToHom (h1 X) ≫ (G2map σ ≫ (Ψ Y)) := by rw [hΨ]
    _ = (eqToHom (h1 X) ≫ G2map σ) ≫ (Ψ Y) := (Category.assoc _ _ _).symm
    _ = ((((alternatingFaceMapComplex (ModuleCat.{0} ℤ) ⋙
            IntRat.mapHomologicalComplex (ComplexShape.down ℕ)).map
              (Functor.whiskerRight σ (Limits.sigmaConst.obj ZMod))) ≫ eqToHom (h1 Y)) ≫
          (Ψ Y)) := by rw [hcoh]
    _ = ((alternatingFaceMapComplex (ModuleCat.{0} ℤ) ⋙
            IntRat.mapHomologicalComplex (ComplexShape.down ℕ)).map
              (Functor.whiskerRight σ (Limits.sigmaConst.obj ZMod)) ≫
          (eqToHom (h1 Y) ≫ (Ψ Y))) := Category.assoc _ _ _
    _ = ((alternatingFaceMapComplex (ModuleCat.{0} ℤ) ⋙
            IntRat.mapHomologicalComplex (ComplexShape.down ℕ)).map
              (Functor.whiskerRight σ (Limits.sigmaConst.obj ZMod))) ≫ (rawIso Y).hom := by
          rw [rawIso_hom]
    _ = FCmap σ ≫ (rawIso Y).hom := rfl

/-! ## The coefficient change `ℤ ⊗ ℚ ≅ ℚ` -/

/-- The isomorphism `C_*(X; ℤ⊗ℚ) ≅ C_*(X;ℚ)`. -/
noncomputable abbrev coeffIso (X : SSet.{0}) : ChQZ X ≅ ChQ X :=
  (alternatingFaceMapComplex (ModuleCat.{0} ℚ)).mapIso
    (Functor.isoWhiskerLeft X
      (Limits.sigmaConst.mapIso Work.StemsB.SphRat.extendScalarsIntRatIso))

theorem coeffIso_hom (X : SSet.{0}) : (coeffIso X).hom =
    (alternatingFaceMapComplex (ModuleCat.{0} ℚ)).map
      (Functor.isoWhiskerLeft X
        (Limits.sigmaConst.mapIso Work.StemsB.SphRat.extendScalarsIntRatIso)).hom := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the coefficient change. -/
theorem coeffIso_naturality {X Y : SSet.{0}} (σ : X ⟶ Y) :
    (coeffIso X).hom ≫ (alternatingFaceMapComplex (ModuleCat.{0} ℚ)).map
        (Functor.whiskerRight σ (Limits.sigmaConst.obj QMod))
      = (alternatingFaceMapComplex (ModuleCat.{0} ℚ)).map
          (Functor.whiskerRight σ (Limits.sigmaConst.obj (IntRat.obj ZMod)))
        ≫ (coeffIso Y).hom := by
  rw [coeffIso_hom, coeffIso_hom, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  exact isoWhiskerLeft_naturality
    (Limits.sigmaConst.mapIso Work.StemsB.SphRat.extendScalarsIntRatIso) σ

/-! ## The full comparison and its naturality -/

/-- **The comparison isomorphism `C_*(X;ℤ) ⊗[ℤ] ℚ ≅ C_*(X;ℚ)`.** -/
noncomputable abbrev Phi (X : SSet.{0}) : FC X ≅ ChQ X :=
  rawIso X ≪≫ coeffIso X

theorem Phi_hom (X : SSet.{0}) : (Phi X).hom = (rawIso X).hom ≫ (coeffIso X).hom :=
  Iso.trans_hom _ _

set_option backward.isDefEq.respectTransparency false in
/-- **Naturality of the comparison in the space.** -/
theorem Phi_naturality {X Y : SSet.{0}} (σ : X ⟶ Y) :
    (Phi X).hom ≫ (alternatingFaceMapComplex (ModuleCat.{0} ℚ)).map
        (Functor.whiskerRight σ (Limits.sigmaConst.obj QMod))
      = (IntRat.mapHomologicalComplex (ComplexShape.down ℕ)).map
          ((alternatingFaceMapComplex (ModuleCat.{0} ℤ)).map
            (Functor.whiskerRight σ (Limits.sigmaConst.obj ZMod)))
        ≫ (Phi Y).hom := by
  have h1' := rawIso_naturality σ
  have h2' := coeffIso_naturality σ
  calc (Phi X).hom ≫ (alternatingFaceMapComplex (ModuleCat.{0} ℚ)).map
        (Functor.whiskerRight σ (Limits.sigmaConst.obj QMod))
      = (rawIso X).hom ≫ ((coeffIso X).hom ≫ (alternatingFaceMapComplex (ModuleCat.{0} ℚ)).map
          (Functor.whiskerRight σ (Limits.sigmaConst.obj QMod))) := by
        rw [Phi_hom, Category.assoc]
    _ = (rawIso X).hom ≫ ((alternatingFaceMapComplex (ModuleCat.{0} ℚ)).map
          (Functor.whiskerRight σ (Limits.sigmaConst.obj (IntRat.obj ZMod))) ≫ (coeffIso Y).hom) := by
        rw [h2']
    _ = ((rawIso X).hom ≫ (alternatingFaceMapComplex (ModuleCat.{0} ℚ)).map
          (Functor.whiskerRight σ (Limits.sigmaConst.obj (IntRat.obj ZMod)))) ≫ (coeffIso Y).hom := by
        rw [Category.assoc]
    _ = (((IntRat.mapHomologicalComplex (ComplexShape.down ℕ)).map
          ((alternatingFaceMapComplex (ModuleCat.{0} ℤ)).map
            (Functor.whiskerRight σ (Limits.sigmaConst.obj ZMod)))) ≫ (rawIso Y).hom) ≫ (coeffIso Y).hom := by
        rw [h1']
    _ = (IntRat.mapHomologicalComplex (ComplexShape.down ℕ)).map
          ((alternatingFaceMapComplex (ModuleCat.{0} ℤ)).map
            (Functor.whiskerRight σ (Limits.sigmaConst.obj ZMod)))
        ≫ ((rawIso Y).hom ≫ (coeffIso Y).hom) := by
        rw [Category.assoc]
    _ = (IntRat.mapHomologicalComplex (ComplexShape.down ℕ)).map
          ((alternatingFaceMapComplex (ModuleCat.{0} ℤ)).map
            (Functor.whiskerRight σ (Limits.sigmaConst.obj ZMod)))
        ≫ (Phi Y).hom := by
        rw [Phi_hom]

/-! ## `- ⊗ ℚ` preserves quasi-isomorphisms -/

/-- **`- ⊗[ℤ] ℚ` preserves quasi-isomorphisms.** -/
theorem isIso_homologyMap_mapHomologicalComplex {K L : ChainComplex (ModuleCat.{0} ℤ) ℕ} (φ : K ⟶ L)
    (n : ℕ) (h : CategoryTheory.IsIso (HomologicalComplex.homologyMap φ n)) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      ((IntRat.mapHomologicalComplex (ComplexShape.down ℕ)).map φ) n) := by
  have hf : (Int.castRingHom ℚ).Flat := by rw [RingHom.Flat]; infer_instance
  haveI : PreservesFiniteLimits IntRat := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  haveI : PreservesFiniteColimits IntRat := inferInstance
  haveI : IntRat.PreservesHomology := inferInstance
  haveI : IntRat.PreservesLeftHomologyOf (K.sc n) := inferInstance
  haveI : IntRat.PreservesLeftHomologyOf (L.sc n) := inferInstance
  set φs := (HomologicalComplex.shortComplexFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n).map φ
    with hφs
  have hnat := ShortComplex.mapHomologyIso_hom_naturality φs IntRat
  have hφ : CategoryTheory.IsIso (ShortComplex.homologyMap φs) := h
  let B' : (IntRat.mapShortComplex.obj ((HomologicalComplex.shortComplexFunctor (ModuleCat.{0} ℤ)
        (ComplexShape.down ℕ) n).obj L)).homology ⟶
      IntRat.obj (((HomologicalComplex.shortComplexFunctor (ModuleCat.{0} ℤ)
        (ComplexShape.down ℕ) n).obj L).homology) :=
    (((HomologicalComplex.shortComplexFunctor (ModuleCat.{0} ℤ)
      (ComplexShape.down ℕ) n).obj L).mapHomologyIso IntRat).hom
  haveI : CategoryTheory.IsIso B' := by
    change CategoryTheory.IsIso ((((HomologicalComplex.shortComplexFunctor (ModuleCat.{0} ℤ)
      (ComplexShape.down ℕ) n).obj L).mapHomologyIso IntRat).hom)
    infer_instance
  have hnat' : ShortComplex.homologyMap (IntRat.mapShortComplex.map φs) ≫ B'
      = ((((HomologicalComplex.shortComplexFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n).obj K).mapHomologyIso
            IntRat).hom ≫ IntRat.map (ShortComplex.homologyMap φs)) := hnat
  have hcast : ShortComplex.homologyMap (IntRat.mapShortComplex.map φs)
      = ((((HomologicalComplex.shortComplexFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n).obj K).mapHomologyIso
            IntRat).hom ≫ IntRat.map (ShortComplex.homologyMap φs)) ≫
          CategoryTheory.inv B' := by
    have step : (ShortComplex.homologyMap (IntRat.mapShortComplex.map φs) ≫ B') ≫
          CategoryTheory.inv B'
        = (((((HomologicalComplex.shortComplexFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n).obj K).mapHomologyIso
              IntRat).hom ≫ IntRat.map (ShortComplex.homologyMap φs)) ≫ CategoryTheory.inv B') :=
      congrArg (fun k => k ≫ CategoryTheory.inv B') hnat'
    rw [← step, Category.assoc, IsIso.hom_inv_id B', Category.comp_id]
  haveI : CategoryTheory.IsIso ((((HomologicalComplex.shortComplexFunctor (ModuleCat.{0} ℤ)
      (ComplexShape.down ℕ) n).obj K).mapHomologyIso IntRat).hom) :=
    (((HomologicalComplex.shortComplexFunctor (ModuleCat.{0} ℤ)
      (ComplexShape.down ℕ) n).obj K).mapHomologyIso IntRat).isIso_hom
  have hthree : CategoryTheory.IsIso (ShortComplex.homologyMap (IntRat.mapShortComplex.map φs)) :=
    hcast ▸ (asIso ((((HomologicalComplex.shortComplexFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n).obj K).mapHomologyIso
        IntRat).hom) ≪≫ asIso (IntRat.map (ShortComplex.homologyMap φs)) ≪≫ (asIso B').symm).isIso_hom
  have hfour : ShortComplex.homologyMap (IntRat.mapShortComplex.map φs)
      = HomologicalComplex.homologyMap
          (((IntRat.mapHomologicalComplex (ComplexShape.down ℕ)).map φ)) n := rfl
  rw [hfour] at hthree
  exact hthree

/-! ## The transfer -/

set_option backward.isDefEq.respectTransparency false in
/-- **The `ℤ → ℚ` transfer of homology isomorphisms.** -/
theorem isIso_homologyMap_rat_of_isIso_int (X Y : TopCat) (g : X ⟶ Y) (n : ℕ)
    (h : CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ X Y g) n)) :
    CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℚ X Y g) n) := by
  set σ := TopCat.toSSet.map g with hσ
  have hZ : Work.Cohomology.chainMap ℤ X Y g = (alternatingFaceMapComplex (ModuleCat.{0} ℤ)).map
      (Functor.whiskerRight σ (Limits.sigmaConst.obj ZMod)) := rfl
  have hQ : Work.Cohomology.chainMap ℚ X Y g = (alternatingFaceMapComplex (ModuleCat.{0} ℚ)).map
      (Functor.whiskerRight σ (Limits.sigmaConst.obj QMod)) := rfl
  rw [hZ] at h
  rw [hQ]
  have hmid : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (((IntRat.mapHomologicalComplex (ComplexShape.down ℕ)).map
        ((alternatingFaceMapComplex (ModuleCat.{0} ℤ)).map
          (Functor.whiskerRight σ (Limits.sigmaConst.obj ZMod)))) :
        FC (TopCat.toSSet.obj X) ⟶ FC (TopCat.toSSet.obj Y)) n) :=
    isIso_homologyMap_mapHomologicalComplex _ n h
  have hsq : (alternatingFaceMapComplex (ModuleCat.{0} ℚ)).map
        (Functor.whiskerRight σ (Limits.sigmaConst.obj QMod))
      = (Phi (TopCat.toSSet.obj X)).inv
        ≫ ((IntRat.mapHomologicalComplex (ComplexShape.down ℕ)).map
            ((alternatingFaceMapComplex (ModuleCat.{0} ℤ)).map
              (Functor.whiskerRight σ (Limits.sigmaConst.obj ZMod))))
        ≫ (Phi (TopCat.toSSet.obj Y)).hom := by
    rw [← Phi_naturality σ, Iso.inv_hom_id_assoc]
  rw [hsq, HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]
  haveI : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Phi (TopCat.toSSet.obj X)).inv n) := inferInstance
  haveI : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      ((IntRat.mapHomologicalComplex (ComplexShape.down ℕ)).map (cmZ σ)) n) := hmid
  haveI : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Phi (TopCat.toSSet.obj Y)).hom n) := inferInstance
  infer_instance

end

end Work.Serre
