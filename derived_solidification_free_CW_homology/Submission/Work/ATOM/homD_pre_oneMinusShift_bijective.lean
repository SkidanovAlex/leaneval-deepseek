import Mathlib
import Submission.Work.ATOM.Defs

/-!
# AREA ATOM — F7 in the derived category

The main result of this file is `Work.ATOM.homD_pre_oneMinusShift_bijective`: precomposition with
`singleC n ((1 - S) ⊗ id_Y)` is bijective on morphisms `Q (singleC n (P ⊗ Y)) ⟶ Q (ιC N)` in the
derived category of light condensed abelian groups, for every complex `N` of solid objects.

The proof is the derived-category form of the "tensor-hom" argument of REFS/01 F6–F7:

* `tensorLeft P ⊣ ihom P` is an adjunction of exact functors, hence (Mathlib
  `Adjunction.localization`) it induces an adjunction `T ⊣ H` on the derived categories, where
  `T = (tensorLeft P).mapDerivedCategory` and `H = (ihom P).mapDerivedCategory`;
* the conjugate (Mathlib's `conjugateEquiv`) of the natural endomorphism
  `τ = whiskerRight oneMinusShift : tensorLeft P ⟶ tensorLeft P` under this adjunction is the
  natural endomorphism `σ = MonoidalClosed.pre oneMinusShift : ihom P ⟶ ihom P`, whose components
  are isomorphisms exactly when the object is solid (`isSolid` *is* the statement that
  `(pre oneMinusShift).app -` is an iso);
* precomposition with `τ` corresponds under the adjunction to postcomposition with the conjugate
  `σ`, and postcomposition with an isomorphism is bijective.

The technical heart is `conjugate_lift`, which identifies the conjugate of
`NatTrans.mapDerivedCategory τ` with `NatTrans.mapDerivedCategory σ` at objects of the form
`Q M`: everything is computed on the nose using the explicit formulas
`NatTrans.mapDerivedCategory_app_Q_obj` and `Adjunction.localization_counit_app`, reducing to the
purely 1-categorical identity `MonoidalClosed.id_tensor_pre_app_comp_ev`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

namespace Work.ATOM

/-- `tensorLeft P` is additive (it is a left adjoint, hence preserves biproducts). -/
instance : (tensorLeft P).Additive := by
  have h : PreservesColimitsOfSize.{0, 0} (tensorLeft P) :=
    (ihom.adjunction P).leftAdjoint_preservesColimits
  have : PreservesColimitsOfShape (Discrete WalkingPair) (tensorLeft P) :=
    h.preservesColimitsOfShape
  have : PreservesBinaryBiproducts (tensorLeft P) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- The "conjugation" formula: for an adjunction `F ⊣ G`, a natural endomorphism `τ` of `F`
and `f : F.obj X ⟶ Y`, transposing `τ.app X ≫ f` is post-composing the transpose of `f` with the
conjugate `G.obj Y ⟶ G.obj Y` of `τ`. -/
theorem homEquiv_comp_conjugate {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) (τ : F ⟶ F) (X : C) (Y : D) (f : F.obj X ⟶ Y) :
    adj.homEquiv X Y (τ.app X ≫ f) =
      adj.homEquiv X Y f ≫ adj.homEquiv (G.obj Y) Y (τ.app (G.obj Y) ≫ adj.counit.app Y) := by
  have h1 : f = F.map (adj.homEquiv X Y f) ≫ adj.counit.app Y := by
    rw [← adj.homEquiv_symm_apply X Y (adj.homEquiv X Y f), Equiv.symm_apply_apply]
  conv_lhs => rw [h1, ← Category.assoc, ← τ.naturality (adj.homEquiv X Y f), Category.assoc]
  rw [adj.homEquiv_naturality_left]

/-- A morphism of cochain complexes all of whose components are isomorphisms is an isomorphism. -/
theorem isIso_of_isIso_f {K L : CochainComplex LightCondAb ℤ} (f : K ⟶ L)
    (h : ∀ i, IsIso (f.f i)) : IsIso f := by
  letI (i : ℤ) : IsIso (f.f i) := h i
  let g : L ⟶ K :=
    { f := fun i => inv (f.f i)
      comm' := by
        intro i j hij
        have h1 : (f.f i ≫ L.d i j) ≫ inv (f.f j) = K.d i j := by
          rw [IsIso.comp_inv_eq, f.comm i j]
        rw [← h1]
        simp [Category.assoc] }
  refine IsIso.mk ⟨g, ?_, ?_⟩
  · apply HomologicalComplex.hom_ext
    intro i
    simp [g, HomologicalComplex.comp_f]
  · apply HomologicalComplex.hom_ext
    intro i
    simp [g, HomologicalComplex.comp_f]

/-- The natural endomorphism `σ = (pre oneMinusShift) : ihom P ⟶ ihom P` becomes an isomorphism
on complexes whose objects are solid. -/
theorem isIso_pre_mapHomologicalComplex (M : CochainComplex LightCondAb ℤ)
    (hM : ∀ i, isSolid (M.X i)) :
    IsIso ((NatTrans.mapHomologicalComplex (MonoidalClosed.pre oneMinusShift)
      (ComplexShape.up ℤ)).app M) := by
  apply isIso_of_isIso_f
  intro i
  rw [NatTrans.mapHomologicalComplex_app_f]
  exact hM i

section ChAdjunction

variable {ι : Type*} {C D : Type*} [Category C] [Category D]
  [HasZeroMorphisms C] [HasZeroMorphisms D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
  [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] (c : ComplexShape ι)

/-- The adjunction `F ⊣ G` induces an adjunction between the degreewise induced functors on
complexes; its unit and counit are the degreewise unit and counit of `F ⊣ G`. -/
noncomputable def mapHomologicalComplexAdj : F.mapHomologicalComplex c ⊣ G.mapHomologicalComplex c :=
  Adjunction.mkOfUnitCounit {
    unit :=
      { app := fun K => HomologicalComplex.Hom.mk (fun i => adj.unit.app (K.X i)) (by
          intro i j hij
          dsimp only [Functor.comp_obj, Functor.id_obj]
          rw [Functor.mapHomologicalComplex_obj_d, Functor.mapHomologicalComplex_obj_d]
          simpa only [Functor.id_map, Functor.comp_map] using (adj.unit.naturality (K.d i j)).symm)
        naturality := fun K L f => by
          apply HomologicalComplex.hom_ext
          intro i
          rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
          dsimp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Functor.id_map]
          rw [Functor.mapHomologicalComplex_map_f, Functor.mapHomologicalComplex_map_f]
          exact adj.unit.naturality (f.f i) }
    counit :=
      { app := fun L => HomologicalComplex.Hom.mk (fun i => adj.counit.app (L.X i)) (by
          intro i j hij
          dsimp only [Functor.comp_obj, Functor.id_obj]
          rw [Functor.mapHomologicalComplex_obj_d, Functor.mapHomologicalComplex_obj_d]
          simpa only [Functor.id_map, Functor.comp_map] using (adj.counit.naturality (L.d i j)).symm)
        naturality := fun L L' f => by
          apply HomologicalComplex.hom_ext
          intro i
          rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
          dsimp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Functor.id_map]
          rw [Functor.mapHomologicalComplex_map_f, Functor.mapHomologicalComplex_map_f]
          exact adj.counit.naturality (f.f i) }
    left_triangle := by
      ext K
      simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Functor.associator_hom_app, Functor.comp_obj, Functor.id_obj, HomologicalComplex.comp_f,
        Category.id_comp]
      rw [Functor.mapHomologicalComplex_map_f]
      exact adj.left_triangle_components (K.X _)
    right_triangle := by
      ext L
      simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Functor.associator_inv_app, Functor.comp_obj, Functor.id_obj, HomologicalComplex.comp_f,
        Category.id_comp]
      rw [Functor.mapHomologicalComplex_map_f]
      exact adj.right_triangle_components (L.X _) }

@[simp]
lemma mapHomologicalComplexAdj_unit_f (K : HomologicalComplex C c) (i : ι) :
    ((mapHomologicalComplexAdj adj c).unit.app K).f i = adj.unit.app (K.X i) := rfl

@[simp]
lemma mapHomologicalComplexAdj_counit_f (L : HomologicalComplex D c) (i : ι) :
    ((mapHomologicalComplexAdj adj c).counit.app L).f i = adj.counit.app (L.X i) := rfl

end ChAdjunction

/-! ### The derived adjunction and the conjugate endomorphism -/

section Derived

variable [PreservesFiniteLimits (tensorLeft P)]

/-- The degreewise tensor product with `P`, as a functor on complexes. -/
abbrev Vc : CochainComplex LightCondAb ℤ ⥤ CochainComplex LightCondAb ℤ :=
  (tensorLeft P).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The degreewise internal hom out of `P`, as a functor on complexes. -/
abbrev Wc : CochainComplex LightCondAb ℤ ⥤ CochainComplex LightCondAb ℤ :=
  (ihom P).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Derived tensor product with `P`. -/
abbrev Td : DLightCondAb ⥤ DLightCondAb := (tensorLeft P).mapDerivedCategory

/-- Derived internal hom out of `P`. -/
abbrev Hd : DLightCondAb ⥤ DLightCondAb := (ihom P).mapDerivedCategory

/-- The endomorphism `(1 - S) ⊗ id` on `P ⊗ -`. -/
abbrev τh : tensorLeft P ⟶ tensorLeft P := (curriedTensor LightCondAb).map oneMinusShift

/-- The conjugate endomorphism `pre (1 - S)` on `ihom P`, which is an isomorphism exactly on
solid objects. -/
abbrev σh : ihom P ⟶ ihom P := MonoidalClosed.pre oneMinusShift

/-- The degreewise endomorphism `(1 - S) ⊗ id` on complexes. -/
abbrev τc : Vc ⟶ Vc := NatTrans.mapHomologicalComplex τh (ComplexShape.up ℤ)

/-- The degreewise conjugate endomorphism. -/
abbrev σc : Wc ⟶ Wc := NatTrans.mapHomologicalComplex σh (ComplexShape.up ℤ)

/-- The endomorphism of the derived tensor product induced by `(1 - S) ⊗ id`. -/
abbrev τd : Td ⟶ Td := NatTrans.mapDerivedCategory τh

/-- The endomorphism of the derived internal hom induced by `pre (1 - S)`. -/
abbrev σd : Hd ⟶ Hd := NatTrans.mapDerivedCategory σh

/-- The adjunction between the degreewise functors. -/
noncomputable def chAdj : Vc ⊣ Wc := mapHomologicalComplexAdj (ihom.adjunction P) (ComplexShape.up ℤ)

instance : CatCommSq Vc DerivedCategory.Q DerivedCategory.Q Td :=
  ⟨(Functor.mapDerivedCategoryFactors (tensorLeft P)).symm⟩

instance : CatCommSq Wc DerivedCategory.Q DerivedCategory.Q Hd :=
  ⟨(Functor.mapDerivedCategoryFactors (ihom P)).symm⟩

/-- The induced adjunction on derived categories: derived tensor product with `P` is left adjoint
to derived internal hom out of `P`. -/
noncomputable def dadj : Td ⊣ Hd :=
  chAdj.localization DerivedCategory.Q
    (HomologicalComplex.quasiIso LightCondAb (ComplexShape.up ℤ)) DerivedCategory.Q
    (HomologicalComplex.quasiIso LightCondAb (ComplexShape.up ℤ)) Td Hd

lemma dadj_counit_app_Q (M : CochainComplex LightCondAb ℤ) :
    dadj.counit.app (DerivedCategory.Q.obj M) =
      Td.map ((Functor.mapDerivedCategoryFactors (ihom P)).hom.app M) ≫
        (Functor.mapDerivedCategoryFactors (tensorLeft P)).hom.app (Wc.obj M) ≫
          DerivedCategory.Q.map (chAdj.counit.app M) := by
  rw [dadj, Adjunction.localization_counit_app]
  rfl

/-- The purely 1-categorical identity underlying the compatibility of the conjugation with the
localization: `τ` and its conjugate `σ` satisfy the defining equation of a conjugate for the
degreewise adjunction. -/
theorem complex_conjugate (M : CochainComplex LightCondAb ℤ) :
    Vc.map (σc.app M) ≫ chAdj.counit.app M = τc.app (Wc.obj M) ≫ chAdj.counit.app M := by
  apply HomologicalComplex.hom_ext
  intro i
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f, mapHomologicalComplexAdj_counit_f,
    ihom.ihom_adjunction_counit]
  exact MonoidalClosed.id_tensor_pre_app_comp_ev oneMinusShift (M.X i)

/-- The natural isomorphism expressing that `DerivedCategory.Q` intertwines `Td` with `Vc`. -/
abbrev φV : DerivedCategory.Q ⋙ Td ≅ Vc ⋙ DerivedCategory.Q :=
  Functor.mapDerivedCategoryFactors (tensorLeft P)

/-- The natural isomorphism expressing that `DerivedCategory.Q` intertwines `Hd` with `Wc`. -/
abbrev φW : DerivedCategory.Q ⋙ Hd ≅ Wc ⋙ DerivedCategory.Q :=
  Functor.mapDerivedCategoryFactors (ihom P)

lemma σd_app_Q (M : CochainComplex LightCondAb ℤ) :
    σd.app (DerivedCategory.Q.obj M) =
      φW.hom.app M ≫ DerivedCategory.Q.map (σc.app M) ≫ φW.inv.app M :=
  NatTrans.mapDerivedCategory_app_Q_obj σh M

lemma τd_app_Q (M : CochainComplex LightCondAb ℤ) :
    τd.app (DerivedCategory.Q.obj M) =
      φV.hom.app M ≫ DerivedCategory.Q.map (τc.app M) ≫ φV.inv.app M :=
  NatTrans.mapDerivedCategory_app_Q_obj τh M

/-- The image under `Td` of a morphism of the form `Q.map f`. -/
lemma Td_map_Q_map {M M' : CochainComplex LightCondAb ℤ} (f : M ⟶ M') :
    Td.map (DerivedCategory.Q.map f) =
      φV.hom.app M ≫ DerivedCategory.Q.map (Vc.map f) ≫ φV.inv.app M' := by
  calc Td.map (DerivedCategory.Q.map f)
      = Td.map (DerivedCategory.Q.map f) ≫ 𝟙 (Td.obj (DerivedCategory.Q.obj M')) :=
        (Category.comp_id _).symm
    _ = Td.map (DerivedCategory.Q.map f) ≫ (φV.hom.app M' ≫ φV.inv.app M') := by
        rw [Iso.hom_inv_id_app]
        rfl
    _ = (Td.map (DerivedCategory.Q.map f) ≫ φV.hom.app M') ≫ φV.inv.app M' :=
        (Category.assoc _ _ _).symm
    _ = (φV.hom.app M ≫ DerivedCategory.Q.map (Vc.map f)) ≫ φV.inv.app M' := by
        rw [Functor.mapDerivedCategoryFactors_hom_naturality]
    _ = φV.hom.app M ≫ DerivedCategory.Q.map (Vc.map f) ≫ φV.inv.app M' :=
        Category.assoc _ _ _

/-- Naturality of `τd` at the canonical isomorphism `Hd.obj (Q.obj M) ≅ Q.obj (Wc.obj M)`. -/
lemma τd_app_Hd (M : CochainComplex LightCondAb ℤ) :
    τd.app (Hd.obj (DerivedCategory.Q.obj M)) =
      Td.map (φW.hom.app M) ≫ τd.app (DerivedCategory.Q.obj (Wc.obj M)) ≫
        Td.map (φW.inv.app M) := by
  have h3 : Td.map (φW.hom.app M) ≫ Td.map (φW.inv.app M) ≫
      τd.app (Hd.obj (DerivedCategory.Q.obj M)) =
      τd.app (Hd.obj (DerivedCategory.Q.obj M)) := by
    rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp]
  rw [← h3]
  erw [τd.naturality (φW.inv.app M)]
  rfl

/-- The conjugate of `τd` is `σd`: this is the compatibility of the conjugation with the
localization, checked at objects of the form `Q.obj M`. -/
theorem conjugate_lift (M : CochainComplex LightCondAb ℤ) :
    dadj.homEquiv (Hd.obj (DerivedCategory.Q.obj M)) (DerivedCategory.Q.obj M)
        (τd.app (Hd.obj (DerivedCategory.Q.obj M)) ≫
          dadj.counit.app (DerivedCategory.Q.obj M)) =
      σd.app (DerivedCategory.Q.obj M) := by
  have aux : Td.map (σd.app (DerivedCategory.Q.obj M)) ≫
        dadj.counit.app (DerivedCategory.Q.obj M) =
      Td.map (φW.hom.app M) ≫ φV.hom.app (Wc.obj M) ≫
        DerivedCategory.Q.map (Vc.map (σc.app M) ≫ chAdj.counit.app M) := by
    rw [σd_app_Q M, dadj_counit_app_Q M, Functor.map_comp, Functor.map_comp,
      Td_map_Q_map (σc.app M)]
    have hcancel : ∀ {Y : DLightCondAb}
        (f : Td.obj (DerivedCategory.Q.obj (Wc.obj M)) ⟶ Y),
        Td.map (φW.inv.app M) ≫ Td.map (φW.hom.app M) ≫ f = f := by
      intro Y f
      rw [show Td.map (φW.inv.app M) = inv (Td.map (φW.hom.app M)) from by
        rw [IsIso.eq_inv_of_hom_inv_id (Iso.hom_inv_id_app φW M), Functor.map_inv]]
      rw [IsIso.inv_hom_id_assoc]
    simp only [Category.assoc]
    rw [hcancel, Iso.inv_hom_id_app_assoc, ← Functor.map_comp]
  have aux' : τd.app (Hd.obj (DerivedCategory.Q.obj M)) ≫
        dadj.counit.app (DerivedCategory.Q.obj M) =
      Td.map (φW.hom.app M) ≫ φV.hom.app (Wc.obj M) ≫
        DerivedCategory.Q.map (τc.app (Wc.obj M) ≫ chAdj.counit.app M) := by
    rw [τd_app_Hd M, τd_app_Q (Wc.obj M), dadj_counit_app_Q M]
    have hcancel : ∀ {Y : DLightCondAb}
        (f : Td.obj (DerivedCategory.Q.obj (Wc.obj M)) ⟶ Y),
        Td.map (φW.inv.app M) ≫ Td.map (φW.hom.app M) ≫ f = f := by
      intro Y f
      rw [show Td.map (φW.inv.app M) = inv (Td.map (φW.hom.app M)) from by
        rw [IsIso.eq_inv_of_hom_inv_id (Iso.hom_inv_id_app φW M), Functor.map_inv]]
      rw [IsIso.inv_hom_id_assoc]
    simp only [Category.assoc]
    rw [hcancel, Iso.inv_hom_id_app_assoc, ← Functor.map_comp]
  have h2 : (dadj.homEquiv (Hd.obj (DerivedCategory.Q.obj M))
      (DerivedCategory.Q.obj M)).symm (σd.app (DerivedCategory.Q.obj M)) =
      τd.app (Hd.obj (DerivedCategory.Q.obj M)) ≫
        dadj.counit.app (DerivedCategory.Q.obj M) := by
    rw [Adjunction.homEquiv_symm_apply, aux, aux', complex_conjugate M]
  rw [← h2, Equiv.apply_symm_apply]

end Derived

/-! ### Toolbox: pre- and post-composition with isomorphisms -/

/-- Precomposition with an isomorphism is a bijection. -/
theorem bijective_precomp_iso {C : Type*} [Category C] {A B Z : C} (e : A ⟶ B) [IsIso e] :
    Function.Bijective (fun φ : B ⟶ Z => e ≫ φ) := by
  refine ⟨fun φ ψ h => ?_, fun φ => ⟨inv e ≫ φ, ?_⟩⟩
  · have h' := congrArg (fun t => inv e ≫ t) h
    simpa only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp] using h'
  · change e ≫ (inv e ≫ φ) = φ
    rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]

/-- Postcomposition with an isomorphism is a bijection. -/
theorem bijective_postcomp_iso {C : Type*} [Category C] {X Y Z : C} (e : Y ⟶ Z) [IsIso e] :
    Function.Bijective (fun f : X ⟶ Y => f ≫ e) := by
  refine ⟨fun f g h => ?_, fun φ => ⟨φ ≫ inv e, ?_⟩⟩
  · have h' := congrArg (fun t => t ≫ inv e) h
    simpa only [Category.assoc, IsIso.hom_inv_id, Category.comp_id] using h'
  · change (φ ≫ inv e) ≫ e = φ
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

section Conjugation

variable {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G : D ⥤ C}

/-- If the conjugate of a natural endomorphism `τ` of the left adjoint `F` is an isomorphism at
`Y`, then precomposition with `τ` is a bijection on morphisms into `Y`. -/
theorem bijective_precomp_of_conjugate_iso (adj : F ⊣ G) (τ : F ⟶ F) (X : C) (Y : D)
    (hiso : IsIso (adj.homEquiv (G.obj Y) Y (τ.app (G.obj Y) ≫ adj.counit.app Y))) :
    Function.Bijective (fun f : F.obj X ⟶ Y => τ.app X ≫ f) := by
  letI := hiso
  have hsq : (fun f : F.obj X ⟶ Y => τ.app X ≫ f) =
      ⇑(adj.homEquiv X Y).symm ∘
        ((fun g : X ⟶ G.obj Y =>
          g ≫ adj.homEquiv (G.obj Y) Y (τ.app (G.obj Y) ≫ adj.counit.app Y)) ∘
            ⇑(adj.homEquiv X Y)) := by
    funext f
    simp only [Function.comp_apply]
    symm
    rw [Equiv.symm_apply_eq]
    exact (homEquiv_comp_conjugate adj τ X Y f).symm
  rw [hsq]
  exact Function.Bijective.comp (Equiv.bijective _)
    (Function.Bijective.comp (bijective_postcomp_iso _) (Equiv.bijective _))

/-- Conjugating an endomorphism by an isomorphism does not change the bijectivity of the
associated precomposition map. -/
theorem bijective_precomp_conj_iff {C : Type*} [Category C] {A B Z : C} (e : A ≅ B)
    (u : B ⟶ B) :
    Function.Bijective (fun ψ : B ⟶ Z => u ≫ ψ) ↔
      Function.Bijective (fun φ : A ⟶ Z => (e.hom ≫ u ≫ e.inv) ≫ φ) := by
  have hsq : (fun φ : A ⟶ Z => (e.hom ≫ u ≫ e.inv) ≫ φ) =
      (fun ψ : B ⟶ Z => e.hom ≫ ψ) ∘
        ((fun ψ : B ⟶ Z => u ≫ ψ) ∘ (fun φ : A ⟶ Z => e.inv ≫ φ)) := by
    funext φ
    simp only [Function.comp_apply, Category.assoc]
  rw [hsq]
  have hA : Function.Bijective (fun ψ : B ⟶ Z => e.hom ≫ ψ) := bijective_precomp_iso e.hom
  have hC : Function.Bijective (fun φ : A ⟶ Z => e.inv ≫ φ) := bijective_precomp_iso e.inv
  constructor
  · intro h
    exact Function.Bijective.comp hA (Function.Bijective.comp h hC)
  · intro h
    exact (Function.Bijective.of_comp_iff (fun ψ : B ⟶ Z => u ≫ ψ) hC).mp
      ((Function.Bijective.of_comp_iff' hA _).mp h)

end Conjugation

section Derived2

variable [PreservesFiniteLimits (tensorLeft P)]

/-- The conjugate of `τd` at `Q.obj M` is an isomorphism when `M` is a complex of solid
objects. -/
lemma isIso_conjugate (M : CochainComplex LightCondAb ℤ) (hM : ∀ i, isSolid (M.X i)) :
    IsIso (dadj.homEquiv (Hd.obj (DerivedCategory.Q.obj M)) (DerivedCategory.Q.obj M)
      (τd.app (Hd.obj (DerivedCategory.Q.obj M)) ≫
        dadj.counit.app (DerivedCategory.Q.obj M))) := by
  rw [conjugate_lift M, σd_app_Q M]
  haveI : IsIso (σc.app M) := isIso_pre_mapHomologicalComplex M hM
  haveI : IsIso (DerivedCategory.Q.map (σc.app M)) := Functor.map_isIso _ _
  haveI : IsIso (φW.hom.app M) := Iso.isIso_hom (φW.app M)
  haveI : IsIso (φW.inv.app M) := Iso.isIso_inv (φW.app M)
  infer_instance

end Derived2

/-- (F7 in the derived category) Assuming `P ⊗ -` is left exact (this is `FlatProp` for `P`,
which is assumed freely by the ATOM area), precomposition with `Q (singleC n ((1-S) ⊗ id_Y))`
is bijective on morphisms from `Q (singleC n (P ⊗ Y))` into `Q (ιC N)` in the derived category,
for every complex `N` of solid objects. -/
theorem homD_pre_oneMinusShift_bijective (N : CochainComplex LightCondensed.Solid ℤ) (n : ℤ)
    (Y : LightCondAb) [CategoryTheory.Limits.PreservesFiniteLimits
      (CategoryTheory.MonoidalCategory.tensorLeft LightCondensed.P)] :
    Function.Bijective (fun φ : DerivedCategory.Q.obj
        ((Work.ATOM.singleC n).obj (Work.ATOM.tmul LightCondensed.P Y)) ⟶
        DerivedCategory.Q.obj (Submission.Blueprint.ιC.obj N) =>
      DerivedCategory.Q.map ((Work.ATOM.singleC n).map (Work.ATOM.preShift Y)) ≫ φ) := by
  have hMsolid : ∀ i, isSolid ((Submission.Blueprint.ιC.obj N).X i) := fun i => (N.X i).property
  have hbij : Function.Bijective (fun φ :
      Td.obj ((DerivedCategory.singleFunctor LightCondAb n).obj Y) ⟶
      DerivedCategory.Q.obj (Submission.Blueprint.ιC.obj N) =>
      τd.app ((DerivedCategory.singleFunctor LightCondAb n).obj Y) ≫ φ) :=
    bijective_precomp_of_conjugate_iso dadj τd _
      (DerivedCategory.Q.obj (Submission.Blueprint.ιC.obj N)) (isIso_conjugate _ hMsolid)
  have hτ : τd.app ((DerivedCategory.singleFunctor LightCondAb n).obj Y) =
      (Functor.mapDerivedCategorySingleFunctor (tensorLeft P) n).hom.app Y ≫
        (DerivedCategory.singleFunctor LightCondAb n).map (τh.app Y) ≫
          (Functor.mapDerivedCategorySingleFunctor (tensorLeft P) n).inv.app Y :=
    NatTrans.mapDerivedCategory_app_singleFunctor_obj τh Y n
  rw [hτ] at hbij
  refine (bijective_precomp_conj_iff
    ((Functor.mapDerivedCategorySingleFunctor (tensorLeft P) n).app Y)
    ((DerivedCategory.singleFunctor LightCondAb n).map (τh.app Y))).mpr ?_
  exact hbij

end Work.ATOM
