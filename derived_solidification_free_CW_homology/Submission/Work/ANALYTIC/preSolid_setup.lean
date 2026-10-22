import Mathlib
import Submission.Work.ANALYTIC.Basic
import Submission.Work.DERFORMAL.Gen.AdjHomotopyCategory

/-!
# Setup for the F7 input of REFS/01 (F6–F7)

This file contains the material used by `Submission.Work.ANALYTIC.preSolid_all`:

* the exact endofunctors `tensorLeft P` (written `L`) and `ihom P` (written `R`) of
  `LightCondAb`, and the natural endomorphisms `tauP` (`M ↦ (1 - S) ⊗ id_M`) and
  `muP` (`pre (1 - S)`);
* the mate identity `mate_abelian` at the level of light condensed abelian groups, which is
  `MonoidalClosed.curry_pre_app`, and its lift `mate_complex` to cochain complexes;
* the induced adjunction `adjD : LD ⊣ RD` on the derived category, obtained from the exact
  adjunction `tensorLeft P ⊣ ihom P` by `Adjunction.localization`;
* the explicit formula for the unit of `adjD` at objects of the form `Q.obj K`, and the
  mate identity `unit_mate` at the derived level.
-/

namespace Work.ANALYTIC

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed

noncomputable section

open _root_.LightCondensed _root_.LightCondensed.Solid

/-! ## The two exact endofunctors `tensorLeft P` and `ihom P` -/

instance instAdditiveTensorLeftP : (tensorLeft P).Additive := by
  have h : PreservesColimitsOfSize.{0,0} (tensorLeft P) :=
    (ihom.adjunction P).leftAdjoint_preservesColimits
  have : PreservesColimitsOfShape (Discrete WalkingPair) (tensorLeft P) := h.preservesColimitsOfShape
  have : PreservesBinaryBiproducts (tensorLeft P) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

instance instPreservesFiniteColimitsTensorLeftP : PreservesFiniteColimits (tensorLeft P) := by
  have h : PreservesColimitsOfSize.{0,0} (tensorLeft P) :=
    (ihom.adjunction P).leftAdjoint_preservesColimits
  exact PreservesColimitsOfSize.preservesFiniteColimits (tensorLeft P)

instance instPreservesFiniteLimitsIhomP : PreservesFiniteLimits (ihom P) := by
  have h : PreservesLimitsOfSize.{0,0} (ihom P) := (ihom.adjunction P).rightAdjoint_preservesLimits
  exact PreservesLimitsOfSize.preservesFiniteLimits (ihom P)

/-- `(1 - S) ⊗ id` as a natural endomorphism of `tensorLeft P`. -/
noncomputable def tauP : tensorLeft P ⟶ tensorLeft P where
  app M := oneMinusShift ▷ M
  naturality _ _ f := whisker_exchange oneMinusShift f

/-- The endomorphism `pre (1 - S)` of `ihom P`, the mate of `tauP`. -/
noncomputable def muP : ihom P ⟶ ihom P := MonoidalClosed.pre oneMinusShift

/-- **The mate identity at the level of light condensed abelian groups.**  Precomposition with
`(1 - S) ⊗ id_M` on `Hom(P ⊗ M, N)` corresponds, under the currying adjunction
`tensorLeft P ⊣ ihom P`, to postcomposition with `pre (1 - S)` on `Hom(M, ihom P N)`.  Taking
`f = id` gives the unit form used below. -/
theorem mate_abelian (N : LightCondAb) :
    (ihom.adjunction P).unit.app N ≫ (ihom P).map (tauP.app N) =
      (ihom.adjunction P).unit.app N ≫ muP.app ((tensorLeft P).obj N) := by
  have key : MonoidalClosed.curry (𝟙 ((tensorLeft P).obj N)) ≫ muP.app ((tensorLeft P).obj N) =
      MonoidalClosed.curry (oneMinusShift ▷ N) := by
    refine (MonoidalClosed.curry_pre_app (A := P) (B := P) oneMinusShift
      (X := (tensorLeft P).obj N) (Y := N) (𝟙 ((tensorLeft P).obj N))).trans ?_
    congr 1
  have hA : (ihom.adjunction P).unit.app N ≫ (ihom P).map (tauP.app N) =
      MonoidalClosed.curry (oneMinusShift ▷ N) :=
    (Adjunction.homEquiv_apply (ihom.adjunction P) N ((tensorLeft P).obj N) (tauP.app N)).symm
  have hη : MonoidalClosed.curry (𝟙 ((tensorLeft P).obj N)) = (ihom.adjunction P).unit.app N := by
    have h := Adjunction.homEquiv_apply (ihom.adjunction P) N ((tensorLeft P).obj N)
      (𝟙 ((tensorLeft P).obj N))
    rw [CategoryTheory.Functor.map_id] at h
    exact h.trans (Category.comp_id _)
  have hB : (ihom.adjunction P).unit.app N ≫ muP.app ((tensorLeft P).obj N) =
      MonoidalClosed.curry (oneMinusShift ▷ N) := by
    rw [← hη]
    exact key
  rw [hA, hB]

/-! ## The lift to cochain complexes -/

/-- The degreewise extension of `tensorLeft P` to cochain complexes. -/
abbrev LC : CochainComplex LightCondAb ℤ ⥤ CochainComplex LightCondAb ℤ :=
  (tensorLeft P).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The degreewise extension of `ihom P` to cochain complexes. -/
abbrev RC : CochainComplex LightCondAb ℤ ⥤ CochainComplex LightCondAb ℤ :=
  (ihom P).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The adjunction of the prolongations of `tensorLeft P ⊣ ihom P`. -/
noncomputable abbrev adjC : LC ⊣ RC :=
  Work.DERFORMAL.Gen.adjMapHomologicalComplex (ihom.adjunction P) (ComplexShape.up ℤ)

/-- Degreewise `(1 - S) ⊗ id`. -/
noncomputable abbrev tauC : LC ⟶ LC := NatTrans.mapHomologicalComplex tauP (ComplexShape.up ℤ)

/-- Degreewise `pre (1 - S)`. -/
noncomputable abbrev muC : RC ⟶ RC := NatTrans.mapHomologicalComplex muP (ComplexShape.up ℤ)

/-- The mate identity for complexes, obtained degreewise from `mate_abelian`. -/
theorem mate_complex (K : CochainComplex LightCondAb ℤ) :
    adjC.unit.app K ≫ RC.map (tauC.app K) = adjC.unit.app K ≫ muC.app (LC.obj K) := by
  apply HomologicalComplex.hom_ext
  intro i
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  exact mate_abelian (K.X i)

/-! ## The lift to the derived category -/

section Derived

variable [PreservesFiniteLimits (tensorLeft P)]

/-- The derived functor of `tensorLeft P`. -/
noncomputable abbrev LD : DLightCondAb ⥤ DLightCondAb := (tensorLeft P).mapDerivedCategory

/-- The derived functor of `ihom P`. -/
noncomputable abbrev RD : DLightCondAb ⥤ DLightCondAb := (ihom P).mapDerivedCategory

/-- The comparison isomorphism `LC ⋙ Q ≅ Q ⋙ LD`. -/
noncomputable abbrev fL : LC ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ LD :=
  ((tensorLeft P).mapDerivedCategoryFactors).symm

/-- The comparison isomorphism `RC ⋙ Q ≅ Q ⋙ RD`. -/
noncomputable abbrev fR : RC ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ RD :=
  ((ihom P).mapDerivedCategoryFactors).symm

instance instCatCommSqL : CatCommSq LC DerivedCategory.Q DerivedCategory.Q LD := ⟨fL⟩

instance instCatCommSqR : CatCommSq RC DerivedCategory.Q DerivedCategory.Q RD := ⟨fR⟩

/-- The class of quasi-isomorphisms of cochain complexes of light condensed abelian groups. -/
noncomputable abbrev W : MorphismProperty (CochainComplex LightCondAb ℤ) :=
  HomologicalComplex.quasiIso LightCondAb (ComplexShape.up ℤ)

/-- The derived adjunction `(tensorLeft P).mapDerivedCategory ⊣ (ihom P).mapDerivedCategory`,
obtained by localizing the exact adjunction `tensorLeft P ⊣ ihom P`. -/
noncomputable abbrev adjD : LD ⊣ RD :=
  adjC.localization DerivedCategory.Q W DerivedCategory.Q W LD RD

/-- The derived version of `(1 - S) ⊗ id`. -/
noncomputable abbrev tauD : LD ⟶ LD := NatTrans.mapDerivedCategory tauP

/-- The derived version of `pre (1 - S)`. -/
noncomputable abbrev muD : RD ⟶ RD := NatTrans.mapDerivedCategory muP

/-- The explicit formula for the unit of the derived adjunction at an object of the form
`Q.obj K`. -/
theorem unit_app_Q (K : CochainComplex LightCondAb ℤ) :
    adjD.unit.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map (adjC.unit.app K) ≫ fR.hom.app (LC.obj K) ≫
        RD.map (fL.hom.app K) := by
  have h1 : CatCommSq.iso RC DerivedCategory.Q DerivedCategory.Q RD = fR := rfl
  have h2 : CatCommSq.iso LC DerivedCategory.Q DerivedCategory.Q LD = fL := rfl
  rw [Adjunction.localization_unit_app, h1, h2]

/-- The explicit formula for `tauD` at an object of the form `Q.obj K`. -/
theorem tauD_app_Q (K : CochainComplex LightCondAb ℤ) :
    tauD.app (DerivedCategory.Q.obj K) =
      fL.inv.app K ≫ DerivedCategory.Q.map (tauC.app K) ≫ fL.hom.app K := by
  rw [NatTrans.mapDerivedCategory_app_Q_obj]
  rfl

/-- The explicit formula for `muD` at an object of the form `Q.obj K`. -/
theorem muD_app_Q (K : CochainComplex LightCondAb ℤ) :
    muD.app (DerivedCategory.Q.obj K) =
      fR.inv.app K ≫ DerivedCategory.Q.map (muC.app K) ≫ fR.hom.app K := by
  rw [NatTrans.mapDerivedCategory_app_Q_obj]
  rfl

/-- **The mate identity at the derived level, tested at `Q.obj K`.** -/
theorem mateK_tauD (K : CochainComplex LightCondAb ℤ) :
    (fR.hom.app (LC.obj K) ≫ RD.map (fL.hom.app K)) ≫ RD.map (tauD.app (DerivedCategory.Q.obj K)) =
      DerivedCategory.Q.map (RC.map (tauC.app K)) ≫
        (fR.hom.app (LC.obj K) ≫ RD.map (fL.hom.app K)) := by
  have key1 : fL.hom.app K ≫ tauD.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map (tauC.app K) ≫ fL.hom.app K := by
    rw [tauD_app_Q K]
    simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  have key4 : fR.hom.app (LC.obj K) ≫ RD.map (DerivedCategory.Q.map (tauC.app K)) =
      DerivedCategory.Q.map (RC.map (tauC.app K)) ≫ fR.hom.app (LC.obj K) :=
    (fR.hom.naturality (tauC.app K)).symm
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp, key1, CategoryTheory.Functor.map_comp]
  rw [← Category.assoc, key4, Category.assoc]

/-- The same computation for `muD`. -/
theorem mateK_muD (K : CochainComplex LightCondAb ℤ) :
    (fR.hom.app (LC.obj K) ≫ RD.map (fL.hom.app K)) ≫
        muD.app (LD.obj (DerivedCategory.Q.obj K)) =
      DerivedCategory.Q.map (muC.app (LC.obj K)) ≫
        (fR.hom.app (LC.obj K) ≫ RD.map (fL.hom.app K)) := by
  have key2 : RD.map (fL.hom.app K) ≫ muD.app (LD.obj (DerivedCategory.Q.obj K)) =
      muD.app (DerivedCategory.Q.obj (LC.obj K)) ≫ RD.map (fL.hom.app K) :=
    muD.naturality (fL.hom.app K)
  have key3 : fR.hom.app (LC.obj K) ≫ fR.inv.app (LC.obj K) =
      𝟙 (DerivedCategory.Q.obj (RC.obj (LC.obj K))) :=
    Iso.hom_inv_id_app fR (LC.obj K)
  rw [Category.assoc, key2, muD_app_Q (LC.obj K)]
  simp only [Category.assoc]
  rw [← Category.assoc, key3]
  exact Category.id_comp _

theorem unit_mate_app_Q (K : CochainComplex LightCondAb ℤ) :
    adjD.unit.app (DerivedCategory.Q.obj K) ≫ RD.map (tauD.app (DerivedCategory.Q.obj K)) =
      adjD.unit.app (DerivedCategory.Q.obj K) ≫
        muD.app (LD.obj (DerivedCategory.Q.obj K)) := by
  have hL : (DerivedCategory.Q.map (adjC.unit.app K) ≫ fR.hom.app (LC.obj K) ≫
        RD.map (fL.hom.app K)) ≫ RD.map (tauD.app (DerivedCategory.Q.obj K)) =
      DerivedCategory.Q.map (adjC.unit.app K ≫ RC.map (tauC.app K)) ≫
        (fR.hom.app (LC.obj K) ≫ RD.map (fL.hom.app K)) := by
    rw [Category.assoc, mateK_tauD K]
    rw [← CategoryTheory.Functor.map_comp_assoc]
  have hR : (DerivedCategory.Q.map (adjC.unit.app K) ≫ fR.hom.app (LC.obj K) ≫
        RD.map (fL.hom.app K)) ≫ muD.app (LD.obj (DerivedCategory.Q.obj K)) =
      DerivedCategory.Q.map (adjC.unit.app K ≫ muC.app (LC.obj K)) ≫
        (fR.hom.app (LC.obj K) ≫ RD.map (fL.hom.app K)) := by
    rw [Category.assoc, mateK_muD K]
    rw [← CategoryTheory.Functor.map_comp_assoc]
  rw [unit_app_Q K, hL, hR, mate_complex K]

/-- **The mate identity at the derived level.**  The unit of the derived adjunction intertwines
`RD.map tauD` with `muD`; equivalently, precomposition with `(1 - S) ⊗ id` corresponds, under the
derived adjunction, to postcomposition with `pre (1 - S)`. -/
theorem unit_mate (c : DLightCondAb) :
    adjD.unit.app c ≫ RD.map (tauD.app c) = adjD.unit.app c ≫ muD.app (LD.obj c) := by
  have h : adjD.unit ≫ Functor.whiskerRight tauD RD = adjD.unit ≫ Functor.whiskerLeft LD muD := by
    apply Localization.natTrans_ext DerivedCategory.Q W
    intro K
    simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] using
      unit_mate_app_Q K
  have h' := congrArg (fun α : 𝟭 DLightCondAb ⟶ LD ⋙ RD => α.app c) h
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] using h'

/-- **The mate identity in `homEquiv` form.**  Under the derived adjunction `LD ⊣ RD`,
precomposition with `tauD` corresponds to postcomposition with `muD`. -/
theorem homEquiv_tauD (A B : DLightCondAb) (ψ : LD.obj A ⟶ B) :
    adjD.homEquiv A B (tauD.app A ≫ ψ) = adjD.homEquiv A B ψ ≫ muD.app B := by
  calc adjD.homEquiv A B (tauD.app A ≫ ψ)
      = adjD.unit.app A ≫ RD.map (tauD.app A) ≫ RD.map ψ := by
        rw [Adjunction.homEquiv_apply, CategoryTheory.Functor.map_comp]
    _ = adjD.unit.app A ≫ muD.app (LD.obj A) ≫ RD.map ψ := by
        rw [← Category.assoc, unit_mate A, Category.assoc]
    _ = adjD.unit.app A ≫ RD.map ψ ≫ muD.app B := by
        rw [← muD.naturality ψ]
    _ = adjD.homEquiv A B ψ ≫ muD.app B := by
        rw [Adjunction.homEquiv_apply, Category.assoc]

end Derived

section Utilities

set_option linter.unusedSimpArgs false in
/-- Precomposition with an isomorphism is bijective. -/
lemma bijective_precomp_iso {C : Type*} [Category C] {A B : C} (e : A ⟶ B) [IsIso e] (Z : C) :
    Function.Bijective (fun φ : B ⟶ Z => e ≫ φ) := by
  refine ⟨fun f g h => ?_, fun φ => ⟨inv e ≫ φ, ?_⟩⟩
  · have h' := congrArg (fun t => inv e ≫ t) h
    simpa only [← Category.assoc, IsIso.inv_hom_id, IsIso.hom_inv_id, Category.id_comp,
      Category.comp_id] using h'
  · change e ≫ (inv e ≫ φ) = φ
    rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]

set_option linter.unusedSimpArgs false in
/-- Postcomposition with an isomorphism is bijective. -/
lemma bijective_postcomp_iso {C : Type*} [Category C] {A B : C} (e : A ⟶ B) [IsIso e] (Z : C) :
    Function.Bijective (fun φ : Z ⟶ A => φ ≫ e) := by
  refine ⟨fun f g h => ?_, fun φ => ⟨φ ≫ inv e, ?_⟩⟩
  · have h' := congrArg (fun t => t ≫ inv e) h
    simpa only [Category.assoc, IsIso.hom_inv_id, IsIso.inv_hom_id, Category.comp_id,
      Category.id_comp] using h'
  · change (φ ≫ inv e) ≫ e = φ
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- Conjugating an endomorphism by an isomorphism does not change the bijectivity of
precomposition with it. -/
lemma bijective_precomp_conj_iff {C : Type*} [Category C] {A B Z : C} (e : A ≅ B) (u : B ⟶ B) :
    Function.Bijective (fun ψ : B ⟶ Z => u ≫ ψ) ↔
      Function.Bijective (fun φ : A ⟶ Z => (e.hom ≫ u ≫ e.inv) ≫ φ) := by
  have hsq : (fun φ : A ⟶ Z => (e.hom ≫ u ≫ e.inv) ≫ φ) =
      (fun ψ : B ⟶ Z => e.hom ≫ ψ) ∘ ((fun ψ : B ⟶ Z => u ≫ ψ) ∘
        (fun φ : A ⟶ Z => e.inv ≫ φ)) := by
    funext φ
    simp only [Function.comp_apply, Category.assoc]
  rw [hsq]
  constructor
  · intro h
    exact (bijective_precomp_iso e.hom Z).comp (h.comp (bijective_precomp_iso e.inv Z))
  · intro h
    have hX : Function.Bijective ((fun ψ : B ⟶ Z => u ≫ ψ) ∘ (fun φ : A ⟶ Z => e.inv ≫ φ)) :=
      (Function.Bijective.of_comp_iff' (bijective_precomp_iso e.hom Z)
        ((fun ψ : B ⟶ Z => u ≫ ψ) ∘ (fun φ : A ⟶ Z => e.inv ≫ φ))).mp h
    exact (Function.Bijective.of_comp_iff (fun ψ : B ⟶ Z => u ≫ ψ)
      (bijective_precomp_iso e.inv Z)).mp hX

end Utilities

end

end Work.ANALYTIC
