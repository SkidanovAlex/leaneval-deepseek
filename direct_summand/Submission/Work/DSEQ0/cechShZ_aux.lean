import Mathlib
import Submission.Work.DSEQ0.cechModelData_exists
import Submission.Work.DSF1.Sheaf.gammaCechPresheaf
import Submission.Work.DSF1.Sheaf.gammaCechComplexFunctor
import Submission.Work.DSF1.Sheaf.mapHomologicalComplex_extendUpNat

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite Limits

namespace Work.DSEQ0

universe u

open scoped Simplicial BigOperators

variable (A : Type u) [CommRing A] (X : AlgebraicGeometry.Scheme.{u})
  (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A))

/-- The named version of the comparison of presheaves `Č ⋙ Γ ≅ cechPresheaf`. -/
noncomputable def gammaPresheaf :
    (cechShPresheaf X) ⋙ (DSMap.GammaA A X f) ≅ (DSMap.cechPresheaf A X f) :=
  NatIso.ofComponents (fun V => Work.DSF1.Sheaf.psi A X f V.unop) (fun {V W} g => by
    have hg : g = (homOfLE (CategoryTheory.leOfHom g.unop)).op := Subsingleton.elim _ _
    rw [hg]
    have h := Work.DSF1.Sheaf.psi_naturality A X f
      (CategoryTheory.leOfHom (homOfLE (CategoryTheory.leOfHom g.unop)))
    rw [show (homOfLE (CategoryTheory.leOfHom (homOfLE (CategoryTheory.leOfHom g.unop)))) =
        (homOfLE (CategoryTheory.leOfHom g.unop)) from Subsingleton.elim _ _] at h
    exact h)

/-- The named version of `gammaCechComplexFunctor`: the comparison of the `Γ`-image of the
sheaf-level Čech complex with the Čech complex of the section presheaf, in `ℕ`-degrees. -/
noncomputable def gammaComplex {ι : Type u} (U : ι → X.Opens) :
    ((DSMap.GammaA A X f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((cechComplexFunctor U).obj (cechShPresheaf X)) ≅
      (cechComplexFunctor U).obj ((cechShPresheaf X) ⋙ (DSMap.GammaA A X f)) := by
  haveI hAdd : (DSMap.GammaA A X f).Additive := inferInstance
  have hF : ∀ {I : Type u} (g : I → X.Modules), PreservesLimit (Discrete.functor g)
      (DSMap.GammaA A X f) := by
    intro I g
    haveI h : PreservesLimitsOfShape (Discrete I) (DSMap.GammaA A X f) := by
      unfold DSMap.GammaA
      have h1 : PreservesLimitsOfShape (Discrete I)
          (SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤) :
            SheafOfModules.{u} X.ringCatSheaf ⥤ _) := inferInstance
      have h2 : PreservesLimitsOfShape (Discrete I)
          (ModuleCat.restrictScalars (DSMap.phi A X f) : ModuleCat.{u} _ ⥤ ModuleCat.{u} A) :=
        inferInstance
      exact @comp_preservesLimitsOfShape _ _ _ _ _ _ _ _ _ _ h1 h2
    exact h.preservesLimit
  let E : SimplicialObject (FormalCoproduct X.Opens) := FormalCoproduct.cech {I := ι, obj := U}
  let WS := (Functor.whiskeringLeft SimplexCategory ((FormalCoproduct X.Opens)ᵒᵖ) X.Modules).obj
    E.rightOp
  let WD := (Functor.whiskeringLeft SimplexCategory ((FormalCoproduct X.Opens)ᵒᵖ)
    (ModuleCat A)).obj E.rightOp
  exact (Work.DSF1.Sheaf.alternatingCofaceMapComplexMapHomologicalComplexIso (DSMap.GammaA A X f)
      (WS.obj ((FormalCoproduct.evalOp X.Opens X.Modules).obj (cechShPresheaf X)))) ≪≫
    (AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat A)).mapIso
      (WD.mapIso (Work.DSF1.Sheaf.evalOpObjIso (DSMap.GammaA A X f) (cechShPresheaf X) hF))

/-- The named version of `mapHomologicalComplex_extendUpNat`: applying an additive functor and then
extending to `ℤ`-degrees is the same as extending and then applying the functor. -/
noncomputable def extendUpNatIso {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] [Limits.HasZeroObject C] [Limits.HasZeroObject D]
    (F : C ⥤ D) [F.Additive] (K : CochainComplex C ℕ) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (K.extend ComplexShape.embeddingUpNat)) ≅
      (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).extend ComplexShape.embeddingUpNat) := by
  let e := ComplexShape.embeddingUpNat
  let M : CochainComplex D ℕ := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K
  let Φ : (o : Option ℕ) →
      F.obj (HomologicalComplex.extend.X K o) ≅ HomologicalComplex.extend.X M o :=
    fun o => match o with
      | some n => Iso.refl _
      | none => IsZero.iso (F.map_isZero (isZero_zero C)) (isZero_zero D)
  have hA : ∀ (o o' : Option ℕ),
      (Φ o).hom ≫ HomologicalComplex.extend.d M o o' =
      F.map (HomologicalComplex.extend.d K o o') ≫ (Φ o').hom := by
    intro o o'
    rcases o with _ | n
    · rcases o' with _ | m
      · rw [HomologicalComplex.extend.d_none_eq_zero K none none rfl,
            HomologicalComplex.extend.d_none_eq_zero M none none rfl, F.map_zero]
        simp
      · rw [HomologicalComplex.extend.d_none_eq_zero K none (some m) rfl,
            HomologicalComplex.extend.d_none_eq_zero M none (some m) rfl, F.map_zero]
        simp
    · rcases o' with _ | m
      · rw [HomologicalComplex.extend.d_none_eq_zero' K (some n) none rfl,
            HomologicalComplex.extend.d_none_eq_zero' M (some n) none rfl, F.map_zero]
        simp
      · rw [show HomologicalComplex.extend.d M (some n) (some m) = M.d n m from rfl,
            show HomologicalComplex.extend.d K (some n) (some m) = K.d n m from rfl]
        show 𝟙 (F.obj (K.X n)) ≫ F.map (K.d n m) = F.map (K.d n m) ≫ 𝟙 (F.obj (K.X m))
        rw [Category.id_comp, Category.comp_id]
  exact HomologicalComplex.Hom.isoOfComponents (fun i' => Φ (e.r i'))
    (fun i' j' _ => hA _ _)

/-- The `ℕ`-degree comparison `Γ(Č) ≅ cech`. -/
noncomputable def gammaComplexFull {ι : Type u} (U : ι → X.Opens) :
    ((DSMap.GammaA A X f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((cechComplexFunctor U).obj (cechShPresheaf X)) ≅ DSMap.cech A X f U :=
  gammaComplex A X f U ≪≫ (cechComplexFunctor U).mapIso (gammaPresheaf A X f)

/-- The canonical comparison `Γ(cechShZ) ≅ cechZ`.

## Intended component computation

The degree-`0` component of `qCanon.hom` (composed with the degree-`0` part
`HomologicalComplex.extendXIso (DSMap.cech A X f U) ComplexShape.embeddingUpNat (i := 0) rfl`
of the extension) is the product over `x : (Work.DSF1.Cech.E U).obj (op ⦋0⦌) |> .I` of the
comparison isomorphisms `Work.DSF1.Sheaf.psi A X f (Work.DSF1.Cech.Eobj U 0 x)`, transported
through the `PreservesProduct.iso` of `DSMap.GammaA A X f` over the degree-`0` product
`⨅ i, U (x i)` (see `Work.DSF1.Sheaf.gammaComplex`, whose last factor
`(cechComplexFunctor U).mapIso (gammaPresheaf A X f)` is handled by
`Work.DSF1.Cech.cechComplexFunctor_map_pi`, and whose middle factor
`(AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat A)).mapIso (...)` has
`AlternatingCofaceMapComplex.map` given by `CochainComplex.ofHom (fun n => f.app ⦋n⦌)`, i.e. its
degree-`0` component is component `⦋0⦌` of `Work.DSF1.Sheaf.evalOpObjIso`, i.e. a
`PreservesProduct.iso`).

`Work.DSEQ0.augR X U h` is definitionally `aug0 X U ≫ (cechSh X U).extendXIso ... .inv` (the
`singleObjXSelf` factors are the identity), and `aug0 X U` is the `Pi.lift` of the restrictions
`Work.DSF1.Sheaf.restr (le_top : Eobj U 0 x ≤ ⊤)`. `DSMap.GammaA` preserves these products, so
`(DSMap.GammaA A X f).map (augR X U h)` is, componentwise, `(GammaA).map (restr le_top)`, and
`Work.DSF1.Sheaf.psi_naturality` gives
`(GammaA).map (restr le_top) ≫ (psi (Eobj U 0 x)).hom = (psi ⊤).hom ≫ cechPresheaf.map (homOfLE le_top).op`.
The right-hand side `(psi ⊤).hom ≫ coaugCech A X f U` is componentwise
`(psi ⊤).hom ≫ cechPresheaf.map (homOfLE le_top).op` (by `Limits.Pi.lift_comp_π`), so the
identity follows componentwise. -/
noncomputable def qCanon {ι : Type u} (U : ι → X.Opens) :
    (((DSMap.GammaA A X f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (cechShZ X U)) ≅ DSMap.cechZ A X f U :=
  extendUpNatIso (DSMap.GammaA A X f) (cechSh X U) ≪≫
    (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat A)).mapIso (gammaComplexFull A X f U)

/-- The degree-`0` map `secSheaf ⊤ ⟶ (cechShZ).X 0` obtained from the augmentation. -/
noncomputable def augR {ι : Type u} (U : ι → X.Opens)
    (h : aug0 X U ≫ (cechSh X U).d 0 1 = 0) :
    Work.DSF1.secSheaf (⊤ : X.Opens) ⟶ (cechShZ X U).X 0 :=
  (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    (Work.DSF1.secSheaf (⊤ : X.Opens))).inv ≫ (augZ X U h).f 0

/-- The map `A ⟶ Γ(X, ⊤)` used in `cechZCompatMap`. -/
noncomputable def linA :
    ModuleCat.of A A ⟶ (DSMap.GammaA A X f).obj (SheafOfModules.unit X.ringCatSheaf) :=
  letI : Algebra A Γ(X, ⊤) := (DSMap.phi A X f).toAlgebra
  show ModuleCat.of A A ⟶ ModuleCat.of A Γ(X, ⊤) from
    ModuleCat.ofHom (Algebra.linearMap A Γ(X, ⊤))

/-- The canonical morphism `𝒪_X ⟶ secSheaf ⊤`. -/
noncomputable def psiUnitHom :
    SheafOfModules.unit X.ringCatSheaf ⟶ Work.DSF1.secSheaf (⊤ : X.Opens) :=
  (Scheme.Modules.restrictAdjunction (⊤ : X.Opens).ι).unit.app
      (SheafOfModules.unit X.ringCatSheaf) ≫
    (Scheme.Modules.pushforward (⊤ : X.Opens).ι).map
      (Scheme.Modules.restrictUnitIso (⊤ : X.Opens).ι).hom

/-- The degree-`0` Čech coaugmentation `Γ(X, ⊤) ⟶ Č⁰`. -/
noncomputable def coaugCech {ι : Type u} (U : ι → X.Opens) :
    (DSMap.cechPresheaf A X f).obj (Opposite.op (⊤ : X.Opens)) ⟶ (DSMap.cech A X f U).X 0 :=
  Work.DSF1.Cech.coaug U (DSMap.cechPresheaf A X f)

end Work.DSEQ0
