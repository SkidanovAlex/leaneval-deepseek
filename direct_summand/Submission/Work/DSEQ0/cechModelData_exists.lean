import Mathlib
import Submission.Work.DSF1.Sheaf.restr_trans
import Submission.Work.DSF1.Sheaf.restr_refl
import Submission.Work.DSF1.Cech.CoaugCycle
import Submission.Work.DSF1.Cech.cechAffineCover_quasiIso
import Submission.Work.DSMX0bU.Main
import Submission.Work.DSG1.Setup

/-!
# `Work.DSEQ0.cechModelData_exists` — the Čech model of `RΓ(X, 𝒪_X)` in the challenge API

This file targets the frozen area `F1` (`DSMap.area_F1_cech`), packaged as
`Work.DSMX0bU.CechModelData`.  The strategy is the classical one:

* build the **sheaf-level Čech complex** `cechShZ X U` of the structure sheaf along the cover `U`
  (its `n`-th term is the product of the sheaves `(j_x)_* 𝒪_{U_x}` over the `(n+1)`-tuples of
  indices, so that its global sections are the challenge's complex `DSMap.cechZ A X f U`);
* the **augmentation** `O_X ⟶ cechShZ X U` (the coaugmentation of the cover) is a quasi-isomorphism:
  the augmented Čech complex resolves the structure sheaf;
* each term of `cechShZ X U` is `Γ`-**acyclic** (products of `(j_W)_*𝒪_W` for affine `W`, and
  Serre's affine vanishing);
* the general Cartan–Eilenberg principle "an acyclic resolution computes the right derived
  functor, compatibly with the units" then identifies `RΓ(X, 𝒪_X)` with the Čech complex.

The inputs are the following five statements, delegated to colleagues and proved in sibling
files under `Submission/Work/DSEQ0/`:

* `Work.DSEQ0.secSheaf_rightDerived_isZero_sep` (Serre's affine vanishing): for an *affine* open
  `W` of a scheme `X` separated over `Spec A`, `R^q Γ(X, (W.ι)_*𝒪_W) = 0` for `q > 0`
  (the separatedness is needed: it makes `W.ι` an affine morphism, `V ⊓ W` affine for affine
  `V`; without it a counterexample exists and the first version of the statement was refuted);
* `Work.DSEQ0.unit_isIso_of_acyclic_complex` (Cartan–Eilenberg, complex level): the unit of the
  right derived functor is an isomorphism at a bounded-below complex all of whose terms are
  acyclic — **proved**;
* `Work.DSEQ0.unit_isIso_cechShZ` (the acyclicity input `h1` below): the sheaf-level Čech complex
  is a complex of `Γ`-acyclics — from the previous two inputs, using that finite intersections of
  affine opens of a separated scheme are affine and that finite products of acyclics are acyclic;
* `Work.DSEQ0.quasiIso_augZ` (the resolution input `hqi` below): the augmentation `aug0` of the
  sheaf-level Čech complex is a cycle and the induced chain map `augZ` is a quasi-isomorphism;
* `Work.DSEQ0.cechShZ_compat` (the comparison `q` and the degree-`0` compatibility `hq` below):
  there is a comparison isomorphism `Γ(Č) ≅ cechZ A X f U` whose degree-`0` part takes the image
  of the augmentation to the challenge's Čech coaugmentation `coaug0`; the coaugmentation `cc`
  is then the explicit composite `cechZCompatMap`.

`cechModelData_of_inputs` assembles these into `CechModelData A X f U`; the one remaining
ingredient there is the *unit compatibility* `hcompat`, the standard naturality statement that
the canonical unit of the right derived functor, transported along the composite isomorphism
built from `singlePlusIso`, `augZ`, the derived-functor unit at the Čech complex and the
comparison, is the Čech coaugmentation.  Combined with `Work.DSF1.Cech.exists_cechZ_lift`
(which produces a coaugmentation with the degree-`0` property, and any two such agree because a
chain map out of a single complex is determined by its degree-`0` component), this is exactly
the frozen `F1` statement.
-/

namespace Work.DSEQ0

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Limits Opposite
open scoped Simplicial BigOperators

universe a b c

variable (X : Scheme.{a})

/-- **The Čech presheaf of the structure sheaf** `V ↦ (j_V)_*𝒪_V`: the building block of the
sheaf-level Čech complex of a family of opens.  (This is `Work.DSF1.secSheaf` with the restriction
maps `Work.DSF1.Sheaf.restr`.) -/
noncomputable def cechShPresheaf : (X.Opens)ᵒᵖ ⥤ X.Modules where
  obj W := Work.DSF1.secSheaf W.unop
  map {W W'} f := Work.DSF1.Sheaf.restr (leOfHom f.unop)
  map_id W := by
    rw [show (leOfHom (𝟙 W.unop : W.unop ⟶ W.unop)) = (le_refl W.unop) from Subsingleton.elim _ _,
      Work.DSF1.Sheaf.restr_refl X W.unop]
  map_comp {W W' W''} f g := by
    rw [Work.DSF1.Sheaf.restr_trans X (leOfHom f.unop) (leOfHom g.unop)]

/-- The sheaf-level Čech complex of the family `U`: `n`-th term the product of `(j_x)_*𝒪` over
the `(n+1)`-tuples of indices. -/
noncomputable abbrev cechSh {ι : Type a} (U : ι → X.Opens) : CochainComplex X.Modules ℕ :=
  (cechComplexFunctor U).obj (cechShPresheaf X)

/-- The same complex shifted to `ℤ`-degrees. -/
noncomputable abbrev cechShZ {ι : Type a} (U : ι → X.Opens) : CochainComplex X.Modules ℤ :=
  (cechSh X U).extend ComplexShape.embeddingUpNat

/-- **The augmentation** `𝒪_X ⟶ Č⁰` of the Čech complex, degree `0`. -/
noncomputable def aug0 {ι : Type a} (U : ι → X.Opens) :
    (cechShPresheaf X).obj (op ⊤) ⟶ (cechSh X U).X 0 :=
  Pi.lift (fun x => (cechShPresheaf X).map (homOfLE (le_top :
    Work.DSF1.Cech.Eobj U 0 x ≤ ⊤)).op)

/-- The augmentation, as a chain map `(single 0 𝒪_X) ⟶ Č` in `ℕ`-degrees, from a proof that
`aug0` is a cycle. -/
noncomputable def augN {ι : Type a} (U : ι → X.Opens)
    (h : aug0 X U ≫ (cechSh X U).d 0 1 = 0) :
    (HomologicalComplex.single X.Modules (ComplexShape.up ℕ) 0).obj
        ((cechShPresheaf X).obj (op ⊤)) ⟶ cechSh X U :=
  HomologicalComplex.mkHomFromSingle (c := ComplexShape.up ℕ) (j := 0) (aug0 X U) (fun k hk => by
    have hk1 : k = 1 := by simpa using hk.symm
    subst hk1
    exact h)

/-- The augmentation in `ℤ`-degrees. -/
noncomputable def augZ {ι : Type a} (U : ι → X.Opens)
    (h : aug0 X U ≫ (cechSh X U).d 0 1 = 0) :
    (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj
        ((cechShPresheaf X).obj (op ⊤)) ⟶ cechShZ X U :=
  (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
      ((cechShPresheaf X).obj (op ⊤)) 0 0 rfl).inv ≫
    HomologicalComplex.extendMap (augN X U h) ComplexShape.embeddingUpNat

/-- The augmentation of the sheaf-level Čech complex, with the structure sheaf `𝒪_X` as source:
a variant in which the (canonical) identification `𝒪_X ≅ (j_⊤)_*𝒪_⊤` is supplied as an
argument. -/
noncomputable def augZTop {ι : Type a} (U : ι → X.Opens)
    (ψ : SheafOfModules.unit X.ringCatSheaf ≅ Work.DSF1.secSheaf (⊤ : X.Opens))
    (h : aug0 X U ≫ (cechSh X U).d 0 1 = 0) :
    (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj
        (SheafOfModules.unit X.ringCatSheaf) ⟶ cechShZ X U :=
  (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).map ψ.hom ≫
    augZ X U h

/-- The map `A[0] ⟶ cechZ` obtained from the augmentation of the sheaf-level Čech complex by
applying `Γ(X, -)` and composing with a comparison `qhom` with the challenge's Čech complex. -/
noncomputable def cechZCompatMap (A : Type a) [CommRing A] (f : X ⟶ Spec (.of A))
    {ι : Type a} (U : ι → X.Opens)
    (ψ : SheafOfModules.unit X.ringCatSheaf ≅ Work.DSF1.secSheaf (⊤ : X.Opens))
    (h : aug0 X U ≫ (cechSh X U).d 0 1 = 0)
    (qhom : ((DSMap.GammaA A X f).mapHomologicalComplex (ComplexShape.up ℤ)).obj (cechShZ X U) ⟶
      DSMap.cechZ A X f U) :
    (HomologicalComplex.single (ModuleCat.{a} A) (ComplexShape.up ℤ) 0).obj (ModuleCat.of A A) ⟶
      DSMap.cechZ A X f U :=
  letI : Algebra A Γ(X, ⊤) := (DSMap.phi A X f).toAlgebra
  (HomologicalComplex.single (ModuleCat.{a} A) (ComplexShape.up ℤ) 0).map
      (ModuleCat.ofHom (Algebra.linearMap A Γ(X, ⊤))) ≫
    (HomologicalComplex.singleMapHomologicalComplex (DSMap.GammaA A X f) (ComplexShape.up ℤ) 0).inv.app
      (SheafOfModules.unit X.ringCatSheaf) ≫
    ((DSMap.GammaA A X f).mapHomologicalComplex (ComplexShape.up ℤ)).map (augZTop X U ψ h) ≫ qhom

/-- **The assembly step of the F1 node.**  Given

* `hqi` : the augmentation `augZ X U h` of the sheaf-level Čech complex is a quasi-isomorphism,
* `h1` : the sheaf-level Čech complex is a complex of `Γ`-acyclic sheaves (the unit of the right
  derived functor of `Γ` is an isomorphism at it),
* `ψ`, `q`, `hq` : the comparison with the challenge's Čech complex `cechZ A X f U`, compatible
  with the coaugmentations (the degree-`0` statement `hq`),

the packaged F1 data `CechModelData A X f U` follows: the coaugmentation is the map
`cechZCompatMap` and the isomorphism `ι(RΓ(X,𝒪_X)) ≅ Q(cechZ)` is the composite of
`singlePlusIso`, the quasi-isomorphism `augZ`, the unit at the Čech complex and the comparison.

The only remaining input is the unit compatibility `hcompat`; it is the statement that the
canonical unit of the right derived functor, transported along this composite, is the
coaugmentation of the Čech complex. -/
theorem cechModelData_of_inputs (A : Type a) [CommRing A] (f : X ⟶ Spec (.of A))
    [hb : HasDerivedCategory.{b} (ModuleCat.{a} A)]
    [hc : HasDerivedCategory.{c} (SheafOfModules X.ringCatSheaf)]
    [hEn : CategoryTheory.EnoughInjectives (SheafOfModules X.ringCatSheaf)]
    {ι : Type a} [Finite ι] (U : ι → X.Opens)
    (h : aug0 X U ≫ (cechSh X U).d 0 1 = 0)
    (hqi : HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ) (augZ X U h))
    (ψ : SheafOfModules.unit X.ringCatSheaf ≅ Work.DSF1.secSheaf (⊤ : X.Opens))
    (q : ((DSMap.GammaA A X f).mapHomologicalComplex (ComplexShape.up ℤ)).obj (cechShZ X U) ≅
      DSMap.cechZ A X f U)
    (hq : CategoryTheory.CategoryStruct.comp
          ((cechZCompatMap (X := X) (A := A) (f := f) (U := U) (ψ := ψ) (h := h) (qhom := q.hom)).f 0)
          ((HomologicalComplex.extendXIso (DSMap.cech A X f U) ComplexShape.embeddingUpNat
            (i := 0) rfl).hom) =
        CategoryTheory.CategoryStruct.comp
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)).hom
          (DSMap.coaug0 A X f U))
    (h1 : ∀ (hh : (cechShZ X U).IsStrictlyGE 0),
      IsIso ((DSMap.GammaA A X f).rightDerivedFunctorPlusUnit.app
        (⟨cechShZ X U, ⟨0, hh⟩⟩ : CochainComplex.Plus X.Modules))) :
    Work.DSMX0bU.CechModelData A X f U := by
  classical
  letI : HasDerivedCategory X.Modules := hc
  letI : CategoryTheory.EnoughInjectives X.Modules := hEn
  let L : CochainComplex.Plus X.Modules := ⟨cechShZ X U, ⟨0, inferInstance⟩⟩
  let M : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let N : X.Modules := (cechShPresheaf X).obj (op ⊤)
  let sM : CochainComplex.Plus X.Modules := Work.DSG1.singlePlusObj X.Modules M
  let sN : CochainComplex.Plus X.Modules := Work.DSG1.singlePlusObj X.Modules N
  let ψP : sM ≅ sN :=
    ObjectProperty.isoMk (CochainComplex.plus X.Modules)
      ((CochainComplex.singleFunctor X.Modules 0).mapIso ψ)
  let augP : sN ⟶ L := ObjectProperty.homMk (augZ X U h)
  haveI haugP : IsIso ((DerivedCategory.Plus.Q).map augP) := by
    have hq' : CochainComplex.Plus.quasiIso X.Modules augP := by
      rw [CochainComplex.Plus.quasiIso_iff]
      change QuasiIso (augZ X U h)
      exact hqi
    exact Localization.inverts _ _ _ hq'
  haveI h1L : IsIso ((DSMap.GammaA A X f).rightDerivedFunctorPlusUnit.app L) :=
    h1 inferInstance
  have ePlus : DSMap.RG A X f ≅
      (DerivedCategory.Plus.Q).obj ((DSMap.GammaA A X f).mapCochainComplexPlus.obj L) :=
    (DSMap.GammaA A X f).rightDerivedFunctorPlus.mapIso
        (Work.DSG1.singlePlusIso X.Modules M) ≪≫
      (DSMap.GammaA A X f).rightDerivedFunctorPlus.mapIso
        ((DerivedCategory.Plus.Q).mapIso ψP) ≪≫
      (DSMap.GammaA A X f).rightDerivedFunctorPlus.mapIso
        (asIso ((DerivedCategory.Plus.Q).map augP)) ≪≫
      (asIso ((DSMap.GammaA A X f).rightDerivedFunctorPlusUnit.app L)).symm
  refine ⟨cechZCompatMap (X := X) (A := A) (f := f) (U := U) (ψ := ψ) (h := h) (qhom := q.hom), ?_, hq, ?_⟩
  · refine (DerivedCategory.Plus.ι.mapIso ePlus) ≪≫
      (DerivedCategory.Plus.QCompιIso (ModuleCat.{a} A)).app
        ((DSMap.GammaA A X f).mapCochainComplexPlus.obj L) ≪≫
      (DerivedCategory.Q).mapIso
        ((Functor.mapCochainComplexPlusCompι (DSMap.GammaA A X f)).app L) ≪≫
      (DerivedCategory.Q).mapIso q
  · sorry

theorem cechModelData_exists (A : Type a) [CommRing A] (X : AlgebraicGeometry.Scheme.{a})
    (f : X ⟶ AlgebraicGeometry.Spec (.of A)) [AlgebraicGeometry.IsProper f] {ι : Type a}
    [Finite ι] (U : ι → X.Opens) (hU : ∀ i, AlgebraicGeometry.IsAffineOpen (U i))
    (hcov : ⨆ i, U i = ⊤) :
    ∀ (_ : HasDerivedCategory.{b} (ModuleCat.{a} A))
      (_ : HasDerivedCategory.{c} (SheafOfModules X.ringCatSheaf))
      (_ : CategoryTheory.EnoughInjectives (SheafOfModules X.ringCatSheaf)),
      Work.DSMX0bU.CechModelData A X f U := by sorry

end Work.DSEQ0
