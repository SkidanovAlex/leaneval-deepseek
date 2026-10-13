import Mathlib
import Submission.Work.DSMap.Map
import Submission.Work.DSG4a.Criterion
import Submission.Work.DSG4a.CriterionPresent
import Submission.Work.DSG4a.cechZ_baseChange

/-!
# DSG4a — the data produced by the areas `F1` and `COH`, and the bridge to the model

This file is the interface of the assembly of the area `G4a`
(`Submission/Work/DSG4a/Main.lean`, `area_G4a_localGlobal_of_models`).  To run the
local-to-global argument one needs, for the chosen finite affine cover `U` of `X`:

* **`F1Data`** — the output of the frozen area `F1` for the cover `U`: a coaugmentation
  `cc : A[0] ⟶ cechZ A X f U` whose degree-`0` part is the Čech coaugmentation (`coaugClause`),
  and an isomorphism `e : ι(RΓ(X,𝒪)) ≅ Q(cechZ A X f U)` carrying the challenge unit to the
  derived image of `cc` (this is exactly the conclusion of `DSMap.area_F1_cech`);
* **`CohData`** — the output of the frozen area `COH`: finiteness of `Hⁱ(RΓ(X,𝒪))` and vanishing
  above some `N`;
* **`IsFreeModel`** — a bounded complex of finite free `A`-modules, the shape of the model
  produced by `Work.DSG4a.exists_model_of_bounded_homology` from `COH` (transported to `cechZ`
  by `Work.DSG4a.cechHomology_finite_isZero`).

The bridge is `f1UnitCompatible_of_lift` (the compatibility clause of `F1` transfers from the
Čech coaugmentation to a lift of it along a quasi-isomorphism), together with the uniqueness of
the Čech coaugmentation `coaug_eq_of_coaugClause` (a chain map out of `A[0]` is determined by
its degree-`0` component, and that component is pinned down by `coaugClause`).
-/

namespace Work.DSG4a

open CategoryTheory AlgebraicGeometry Limits

set_option backward.isDefEq.respectTransparency false

universe u

/-- `A` concentrated in degree `0`, as a cochain complex — the source of every coaugmentation. -/
noncomputable abbrev singleZ (A : Type u) [CommRing A] : CochainComplex (ModuleCat.{u} A) ℤ :=
  (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj (ModuleCat.of A A)

/-- **The degree-`0` clause of the area `F1`**: the component of the coaugmentation `cc` in
degree `0` is the Čech coaugmentation `coaug0`.  (Since `A[0]` is concentrated in degree `0`,
this clause determines `cc` completely — see `coaug_eq_of_coaugClause`.) -/
def coaugClause {A : Type u} [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    {ι : Type u} (U : ι → X.Opens) (cc : singleZ A ⟶ DSMap.cechZ A X f U) : Prop :=
  cc.f 0 ≫ ((DSMap.cech A X f U).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).hom =
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)).hom ≫
      DSMap.coaug0 A X f U

/-- **The conclusion of the frozen area `F1`** (`DSMap.area_F1_cech`), for the cover `U`. -/
def F1Data (A : Type u) [CommRing A] [HasDerivedCategory (ModuleCat.{u} A)]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) [HasDerivedCategory (SheafOfModules X.ringCatSheaf)]
    [EnoughInjectives (SheafOfModules X.ringCatSheaf)] {ι : Type u} (U : ι → X.Opens) : Prop :=
  ∃ (cc : singleZ A ⟶ DSMap.cechZ A X f U)
    (e : DerivedCategory.Plus.ι.obj (DSMap.RG A X f) ≅
      DerivedCategory.Q.obj (DSMap.cechZ A X f U)),
    coaugClause X f U cc ∧
      DerivedCategory.Plus.ι.map (DSMap.rgUnit A X f) ≫ e.hom =
        Criterion.unitComparison A (DSMap.cechZ A X f U) cc

/-- **The conclusion of the frozen area `COH`** (`DSMap.area_COH`): the cohomology of
`RΓ(X,𝒪_X)` is finite in every degree and vanishes above `N`. -/
def CohData (A : Type u) [CommRing A] [HasDerivedCategory (ModuleCat.{u} A)]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) [HasDerivedCategory (SheafOfModules X.ringCatSheaf)]
    [EnoughInjectives (SheafOfModules X.ringCatSheaf)] : Prop :=
  ∃ N : ℤ, ∀ i : ℤ,
    Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
      (DerivedCategory.Plus.ι.obj (DSMap.RG A X f))) ∧
    (N < i → IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
      (DerivedCategory.Plus.ι.obj (DSMap.RG A X f))))

/-- **A finite free model**: a cochain complex of `A`-modules with finitely generated free
terms which vanishes in all sufficiently large degrees.  Such a complex is K-projective
(`CochainComplex.isKProjective_of_projective`).  Only *one-sided* boundedness is required — a
two-sided bound would force finite projective dimension — and it is what both the model driver
`Work.DSG4a.exists_model_of_bounded_homology` and its base change produce. -/
def IsFreeModel (A : Type u) [CommRing A] (P : CochainComplex (ModuleCat.{u} A) ℤ) : Prop :=
  (∀ j, Module.Finite A (P.X j)) ∧ (∀ j, Module.Free A (P.X j)) ∧
    (∃ b : ℤ, P.IsStrictlyLE b)

/-- A finite free model is K-projective. -/
theorem IsFreeModel.isKProjective {A : Type u} [CommRing A]
    {P : CochainComplex (ModuleCat.{u} A) ℤ} (h : IsFreeModel A P) :
    CochainComplex.IsKProjective P := by
  obtain ⟨hfin, hfree, b, hb⟩ := h
  haveI : P.IsStrictlyLE b := hb
  haveI : ∀ j, Projective (P.X j) := fun j => by
    haveI := hfree j
    infer_instance
  exact CochainComplex.isKProjective_of_projective P b

/-- The Čech complex of a family of opens, in `ℤ`-degrees, is concentrated in degrees `≥ 0`:
this is the instance needed by the model driver `Work.DSG4a.exists_model_of_bounded_homology`
when it is applied to `DSMap.cechZ A X f U`.  (Mathlib has the corresponding instance for
`X.extend embeddingUpNat`, but `DSMap.cechZ` is an irreducible `def`, so instance search does not
find it.) -/
instance cechZ_isStrictlyGE {A : Type u} [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    {ι : Type u} (U : ι → X.Opens) : (DSMap.cechZ A X f U).IsStrictlyGE 0 := by
  show CochainComplex.IsStrictlyGE ((DSMap.cech A X f U).extend ComplexShape.embeddingUpNat) 0
  infer_instance

/-- **The Čech coaugmentation is unique.**  Two chain maps `A[0] ⟶ cechZ A X f U` whose
degree-`0` component is the Čech coaugmentation coincide: in degrees other than `0` the source
is a zero object, and in degree `0` the equality can be cancelled against the isomorphism
`cechZ⁰ ≅ cech⁰`. -/
theorem coaug_eq_of_coaugClause {A : Type u} [CommRing A] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of A)} {ι : Type u} {U : ι → X.Opens} {cc cc' : singleZ A ⟶ DSMap.cechZ A X f U}
    (h : coaugClause X f U cc) (h' : coaugClause X f U cc') : cc = cc' := by
  have h0 : cc.f 0 = cc'.f 0 := by
    have h1 :
        cc.f 0 ≫ ((DSMap.cech A X f U).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).hom =
        cc'.f 0 ≫ ((DSMap.cech A X f U).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).hom := by
      rw [coaugClause] at h h'
      rw [h, h']
    exact (cancel_mono _).mp h1
  refine HomologicalComplex.Hom.ext ?_
  funext i
  by_cases hi : i = 0
  · subst hi; exact h0
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (ModuleCat.of A A) i hi
      ).eq_of_src _ _

/-- **The compatibility clause of `F1` transfers to a lift.**  If `cc₀` is the Čech
coaugmentation of `F1`, `q : P ⟶ cechZ A X f U` is a quasi-isomorphism and `cc` is a lift of
`cc₀` along `q` in the derived category, then the isomorphism
`e = e₀ ≪≫ (asIso (Q.map q)).symm` satisfies the compatibility clause of `F1` with respect to
`cc`; hence the criterion `isSplitMono_rgUnit_iff_chainSplit` applies to `(P, cc)`. -/
theorem f1UnitCompatible_of_lift {A : Type u} [CommRing A] [HasDerivedCategory (ModuleCat.{u} A)]
    {X : Scheme.{u}} {f : X ⟶ Spec (.of A)} [HasDerivedCategory (SheafOfModules X.ringCatSheaf)]
    [EnoughInjectives (SheafOfModules X.ringCatSheaf)] {ι : Type u} {U : ι → X.Opens}
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (q : P ⟶ DSMap.cechZ A X f U) (hq : QuasiIso q)
    (cc₀ : singleZ A ⟶ DSMap.cechZ A X f U)
    (e₀ : DerivedCategory.Plus.ι.obj (DSMap.RG A X f) ≅
      DerivedCategory.Q.obj (DSMap.cechZ A X f U))
    (he₀ : DerivedCategory.Plus.ι.map (DSMap.rgUnit A X f) ≫ e₀.hom =
      Criterion.unitComparison A (DSMap.cechZ A X f U) cc₀)
    (cc : singleZ A ⟶ P)
    (hlift : DerivedCategory.Q.map cc₀ = DerivedCategory.Q.map cc ≫ DerivedCategory.Q.map q) :
    Criterion.F1UnitCompatible P cc (e₀ ≪≫ (asIso (DerivedCategory.Q.map q)).symm) := by
  have : IsIso (DerivedCategory.Q.map q) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u} A) q).mpr hq
  rw [Criterion.F1UnitCompatible]
  have key : Criterion.unitComparison A P cc =
      Criterion.unitComparison A (DSMap.cechZ A X f U) cc₀ ≫
        (asIso (DerivedCategory.Q.map q)).inv := by
    simp only [Criterion.unitComparison]
    rw [hlift]
    simp
  rw [key, Iso.trans_hom, ← Category.assoc, he₀]
  rfl

/-- **The criterion for the challenge unit, from the `F1` data and a model.**  For a
K-projective `P` with a quasi-isomorphism `q : P ⟶ cechZ A X f U` and a lift `cc` of the Čech
coaugmentation, `IsSplitMono (rgUnit A X f)` is equivalent to the unimodularity of the model
element `modelElem P cc`.  This is `isSplitMono_rgUnit_iff_chainSplit` composed with
`chainSplit_iff_isUnimodular`. -/
theorem isSplitMono_iff_isUnimodular_of_lift {A : Type u} [CommRing A]
    [HasDerivedCategory (ModuleCat.{u} A)] {X : Scheme.{u}} {f : X ⟶ Spec (.of A)}
    [HasDerivedCategory (SheafOfModules X.ringCatSheaf)]
    [EnoughInjectives (SheafOfModules X.ringCatSheaf)] {ι : Type u} {U : ι → X.Opens}
    (P : CochainComplex (ModuleCat.{u} A) ℤ) [CochainComplex.IsKProjective P]
    (q : P ⟶ DSMap.cechZ A X f U) (hq : QuasiIso q)
    (cc₀ : singleZ A ⟶ DSMap.cechZ A X f U)
    (e₀ : DerivedCategory.Plus.ι.obj (DSMap.RG A X f) ≅
      DerivedCategory.Q.obj (DSMap.cechZ A X f U))
    (he₀ : DerivedCategory.Plus.ι.map (DSMap.rgUnit A X f) ≫ e₀.hom =
      Criterion.unitComparison A (DSMap.cechZ A X f U) cc₀)
    (cc : singleZ A ⟶ P)
    (hlift : DerivedCategory.Q.map cc₀ = DerivedCategory.Q.map cc ≫ DerivedCategory.Q.map q) :
    IsSplitMono (DSMap.rgUnit A X f) ↔
      Module.IsUnimodular A (Criterion.modelElem P cc) :=
  (isSplitMono_rgUnit_iff_chainSplit X f P cc (e₀ ≪≫ (asIso (DerivedCategory.Q.map q)).symm)
      (f1UnitCompatible_of_lift P q hq cc₀ e₀ he₀ cc hlift)).trans
    (chainSplit_iff_isUnimodular P cc)

end Work.DSG4a
