import Mathlib
import Submission.Work.DSG1.Basic
import Submission.Work.DSG1.flasque_complex_acyclic
import Submission.Work.DSG1.injective_isFlasque
import Submission.Work.DSG1.quasiIso_of_acyclic_mappingCone

/-!
# The unit of `RΓ(X, −)` is an isomorphism on a bounded below complex of flasque sheaves

`Work.DSG1.unitIsoOfFlasqueM`: if `K` is a bounded below complex of sheaves of `𝒪_X`-modules
whose underlying sheaves of abelian groups are flasque, then the unit of the right derived functor
of `Γ(X, −)` (viewed in `A`-modules through `f : X ⟶ Spec A`) is an isomorphism at `K`.  This is
the Cartan–Eilenberg statement that a bounded below complex of flasque sheaves computes its own
hypercohomology.

Strategy (Godement, Hartshorne III.2.5):

* replace `K` by a bounded below complex of injective sheaves `I` via a quasi-isomorphism
  `i : K ⟶ I` (Mathlib's `CochainComplex.Plus.exists_quasiIso_injective`); the terms of `I` are
  injective, hence flasque (`Work.DSG1.injective_isFlasque`);
* the unit of `RΓ(X,−)` is an isomorphism at any bounded below complex of injective objects
  (Mathlib's instance, made available through `isIso_unit_at_injective`), and naturality of the
  unit at `i` shows that the unit at `K` is an isomorphism as soon as `Q(Γ(i))` is an isomorphism;
* `Γ(i)` is a quasi-isomorphism because `Γ` preserves quasi-isomorphisms between bounded below
  complexes of flasque sheaves (`flasqueQuasiIsoM` below, proved through the mapping cone and
  `Work.DSG1.flasque_complex_acyclic`: the cone of `i` is acyclic with flasque terms, so its
  global sections are acyclic).
-/

namespace Work.DSG1

open CategoryTheory AlgebraicGeometry Limits

set_option maxHeartbeats 800000

universe a u v w

set_option linter.style.haveILetI false

/-- If `F : C ⥤ D` is an additive functor between abelian categories, `C` has enough injectives
and `L` is a bounded below complex of injective objects, then the unit of the right derived
functor of `F` is an isomorphism at `L`.  This is Mathlib's instance for bounded below complexes
of injective objects, made applicable through an auxiliary lemma (the instance itself is not
picked up by type class search in the universe/abbreviation configuration of this statement). -/
private lemma isIso_unit_at_injective {C D : Type*} [Category C] [Category D] [Abelian C]
    [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D] (F : C ⥤ D) [F.Additive]
    [EnoughInjectives C] (L : CochainComplex.Plus (InjectiveObject C)) :
    IsIso (F.rightDerivedFunctorPlusUnit.app ((InjectiveObject.ι C).mapCochainComplexPlus.obj L)) :=
  inferInstance

/-- **A biproduct of two flasque sheaves of `𝒪_X`-modules is flasque.**

A section `s` over `V` of `P ≅ M ⊞ N` decomposes as `q₁ (j₁ s) + q₂ (j₂ s)` where `j₁`, `j₂` are
the two projections and `q₁`, `q₂` the two inclusions (`biprod.total`); the `M`-part and the
`N`-part extend to `U` by flasqueness of `M` and `N`, and the sum of the two extensions is the
required extension of `s`. -/
private theorem bpAux {X : Scheme.{u}} {M N P : X.Modules} (e : M ⊞ N ≅ P)
    (hM : TopCat.Presheaf.IsFlasque ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).obj)
    (hN : TopCat.Presheaf.IsFlasque ((SheafOfModules.toSheaf X.ringCatSheaf).obj N).obj) :
    TopCat.Presheaf.IsFlasque ((SheafOfModules.toSheaf X.ringCatSheaf).obj P).obj := by
  let T := Scheme.Modules.toPresheaf X
  haveI hT : T.Additive := ⟨fun {M N f g} => by
    have h : (SheafOfModules.toSheaf X.ringCatSheaf).map (f + g) =
        (SheafOfModules.toSheaf X.ringCatSheaf).map f +
          (SheafOfModules.toSheaf X.ringCatSheaf).map g :=
      Functor.map_add (F := SheafOfModules.toSheaf X.ringCatSheaf) (f := f) (g := g)
    exact congrArg (fun (v : (SheafOfModules.toSheaf X.ringCatSheaf).obj M ⟶
      (SheafOfModules.toSheaf X.ringCatSheaf).obj N) => v.hom) h⟩
  -- the two projections `P ⟶ M`, `P ⟶ N` and the two inclusions `M ⟶ P`, `N ⟶ P`
  let j₁ : P ⟶ M := e.inv ≫ biprod.fst
  let q₁ : M ⟶ P := biprod.inl ≫ e.hom
  let j₂ : P ⟶ N := e.inv ≫ biprod.snd
  let q₂ : N ⟶ P := biprod.inr ≫ e.hom
  have htot : j₁ ≫ q₁ + j₂ ≫ q₂ = 𝟙 P := by
    dsimp only [j₁, q₁, j₂, q₂]
    calc (e.inv ≫ biprod.fst) ≫ (biprod.inl ≫ e.hom) +
          (e.inv ≫ biprod.snd) ≫ (biprod.inr ≫ e.hom)
        = (e.inv ≫ (biprod.fst ≫ biprod.inl)) ≫ e.hom +
          (e.inv ≫ (biprod.snd ≫ biprod.inr)) ≫ e.hom := by
            simp only [Category.assoc]
      _ = (e.inv ≫ (biprod.fst ≫ biprod.inl) +
            e.inv ≫ (biprod.snd ≫ biprod.inr)) ≫ e.hom := by
            rw [Preadditive.add_comp]
      _ = (e.inv ≫ (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr)) ≫ e.hom := by
            rw [Preadditive.comp_add]
      _ = (e.inv ≫ 𝟙 (M ⊞ N)) ≫ e.hom := by rw [biprod.total]
      _ = 𝟙 P := by simp
  -- the same identity on the level of presheaves of abelian groups
  have hkey : T.map j₁ ≫ T.map q₁ + T.map j₂ ≫ T.map q₂ = 𝟙 (T.obj P) := by
    rw [← T.map_comp, ← T.map_comp, ← T.map_add, htot, T.map_id]
  -- a section over `V` splits as the sum of an `M`-part and an `N`-part
  have hsec : ∀ {V : (TopologicalSpace.Opens X)ᵒᵖ} (s : (T.obj P).obj V),
      (T.map q₁).app V ((T.map j₁).app V s) + (T.map q₂).app V ((T.map j₂).app V s) = s := by
    intro V s
    have h : ((T.map j₁ ≫ T.map q₁ + T.map j₂ ≫ T.map q₂).app V) s = s := by
      rw [hkey, NatTrans.id_app, ConcreteCategory.id_apply]
    rw [NatTrans.app_add, NatTrans.comp_app, NatTrans.comp_app,
      AddCommGrpCat.hom_add_apply, ConcreteCategory.comp_apply,
      ConcreteCategory.comp_apply] at h
    exact h
  refine TopCat.Presheaf.IsFlasque.mk (fun {U V} i => ?_)
  rw [AddCommGrpCat.epi_iff_surjective]
  intro s
  obtain ⟨m', hm'⟩ := (AddCommGrpCat.epi_iff_surjective ((T.obj M).map i)).mp (hM.epi i)
    ((T.map j₁).app V s)
  obtain ⟨n', hn'⟩ := (AddCommGrpCat.epi_iff_surjective ((T.obj N).map i)).mp (hN.epi i)
    ((T.map j₂).app V s)
  refine ⟨(T.map q₁).app U m' + (T.map q₂).app U n', ?_⟩
  erw [map_add]
  erw [← NatTrans.naturality_apply (T.map q₁) i m',
    ← NatTrans.naturality_apply (T.map q₂) i n', hm', hn']
  exact hsec (V := V) s

/-
The `Scheme.Modules` reducibility hint: `Scheme.Modules X` is by definition
`SheafOfModules X.ringCatSheaf`, but as a plain `def` type class inference cannot always see
through it, which makes the instances of `X.Modules` syntactically different from those of
`SheafOfModules X.ringCatSheaf`.
-/
set_option allowUnsafeReducibility true
attribute [local reducible] AlgebraicGeometry.Scheme.Modules

/-- The mapping cone of a quasi-isomorphism of cochain complexes in an abelian category is
acyclic.  (Copy of `Work.DSG1.acyclic_cone_of_quasiIso`, kept local so as to depend only on
Mathlib; the version `Work.DSG1.acyclic_mappingCone_of_quasiIso` is specialised to modules over a
ring, whereas here it is applied to complexes of `𝒪_X`-modules.) -/
private theorem acyclic_cone_of_quasiIso_aux {C : Type u} [Category.{v} C] [Abelian C]
    {K L : CochainComplex C ℤ} (f : K ⟶ L) (h : QuasiIso f) :
    (CochainComplex.mappingCone f).Acyclic := by
  have hq : HomotopyCategory.quasiIso C (ComplexShape.up ℤ)
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map f) :=
    (HomotopyCategory.quotient_map_mem_quasiIso_iff f).mpr
      ((HomologicalComplex.mem_quasiIso_iff f).mpr h)
  rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic] at hq
  have hT := HomotopyCategory.mappingCone_triangleh_distinguished f
  have h3 : HomotopyCategory.subcategoryAcyclic C
      (CochainComplex.mappingCone.triangleh f).obj₃ :=
    (CategoryTheory.ObjectProperty.trW_iff_of_distinguished _ _ hT).mp hq
  rw [show (CochainComplex.mappingCone.triangleh f).obj₃ =
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        (CochainComplex.mappingCone f) from rfl] at h3
  exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
    (CochainComplex.mappingCone f)).mp h3

/-- **`Γ(X,−)` preserves quasi-isomorphisms between bounded below complexes of flasque sheaves.**
(Cartan–Eilenberg.)  The mapping cone of `i` is acyclic and has flasque terms — its `n`-th term is
the biproduct `K^{n+1} ⊞ I^n`, flasque by `Work.DSG1P.isFlasqueModBiprod` — so by
`Work.DSG1.flasque_complex_acyclic` its global sections form an acyclic complex.  The mapping cone
commutes with `Γ` (`CochainComplex.mappingCone.mapHomologicalComplexIso`) and a morphism of
cochain complexes with acyclic mapping cone is a quasi-isomorphism. -/
theorem flasqueQuasiIsoM {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A))
    {K I : CochainComplex.Plus X.Modules}
    (i : K ⟶ I) (hi : CochainComplex.Plus.quasiIso X.Modules i)
    (hK : ∀ n : ℤ, TopCat.Presheaf.IsFlasque
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj (K.obj.X n)).obj)
    (hI : ∀ n : ℤ, TopCat.Presheaf.IsFlasque
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj (I.obj.X n)).obj) :
    CochainComplex.Plus.quasiIso (ModuleCat A)
      ((DSMap.GammaA A X f).mapCochainComplexPlus.map i) := by
  rw [CochainComplex.Plus.quasiIso_iff]
  change QuasiIso (((DSMap.GammaA A X f).mapHomologicalComplex (ComplexShape.up ℤ)).map i.hom)
  have hqi : QuasiIso i.hom := (CochainComplex.Plus.quasiIso_iff X.Modules i).mp hi
  have hcone : (CochainComplex.mappingCone i.hom).Acyclic :=
    acyclic_cone_of_quasiIso_aux i.hom hqi
  -- the mapping cone, as a bounded below complex
  obtain ⟨nK, hnK⟩ := K.2
  obtain ⟨nI, hnI⟩ := I.2
  have hbdd : CochainComplex.plus X.Modules (CochainComplex.mappingCone i.hom) := by
    refine ⟨min (nK - 1) nI, ?_⟩
    rw [CochainComplex.isStrictlyGE_iff]
    intro k hk
    have hk2 : k < nI := lt_of_lt_of_le hk (min_le_right _ _)
    have h1 : IsZero (K.obj.X (k + 1)) :=
      (CochainComplex.isStrictlyGE_iff K.obj nK).mp hnK (k + 1) (by omega)
    have h2 : IsZero (I.obj.X k) :=
      (CochainComplex.isStrictlyGE_iff I.obj nI).mp hnI k hk2
    have hb : IsZero (K.obj.X (k + 1) ⊞ I.obj.X k) := by
      rw [biprod_isZero_iff]
      exact ⟨h1, h2⟩
    exact IsZero.of_iso hb (HomologicalComplex.homotopyCofiber.XIsoBiprod i.hom k (k + 1) rfl)
  let Cc : CochainComplex.Plus X.Modules := ⟨CochainComplex.mappingCone i.hom, hbdd⟩
  -- the terms of the cone are biproducts of flasque sheaves, hence flasque
  have hfl : ∀ n : ℤ, IsFlasqueMod (Cc.obj.X n) := by
    intro n
    have hb : IsFlasqueMod (K.obj.X (n + 1) ⊞ I.obj.X n) :=
      bpAux (Iso.refl _) (hK (n + 1)) (hI n)
    exact IsFlasqueMod.of_iso
      (HomologicalComplex.homotopyCofiber.XIsoBiprod i.hom n (n + 1) rfl).symm hb
  have hcr : (((DSMap.GammaA A X f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (CochainComplex.mappingCone i.hom)).Acyclic :=
    flasque_complex_acyclic f Cc hfl hcone
  have hacon : (CochainComplex.mappingCone
      (((DSMap.GammaA A X f).mapHomologicalComplex (ComplexShape.up ℤ)).map i.hom)).Acyclic :=
    fun n => HomologicalComplex.ExactAt.of_iso (hcr n)
      (CochainComplex.mappingCone.mapHomologicalComplexIso i.hom (DSMap.GammaA A X f))
  exact quasiIso_of_acyclic_mappingCone _ hacon

theorem unitIsoOfFlasqueM (A : Type a) [CommRing A] {X : Scheme}
    (f : X ⟶ Spec (.of A))
    [HasDerivedCategory (ModuleCat A)]
    [HasDerivedCategory (SheafOfModules X.ringCatSheaf)]
    [EnoughInjectives (SheafOfModules X.ringCatSheaf)]
    (K : CochainComplex.Plus X.Modules)
    (hK : ∀ n : ℤ, TopCat.Presheaf.IsFlasque
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj (K.obj.X n)).obj) :
    IsIso ((DSMap.GammaA A X f).rightDerivedFunctorPlusUnit.app K) := by
  obtain ⟨n₀, hn₀⟩ := K.property
  haveI : K.obj.IsStrictlyGE n₀ := hn₀
  obtain ⟨L, hL, i, hi⟩ := CochainComplex.Plus.exists_quasiIso_injective K n₀
  -- the terms of the injective resolution `(InjectiveObject.ι X.Modules).mapCochainComplexPlus.obj L`
  -- are injective, hence flasque
  have hI : ∀ n : ℤ, TopCat.Presheaf.IsFlasque
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj (L.obj.X n).obj).obj :=
    fun n => @injective_isFlasque X (L.obj.X n).obj (L.obj.X n).2
  -- `Γ` sends the quasi-isomorphism `i` to a quasi-isomorphism
  have hFi : CochainComplex.Plus.quasiIso (ModuleCat A)
      ((DSMap.GammaA A X f).mapCochainComplexPlus.map i) :=
    flasqueQuasiIsoM f i hi hK hI
  -- the unit is an isomorphism at the complex of injectives
  haveI hIsoI : IsIso ((DSMap.GammaA A X f).rightDerivedFunctorPlusUnit.app
      ((InjectiveObject.ι X.Modules).mapCochainComplexPlus.obj L)) :=
    isIso_unit_at_injective (DSMap.GammaA A X f) L
  -- `DerivedCategory.Plus.Q` inverts the quasi-isomorphism `i`
  haveI hQi : IsIso ((DerivedCategory.Plus.Q (C := SheafOfModules X.ringCatSheaf)).map i) :=
    Localization.inverts (DerivedCategory.Plus.Q (C := SheafOfModules X.ringCatSheaf))
      (CochainComplex.Plus.quasiIso (SheafOfModules X.ringCatSheaf)) i hi
  -- so does `Q` applied to `Γ(i)`
  haveI hα : IsIso
      (((DSMap.GammaA A X f).mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q).map i) :=
    Localization.inverts (DerivedCategory.Plus.Q (C := ModuleCat A))
      (CochainComplex.Plus.quasiIso (ModuleCat A))
      ((DSMap.GammaA A X f).mapCochainComplexPlus.map i) hFi
  haveI hβ : IsIso
      (((DerivedCategory.Plus.Q (C := SheafOfModules X.ringCatSheaf)) ⋙
        (DSMap.GammaA A X f).rightDerivedFunctorPlus).map i) :=
    Functor.map_isIso ((DSMap.GammaA A X f).rightDerivedFunctorPlus)
      ((DerivedCategory.Plus.Q (C := SheafOfModules X.ringCatSheaf)).map i)
  -- naturality of the unit at `i`
  have key : ((DSMap.GammaA A X f).mapCochainComplexPlus ⋙
          (DerivedCategory.Plus.Q (C := ModuleCat A))).map i ≫
        (DSMap.GammaA A X f).rightDerivedFunctorPlusUnit.app
          ((InjectiveObject.ι X.Modules).mapCochainComplexPlus.obj L) =
      (DSMap.GammaA A X f).rightDerivedFunctorPlusUnit.app K ≫
        (((DerivedCategory.Plus.Q (C := SheafOfModules X.ringCatSheaf)) ⋙
          (DSMap.GammaA A X f).rightDerivedFunctorPlus).map i) :=
    ((DSMap.GammaA A X f).rightDerivedFunctorPlusUnit).naturality i
  -- hence the unit at `K` is a composite of isomorphisms
  haveI hcomp : IsIso ((DSMap.GammaA A X f).rightDerivedFunctorPlusUnit.app K ≫
      (((DerivedCategory.Plus.Q (C := SheafOfModules X.ringCatSheaf)) ⋙
        (DSMap.GammaA A X f).rightDerivedFunctorPlus).map i)) := by
    rw [← key]
    infer_instance
  exact IsIso.of_isIso_comp_right
    ((DSMap.GammaA A X f).rightDerivedFunctorPlusUnit.app K)
    (((DerivedCategory.Plus.Q (C := SheafOfModules X.ringCatSheaf)) ⋙
      (DSMap.GammaA A X f).rightDerivedFunctorPlus).map i)

end Work.DSG1
