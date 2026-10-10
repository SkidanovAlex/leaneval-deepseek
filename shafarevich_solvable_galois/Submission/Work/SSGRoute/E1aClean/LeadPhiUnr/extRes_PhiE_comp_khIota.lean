import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Submission.Work.SSGRoute.E1aClean.archimedeanComparisonSES
import Submission.Work.SSGRoute.E1aClean.finPlaceSquare
import Submission.Work.SSGRoute.ExtChain.exists_khLift_of_extToIdeles_eq_zero
import Submission.Work.SSGRoute.PT.E1aFinBox.freeCoverCompat_comp_hom
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The comparison square crux `extRes_PhiE_comp_khIota`

Both sides of the equation are `PhiE`-images of degree-`0` classes: the left one is the `Ext`-class
obtained by restricting the level-`1` `PhiE`-class along `D_q ≤ Gal(K/k)` and pushing the
coefficients along the `D_q`-equivariant inclusion `Kˣ ↪ (K^h)ˣ`; the right one is the
level-`2` `PhiE`-class transported along `e : D_q ≃* Gal(K^h/k^h)`.  The proof splits into

* `PhiSqAux` — generic `Ext⁰`/cast bookkeeping, the two generic reductions `crux_of_degZero`
  and `degZero_of_pointwise`, and the specific pointwise identity `crux_pointwise`; and
* the theorem itself, which applies `PT.PhiEgen_res_compat` twice (`D.subtype`, then `e.symm`) and
  then the three reductions.

The pointwise identity is the arithmetic heart: the `Ωˣ`-images of the two sides are both
`ñ ∘ freeCoverCompat(levelTwoGroupHom) ∘ κ_{R₂}`, by `hy`, `hy₂`, the kernel-inclusion lemma
twice, `freeCoverCompat_comp_hom`, the definitional `levelTwoLift`, `khIota_apply` and injectivity
of `algebraMap K^h → Ω`.
-/

namespace Work.SSGRoute.E1aClean.LeadPhiUnr.PhiSqAux

open CategoryTheory SSGRoute.PTExt

attribute [local instance 10000] Work.SSGRoute.homCoind.instDistribMulActionAlgEquiv

noncomputable section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## G0. Generic bookkeeping -/

theorem ext_addEquiv₀_mk₀ {C : Type*} [Category C] [Abelian C] [HasExt C]
    {X Y : C} (f : X ⟶ Y) :
    CategoryTheory.Abelian.Ext.addEquiv₀ (CategoryTheory.Abelian.Ext.mk₀ f) = f := by
  have h1 : CategoryTheory.Abelian.Ext.mk₀ f
      = CategoryTheory.Abelian.Ext.addEquiv₀.symm f := by
    conv_lhs => rw [← AddEquiv.apply_symm_apply CategoryTheory.Abelian.Ext.addEquiv₀ f]
    exact CategoryTheory.Abelian.Ext.mk₀_addEquiv₀_apply _
  rw [h1, AddEquiv.apply_symm_apply]

theorem ext_addEquiv₀_mk₀_comp {C : Type*} [Category C] [Abelian C] [HasExt C]
    {A B D : C} (g : A ⟶ B) (z : CategoryTheory.Abelian.Ext B D 0) :
    CategoryTheory.Abelian.Ext.addEquiv₀
        ((CategoryTheory.Abelian.Ext.mk₀ g).comp z (zero_add 0))
      = g ≫ CategoryTheory.Abelian.Ext.addEquiv₀ z := by
  conv_lhs => rw [← CategoryTheory.Abelian.Ext.mk₀_addEquiv₀_apply z]
  rw [CategoryTheory.Abelian.Ext.mk₀_comp_mk₀, ext_addEquiv₀_mk₀]

theorem ext_addEquiv₀_comp_mk₀ {C : Type*} [Category C] [Abelian C] [HasExt C]
    {A B D : C} (z : CategoryTheory.Abelian.Ext A B 0) (u : B ⟶ D) :
    CategoryTheory.Abelian.Ext.addEquiv₀
        (z.comp (CategoryTheory.Abelian.Ext.mk₀ u) (zero_add 0))
      = CategoryTheory.Abelian.Ext.addEquiv₀ z ≫ u := by
  conv_lhs => rw [← CategoryTheory.Abelian.Ext.mk₀_addEquiv₀_apply z]
  rw [CategoryTheory.Abelian.Ext.mk₀_comp_mk₀, ext_addEquiv₀_mk₀]

theorem ext_addEquiv₀_mapExtAddHom {C D : Type*} [Category C] [Abelian C] [HasExt C]
    [Category D] [Abelian D] [HasExt D] (F : C ⥤ D) [F.Additive]
    [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
    {X Y : C} (z : CategoryTheory.Abelian.Ext X Y 0) :
    CategoryTheory.Abelian.Ext.addEquiv₀ ((F.mapExtAddHom X Y 0) z)
      = F.map (CategoryTheory.Abelian.Ext.addEquiv₀ z) := by
  conv_lhs => rw [← CategoryTheory.Abelian.Ext.mk₀_addEquiv₀_apply z]
  rw [CategoryTheory.Functor.mapExtAddHom_apply,
    CategoryTheory.Abelian.Ext.mapExactFunctor_mk₀]
  exact ext_addEquiv₀_mk₀ _

theorem PhiEgen_ndrec {G : Type} [Group G] [Fintype G] {X Y Y' : Rep.{0} SSGRoute.PTExt.Coeff G}
    (h : Y = Y')
    (w : CategoryTheory.Abelian.Ext
      (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover X)) Y 0) :
    Work.SSGRoute.PT.PhiEgen X Y' (h ▸ w) = h ▸ (Work.SSGRoute.PT.PhiEgen X Y w) := by
  cases h
  rfl

theorem ext_addEquiv₀_ndrec {G : Type} [Group G] {A B X : Rep.{0} SSGRoute.PTExt.Coeff G}
    (h : A = B) (y : CategoryTheory.Abelian.Ext X A 0) :
    CategoryTheory.Abelian.Ext.addEquiv₀ (h ▸ y)
      = h ▸ (CategoryTheory.Abelian.Ext.addEquiv₀ y) := by
  cases h
  rfl

theorem rep_ndrec_hom_apply {k : Type} [Semiring k] {G : Type} [Monoid G] {A B Y : Rep k G}
    (h : A = B) (χ : A ⟶ Y) (x : B.V) :
    (h ▸ χ).hom x = χ.hom (cast (congrArg Rep.V h.symm) x) := by
  cases h
  rfl

theorem cast_congrArg_RepV_res {k : Type} [Semiring k] {G G' : Type} [Monoid G] [Monoid G']
    (e : G ≃* G') (M : Rep k G')
    (h : Rep.res e.symm.toMonoidHom (Rep.res e.toMonoidHom M) = M)
    (x : (Rep.res e.symm.toMonoidHom (Rep.res e.toMonoidHom M)).V) :
    (cast (congrArg Rep.V h) x : M.V) = x := by
  have hh : congrArg Rep.V h = rfl := Subsingleton.elim _ _
  rw [hh]
  rfl

theorem rep_ndrec_hom_apply_tgt {k : Type} [Semiring k] {G : Type} [Monoid G] {A Y Y' : Rep k G}
    (h : Y = Y') (χ : A ⟶ Y) (x : A.V) :
    (h ▸ χ).hom x = cast (congrArg Rep.V h) (χ.hom x) := by
  cases h
  rfl

theorem cast_congrArg_RepV_res' {k : Type} [Semiring k] {G G' : Type} [Monoid G] [Monoid G']
    (e : G ≃* G') (M : Rep k G')
    (h : M = Rep.res e.symm.toMonoidHom (Rep.res e.toMonoidHom M)) (x : M.V) :
    (cast (congrArg Rep.V h) x : (Rep.res e.symm.toMonoidHom (Rep.res e.toMonoidHom M)).V) = x := by
  have hh : congrArg Rep.V h = rfl := Subsingleton.elim _ _
  rw [hh]
  rfl

theorem freeCoverCompat_comp_apply {G H L : Type} [Group G] [Group H] [Group L]
    (φ : H →* G) (ψ : L →* H) (X : Rep.{0} SSGRoute.PTExt.Coeff G)
    (u : (Rep.free SSGRoute.PTExt.Coeff L X.V).V) :
    (Rep.Hom.hom (Work.SSGRoute.PT.freeCoverCompat (φ.comp ψ) X)) u
      = (Rep.Hom.hom (Work.SSGRoute.PT.freeCoverCompat φ X))
          ((Rep.Hom.hom (Work.SSGRoute.PT.freeCoverCompat ψ (Rep.res φ X))) u) := by
  rw [Work.SSGRoute.PT.E1aFinBox.freeCoverCompat_comp_hom]
  rw [Rep.comp_apply]
  rfl

/-- The coefficient cast of a degree-0 class, with the motive fixed (a bare `h ▸ y₂` in a
statement elaborates with a wrong motive, measured). -/
abbrev castCoeff0 {G : Type} [Group G] {X M M' : Rep.{0} SSGRoute.PTExt.Coeff G} (h : M = M')
    (y : CategoryTheory.Abelian.Ext X M 0) : CategoryTheory.Abelian.Ext X M' 0 := h ▸ y

/-! ## R1. GENERIC reduction: crux ⇐ equality of degree-0 classes -/

theorem crux_of_degZero {G D L : Type} [Group G] [Group D] [Group L]
    [Fintype G] [Fintype D] [Fintype L]
    (φ : D →* G) (e : D ≃* L)
    (X U₁ : Rep.{0} SSGRoute.PTExt.Coeff G) (U₂ : Rep.{0} SSGRoute.PTExt.Coeff L)
    (ι : Rep.res φ U₁ ⟶ Rep.res e.toMonoidHom U₂)
    (y : CategoryTheory.Abelian.Ext
      (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover X)) U₁ 0)
    (y₂ : CategoryTheory.Abelian.Ext
      (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover
        (Rep.res e.symm.toMonoidHom (Rep.res φ X)))) U₂ 0)
    (Φ₁ : CategoryTheory.ShortComplex.Hom (Work.SSGRoute.freeCoverSES (Rep.res φ X))
      ((Work.SSGRoute.freeCoverSES X).map (Rep.resFunctor (k := SSGRoute.PTExt.Coeff) φ)))
    (hΦ₁ : ∀ w : CategoryTheory.Abelian.Ext
        (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover X)) U₁ 0,
      (Rep.resFunctor (k := SSGRoute.PTExt.Coeff) φ).mapExtAddHom X U₁ 1
          (Work.SSGRoute.PT.PhiEgen X U₁ w) =
        Work.SSGRoute.PT.PhiEgen (Rep.res φ X)
          ((Rep.resFunctor (k := SSGRoute.PTExt.Coeff) φ).obj U₁)
          ((CategoryTheory.Abelian.Ext.mk₀ Φ₁.τ₁).comp
            ((Rep.resFunctor (k := SSGRoute.PTExt.Coeff) φ).mapExtAddHom
              (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover X)) U₁ 0 w) (zero_add 0)))
    (Φ₂ : CategoryTheory.ShortComplex.Hom
      (Work.SSGRoute.freeCoverSES (Rep.res e.symm.toMonoidHom (Rep.res φ X)))
      ((Work.SSGRoute.freeCoverSES (Rep.res φ X)).map
        (Rep.resFunctor (k := SSGRoute.PTExt.Coeff) e.symm.toMonoidHom)))
    (hΦ₂ : ∀ w : CategoryTheory.Abelian.Ext
        (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover (Rep.res φ X)))
        (Rep.res e.toMonoidHom U₂) 0,
      (Rep.resFunctor (k := SSGRoute.PTExt.Coeff) e.symm.toMonoidHom).mapExtAddHom
          (Rep.res φ X) (Rep.res e.toMonoidHom U₂) 1
          (Work.SSGRoute.PT.PhiEgen (Rep.res φ X) (Rep.res e.toMonoidHom U₂) w) =
        Work.SSGRoute.PT.PhiEgen (Rep.res e.symm.toMonoidHom (Rep.res φ X))
          ((Rep.resFunctor (k := SSGRoute.PTExt.Coeff) e.symm.toMonoidHom).obj
            (Rep.res e.toMonoidHom U₂))
          ((CategoryTheory.Abelian.Ext.mk₀ Φ₂.τ₁).comp
            ((Rep.resFunctor (k := SSGRoute.PTExt.Coeff) e.symm.toMonoidHom).mapExtAddHom
              (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover (Rep.res φ X)))
              (Rep.res e.toMonoidHom U₂) 0 w) (zero_add 0)))
    (hdd : (CategoryTheory.Abelian.Ext.mk₀ Φ₂.τ₁).comp
        ((Rep.resFunctor (k := SSGRoute.PTExt.Coeff) e.symm.toMonoidHom).mapExtAddHom
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover (Rep.res φ X)))
          (Rep.res e.toMonoidHom U₂) 0
          (((CategoryTheory.Abelian.Ext.mk₀ Φ₁.τ₁).comp
            ((Rep.resFunctor (k := SSGRoute.PTExt.Coeff) φ).mapExtAddHom
              (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover X)) U₁ 0 y)
              (zero_add 0)).comp (CategoryTheory.Abelian.Ext.mk₀ ι) (zero_add 0)))
        (zero_add 0)
      = castCoeff0 (Work.SSGRoute.E1aClean.res_comp_symm_self e U₂).symm y₂) :
    (SSGRoute.PTExt.extRes φ (Work.SSGRoute.PT.PhiEgen X U₁ y)).comp
        (CategoryTheory.Abelian.Ext.mk₀ ι) (add_zero 1)
      = Work.SSGRoute.E1aClean.extResEquivExplicit e (Rep.res φ X) (Rep.res e.toMonoidHom U₂)
          ((Work.SSGRoute.E1aClean.res_comp_symm_self e U₂).symm ▸
            Work.SSGRoute.PT.PhiEgen (Rep.res e.symm.toMonoidHom (Rep.res φ X)) U₂ y₂) := by
  apply (Work.SSGRoute.E1aClean.extResEquivExplicit e (Rep.res φ X)
    (Rep.res e.toMonoidHom U₂)).symm.injective
  rw [AddEquiv.symm_apply_apply, Work.SSGRoute.E1aClean.extResEquivExplicit_symm_apply]
  have hu : (SSGRoute.PTExt.extRes φ (Work.SSGRoute.PT.PhiEgen X U₁ y)).comp
        (CategoryTheory.Abelian.Ext.mk₀ ι) (add_zero 1)
      = Work.SSGRoute.PT.PhiEgen (Rep.res φ X) (Rep.res e.toMonoidHom U₂)
          (((CategoryTheory.Abelian.Ext.mk₀ Φ₁.τ₁).comp
            ((Rep.resFunctor (k := SSGRoute.PTExt.Coeff) φ).mapExtAddHom
              (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover X)) U₁ 0 y)
              (zero_add 0)).comp (CategoryTheory.Abelian.Ext.mk₀ ι) (zero_add 0)) := by
    have h1 : SSGRoute.PTExt.extRes φ (Work.SSGRoute.PT.PhiEgen X U₁ y)
        = (Rep.resFunctor (k := SSGRoute.PTExt.Coeff) φ).mapExtAddHom X U₁ 1
            (Work.SSGRoute.PT.PhiEgen X U₁ y) := by
      unfold SSGRoute.PTExt.extRes
      rw [CategoryTheory.Functor.mapExtAddHom_apply]
    rw [h1, hΦ₁ y, Work.SSGRoute.PT.PhiEgen_apply, Work.SSGRoute.PT.PhiEgen_apply]
    exact CategoryTheory.Abelian.Ext.comp_assoc_of_third_deg_zero _ _ _ _
  rw [hu, hΦ₂, hdd]
  exact PhiEgen_ndrec _ y₂

/-! ## R2. GENERIC: equality of degree-0 classes ⇐ pointwise identity -/

theorem degZero_of_pointwise {G D L : Type} [Group G] [Group D] [Group L]
    [Fintype G] [Fintype D] [Fintype L]
    (φ : D →* G) (e : D ≃* L)
    (X U₁ : Rep.{0} SSGRoute.PTExt.Coeff G) (U₂ : Rep.{0} SSGRoute.PTExt.Coeff L)
    (ι : Rep.res φ U₁ ⟶ Rep.res e.toMonoidHom U₂)
    (y : CategoryTheory.Abelian.Ext
      (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover X)) U₁ 0)
    (y₂ : CategoryTheory.Abelian.Ext
      (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover
        (Rep.res e.symm.toMonoidHom (Rep.res φ X)))) U₂ 0)
    (Φ₁ : CategoryTheory.ShortComplex.Hom (Work.SSGRoute.freeCoverSES (Rep.res φ X))
      ((Work.SSGRoute.freeCoverSES X).map (Rep.resFunctor (k := SSGRoute.PTExt.Coeff) φ)))
    (Φ₂ : CategoryTheory.ShortComplex.Hom
      (Work.SSGRoute.freeCoverSES (Rep.res e.symm.toMonoidHom (Rep.res φ X)))
      ((Work.SSGRoute.freeCoverSES (Rep.res φ X)).map
        (Rep.resFunctor (k := SSGRoute.PTExt.Coeff) e.symm.toMonoidHom)))
    (hpt : ∀ r : (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover
        (Rep.res e.symm.toMonoidHom (Rep.res φ X)))).V,
      (Rep.Hom.hom ι) ((CategoryTheory.Abelian.Ext.addEquiv₀ y).hom
          ((Rep.Hom.hom Φ₁.τ₁) ((Rep.Hom.hom Φ₂.τ₁) r)))
        = (CategoryTheory.Abelian.Ext.addEquiv₀ y₂).hom r) :
    (CategoryTheory.Abelian.Ext.mk₀ Φ₂.τ₁).comp
        ((Rep.resFunctor (k := SSGRoute.PTExt.Coeff) e.symm.toMonoidHom).mapExtAddHom
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover (Rep.res φ X)))
          (Rep.res e.toMonoidHom U₂) 0
          (((CategoryTheory.Abelian.Ext.mk₀ Φ₁.τ₁).comp
            ((Rep.resFunctor (k := SSGRoute.PTExt.Coeff) φ).mapExtAddHom
              (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover X)) U₁ 0 y)
              (zero_add 0)).comp (CategoryTheory.Abelian.Ext.mk₀ ι) (zero_add 0)))
        (zero_add 0)
      = castCoeff0 (Work.SSGRoute.E1aClean.res_comp_symm_self e U₂).symm y₂ := by
  apply CategoryTheory.Abelian.Ext.addEquiv₀.injective
  unfold castCoeff0
  rw [ext_addEquiv₀_ndrec, ext_addEquiv₀_mk₀_comp]
  erw [ext_addEquiv₀_mapExtAddHom]
  erw [ext_addEquiv₀_comp_mk₀, ext_addEquiv₀_mk₀_comp]
  erw [ext_addEquiv₀_mapExtAddHom]
  apply Rep.hom_ext
  apply DFunLike.ext
  intro r
  erw [rep_ndrec_hom_apply_tgt (Work.SSGRoute.E1aClean.res_comp_symm_self e U₂).symm
    (CategoryTheory.Abelian.Ext.addEquiv₀ y₂) r]
  erw [cast_congrArg_RepV_res' e U₂ (Work.SSGRoute.E1aClean.res_comp_symm_self e U₂).symm _]
  exact hpt r

/-! ## R3. SPECIFIC: the pointwise identity (the arithmetic heart) -/

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
theorem crux_pointwise
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    [IsSepClosure ↥K Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (hAq : ∀ x : NumberField.RingOfIntegers ↥K,
      x ∈ q.asIdeal ↔ A.valuation (((x : ↥K) : Ω)) < 1)
    [hNorm : Normal ↥(Work.SSGRoute.E1aClean.decompField k Ω A)
      ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)]
    (e : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) ≃*
      (↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A) ≃ₐ[
          ↥(Work.SSGRoute.E1aClean.decompField k Ω A)]
        ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)))
    (hφres : ∀ g : Ω ≃ₐ[↥(Work.SSGRoute.E1aClean.decompField k Ω A)] Ω,
      Work.SSGRoute.E1aClean.levelTwoGroupHom k Ω K A hA q hAq e
          (SSGRoute.res ↥(Work.SSGRoute.E1aClean.decompField k Ω A)
            (Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A) g)
        = SSGRoute.res k K (AlgEquiv.restrictScalars k g))
    [inst : Algebra (q.adicCompletion ↥K) (NK.NeukirchUchida.placeCompletion A)]
    (halg : ∀ z : q.adicCompletion ↥K,
      algebraMap (q.adicCompletion ↥K) (NK.NeukirchUchida.placeCompletion A) z =
        NK.NeukirchUchida.adicCompletionToPlaceCompletion q A
          (Work.SSGRoute.place_comap_valuationSubringAtPrime k Ω K A hA q hAq) z)
    (he : ∀ (τ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q))) (x : ↥K),
      ((e τ) ⟨(x : Ω), Work.SSGRoute.E1aClean.le_henselField k Ω K A x.2⟩ : Ω)
        = ((τ : ↥K ≃ₐ[k] ↥K) x : Ω))
    [instA : IsAlgClosure ↥(Work.SSGRoute.E1aClean.decompField k Ω A) Ω]
    [instF : FiniteDimensional ↥(Work.SSGRoute.E1aClean.decompField k Ω A)
      ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)]
    [instG : IsGalois ↥(Work.SSGRoute.E1aClean.decompField k Ω A)
      ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)]
    (X : Rep.{0} SSGRoute.PTExt.Coeff (↥K ≃ₐ[k] ↥K)) [Module.Finite ℤ X.V]
    (ñ : Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := k) (Ω := Ω) (K := K) X)
    (y : CategoryTheory.Abelian.Ext.{0}
      (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k := k) (Ω := Ω) (K := K) X)
      (SSGRoute.PTExt.unitsK k K) 0)
    (hy : (Work.SSGRoute.ExtChain.E1cGeneric.piH (k := k) (Ω := Ω) (K := K) X ñ
            : Work.SSGRoute.homCoind k Ω K
              (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k := k) (Ω := Ω) (K := K) X))
        = ↑(Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap (k := k) (Ω := Ω) (K := K)
              (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k := k) (Ω := Ω) (K := K) X) y))
    (ñ₂ : Work.SSGRoute.ExtChain.E1cGeneric.E1cN
      (k := ↥(Work.SSGRoute.E1aClean.decompField k Ω A)) (Ω := Ω)
      (K := Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)
      (Work.SSGRoute.E1aClean.levelTwoCoeff k Ω K A hA q hAq e X))
    (hñ₂ : ñ₂ = Work.SSGRoute.E1aClean.levelTwoLift k Ω K A hA q hAq e X ñ)
    (y₂ : CategoryTheory.Abelian.Ext.{0}
      (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1
        (k := ↥(Work.SSGRoute.E1aClean.decompField k Ω A)) (Ω := Ω)
        (K := Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)
        (Work.SSGRoute.E1aClean.levelTwoCoeff k Ω K A hA q hAq e X))
      (SSGRoute.PTExt.unitsK ↥(Work.SSGRoute.E1aClean.decompField k Ω A)
        ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)) 0)
    (hy₂ : (Work.SSGRoute.ExtChain.E1cGeneric.piH
              (k := ↥(Work.SSGRoute.E1aClean.decompField k Ω A)) (Ω := Ω)
              (K := Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)
              (Work.SSGRoute.E1aClean.levelTwoCoeff k Ω K A hA q hAq e X) ñ₂
            : Work.SSGRoute.homCoind ↥(Work.SSGRoute.E1aClean.decompField k Ω A) Ω
                (Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)
                (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1
                  (k := ↥(Work.SSGRoute.E1aClean.decompField k Ω A)) (Ω := Ω)
                  (K := Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)
                  (Work.SSGRoute.E1aClean.levelTwoCoeff k Ω K A hA q hAq e X)))
        = ↑(Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap
              (k := ↥(Work.SSGRoute.E1aClean.decompField k Ω A)) (Ω := Ω)
              (K := Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)
              (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1
                (k := ↥(Work.SSGRoute.E1aClean.decompField k Ω A)) (Ω := Ω)
                (K := Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)
                (Work.SSGRoute.E1aClean.levelTwoCoeff k Ω K A hA q hAq e X)) y₂))

    (Φ₁ : CategoryTheory.ShortComplex.Hom (Work.SSGRoute.freeCoverSES (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype X))
      ((Work.SSGRoute.freeCoverSES X).map
        (Rep.resFunctor (k := SSGRoute.PTExt.Coeff) (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype)))
    (hΦ₁₂ : Φ₁.τ₂ = Work.SSGRoute.PT.freeCoverCompat (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype X)
    (Φ₂ : CategoryTheory.ShortComplex.Hom
      (Work.SSGRoute.freeCoverSES (Rep.res e.symm.toMonoidHom (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype X)))
      ((Work.SSGRoute.freeCoverSES (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype X)).map
        (Rep.resFunctor (k := SSGRoute.PTExt.Coeff) e.symm.toMonoidHom)))
    (hΦ₂₂ : Φ₂.τ₂ = Work.SSGRoute.PT.freeCoverCompat e.symm.toMonoidHom (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype X)) :
    ∀ r : (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover
        (Rep.res e.symm.toMonoidHom (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype X)))).V,
      (Rep.Hom.hom (Work.SSGRoute.ExtChain.khIota (k := k) (Ω := Ω) (K := K) A q e he))
          ((CategoryTheory.Abelian.Ext.addEquiv₀ y).hom
            ((Rep.Hom.hom Φ₁.τ₁) ((Rep.Hom.hom Φ₂.τ₁) r)))
        = (CategoryTheory.Abelian.Ext.addEquiv₀ y₂).hom r := by
  intro r
  have hval₁ : ∀ s : (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k := k) (Ω := Ω) (K := K) X).V,
      Additive.ofMul (Units.map (algebraMap ↥K Ω).toMonoidHom (Additive.toMul
        ((CategoryTheory.Abelian.Ext.addEquiv₀ y).hom s)))
        = ñ ((Work.SSGRoute.ExtChain.E1cGeneric.kappa (k := k) (Ω := Ω) (K := K) X) s) := by
    intro s
    have h := DFunLike.congr_fun hy s
    rw [Work.SSGRoute.ExtChain.E1cGeneric.piH_apply, AddMonoidHom.comp_apply,
      Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap_apply_toCoindH0,
      Work.SSGRoute.toCoindH0_apply] at h
    exact h.symm
  have hval₂ : ∀ r' : (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1
      (k := ↥(Work.SSGRoute.E1aClean.decompField k Ω A)) (Ω := Ω)
      (K := Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)
      (Work.SSGRoute.E1aClean.levelTwoCoeff k Ω K A hA q hAq e X)).V,
      Additive.ofMul (Units.map
        (algebraMap ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A) Ω).toMonoidHom
        (Additive.toMul ((CategoryTheory.Abelian.Ext.addEquiv₀ y₂).hom r')))
        = ñ₂ ((Work.SSGRoute.ExtChain.E1cGeneric.kappa
            (k := ↥(Work.SSGRoute.E1aClean.decompField k Ω A)) (Ω := Ω)
            (K := Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)
            (Work.SSGRoute.E1aClean.levelTwoCoeff k Ω K A hA q hAq e X)) r') := by
    intro r'
    have h := DFunLike.congr_fun hy₂ r'
    rw [Work.SSGRoute.ExtChain.E1cGeneric.piH_apply, AddMonoidHom.comp_apply,
      Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap_apply_toCoindH0,
      Work.SSGRoute.toCoindH0_apply] at h
    exact h.symm
  have hmap : ∀ u : (↥K)ˣ,
      Units.map (algebraMap ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A) Ω).toMonoidHom
          (Units.map (Work.SSGRoute.ExtChain.khIncl (k := k) (Ω := Ω) (K := K) A) u)
        = Units.map (algebraMap ↥K Ω).toMonoidHom u := by
    intro u
    apply Units.ext
    rfl
  have hcov : (Rep.Hom.hom (CategoryTheory.Limits.kernel.ι (Work.SSGRoute.freeCover X)))
          ((Rep.Hom.hom Φ₁.τ₁) ((Rep.Hom.hom Φ₂.τ₁) r))
        = (Rep.Hom.hom (Work.SSGRoute.PT.freeCoverCompat
              (Work.SSGRoute.E1aClean.levelTwoGroupHom k Ω K A hA q hAq e) X))
            ((Rep.Hom.hom (CategoryTheory.Limits.kernel.ι
              (Work.SSGRoute.freeCover
                (Work.SSGRoute.E1aClean.levelTwoCoeff k Ω K A hA q hAq e X)))) r) := by
    have h1 := Work.SSGRoute.E1aClean.freeCoverSES_res_comparison_kernel_apply
      (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype X Φ₁
      (Rep.Hom.hom Φ₂.τ₁ r)
    rw [hΦ₁₂] at h1
    have h2 := Work.SSGRoute.E1aClean.freeCoverSES_res_comparison_kernel_apply
      e.symm.toMonoidHom (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype X) Φ₂ r
    rw [hΦ₂₂] at h2
    rw [h1, h2]
    exact (freeCoverCompat_comp_apply
      (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype
      e.symm.toMonoidHom X _).symm
  have hfin : ñ ((Work.SSGRoute.ExtChain.E1cGeneric.kappa (k := k) (Ω := Ω) (K := K) X)
        ((Rep.Hom.hom Φ₁.τ₁) ((Rep.Hom.hom Φ₂.τ₁) r)))
      = ñ₂ ((Work.SSGRoute.ExtChain.E1cGeneric.kappa
          (k := ↥(Work.SSGRoute.E1aClean.decompField k Ω A)) (Ω := Ω)
          (K := Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)
          (Work.SSGRoute.E1aClean.levelTwoCoeff k Ω K A hA q hAq e X)) r) := by
    rw [hñ₂, Work.SSGRoute.ExtChain.E1cGeneric.kappa_apply,
      Work.SSGRoute.ExtChain.E1cGeneric.kappa_apply, hcov]
    rfl
  have hΩ := congrArg Additive.toMul ((hval₁ _).trans (hfin.trans (hval₂ r).symm))
  apply Additive.toMul.injective
  apply Units.map_injective (f := (algebraMap
    ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A) Ω).toMonoidHom)
    (algebraMap ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A) Ω).injective
  rw [Work.SSGRoute.ExtChain.khIota_apply]
  erw [hmap]
  exact hΩ

end

end Work.SSGRoute.E1aClean.LeadPhiUnr.PhiSqAux

namespace Work.SSGRoute.E1aClean.LeadPhiUnr

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
theorem extRes_PhiE_comp_khIota
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    [IsSepClosure ↥K Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (hAq : ∀ x : NumberField.RingOfIntegers ↥K,
      x ∈ q.asIdeal ↔ A.valuation (((x : ↥K) : Ω)) < 1)
    [hNorm : Normal ↥(Work.SSGRoute.E1aClean.decompField k Ω A)
      ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)]
    (e : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) ≃*
      (↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A) ≃ₐ[
          ↥(Work.SSGRoute.E1aClean.decompField k Ω A)]
        ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)))
    (hφres : ∀ g : Ω ≃ₐ[↥(Work.SSGRoute.E1aClean.decompField k Ω A)] Ω,
      Work.SSGRoute.E1aClean.levelTwoGroupHom k Ω K A hA q hAq e
          (SSGRoute.res ↥(Work.SSGRoute.E1aClean.decompField k Ω A)
            (Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A) g)
        = SSGRoute.res k K (AlgEquiv.restrictScalars k g))
    [inst : Algebra (q.adicCompletion ↥K) (NK.NeukirchUchida.placeCompletion A)]
    (halg : ∀ z : q.adicCompletion ↥K,
      algebraMap (q.adicCompletion ↥K) (NK.NeukirchUchida.placeCompletion A) z =
        NK.NeukirchUchida.adicCompletionToPlaceCompletion q A
          (Work.SSGRoute.place_comap_valuationSubringAtPrime k Ω K A hA q hAq) z)
    (he : ∀ (τ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q))) (x : ↥K),
      ((e τ) ⟨(x : Ω), Work.SSGRoute.E1aClean.le_henselField k Ω K A x.2⟩ : Ω)
        = ((τ : ↥K ≃ₐ[k] ↥K) x : Ω))
    [instA : IsAlgClosure ↥(Work.SSGRoute.E1aClean.decompField k Ω A) Ω]
    [instF : FiniteDimensional ↥(Work.SSGRoute.E1aClean.decompField k Ω A)
      ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)]
    [instG : IsGalois ↥(Work.SSGRoute.E1aClean.decompField k Ω A)
      ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)]
    (X : Rep.{0} SSGRoute.PTExt.Coeff (↥K ≃ₐ[k] ↥K)) [Module.Finite ℤ X.V]
    (ñ : Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := k) (Ω := Ω) (K := K) X)
    (y : CategoryTheory.Abelian.Ext.{0}
      (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k := k) (Ω := Ω) (K := K) X)
      (SSGRoute.PTExt.unitsK k K) 0)
    (hy : (Work.SSGRoute.ExtChain.E1cGeneric.piH (k := k) (Ω := Ω) (K := K) X ñ
            : Work.SSGRoute.homCoind k Ω K
              (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k := k) (Ω := Ω) (K := K) X))
        = ↑(Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap (k := k) (Ω := Ω) (K := K)
              (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k := k) (Ω := Ω) (K := K) X) y))
    (ñ₂ : Work.SSGRoute.ExtChain.E1cGeneric.E1cN
      (k := ↥(Work.SSGRoute.E1aClean.decompField k Ω A)) (Ω := Ω)
      (K := Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)
      (Work.SSGRoute.E1aClean.levelTwoCoeff k Ω K A hA q hAq e X))
    (hñ₂ : ñ₂ = Work.SSGRoute.E1aClean.levelTwoLift k Ω K A hA q hAq e X ñ)
    (y₂ : CategoryTheory.Abelian.Ext.{0}
      (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1
        (k := ↥(Work.SSGRoute.E1aClean.decompField k Ω A)) (Ω := Ω)
        (K := Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)
        (Work.SSGRoute.E1aClean.levelTwoCoeff k Ω K A hA q hAq e X))
      (SSGRoute.PTExt.unitsK ↥(Work.SSGRoute.E1aClean.decompField k Ω A)
        ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)) 0)
    (hy₂ : (Work.SSGRoute.ExtChain.E1cGeneric.piH
              (k := ↥(Work.SSGRoute.E1aClean.decompField k Ω A)) (Ω := Ω)
              (K := Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)
              (Work.SSGRoute.E1aClean.levelTwoCoeff k Ω K A hA q hAq e X) ñ₂
            : Work.SSGRoute.homCoind ↥(Work.SSGRoute.E1aClean.decompField k Ω A) Ω
                (Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)
                (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1
                  (k := ↥(Work.SSGRoute.E1aClean.decompField k Ω A)) (Ω := Ω)
                  (K := Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)
                  (Work.SSGRoute.E1aClean.levelTwoCoeff k Ω K A hA q hAq e X)))
        = ↑(Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap
              (k := ↥(Work.SSGRoute.E1aClean.decompField k Ω A)) (Ω := Ω)
              (K := Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)
              (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1
                (k := ↥(Work.SSGRoute.E1aClean.decompField k Ω A)) (Ω := Ω)
                (K := Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)
                (Work.SSGRoute.E1aClean.levelTwoCoeff k Ω K A hA q hAq e X)) y₂)) :
    (SSGRoute.PTExt.extRes (SSGRoute.PTExt.decompK (k := k)
        (NK.GlobalCFT.Place.ofFinite q)).subtype
      (Work.SSGRoute.ExtChain.E1cGeneric.PhiE (k := k) (Ω := Ω) (K := K) X y)).comp
      (CategoryTheory.Abelian.Ext.mk₀
        (Work.SSGRoute.ExtChain.khIota (k := k) (Ω := Ω) (K := K) A q e he)) (add_zero 1)
    = Work.SSGRoute.E1aClean.extResEquivExplicit e
        (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype X)
        (Rep.res e.toMonoidHom
          (SSGRoute.PTExt.unitsK ↥(Work.SSGRoute.E1aClean.decompField k Ω A)
            ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)))
        ((Work.SSGRoute.E1aClean.res_comp_symm_self e
            (SSGRoute.PTExt.unitsK ↥(Work.SSGRoute.E1aClean.decompField k Ω A)
              ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A))).symm ▸
          (Work.SSGRoute.ExtChain.E1cGeneric.PhiE
            (k := ↥(Work.SSGRoute.E1aClean.decompField k Ω A)) (Ω := Ω)
            (K := Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)
            (Rep.res e.symm.toMonoidHom
              (Rep.res (SSGRoute.PTExt.decompK (k := k)
                (NK.GlobalCFT.Place.ofFinite q)).subtype X)) y₂)) := by
  classical
  haveI : Fintype (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) := Fintype.ofFinite _
  haveI : Fintype (↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A) ≃ₐ[
      ↥(Work.SSGRoute.E1aClean.decompField k Ω A)]
      ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)) := Fintype.ofFinite _
  obtain ⟨Φ₁, hΦ₁₂, -, hΦ₁cl⟩ := Work.SSGRoute.PT.PhiEgen_res_compat
    (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype X (SSGRoute.PTExt.unitsK k K)
  obtain ⟨Φ₂, hΦ₂₂, -, hΦ₂cl⟩ := Work.SSGRoute.PT.PhiEgen_res_compat
    e.symm.toMonoidHom (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype X) (Rep.res e.toMonoidHom (SSGRoute.PTExt.unitsK ↥(Work.SSGRoute.E1aClean.decompField k Ω A) ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)))
  exact PhiSqAux.crux_of_degZero (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype e X (SSGRoute.PTExt.unitsK k K) (SSGRoute.PTExt.unitsK ↥(Work.SSGRoute.E1aClean.decompField k Ω A) ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A))
    (Work.SSGRoute.ExtChain.khIota (k := k) (Ω := Ω) (K := K) A q e he) y y₂
    Φ₁ hΦ₁cl Φ₂ hΦ₂cl
    (PhiSqAux.degZero_of_pointwise (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype e X (SSGRoute.PTExt.unitsK k K) (SSGRoute.PTExt.unitsK ↥(Work.SSGRoute.E1aClean.decompField k Ω A) ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A))
      (Work.SSGRoute.ExtChain.khIota (k := k) (Ω := Ω) (K := K) A q e he) y y₂ Φ₁ Φ₂
      (PhiSqAux.crux_pointwise k Ω K A hA q hAq e hφres halg he X ñ y hy ñ₂ hñ₂ y₂ hy₂
        Φ₁ hΦ₁₂ Φ₂ hΦ₂₂))

end Work.SSGRoute.E1aClean.LeadPhiUnr
