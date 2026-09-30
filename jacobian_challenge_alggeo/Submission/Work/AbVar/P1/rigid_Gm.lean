import Mathlib
import Submission.Work.AbVar.Basic
import Submission.Work.AbVar.TestObjects
import Submission.Work.AbVar.TestObjects.gm_geometricallyIntegral
import Submission.Work.AbVar.P1.isIntegral_tensorObj_Gm
import Submission.Work.AbVar.Rigidity.range_sectionLeft

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option maxHeartbeats 1000000

namespace Work.AbVar.P1

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open AlgebraicGeometry
open scoped MonObj MonoidalCategory

universe u

section Constancy

/-! ## Constancy of morphisms into an affine open, over the spectrum of a field

This is a universe-polymorphic version of `Work.AbVar.Rigidity.const_of_affineOpen`: a morphism
from an integral, universally closed `τ`-scheme `V` with a section `v` of its structure map, whose
image lies in an affine open `U`, is the composite of the structure map with its value at `v`. -/

private lemma appTop_section_comp_eq_id {τ : Type u} [Field τ] {V : Scheme.{u}}
    (π : V ⟶ Spec (CommRingCat.of τ)) [IsIntegral V] [UniversallyClosed π]
    (v : Spec (CommRingCat.of τ) ⟶ V) (hv : v ≫ π = 𝟙 _) :
    v.appTop ≫ π.appTop = 𝟙 Γ(V, ⊤) := by
  have hfield : IsField (↑Γ(V,⊤)) := isField_of_universallyClosed τ π
  letI : Field (↑Γ(V,⊤)) := hfield.toField
  have hqp : π.appTop ≫ v.appTop = 𝟙 Γ(Spec (CommRingCat.of τ), ⊤) := by
    have h := congrArg Scheme.Hom.appTop hv
    rwa [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop] at h
  have hinj : Function.Injective v.appTop.hom := by
    rw [RingHom.injective_iff_ker_eq_bot]
    rcases Ideal.eq_bot_or_top (RingHom.ker v.appTop.hom) with h | h
    · exact h
    · exfalso
      have h1 : (1 : ↑Γ(V,⊤)) ∈ RingHom.ker v.appTop.hom := by rw [h]; exact Submodule.mem_top
      rw [RingHom.mem_ker, map_one] at h1
      exact one_ne_zero h1
  have hpt : ∀ y : ↑Γ(Spec (CommRingCat.of τ),⊤), v.appTop.hom (π.appTop.hom y) = y := by
    intro y
    have := congrArg (fun f : Γ(Spec (CommRingCat.of τ),⊤) ⟶ Γ(Spec (CommRingCat.of τ),⊤) =>
      (ConcreteCategory.hom f) y) hqp
    simpa [CommRingCat.comp_apply, ConcreteCategory.id_apply] using this
  ext x
  simp only [CommRingCat.comp_apply, ConcreteCategory.id_apply]
  exact hinj (by rw [hpt (v.appTop.hom x)])

private lemma const_of_spec {τ : Type u} [Field τ] {V : Scheme.{u}}
    (π : V ⟶ Spec (CommRingCat.of τ)) [IsIntegral V] [UniversallyClosed π]
    (v : Spec (CommRingCat.of τ) ⟶ V) (hv : v ≫ π = 𝟙 _)
    {A : CommRingCat.{u}} (g : V ⟶ Spec A) : g = π ≫ (v ≫ g) := by
  have hkey : v.appTop ≫ π.appTop = 𝟙 Γ(V, ⊤) := appTop_section_comp_eq_id π v hv
  refine ext_to_Spec (R := ↥A) ?_
  rw [Scheme.Γ_map_op, Scheme.Γ_map_op, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
  have h1 : (g.appTop ≫ v.appTop) ≫ π.appTop = g.appTop := by
    rw [Category.assoc, hkey, Category.comp_id]
  rw [h1]

private lemma const_of_affine {τ : Type u} [Field τ] {V : Scheme.{u}}
    (π : V ⟶ Spec (CommRingCat.of τ)) [IsIntegral V] [UniversallyClosed π]
    (v : Spec (CommRingCat.of τ) ⟶ V) (hv : v ≫ π = 𝟙 _)
    {Y : Scheme.{u}} [IsAffine Y] (f : V ⟶ Y) : f = π ≫ (v ≫ f) := by
  have h := const_of_spec π v hv (f ≫ Y.isoSpec.hom)
  rw [show (π ≫ (v ≫ f ≫ Y.isoSpec.hom)) = (π ≫ (v ≫ f)) ≫ Y.isoSpec.hom from by
        simp only [Category.assoc]] at h
  exact (cancel_mono Y.isoSpec.hom).mp h

/-- A morphism from an integral, universally closed `τ`-scheme with a `τ`-section into an affine
open subscheme is constant. -/
lemma const_of_affineOpen' {τ : Type u} [Field τ] {V W : Scheme.{u}}
    (π : V ⟶ Spec (CommRingCat.of τ)) [hint : IsIntegral V] [huc : UniversallyClosed π]
    (v : Spec (CommRingCat.of τ) ⟶ V) (hv : v ≫ π = 𝟙 _)
    (U : W.Opens) (hU : IsAffineOpen U) (σ : V ⟶ W) (hσ : Set.range σ ⊆ (U : Set W)) :
    σ = π ≫ (v ≫ σ) := by
  haveI : IsAffine (↑U : Scheme.{u}) := hU
  have hσ' : Set.range σ ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]; exact hσ
  have hfac : IsOpenImmersion.lift U.ι σ hσ' ≫ U.ι = σ :=
    IsOpenImmersion.lift_fac U.ι σ hσ'
  have hconst := const_of_affine π v hv (IsOpenImmersion.lift U.ι σ hσ')
  calc σ = IsOpenImmersion.lift U.ι σ hσ' ≫ U.ι := hfac.symm
    _ = (π ≫ (v ≫ IsOpenImmersion.lift U.ι σ hσ')) ≫ U.ι := by
          conv_lhs => rw [hconst]
    _ = π ≫ (v ≫ σ) := by
          rw [Category.assoc, Category.assoc, hfac]

end Constancy

open CategoryTheory in
/-- Milne's rigidity argument, specialised to `W = 𝔾_m`: a morphism `f : X ⊗ 𝔾_m ⟶ A` into a
proper group scheme which collapses on *both* coordinate axes `X ⊗ {1}` and `{x₀} ⊗ 𝔾_m`
collapses everywhere.

Intended proof (Milne, *Abelian Varieties*, Theorem 1.1, adapted; please prove this directly,
do NOT reduce it to `Work.AbVar.Rigidity.rigidity`):
* `X ⊗ 𝔾_m` is integral, in particular irreducible and reduced
  (`Work.AbVar.P1.isIntegral_tensorObj_Gm`).
* Choose an affine open `U₀ ∋ η[A]` and let `Z := snd '' (f ⁻¹' (A ∖ U₀))` in `𝔾_m`; it is
  closed because `snd X (𝔾_m k) : X ⊗ 𝔾_m ⟶ 𝔾_m` is a closed map (`X` is proper over `k`).
* `1 ∉ Z` by `h1`, so for every point `g ∉ Z` the fibre map `f(·,g) : X ⟶ A` has image inside
  the affine open `U₀`; apply `Work.AbVar.P1.const_of_image_subset_isAffine` to see that
  `f(·,g)` is constant.
* That constant equals `η[A]` by `h2`, so `f` and the constant morphism `η[A]` agree on the
  nonempty open `X ⊗ (𝔾_m ∖ Z)`; since `X ⊗ 𝔾_m` is irreducible this open is dense, and since
  `X ⊗ 𝔾_m` is reduced and `A` is separated (`IsProper` gives `IsSeparated`) the two morphisms
  are equal (`AlgebraicGeometry.ext_of_isDominant_of_isSeparated`). -/
theorem rigid_Gm {k : Type*} [Field k] {X A : Work.AbVar.Sch k}
    [AlgebraicGeometry.IsProper X.hom] [AlgebraicGeometry.GeometricallyIntegral X.hom]
    [CategoryTheory.GrpObj A] [AlgebraicGeometry.IsProper A.hom]
    (x0 : Work.AbVar.Point X)
    (f : MonoidalCategoryStruct.tensorObj X (Work.AbVar.Gm k) ⟶ A)
    (h1 : Work.AbVar.sectionLeft X (Work.AbVar.Gm k)
        (CategoryTheory.MonObj.one (X := Work.AbVar.Gm k)) ≫ f =
      SemiCartesianMonoidalCategory.toUnit X ≫ CategoryTheory.MonObj.one (X := A))
    (h2 : Work.AbVar.sectionRight X (Work.AbVar.Gm k) x0 ≫ f =
      SemiCartesianMonoidalCategory.toUnit (Work.AbVar.Gm k) ≫ CategoryTheory.MonObj.one (X := A)) :
    f = SemiCartesianMonoidalCategory.toUnit (MonoidalCategoryStruct.tensorObj X (Work.AbVar.Gm k)) ≫
      CategoryTheory.MonObj.one (X := A) := by
  classical
  haveI hXYint : IsIntegral (MonoidalCategoryStruct.tensorObj X (Work.AbVar.Gm k)).left :=
    isIntegral_tensorObj_Gm
  haveI hsub : Subsingleton ↥(Over.left (𝟙_ (Work.AbVar.Sch k))) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  -- ## Step 1: an affine open `U` of `A` containing the unit section.
  obtain ⟨U, hUaff, hcU⟩ : ∃ U : A.left.Opens, IsAffineOpen U ∧
      (CategoryTheory.MonObj.one (X := A)).left (IsLocalRing.closedPoint k) ∈ U := by
    obtain ⟨-, ⟨U, hU, rfl⟩, hcU, -⟩ :=
      A.left.isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ ((CategoryTheory.MonObj.one (X := A)).left (IsLocalRing.closedPoint k)))
        isOpen_univ
    exact ⟨U, hU, hcU⟩
  -- ## Step 2: the open subset `V` of `𝔾_m` of points whose fibre maps into `U`.
  let V : Set (Work.AbVar.Gm k).left :=
    ((SemiCartesianMonoidalCategory.snd X (Work.AbVar.Gm k)).left ''
      (f.left ⁻¹' ((U : Set A.left))ᶜ))ᶜ
  have hVopen : IsOpen V := by
    have hmap : IsClosedMap (SemiCartesianMonoidalCategory.snd X (Work.AbVar.Gm k)).left := by
      haveI : IsProper (SemiCartesianMonoidalCategory.snd X (Work.AbVar.Gm k)).left :=
        inferInstanceAs (IsProper (pullback.snd X.hom (Work.AbVar.Gm k).hom))
      exact (SemiCartesianMonoidalCategory.snd X (Work.AbVar.Gm k)).left.isClosedMap
    have hclosed : IsClosed (f.left ⁻¹' ((U : Set A.left))ᶜ) :=
      U.isOpen.isClosed_compl.preimage f.left.continuous
    exact (hmap _ hclosed).isOpen_compl
  have hViff : ∀ y : (Work.AbVar.Gm k).left, y ∈ V ↔
      ∀ ξ : (MonoidalCategoryStruct.tensorObj X (Work.AbVar.Gm k)).left,
        (SemiCartesianMonoidalCategory.snd X (Work.AbVar.Gm k)).left ξ = y →
          f.left ξ ∈ (U : Set A.left) := by
    intro y
    constructor
    · intro hy ξ hξ
      by_contra hfξ
      refine hy ?_
      refine ⟨ξ, ?_, hξ⟩
      simpa using hfξ
    · intro h
      rintro ⟨ξ, hfξ, hξ⟩
      have hfξ' : f.left ξ ∉ (U : Set A.left) := by simpa using hfξ
      exact hfξ' (h ξ hξ)
  -- ## Step 3: the unit point lies in `V`, by `h1`.
  have hbV : (CategoryTheory.MonObj.one (X := Work.AbVar.Gm k)).left
      (IsLocalRing.closedPoint k) ∈ V := by
    rw [hViff]
    intro ξ hξ
    have hmem : ξ ∈ (SemiCartesianMonoidalCategory.snd X (Work.AbVar.Gm k)).left ⁻¹'
        Set.range (CategoryTheory.MonObj.one (X := Work.AbVar.Gm k)).left := by
      rw [Set.mem_preimage]
      exact ⟨IsLocalRing.closedPoint k, hξ.symm⟩
    rw [← Work.AbVar.Rigidity.range_sectionLeft X (Work.AbVar.Gm k)
      (CategoryTheory.MonObj.one (X := Work.AbVar.Gm k))] at hmem
    obtain ⟨x, hx⟩ := hmem
    have hcomp : (f.left ∘ (Work.AbVar.sectionLeft X (Work.AbVar.Gm k)
        (CategoryTheory.MonObj.one (X := Work.AbVar.Gm k))).left)
        = ((CategoryTheory.MonObj.one (X := A)).left ∘
            (SemiCartesianMonoidalCategory.toUnit X).left) := by
      funext t
      have hh := congrArg Over.Hom.left h1
      rw [Over.comp_left, Over.comp_left] at hh
      have hhx := congr($hh t)
      simpa only [Scheme.Hom.comp_apply, Function.comp_apply] using hhx
    have hval : f.left ((Work.AbVar.sectionLeft X (Work.AbVar.Gm k)
        (CategoryTheory.MonObj.one (X := Work.AbVar.Gm k))).left x)
        = (CategoryTheory.MonObj.one (X := A)).left (IsLocalRing.closedPoint k) := by
      calc f.left ((Work.AbVar.sectionLeft X (Work.AbVar.Gm k)
              (CategoryTheory.MonObj.one (X := Work.AbVar.Gm k))).left x)
          = (f.left ∘ (Work.AbVar.sectionLeft X (Work.AbVar.Gm k)
              (CategoryTheory.MonObj.one (X := Work.AbVar.Gm k))).left) x := rfl
        _ = ((CategoryTheory.MonObj.one (X := A)).left ∘
              (SemiCartesianMonoidalCategory.toUnit X).left) x := by rw [hcomp]
        _ = (CategoryTheory.MonObj.one (X := A)).left
              ((SemiCartesianMonoidalCategory.toUnit X).left x) := rfl
        _ = (CategoryTheory.MonObj.one (X := A)).left (IsLocalRing.closedPoint k) := by
              congr 1
              exact Subsingleton.elim _ _
    rw [← hx, hval]
    exact hcU
  -- ## Step 4: the constant map with value `η[A]`.
  set g : MonoidalCategoryStruct.tensorObj X (Work.AbVar.Gm k) ⟶ A :=
    SemiCartesianMonoidalCategory.toUnit (MonoidalCategoryStruct.tensorObj X (Work.AbVar.Gm k)) ≫
      CategoryTheory.MonObj.one (X := A) with hg
  have hgl : g.left = (MonoidalCategoryStruct.tensorObj X (Work.AbVar.Gm k)).hom
      ≫ (CategoryTheory.MonObj.one (X := A)).left := by
    rw [hg, Over.comp_left, Over.toUnit_left]
  have hsec : Work.AbVar.sectionRight X (Work.AbVar.Gm k) x0 ≫ g =
      Work.AbVar.sectionRight X (Work.AbVar.Gm k) x0 ≫ f := by
    rw [hg, ← Category.assoc, SemiCartesianMonoidalCategory.comp_toUnit, ← h2]
  -- ## Step 5: the fibre-wise equality over every point of `V`.
  have hfib : ∀ y ∈ V,
      (((SemiCartesianMonoidalCategory.snd X (Work.AbVar.Gm k)).left).fiberι y) ≫ f.left =
        (((SemiCartesianMonoidalCategory.snd X (Work.AbVar.Gm k)).left).fiberι y) ≫ g.left := by
    intro y hy
    haveI hbproper : IsProper ((SemiCartesianMonoidalCategory.snd X (Work.AbVar.Gm k)).left) :=
      inferInstanceAs (IsProper (pullback.snd X.hom (Work.AbVar.Gm k).hom))
    haveI hbgeo : GeometricallyIntegral
        ((SemiCartesianMonoidalCategory.snd X (Work.AbVar.Gm k)).left) :=
      inferInstanceAs (GeometricallyIntegral (pullback.snd X.hom (Work.AbVar.Gm k).hom))
    haveI hucb : UniversallyClosed
        ((SemiCartesianMonoidalCategory.snd X (Work.AbVar.Gm k)).left) := inferInstance
    haveI hπuc : UniversallyClosed
        (Scheme.Hom.fiberToSpecResidueField
          ((SemiCartesianMonoidalCategory.snd X (Work.AbVar.Gm k)).left) y) :=
      show UniversallyClosed (pullback.snd
        ((SemiCartesianMonoidalCategory.snd X (Work.AbVar.Gm k)).left)
        ((Work.AbVar.Gm k).left.fromSpecResidueField y)) from inferInstance
    -- the section of the fibre structure map induced by `x₀`
    let s : Spec ((Work.AbVar.Gm k).left.residueField y) ⟶
        (SemiCartesianMonoidalCategory.snd X (Work.AbVar.Gm k)).left.fiber y :=
      pullback.lift ((Work.AbVar.Gm k).left.fromSpecResidueField y ≫
          (Work.AbVar.sectionRight X (Work.AbVar.Gm k) x0).left) (𝟙 _) (by
        simp only [Category.assoc, ← Over.comp_left, Work.AbVar.sectionRight_snd, Over.id_left,
          Category.comp_id, Category.id_comp])
    have hs : s ≫ ((SemiCartesianMonoidalCategory.snd X (Work.AbVar.Gm k)).left).fiberι y =
        (Work.AbVar.Gm k).left.fromSpecResidueField y ≫
          (Work.AbVar.sectionRight X (Work.AbVar.Gm k) x0).left :=
      pullback.lift_fst _ _ _
    have hsv : s ≫ Scheme.Hom.fiberToSpecResidueField
        ((SemiCartesianMonoidalCategory.snd X (Work.AbVar.Gm k)).left) y =
        𝟙 (Spec ((Work.AbVar.Gm k).left.residueField y)) := pullback.lift_snd _ _ _
    -- the images of the two restricted morphisms lie in the affine open `U`
    have hσUf : Set.range (Scheme.Hom.fiberι
        ((SemiCartesianMonoidalCategory.snd X (Work.AbVar.Gm k)).left) y ≫ f.left)
        ⊆ (U : Set A.left) := by
      rintro _ ⟨w, rfl⟩
      have hmem : (SemiCartesianMonoidalCategory.snd X (Work.AbVar.Gm k)).left
          (((SemiCartesianMonoidalCategory.snd X (Work.AbVar.Gm k)).left).fiberι y w) = y := by
        have hfac := congrArg (fun m => m w) (Scheme.Hom.fiber_fac
          ((SemiCartesianMonoidalCategory.snd X (Work.AbVar.Gm k)).left) y)
        simpa only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] using hfac
      exact (hViff y).mp hy _ hmem
    have hσUg : Set.range (Scheme.Hom.fiberι
        ((SemiCartesianMonoidalCategory.snd X (Work.AbVar.Gm k)).left) y ≫ g.left)
        ⊆ (U : Set A.left) := by
      rintro _ ⟨w, rfl⟩
      rw [Scheme.Hom.comp_apply, hgl, Scheme.Hom.comp_apply]
      have hw : (MonoidalCategoryStruct.tensorObj X (Work.AbVar.Gm k)).hom
          (((SemiCartesianMonoidalCategory.snd X (Work.AbVar.Gm k)).left).fiberι y w)
          = IsLocalRing.closedPoint k := Subsingleton.elim _ _
      rw [hw]
      exact hcU
    haveI hintfib : IsIntegral (((SemiCartesianMonoidalCategory.snd X
      (Work.AbVar.Gm k)).left).fiber y) := inferInstance
    have hconstf := const_of_affineOpen'
      (V := ((SemiCartesianMonoidalCategory.snd X (Work.AbVar.Gm k)).left).fiber y)
      (W := A.left)
      (π := (SemiCartesianMonoidalCategory.snd X (Work.AbVar.Gm k)).left.fiberToSpecResidueField y)
      (hint := hintfib) (huc := hπuc)
      (v := s) (hv := hsv) U hUaff
      ((((SemiCartesianMonoidalCategory.snd X (Work.AbVar.Gm k)).left).fiberι y) ≫ f.left)
      hσUf
    have hconstg := const_of_affineOpen'
      (V := ((SemiCartesianMonoidalCategory.snd X (Work.AbVar.Gm k)).left).fiber y)
      (W := A.left)
      (π := (SemiCartesianMonoidalCategory.snd X (Work.AbVar.Gm k)).left.fiberToSpecResidueField y)
      (hint := hintfib) (huc := hπuc)
      (v := s) (hv := hsv) U hUaff
      ((((SemiCartesianMonoidalCategory.snd X (Work.AbVar.Gm k)).left).fiberι y) ≫ g.left)
      hσUg
    have hvals : s ≫ ((SemiCartesianMonoidalCategory.snd X (Work.AbVar.Gm k)).left).fiberι y
          ≫ f.left
        = s ≫ ((SemiCartesianMonoidalCategory.snd X (Work.AbVar.Gm k)).left).fiberι y ≫ g.left := by
      calc s ≫ ((SemiCartesianMonoidalCategory.snd X (Work.AbVar.Gm k)).left).fiberι y ≫ f.left
          = (s ≫ ((SemiCartesianMonoidalCategory.snd X (Work.AbVar.Gm k)).left).fiberι y)
              ≫ f.left := (Category.assoc _ _ _).symm
        _ = ((Work.AbVar.Gm k).left.fromSpecResidueField y ≫
              (Work.AbVar.sectionRight X (Work.AbVar.Gm k) x0).left) ≫ f.left := by rw [hs]
        _ = (Work.AbVar.Gm k).left.fromSpecResidueField y
              ≫ ((Work.AbVar.sectionRight X (Work.AbVar.Gm k) x0).left ≫ f.left) :=
            Category.assoc _ _ _
        _ = (Work.AbVar.Gm k).left.fromSpecResidueField y
              ≫ ((Work.AbVar.sectionRight X (Work.AbVar.Gm k) x0 ≫ f).left) := by
            rw [← Over.comp_left]
        _ = (Work.AbVar.Gm k).left.fromSpecResidueField y
              ≫ ((Work.AbVar.sectionRight X (Work.AbVar.Gm k) x0 ≫ g).left) := by rw [hsec]
        _ = (Work.AbVar.Gm k).left.fromSpecResidueField y
              ≫ ((Work.AbVar.sectionRight X (Work.AbVar.Gm k) x0).left ≫ g.left) := by
            rw [Over.comp_left]
        _ = ((Work.AbVar.Gm k).left.fromSpecResidueField y ≫
              (Work.AbVar.sectionRight X (Work.AbVar.Gm k) x0).left) ≫ g.left :=
            (Category.assoc _ _ _).symm
        _ = (s ≫ ((SemiCartesianMonoidalCategory.snd X (Work.AbVar.Gm k)).left).fiberι y)
              ≫ g.left := by rw [hs]
        _ = s ≫ ((SemiCartesianMonoidalCategory.snd X (Work.AbVar.Gm k)).left).fiberι y
              ≫ g.left := Category.assoc _ _ _
    have hfib_eq : Scheme.Hom.fiberι ((SemiCartesianMonoidalCategory.snd X
        (Work.AbVar.Gm k)).left) y ≫ f.left
        = Scheme.Hom.fiberToSpecResidueField ((SemiCartesianMonoidalCategory.snd X
            (Work.AbVar.Gm k)).left) y ≫ (s ≫ Scheme.Hom.fiberι
              ((SemiCartesianMonoidalCategory.snd X (Work.AbVar.Gm k)).left) y ≫ f.left) :=
      hconstf
    have hfib_eqg : Scheme.Hom.fiberι ((SemiCartesianMonoidalCategory.snd X
        (Work.AbVar.Gm k)).left) y ≫ g.left
        = Scheme.Hom.fiberToSpecResidueField ((SemiCartesianMonoidalCategory.snd X
            (Work.AbVar.Gm k)).left) y ≫ (s ≫ Scheme.Hom.fiberι
              ((SemiCartesianMonoidalCategory.snd X (Work.AbVar.Gm k)).left) y ≫ g.left) :=
      hconstg
    calc Scheme.Hom.fiberι ((SemiCartesianMonoidalCategory.snd X (Work.AbVar.Gm k)).left) y
          ≫ f.left
        = Scheme.Hom.fiberToSpecResidueField ((SemiCartesianMonoidalCategory.snd X
            (Work.AbVar.Gm k)).left) y ≫ (s ≫ Scheme.Hom.fiberι
              ((SemiCartesianMonoidalCategory.snd X (Work.AbVar.Gm k)).left) y ≫ f.left) :=
          hfib_eq
      _ = Scheme.Hom.fiberToSpecResidueField ((SemiCartesianMonoidalCategory.snd X
            (Work.AbVar.Gm k)).left) y ≫ (s ≫ Scheme.Hom.fiberι
              ((SemiCartesianMonoidalCategory.snd X (Work.AbVar.Gm k)).left) y ≫ g.left) :=
          by rw [hvals]
      _ = Scheme.Hom.fiberι ((SemiCartesianMonoidalCategory.snd X (Work.AbVar.Gm k)).left) y
            ≫ g.left := hfib_eqg.symm
  -- ## Step 6: assemble on the dense set `snd ⁻¹' V`.
  have hdenseS : Dense ((SemiCartesianMonoidalCategory.snd X (Work.AbVar.Gm k)).left ⁻¹' V) := by
    haveI : GeometricallyIntegral (Work.AbVar.Gm k).hom :=
      Work.AbVar.TestObjects.gm_geometricallyIntegral
    haveI : IsIntegral (Work.AbVar.Gm k).left :=
      GeometricallyIntegral.isIntegral_of_subsingleton (Work.AbVar.Gm k).hom
    haveI : IsProper (SemiCartesianMonoidalCategory.snd X (Work.AbVar.Gm k)).left :=
      inferInstanceAs (IsProper (pullback.snd X.hom (Work.AbVar.Gm k).hom))
    haveI huo : UniversallyOpen (SemiCartesianMonoidalCategory.snd X (Work.AbVar.Gm k)).left :=
      inferInstanceAs (UniversallyOpen (pullback.snd X.hom (Work.AbVar.Gm k).hom))
    have hopen : IsOpenMap (SemiCartesianMonoidalCategory.snd X (Work.AbVar.Gm k)).left :=
      (SemiCartesianMonoidalCategory.snd X (Work.AbVar.Gm k)).left.isOpenMap
    exact (IsOpen.dense hVopen ⟨_, hbV⟩).preimage hopen
  have hmain : f.left = g.left := by
    refine ext_of_fromSpecResidueField_eq f.left g.left A.hom
      ((SemiCartesianMonoidalCategory.snd X (Work.AbVar.Gm k)).left ⁻¹' V) hdenseS ?_ ?_
    · intro ξ hξ
      rw [← Scheme.Hom.asFiberHom_fiberι
        ((SemiCartesianMonoidalCategory.snd X (Work.AbVar.Gm k)).left) ξ]
      rw [Category.assoc, Category.assoc]
      rw [hfib _ hξ]
    · rw [Over.w f, Over.w g]
  exact (Over.OverMorphism.ext hmain).trans hg

end Work.AbVar.P1
