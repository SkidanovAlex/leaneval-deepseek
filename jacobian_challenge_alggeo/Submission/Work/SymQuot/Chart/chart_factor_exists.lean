/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Existence of the chart factorisation (area SY)

If `U ⊆ X` is a `Γ`-invariant affine open subscheme with chart `chart U = Spec Γ(X,U)^Γ`, and
`f : X ⟶ Z` is a `Γ`-invariant morphism, then the restriction `U.ι ≫ f : U ⟶ Z` factors through
the chart map `chartMap U : U ⟶ chart U`.

The factorisation is built by gluing: for every point of `U` there is a `Γ`-invariant section `s`
over `U` whose basic open lies over an affine open `V ⊆ Z`
(`Work.SymQuot.Chart.exists_piece_index`), and on such a basic open the restriction of `f`
factors through the chart map by the affine target case
(`Work.SymQuot.Chart.exists_chart_factor_piece`).  The charts of these basic opens cover
`chart U`; the compatibility of the pieces is `Work.SymQuot.Chart.chart_piece_compat` (which
uses the uniqueness `Work.SymQuot.Chart.chart_factor_unique`), and the triangle identity is
checked on the cover of `U` by the basic opens.
-/
import Mathlib
import Submission.Work.SymQuot.Quotient
import Submission.Work.SymQuot.Chart.chart_factor_unique
import Submission.Work.SymQuot.Chart.chart_factor_aux
import Submission.Work.SymQuot.Chart.exists_basicOpen_invariant_sub
import Submission.Work.SymQuot.Chart.chartRes_aux
import Submission.Work.SymQuot.Chart.isAffineOpen_inf_of_le
import Submission.Work.SymQuot.Chart.chartRes_isOpen_range
import Submission.Work.SymQuot.Chart.chartRes_pullback_iso
import Submission.Work.SymQuot.Chart.chartRes_isOpenImmersion_alt
import Submission.Work.SymQuot.Chart.chart_piece_compat
import Submission.Work.SymQuot.Chart.exists_piece_index

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


open CategoryTheory Limits AlgebraicGeometry
open scoped Classical
set_option autoImplicit false
universe u

namespace Work.SymQuot.Chart

theorem pullback_chartRes_iso_aux {Γ : Type u} [Group Γ] [Fintype Γ]
    {X : AlgebraicGeometry.Scheme.{u}} (A : Work.SymQuot.GAction Γ X)
    {W₁ W₂ U : X.Opens} (h₁ : W₁ ≤ U) (h₂ : W₂ ≤ U)
    (hU : AlgebraicGeometry.IsAffineOpen U) (hW₁a : AlgebraicGeometry.IsAffineOpen W₁)
    (hW₂a : AlgebraicGeometry.IsAffineOpen W₂) (hUi : A.IsInvariantOpen U)
    (hW₁i : A.IsInvariantOpen W₁) (hW₂i : A.IsInvariantOpen W₂) :
    ∃ e : CategoryTheory.Limits.pullback
          (A.chartRes W₁ U h₁ hUi hW₁i) (A.chartRes W₂ U h₂ hUi hW₂i) ≅
        A.chart (W₁ ⊓ W₂) (hW₁i.inf hW₂i),
      CategoryTheory.CategoryStruct.comp e.hom
          (A.chartRes (W₁ ⊓ W₂) W₁ (inf_le_left) hW₁i (hW₁i.inf hW₂i)) =
        CategoryTheory.Limits.pullback.fst _ _ ∧
      CategoryTheory.CategoryStruct.comp e.hom
          (A.chartRes (W₁ ⊓ W₂) W₂ (inf_le_right) hW₂i (hW₁i.inf hW₂i)) =
        CategoryTheory.Limits.pullback.snd _ _ := by
  have hVU : W₁ ⊓ W₂ ≤ U := inf_le_left.trans h₁
  have hVa : IsAffineOpen (W₁ ⊓ W₂) := isAffineOpen_inf_of_le h₁ h₂ hU hW₁a hW₂a
  have hVi : A.IsInvariantOpen (W₁ ⊓ W₂) := hW₁i.inf hW₂i
  haveI i₁ : IsOpenImmersion (A.chartRes W₁ U h₁ hUi hW₁i) :=
    chartRes_isOpenImmersion_alt A h₁ hU hW₁a hUi hW₁i
  haveI i₂ : IsOpenImmersion (A.chartRes W₂ U h₂ hUi hW₂i) :=
    chartRes_isOpenImmersion_alt A h₂ hU hW₂a hUi hW₂i
  haveI i₃ : IsOpenImmersion (A.chartRes (W₁ ⊓ W₂) U hVU hUi hVi) :=
    chartRes_isOpenImmersion_alt A hVU hU hVa hUi hVi
  haveI i₄ : IsOpenImmersion (pullback.fst (A.chartRes W₁ U h₁ hUi hW₁i)
      (A.chartRes W₂ U h₂ hUi hW₂i)) :=
    MorphismProperty.of_isPullback
      (IsPullback.of_hasPullback (A.chartRes W₁ U h₁ hUi hW₁i)
        (A.chartRes W₂ U h₂ hUi hW₂i)).flip i₂
  haveI i₅ : IsOpenImmersion (pullback.fst (A.chartRes W₁ U h₁ hUi hW₁i)
      (A.chartRes W₂ U h₂ hUi hW₂i) ≫ A.chartRes W₁ U h₁ hUi hW₁i) :=
    IsOpenImmersion.comp _ _
  have hrange : Set.range ⇑(pullback.fst (A.chartRes W₁ U h₁ hUi hW₁i)
        (A.chartRes W₂ U h₂ hUi hW₂i) ≫ A.chartRes W₁ U h₁ hUi hW₁i)
      = Set.range ⇑(A.chartRes (W₁ ⊓ W₂) U hVU hUi hVi) := by
    have key₁ : Set.range ⇑(A.chartRes W₁ U h₁ hUi hW₁i) =
        ⇑(A.chartMap U hUi) '' Set.range ⇑(X.homOfLE (U := W₁) (V := U) h₁) :=
      range_chartRes A h₁ hUi hW₁a hW₁i
    have key₂ : Set.range ⇑(A.chartRes W₂ U h₂ hUi hW₂i) =
        ⇑(A.chartMap U hUi) '' Set.range ⇑(X.homOfLE (U := W₂) (V := U) h₂) :=
      range_chartRes A h₂ hUi hW₂a hW₂i
    have key₃ : Set.range ⇑(A.chartRes (W₁ ⊓ W₂) U hVU hUi hVi) =
        ⇑(A.chartMap U hUi) '' Set.range ⇑(X.homOfLE (U := W₁ ⊓ W₂) (V := U) hVU) :=
      range_chartRes A hVU hUi hVa hVi
    have key₄ : ⇑(A.chartMap U hUi) '' Set.range ⇑(X.homOfLE (U := W₁) (V := U) h₁) ∩
          ⇑(A.chartMap U hUi) '' Set.range ⇑(X.homOfLE (U := W₂) (V := U) h₂)
        = ⇑(A.chartMap U hUi) '' Set.range ⇑(X.homOfLE (U := W₁ ⊓ W₂) (V := U) hVU) :=
      chartMap_image_inf A h₁ h₂ hU hUi hW₁i hW₂i
    have hcomp : Set.range ⇑(pullback.fst (A.chartRes W₁ U h₁ hUi hW₁i)
          (A.chartRes W₂ U h₂ hUi hW₂i) ≫ A.chartRes W₁ U h₁ hUi hW₁i)
        = ↑(Scheme.Hom.opensRange (A.chartRes W₁ U h₁ hUi hW₁i) ⊓
            Scheme.Hom.opensRange (A.chartRes W₂ U h₂ hUi hW₂i)) := by
      change Set.range (⇑(A.chartRes W₁ U h₁ hUi hW₁i) ∘
        ⇑(pullback.fst (A.chartRes W₁ U h₁ hUi hW₁i) (A.chartRes W₂ U h₂ hUi hW₂i))) = _
      rw [Set.range_comp, IsOpenImmersion.range_pullbackFst (A.chartRes W₂ U h₂ hUi hW₂i)
        (A.chartRes W₁ U h₁ hUi hW₁i)]
      rw [← Scheme.Hom.coe_image, Scheme.Hom.image_preimage_eq_opensRange_inf]
    rw [hcomp, key₃]
    rw [show (↑(Scheme.Hom.opensRange (A.chartRes W₁ U h₁ hUi hW₁i) ⊓
        Scheme.Hom.opensRange (A.chartRes W₂ U h₂ hUi hW₂i)) : Set (A.chart U hUi))
        = ⇑(A.chartMap U hUi) '' Set.range ⇑(X.homOfLE (U := W₁) (V := U) h₁) ∩
          ⇑(A.chartMap U hUi) '' Set.range ⇑(X.homOfLE (U := W₂) (V := U) h₂) from by
      simp only [TopologicalSpace.Opens.coe_inf, Scheme.Hom.coe_opensRange, key₁, key₂]]
    rw [key₄]
  refine ⟨IsOpenImmersion.isoOfRangeEq _ _ hrange, ?_, ?_⟩
  · have hfac := IsOpenImmersion.isoOfRangeEq_hom_fac
        (pullback.fst (A.chartRes W₁ U h₁ hUi hW₁i) (A.chartRes W₂ U h₂ hUi hW₂i) ≫
          A.chartRes W₁ U h₁ hUi hW₁i)
        (A.chartRes (W₁ ⊓ W₂) U hVU hUi hVi) hrange
    have hC : A.chartRes (W₁ ⊓ W₂) W₁ (inf_le_left) hW₁i (hW₁i.inf hW₂i) ≫
        A.chartRes W₁ U h₁ hUi hW₁i = A.chartRes (W₁ ⊓ W₂) U hVU hUi hVi :=
      Work.SymQuot.GAction.chartRes_comp A (W₁ ⊓ W₂) W₁ U (inf_le_left : W₁ ⊓ W₂ ≤ W₁) h₁
        hUi hW₁i (hW₁i.inf hW₂i)
    refine (cancel_mono (A.chartRes W₁ U h₁ hUi hW₁i)).mp ?_
    rw [Category.assoc, hC, hfac]
  · have hfac := IsOpenImmersion.isoOfRangeEq_hom_fac
        (pullback.fst (A.chartRes W₁ U h₁ hUi hW₁i) (A.chartRes W₂ U h₂ hUi hW₂i) ≫
          A.chartRes W₁ U h₁ hUi hW₁i)
        (A.chartRes (W₁ ⊓ W₂) U hVU hUi hVi) hrange
    have hC : A.chartRes (W₁ ⊓ W₂) W₂ (inf_le_right) hW₂i (hW₁i.inf hW₂i) ≫
        A.chartRes W₂ U h₂ hUi hW₂i = A.chartRes (W₁ ⊓ W₂) U hVU hUi hVi := by
      rw [Work.SymQuot.GAction.chartRes_comp A (W₁ ⊓ W₂) W₂ U (inf_le_right : W₁ ⊓ W₂ ≤ W₂) h₂
        hUi hW₂i (hW₁i.inf hW₂i)]
    refine (cancel_mono (A.chartRes W₂ U h₂ hUi hW₂i)).mp ?_
    rw [Category.assoc, hC, hfac, ← pullback.condition]

lemma isInvariantOpen_basicOpen_of_mem_invariants {Γ : Type u} [Group Γ] [Fintype Γ]
    {X : AlgebraicGeometry.Scheme.{u}} (A : Work.SymQuot.GAction Γ X) {U : X.Opens}
    (hUi : A.IsInvariantOpen U) (s : ↥(A.invariants U hUi)) :
    A.IsInvariantOpen (X.basicOpen (s : Γ(X,U))) := by
  refine isInvariantOpen_basicOpen A hUi (s : Γ(X,U)) (fun g => ?_)
  have h := (Work.SymQuot.GAction.mem_invariants_iff A hUi (s : Γ(X,U))).mp s.2 g⁻¹
  simpa using h

theorem chart_factor_exists {Γ : Type u} [Group Γ] [Fintype Γ] {X : AlgebraicGeometry.Scheme.{u}}
    (A : Work.SymQuot.GAction Γ X) {U : X.Opens} (hUa : IsAffineOpen U) (hUi : A.IsInvariantOpen U)
    {Z : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Z) (hf : A.IsInvariantMorphism f) :
    ∃ g : A.chart U hUi ⟶ Z, A.chartMap U hUi ≫ g = U.ι ≫ f := by
  classical
  let Idx := { p : Z.Opens × ↥(A.invariants U hUi) //
      IsAffineOpen p.1 ∧ X.basicOpen (p.2 : Γ(X,U)) ≤ U ⊓ f ⁻¹ᵁ p.1 }
  let W : Idx → X.Opens := fun i => X.basicOpen (i.1.2 : Γ(X,U))
  have hWa : ∀ i : Idx, IsAffineOpen (W i) := fun i => hUa.basicOpen (i.1.2 : Γ(X,U))
  have hWi : ∀ i : Idx, A.IsInvariantOpen (W i) :=
    fun i => isInvariantOpen_basicOpen_of_mem_invariants A hUi i.1.2
  have hWU : ∀ i : Idx, W i ≤ U := fun i => (i.2.2).trans inf_le_left
  have hWV : ∀ i : Idx, W i ≤ f ⁻¹ᵁ i.1.1 := fun i => (i.2.2).trans inf_le_right
  have piece : ∀ i : Idx, ∃ p : A.chart (W i) (hWi i) ⟶ i.1.1,
      A.chartMap (W i) (hWi i) ≫ p ≫ (i.1.1).ι = (W i).ι ≫ f :=
    fun i => exists_chart_factor_piece A (hWa i) (hWi i) (i.2.1) f hf (hWV i)
  let pc : ∀ i : Idx, A.chart (W i) (hWi i) ⟶ i.1.1 := fun i => (piece i).choose
  have pc_spec : ∀ i : Idx,
      A.chartMap (W i) (hWi i) ≫ pc i ≫ (i.1.1).ι = (W i).ι ≫ f :=
    fun i => (piece i).choose_spec
  let gPiece : ∀ i : Idx, A.chart (W i) (hWi i) ⟶ Z := fun i => pc i ≫ (i.1.1).ι
  have gPiece_spec : ∀ i : Idx, A.chartMap (W i) (hWi i) ≫ gPiece i = (W i).ι ≫ f :=
    fun i => pc_spec i
  have idx_exists : ∀ y : U.toScheme, ∃ i : Idx, U.ι y ∈ W i := by
    intro y
    obtain ⟨V, hVa, s, hle, hmem⟩ := exists_piece_index A hUa hUi f hf y
    exact ⟨⟨(V, s), hVa, hle⟩, hmem⟩
  let fRes : ∀ i : Idx, A.chart (W i) (hWi i) ⟶ A.chart U hUi :=
    fun i => A.chartRes (W i) U (hWU i) hUi (hWi i)
  have compat : ∀ i j : Idx,
      pullback.fst (fRes i) (fRes j) ≫ gPiece i = pullback.snd (fRes i) (fRes j) ≫ gPiece j := by
    intro i j
    obtain ⟨e, he₁, he₂⟩ :=
      pullback_chartRes_iso_aux A (hWU i) (hWU j) hUa (hWa i) (hWa j) hUi (hWi i) (hWi j)
    rw [← he₁, ← he₂, Category.assoc, Category.assoc,
      chart_piece_compat A (hWU i) (hWU j) hUa (hWa i) (hWa j) (hWi i) (hWi j)
        (gPiece_spec i) (gPiece_spec j)]
  let 𝒰 : (A.chart U hUi).OpenCover :=
    { I₀ := Idx
      X := fun i => A.chart (W i) (hWi i)
      f := fRes
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        refine ⟨fun x => ?_, fun i => ?_⟩
        · obtain ⟨y, hy⟩ := chartMap_surjective_of_affine A hUa hUi x
          obtain ⟨i, hi⟩ := idx_exists y
          refine ⟨i, ?_⟩
          rw [Set.mem_range]
          obtain ⟨y', hy'⟩ := (mem_range_homOfLE (hWU i)).mpr hi
          refine ⟨A.chartMap (W i) (hWi i) y', ?_⟩
          have hcomp := congrArg (fun (m : (W i).toScheme ⟶ A.chart U hUi) => ⇑m y')
            (chartRes_chartMap A (hWU i) hUi (hWi i))
          simp only [Scheme.Hom.comp_apply] at hcomp
          rw [← hcomp, hy', hy]
        · exact chartRes_isOpenImmersion_alt A (hWU i) hUa (hWa i) hUi (hWi i) }
  let g : A.chart U hUi ⟶ Z := 𝒰.glueMorphisms gPiece compat
  have hg : ∀ i : Idx, fRes i ≫ g = gPiece i := fun i => 𝒰.ι_glueMorphisms gPiece compat i
  refine ⟨g, ?_⟩
  let 𝒱 : U.toScheme.OpenCover :=
    { I₀ := Idx
      X := fun i => (W i).toScheme
      f := fun i => X.homOfLE (hWU i)
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨fun y => by
          obtain ⟨i, hi⟩ := idx_exists y
          exact ⟨i, (mem_range_homOfLE (hWU i)).mpr hi⟩, fun i => inferInstance⟩ }
  refine 𝒱.hom_ext _ _ (fun i => ?_)
  have h1 : X.homOfLE (hWU i) ≫ A.chartMap U hUi = A.chartMap (W i) (hWi i) ≫ fRes i :=
    chartRes_chartMap A (hWU i) hUi (hWi i)
  have h2 : X.homOfLE (hWU i) ≫ U.ι = (W i).ι := Scheme.homOfLE_ι X (hWU i)
  rw [← Category.assoc, ← Category.assoc, h1, h2, Category.assoc, hg i, gPiece_spec i]

end Work.SymQuot.Chart
