import Mathlib
import Submission.Work.SymQuot.Chart
import Submission.Work.SymQuot.Chart.chartRes_chartMap
import Submission.Work.SymQuot.Invariants.surjective_specMap_fixedPoints
import Submission.Work.SymQuot.Chart.chartRes_isOpenImmersion_alt
import Submission.Work.SymQuot.Chart.chartMap_fiber_orbit
import Submission.Work.SymQuot.Chart.chartMap_image_inf
import Submission.Work.SymQuot.Chart.isAffineOpen_inf_of_le
import Submission.Work.SymQuot.Chart.chartRes_isEmbedding

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.SymQuot.Chart

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

variable {G : Type*} [Group G] [Finite G] {X : AlgebraicGeometry.Scheme}

/-- The image of a chart restriction is the image of the corresponding open under the
chart map of the ambient open. -/
lemma range_chartRes (A : Work.SymQuot.GAction G X) {V U : X.Opens} (h : V ≤ U)
    (hUi : A.IsInvariantOpen U) (hVa : IsAffineOpen V) (hVi : A.IsInvariantOpen V) :
    Set.range ⇑(A.chartRes V U h hUi hVi) =
      ⇑(A.chartMap U hUi) '' Set.range ⇑(X.homOfLE (U := V) (V := U) h) := by
  have hsurj := chartMap_surjective A hVa hVi
  have key : ∀ x : ↑V, A.chartRes V U h hUi hVi (A.chartMap V hVi x)
      = A.chartMap U hUi (X.homOfLE (U := V) (V := U) h x) := by
    intro x
    have hh := congrArg (fun (f : ↑V ⟶ A.chart U hUi) => f x)
      (Work.SymQuot.Chart.chartRes_chartMap (A := A) h hUi hVi)
    simpa [Scheme.Hom.comp_apply] using hh.symm
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨z, rfl⟩
    obtain ⟨x, rfl⟩ := hsurj z
    exact ⟨_, ⟨x, rfl⟩, (key x).symm⟩
  · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨A.chartMap V hVi x, key x⟩

theorem chartRes_pullback_iso {G : Type*} [Group G] [Finite G] {X : AlgebraicGeometry.Scheme}
    (A : Work.SymQuot.GAction G X) {W₁ W₂ U : X.Opens} (h₁ : W₁ ≤ U) (h₂ : W₂ ≤ U)
    (hU : AlgebraicGeometry.IsAffineOpen U) (hW₁a : AlgebraicGeometry.IsAffineOpen W₁)
    (hW₂a : AlgebraicGeometry.IsAffineOpen W₂) (hUi : A.IsInvariantOpen U)
    (hW₁i : A.IsInvariantOpen W₁) (hW₂i : A.IsInvariantOpen W₂) :
    Nonempty (CategoryTheory.Limits.pullback
        (Work.SymQuot.GAction.chartRes A W₁ U h₁ hUi hW₁i)
        (Work.SymQuot.GAction.chartRes A W₂ U h₂ hUi hW₂i) ≅
      Work.SymQuot.GAction.chart A (W₁ ⊓ W₂) (hW₁i.inf hW₂i)) := by
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
  refine ⟨IsOpenImmersion.isoOfRangeEq
    (pullback.fst (A.chartRes W₁ U h₁ hUi hW₁i) (A.chartRes W₂ U h₂ hUi hW₂i) ≫
      A.chartRes W₁ U h₁ hUi hW₁i)
    (A.chartRes (W₁ ⊓ W₂) U hVU hUi hVi) ?_⟩
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

end Work.SymQuot.Chart
