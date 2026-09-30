/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The chart diagram of a finite group quotient is locally directed (area SY)

For a scheme `X` with an action of a finite group `G` and an invariant affine open cover, the
diagram

`D.Chart ⥤ Scheme,   U ↦ chart U = Spec Γ(X,U)^G,   (U ≤ V) ↦ chartRes`

is locally directed: the images of `chart U` and `chart V` inside `chart W` (for `U, V ≤ W`)
intersect in the image of `chart (U ⊓ V)`, and moreover the intersection is *saturated*, so a
point of the intersection is the image of a point of `chart (U ⊓ V)`.

This is the second of the two inputs to Mathlib's `Scheme.IsLocallyDirected` construction of the
quotient `X/G` (the first being that the transition maps are open immersions,
`chartRes_isOpenImmersion_alt`).
-/
import Mathlib
import Submission.Work.SymQuot.QuotientData
import Submission.Work.SymQuot.Chart.chartMap_image_inf
import Submission.Work.SymQuot.Chart.chartMap_fiber_orbit
import Submission.Work.SymQuot.Chart.chartRes_isOpen_range
import Submission.Work.SymQuot.Chart.chartRes_isEmbedding

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

namespace Work.SymQuot.Chart

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

/-- **The local model of local directedness.**  Let `G` be a finite group acting on a scheme `X`
and let `W₁, W₂ ⊆ U` be `G`-invariant affine opens.  If two points `xi ∈ chart W₁` and
`xj ∈ chart W₂` have the same image in `chart U`, then they are the images of a common point of
`chart (W₁ ⊓ W₂)`.

The proof uses that the range of `chartRes W U` is `chartMap U '' W`
(`range_chartRes_eq_image_homOfLE`) and that the images of `W₁` and `W₂` in `chart U` intersect in
the image of `W₁ ⊓ W₂` (`chartMap_image_inf`); injectivity of `chartRes W U`
(`chartRes_isEmbedding`) then identifies the resulting point of `chart (W₁ ⊓ W₂)` with `xi` and
`xj`. -/
theorem exists_chart_point_of_chartRes_eq {G : Type u} [Group G] [Finite G]
    {X : AlgebraicGeometry.Scheme.{u}} (A : Work.SymQuot.GAction G X)
    {W₁ W₂ U : X.Opens} (h₁ : W₁ ≤ U) (h₂ : W₂ ≤ U)
    (hU : IsAffineOpen U) (hUi : A.IsInvariantOpen U)
    (hW₁a : IsAffineOpen W₁) (hW₂a : IsAffineOpen W₂)
    (hW₁ : A.IsInvariantOpen W₁) (hW₂ : A.IsInvariantOpen W₂)
    (xi : A.chart W₁ hW₁) (xj : A.chart W₂ hW₂)
    (h : A.chartRes W₁ U h₁ hUi hW₁ xi = A.chartRes W₂ U h₂ hUi hW₂ xj) :
    ∃ x : A.chart (W₁ ⊓ W₂) (hW₁.inf hW₂),
      A.chartRes (W₁ ⊓ W₂) W₁ inf_le_left hW₁ (hW₁.inf hW₂) x = xi ∧
      A.chartRes (W₁ ⊓ W₂) W₂ inf_le_right hW₂ (hW₁.inf hW₂) x = xj := by
  let z : A.chart U hUi := A.chartRes W₁ U h₁ hUi hW₁ xi
  have hz₁_in : z ∈ Set.range ⇑(A.chartRes W₁ U h₁ hUi hW₁) := ⟨xi, rfl⟩
  have hz₂_in : z ∈ Set.range ⇑(A.chartRes W₂ U h₂ hUi hW₂) := ⟨xj, h.symm⟩
  rw [range_chartRes_eq_image_homOfLE A h₁ hUi hW₁a hW₁] at hz₁_in
  rw [range_chartRes_eq_image_homOfLE A h₂ hUi hW₂a hW₂] at hz₂_in
  have hz_in : z ∈ ⇑(A.chartMap U hUi) '' Set.range ⇑(X.homOfLE h₁) ∩
      ⇑(A.chartMap U hUi) '' Set.range ⇑(X.homOfLE h₂) := ⟨hz₁_in, hz₂_in⟩
  rw [chartMap_image_inf A h₁ h₂ hU hUi hW₁ hW₂] at hz_in
  obtain ⟨c, hc, hcz⟩ := hz_in
  obtain ⟨c', hc'⟩ := hc
  refine ⟨A.chartMap (W₁ ⊓ W₂) (hW₁.inf hW₂) c', ?_, ?_⟩
  · have hinj : Function.Injective ⇑(A.chartRes W₁ U h₁ hUi hW₁) :=
      (chartRes_isEmbedding A h₁ hU hW₁a hUi hW₁).injective
    refine hinj ?_
    have hnat := chartRes_chartMap (A := A) (inf_le_left.trans h₁) hUi (hW₁.inf hW₂)
    have hnat_c' := congrArg (fun f => f c') hnat
    simp only [Scheme.Hom.comp_apply] at hnat_c'
    rw [hc', hcz] at hnat_c'
    have hcomp := Work.SymQuot.GAction.chartRes_comp A (W₁ ⊓ W₂) W₁ U inf_le_left h₁
      hUi hW₁ (hW₁.inf hW₂)
    rw [← Scheme.Hom.comp_apply, hcomp]
    exact hnat_c'.symm
  · have hinj : Function.Injective ⇑(A.chartRes W₂ U h₂ hUi hW₂) :=
      (chartRes_isEmbedding A h₂ hU hW₂a hUi hW₂).injective
    refine hinj ?_
    rw [← h]
    have hnat := chartRes_chartMap (A := A) (inf_le_right.trans h₂) hUi (hW₁.inf hW₂)
    have hnat_c' := congrArg (fun f => f c') hnat
    simp only [Scheme.Hom.comp_apply] at hnat_c'
    rw [hc', hcz] at hnat_c'
    have hcomp := Work.SymQuot.GAction.chartRes_comp A (W₁ ⊓ W₂) W₂ U inf_le_right h₂
      hUi hW₂ (hW₁.inf hW₂)
    rw [← Scheme.Hom.comp_apply, hcomp]
    exact hnat_c'.symm

theorem chartFunctor_isLocallyDirected {Γ : Type*} [Group Γ] [Fintype Γ]
    {X : AlgebraicGeometry.Scheme} (D : Work.SymQuot.QuotientData Γ X) :
    CategoryTheory.Functor.IsLocallyDirected
      (CategoryTheory.Functor.comp (Work.SymQuot.QuotientData.chartFunctor D)
        AlgebraicGeometry.Scheme.forget) := by
  refine ⟨fun {i j k} fi fj xi xj hxij => ?_⟩
  have h : D.action.chartRes i.1 k.1 (leOfHom fi) k.2.2 i.2.2 xi =
      D.action.chartRes j.1 k.1 (leOfHom fj) k.2.2 j.2.2 xj := hxij
  obtain ⟨x, hx₁, hx₂⟩ := exists_chart_point_of_chartRes_eq D.action (leOfHom fi) (leOfHom fj)
    k.2.1 k.2.2 i.2.1 j.2.1 i.2.2 j.2.2 xi xj h
  refine ⟨D.inf i j, homOfLE (inf_le_left : (D.inf i j).1 ≤ i.1),
    homOfLE (inf_le_right : (D.inf i j).1 ≤ j.1), x, ?_, ?_⟩
  · exact hx₁
  · exact hx₂

/-! ## The locally directed instance

Mathlib's `Scheme.IsLocallyDirected` machinery consumes the local directedness as a *typeclass
instance* (`Scheme.IsLocallyDirected.openCover`, `HasColimit`, `colimit.ι`, ...), so we register
`chartFunctor_isLocallyDirected` as an instance as well.  The index `D` is found by unification
from the goal, so this instance is available wherever `D.chartFunctor` is. -/
instance chartFunctor_isLocallyDirected_inst {Γ : Type*} [Group Γ] [Fintype Γ]
    {X : AlgebraicGeometry.Scheme} (D : Work.SymQuot.QuotientData Γ X) :
    CategoryTheory.Functor.IsLocallyDirected
      (CategoryTheory.Functor.comp (Work.SymQuot.QuotientData.chartFunctor D)
        AlgebraicGeometry.Scheme.forget) :=
  chartFunctor_isLocallyDirected D

end Work.SymQuot.Chart
