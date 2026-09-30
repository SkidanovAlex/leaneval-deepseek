import Mathlib
import Submission.Work.SymQuot.QuotientMap
import Submission.Work.SymQuot.Chart.exists_chart_factor
import Submission.Work.SymQuot.Chart.quotient_desc

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

namespace Work.SymQuot.Chart

/-- **Universal property of the quotient `X/Γ`.**  A `Γ`-invariant morphism `f : X ⟶ Z` factors
uniquely through the quotient map `quotientMap : X ⟶ X/Γ`.

On each chart `U` of the invariant affine open cover, `f` restricts to a morphism
`U ⟶ Z` which factors uniquely through the chart map `chartMap U : U ⟶ chart U`
(`Work.SymQuot.Chart.exists_chart_factor`); the resulting morphisms `ψ U : chart U ⟶ Z` are
compatible over the chart diagram (transitivity of `chartRes` and `chartRes_chartMap`), so the
colimit universal property (`Work.SymQuot.Chart.quotient_desc`) produces `g`.  That a morphism
`g'` out of the quotient factors a given `f` through the quotient map iff it restricts to `ψ U` on
each chart (uniqueness of the chart factorisation) gives both existence and uniqueness. -/
theorem quotient_lift {Γ : Type*} [Group Γ] [Fintype Γ] {X : AlgebraicGeometry.Scheme}
    (D : Work.SymQuot.QuotientData Γ X) {Z : AlgebraicGeometry.Scheme} (f : X ⟶ Z)
    (hf : D.action.IsInvariantMorphism f) :
    ∃! g : D.Quotient ⟶ Z,
      CategoryTheory.CategoryStruct.comp D.quotientMap g = f := by
  classical
  -- The factorisation of `f` through each chart, and its uniqueness.
  have hψ : ∀ U : D.Chart, ∃! g : D.chart U ⟶ Z,
      D.action.chartMap U.1 U.2.2 ≫ g = U.1.ι ≫ f :=
    fun U => exists_chart_factor D.action U.2.1 U.2.2 f hf
  let ψ : ∀ U : D.Chart, D.chart U ⟶ Z := fun U => (hψ U).choose
  have ψ_spec : ∀ U : D.Chart, D.action.chartMap U.1 U.2.2 ≫ ψ U = U.1.ι ≫ f :=
    fun U => (hψ U).choose_spec.1
  have ψ_unique : ∀ (U : D.Chart) (g : D.chart U ⟶ Z),
      D.action.chartMap U.1 U.2.2 ≫ g = U.1.ι ≫ f → g = ψ U :=
    fun U g hg => (hψ U).choose_spec.2 g hg
  -- The family `ψ` is compatible over the chart diagram.
  have hcompat : ∀ {U V : D.Chart} (h : U ⟶ V),
      D.chartFunctor.map h ≫ ψ V = ψ U := by
    intro U V h
    refine ψ_unique U _ ?_
    change D.action.chartMap U.1 U.2.2 ≫
      (D.action.chartRes U.1 V.1 (leOfHom h) V.2.2 U.2.2 ≫ ψ V) = U.1.ι ≫ f
    rw [← Category.assoc,
      ← Work.SymQuot.Chart.chartRes_chartMap D.action (leOfHom h) V.2.2 U.2.2,
      Category.assoc, ψ_spec V, ← Category.assoc, Scheme.homOfLE_ι]
  -- The descent of `ψ` to the quotient.
  obtain ⟨g, hg_spec, hg_uniq⟩ := Work.SymQuot.Chart.quotient_desc D ψ hcompat
  -- The open cover of `X` by the invariant affine opens.
  let 𝒰 : X.OpenCover := {
    I₀ := D.Chart
    X := fun U => U.1.toScheme
    f := fun U => U.1.ι
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      refine ⟨fun x => ?_, fun i => inferInstance⟩
      obtain ⟨U, hUa, hUi, hxU⟩ := D.covers x
      exact ⟨⟨U, hUa, hUi⟩, ⟨x, hxU⟩, rfl⟩ }
  -- Factoring `f` through `quotientMap` is the same as restricting to `ψ` on every chart.
  have key : ∀ (g' : D.Quotient ⟶ Z),
      (D.quotientMap ≫ g' = f) ↔ ∀ U : D.Chart, D.chartι U ≫ g' = ψ U := by
    intro g'
    constructor
    · intro hg' U
      refine ψ_unique U _ ?_
      rw [← Category.assoc, ← Work.SymQuot.QuotientData.quotientMap_chartι D U,
        Category.assoc, hg']
    · intro hg'
      refine 𝒰.hom_ext _ _ (fun U => ?_)
      rw [← Category.assoc, Work.SymQuot.QuotientData.quotientMap_chartι D U,
        Category.assoc, hg' U, ψ_spec U]
  exact ⟨g, (key g).mpr hg_spec, fun g' hg' => hg_uniq g' ((key g').mp hg')⟩

end Work.SymQuot.Chart
