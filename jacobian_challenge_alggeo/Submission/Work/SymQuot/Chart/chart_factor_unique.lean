/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Uniqueness of the chart factorisation (area SY)

If `U ⊆ X` is a `Γ`-invariant affine open subscheme with chart `chart U = Spec Γ(X,U)^Γ`, and
`g, g' : chart U ⟶ Z` become equal after precomposition with the chart map `chartMap U : U ⟶ chart U`,
then `g = g'`.  This is the uniqueness half of `Work.SymQuot.Chart.exists_chart_factor`; it uses
that `chartMap U` is surjective on points and that its maps on sections are injective
(`Work.SymQuot.Chart.chart_app_injective`).
-/
import Mathlib
import Submission.Work.SymQuot.Quotient
import Submission.Work.SymQuot.Chart.chart_app_injective

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot.Chart

/-- `Scheme.Hom.appLE` is insensitive to the proof of the inequality; consequently the two
`appLE`s of two *equal* morphisms into a fixed open agree. -/
lemma appLE_congr_hom {X Y : AlgebraicGeometry.Scheme} {f f' : X ⟶ Y} (h : f = f')
    (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ f' ⁻¹ᵁ U) :
    f.appLE U V e = f'.appLE U V e' := by
  subst h
  simp only [Scheme.Hom.appLE]

/-- **Uniqueness of the factorisation through the chart map.**  A morphism out of the chart
`chart U = Spec Γ(X,U)^Γ` of an invariant affine open is determined by its composite with the
chart map `chartMap U : U ⟶ chart U`. -/
theorem chart_factor_unique {Γ : Type u} [Group Γ] [Fintype Γ] {X : AlgebraicGeometry.Scheme.{u}}
    (A : Work.SymQuot.GAction Γ X) {U : X.Opens} (hUa : IsAffineOpen U) (hUi : A.IsInvariantOpen U)
    {Z : AlgebraicGeometry.Scheme.{u}} {g g' : A.chart U hUi ⟶ Z}
    (hpp : A.chartMap U hUi ≫ g = A.chartMap U hUi ≫ g') : g = g' := by
  -- The two morphisms agree on the points of the chart, the chart map being surjective.
  have hbase_pt : ⇑g = ⇑g' := by
    funext x
    obtain ⟨y, rfl⟩ := Work.SymQuot.Chart.chartMap_surjective_of_affine A hUa hUi x
    exact congrFun (congrArg (fun m : U.toScheme ⟶ Z => ⇑m) hpp) y
  have h_base : g.base = g'.base := TopCat.ext (fun x => congr_fun hbase_pt x)
  -- It remains to compare the maps on the structure sheaves.
  refine Scheme.Hom.ext h_base (fun W => ?_)
  have hh : (TopologicalSpace.Opens.map g'.base).obj W = (TopologicalSpace.Opens.map g.base).obj W := by
    rw [h_base.symm]
  change g.app W ≫ (A.chart U hUi).presheaf.map (eqToHom hh).op = g'.app W
  -- Rewrite both sides as `appLE`'s into the *same* open `g' ⁻¹ᵁ W`.
  have hV : (TopologicalSpace.Opens.map g'.base).obj W ≤ g ⁻¹ᵁ W := le_of_eq hh
  have hL : g.app W ≫ (A.chart U hUi).presheaf.map (eqToHom hh).op
      = g.appLE W (g' ⁻¹ᵁ W) hV := rfl
  rw [hL, ← Scheme.Hom.appLE_eq_app g' (U := W)]
  -- Composing with the (injective) sections map of the chart map over `g' ⁻¹ᵁ W` suffices.
  have hpinj : Function.Injective ⇑((A.chartMap U hUi).app (g' ⁻¹ᵁ W)) :=
    Work.SymQuot.Chart.chart_app_injective A hUa hUi (g' ⁻¹ᵁ W)
  have key : g.appLE W (g' ⁻¹ᵁ W) hV ≫ (A.chartMap U hUi).app (g' ⁻¹ᵁ W)
      = g'.appLE W (g' ⁻¹ᵁ W) le_rfl ≫ (A.chartMap U hUi).app (g' ⁻¹ᵁ W) := by
    rw [← Scheme.Hom.appLE_eq_app (A.chartMap U hUi) (U := g' ⁻¹ᵁ W)]
    rw [Scheme.Hom.appLE_comp_appLE (f := A.chartMap U hUi) (g := g),
        Scheme.Hom.appLE_comp_appLE (f := A.chartMap U hUi) (g := g')]
    exact appLE_congr_hom hpp W ((A.chartMap U hUi) ⁻¹ᵁ (g' ⁻¹ᵁ W)) _ _
  apply ConcreteCategory.hom_ext
  intro b
  apply hpinj
  have hb : (g.appLE W (g' ⁻¹ᵁ W) hV ≫ (A.chartMap U hUi).app (g' ⁻¹ᵁ W)) b
      = (g'.appLE W (g' ⁻¹ᵁ W) le_rfl ≫ (A.chartMap U hUi).app (g' ⁻¹ᵁ W)) b := by rw [key]
  simpa only [CommRingCat.comp_apply] using hb

end Work.SymQuot.Chart
