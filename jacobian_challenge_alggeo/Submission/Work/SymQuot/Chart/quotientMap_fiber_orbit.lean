import Mathlib
import Submission.Work.SymQuot.QuotientMap
import Submission.Work.SymQuot.Quotient
import Submission.Work.SymQuot.Chart.chartMap_fiber_orbit
import Submission.Work.SymQuot.Chart.chartRes_chartMap
import Submission.Work.SymQuot.Chart.chartRes_isEmbedding

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

namespace Work.SymQuot.Chart

theorem quotientMap_fiber_orbit {Γ : Type*} [Group Γ] [Fintype Γ] {X : AlgebraicGeometry.Scheme}
    (D : Work.SymQuot.QuotientData Γ X) {x y : X}
    (h : D.quotientMap x = D.quotientMap y) :
    y ∈ D.action.orbit x := by
  obtain ⟨U, hUa, hUi, hxU⟩ := D.covers x
  obtain ⟨V, hVa, hVi, hyV⟩ := D.covers y
  have hqU : D.quotientMap x =
      D.chartι (⟨U, hUa, hUi⟩ : D.Chart) (D.action.chartMap U hUi ⟨x, hxU⟩) := by
    have h1 : (U.ι ≫ D.quotientMap) ⟨x, hxU⟩ =
        (D.action.chartMap U hUi ≫ D.chartι (⟨U, hUa, hUi⟩ : D.Chart)) ⟨x, hxU⟩ :=
      congrArg (fun (f : (⟨U, hUa, hUi⟩ : D.Chart).1.toScheme ⟶ D.Quotient) => f ⟨x, hxU⟩)
        (D.quotientMap_chartι ⟨U, hUa, hUi⟩)
    have h2 : D.quotientMap (U.ι ⟨x, hxU⟩) =
        D.chartι (⟨U, hUa, hUi⟩ : D.Chart) (D.action.chartMap U hUi ⟨x, hxU⟩) := h1
    simpa using h2
  have hqV : D.quotientMap y =
      D.chartι (⟨V, hVa, hVi⟩ : D.Chart) (D.action.chartMap V hVi ⟨y, hyV⟩) := by
    have h1 : (V.ι ≫ D.quotientMap) ⟨y, hyV⟩ =
        (D.action.chartMap V hVi ≫ D.chartι (⟨V, hVa, hVi⟩ : D.Chart)) ⟨y, hyV⟩ :=
      congrArg (fun (f : (⟨V, hVa, hVi⟩ : D.Chart).1.toScheme ⟶ D.Quotient) => f ⟨y, hyV⟩)
        (D.quotientMap_chartι ⟨V, hVa, hVi⟩)
    have h2 : D.quotientMap (V.ι ⟨y, hyV⟩) =
        D.chartι (⟨V, hVa, hVi⟩ : D.Chart) (D.action.chartMap V hVi ⟨y, hyV⟩) := h1
    simpa using h2
  -- both points lie in the same chart of the quotient: pass to a common refinement `W`
  have h' : D.chartι (⟨U, hUa, hUi⟩ : D.Chart) (D.action.chartMap U hUi ⟨x, hxU⟩) =
      D.chartι (⟨V, hVa, hVi⟩ : D.Chart) (D.action.chartMap V hVi ⟨y, hyV⟩) :=
    hqU.symm.trans (h.trans hqV)
  obtain ⟨W, hWU, hWV, z, hzU, hzV⟩ := D.chartι_eq_iff.mp h'
  obtain ⟨w1, hw1⟩ := chartMap_surjective D.action W.2.1 W.2.2 z
  have hWUle : W.1 ≤ U := leOfHom hWU
  have hWVle : W.1 ≤ V := leOfHom hWV
  -- the common point `w1` of `W` maps to a point of `U` with the same chart image as `x`
  have hAU : D.action.chartMap U hUi (X.homOfLE hWUle w1) =
      D.action.chartMap U hUi ⟨x, hxU⟩ := by
    have hnat := congrArg (fun f => f w1) (chartRes_chartMap (A := D.action) hWUle hUi W.2.2)
    simp only [Scheme.Hom.comp_apply] at hnat
    rw [hnat, hw1]
    exact hzU
  have hAV : D.action.chartMap V hVi (X.homOfLE hWVle w1) =
      D.action.chartMap V hVi ⟨y, hyV⟩ := by
    have hnat := congrArg (fun f => f w1) (chartRes_chartMap (A := D.action) hWVle hVi W.2.2)
    simp only [Scheme.Hom.comp_apply] at hnat
    rw [hnat, hw1]
    exact hzV
  -- the fibres of the chart maps are the orbits
  obtain ⟨g₁, hg₁⟩ := chartMap_fiber_orbit D.action hUa hUi hAU
  obtain ⟨g₂, hg₂⟩ := chartMap_fiber_orbit D.action hVa hVi hAV
  have hιWU : U.ι (X.homOfLE hWUle w1) = W.1.ι w1 :=
    congrArg (fun f => f w1) (Scheme.homOfLE_ι X hWUle)
  have hιWV : V.ι (X.homOfLE hWVle w1) = W.1.ι w1 :=
    congrArg (fun f => f w1) (Scheme.homOfLE_ι X hWVle)
  have hιx : U.ι ⟨x, hxU⟩ = x := rfl
  have hιy : V.ι ⟨y, hyV⟩ = y := rfl
  have hg₁' : D.action.hom g₁ x = W.1.ι w1 := by
    calc D.action.hom g₁ x = D.action.hom g₁ (U.ι ⟨x, hxU⟩) := by rw [hιx]
      _ = U.ι (X.homOfLE hWUle w1) := hg₁
      _ = W.1.ι w1 := hιWU
  have hg₂' : D.action.hom g₂ y = W.1.ι w1 := by
    calc D.action.hom g₂ y = D.action.hom g₂ (V.ι ⟨y, hyV⟩) := by rw [hιy]
      _ = V.ι (X.homOfLE hWVle w1) := hg₂
      _ = W.1.ι w1 := hιWV
  have key : D.action.hom g₁ x = D.action.hom g₂ y := hg₁'.trans hg₂'.symm
  refine ⟨g₂⁻¹ * g₁, ?_⟩
  rw [D.action.hom_mul g₂⁻¹ g₁]
  show D.action.hom g₂⁻¹ (D.action.hom g₁ x) = y
  rw [key]
  show D.action.hom g₂⁻¹ (D.action.hom g₂ y) = y
  rw [← Scheme.Hom.comp_apply, D.action.inv_hom_inv]
  rfl

end Work.SymQuot.Chart
