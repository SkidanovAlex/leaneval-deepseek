import Mathlib
import Submission.Work.SymQuot.Quotient

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


open CategoryTheory Limits AlgebraicGeometry

namespace Work.SymQuot.Chart

/-- Descent for the quotient: a morphism out of the locally directed colimit `D.Quotient` is the
same thing as a compatible family of morphisms out of the charts.

The family `ψ` is a cocone over `D.chartFunctor` with point `Z` (the compatibility hypothesis
`hψ` is exactly the naturality of the cocone), so `colimit.desc` produces the morphism `g`, and
both existence and uniqueness are the universal property of the colimit (`colimit.ι_desc` and
`colimit.hom_ext`). -/
theorem quotient_desc {Γ : Type*} [Group Γ] [Fintype Γ] {X : AlgebraicGeometry.Scheme}
    (D : Work.SymQuot.QuotientData Γ X) {Z : AlgebraicGeometry.Scheme}
    (ψ : ∀ U : D.Chart, D.chart U ⟶ Z)
    (hψ : ∀ {U V : D.Chart} (h : U ⟶ V),
      CategoryTheory.CategoryStruct.comp (D.chartFunctor.map h) (ψ V) = ψ U) :
    ∃! g : D.Quotient ⟶ Z,
      ∀ U : D.Chart, CategoryTheory.CategoryStruct.comp (D.chartι U) g = ψ U := by
  let s : Cocone D.chartFunctor :=
    { pt := Z
      ι := { app := fun U => ψ U
             naturality := fun {U V} h => hψ h } }
  have hfac : ∀ U : D.Chart, D.chartι U ≫ colimit.desc D.chartFunctor s = ψ U :=
    fun U => colimit.ι_desc s U
  refine ⟨colimit.desc D.chartFunctor s, hfac, ?_⟩
  intro g hg
  refine colimit.hom_ext fun U => ?_
  show D.chartι U ≫ g = D.chartι U ≫ colimit.desc D.chartFunctor s
  rw [hg U, hfac U]

end Work.SymQuot.Chart
