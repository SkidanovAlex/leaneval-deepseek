import Mathlib
import Submission.Work.SymQuot.Chart.chart_factor_unique
import Submission.Work.SymQuot.Chart.chartRes_chartMap
import Submission.Work.SymQuot.Chart.isAffineOpen_inf_of_le

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


universe u

namespace Work.SymQuot.Chart

theorem chart_piece_compat {Γ : Type u} [Group Γ] [Fintype Γ]
    {X : AlgebraicGeometry.Scheme.{u}} (A : Work.SymQuot.GAction Γ X)
    {W₁ W₂ U : X.Opens} (h₁ : W₁ ≤ U) (h₂ : W₂ ≤ U)
    (hU : AlgebraicGeometry.IsAffineOpen U) (hW₁a : AlgebraicGeometry.IsAffineOpen W₁)
    (hW₂a : AlgebraicGeometry.IsAffineOpen W₂)
    (hW₁i : A.IsInvariantOpen W₁) (hW₂i : A.IsInvariantOpen W₂)
    {Z : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ Z}
    {g₁ : Work.SymQuot.GAction.chart A W₁ hW₁i ⟶ Z}
    {g₂ : Work.SymQuot.GAction.chart A W₂ hW₂i ⟶ Z}
    (hg₁ : CategoryTheory.CategoryStruct.comp (A.chartMap W₁ hW₁i) g₁ =
      CategoryTheory.CategoryStruct.comp W₁.ι f)
    (hg₂ : CategoryTheory.CategoryStruct.comp (A.chartMap W₂ hW₂i) g₂ =
      CategoryTheory.CategoryStruct.comp W₂.ι f) :
    CategoryTheory.CategoryStruct.comp
        (Work.SymQuot.GAction.chartRes A (W₁ ⊓ W₂) W₁ (inf_le_left) hW₁i
          (hW₁i.inf hW₂i)) g₁ =
      CategoryTheory.CategoryStruct.comp
        (Work.SymQuot.GAction.chartRes A (W₁ ⊓ W₂) W₂ (inf_le_right) hW₂i
          (hW₁i.inf hW₂i)) g₂ := by
  have hinf : AlgebraicGeometry.IsAffineOpen (W₁ ⊓ W₂) :=
    isAffineOpen_inf_of_le h₁ h₂ hU hW₁a hW₂a
  have hinfi : A.IsInvariantOpen (W₁ ⊓ W₂) := hW₁i.inf hW₂i
  apply Work.SymQuot.Chart.chart_factor_unique A hinf hinfi
  have key₁ : CategoryTheory.CategoryStruct.comp (A.chartMap (W₁ ⊓ W₂) hinfi)
      (CategoryTheory.CategoryStruct.comp
        (Work.SymQuot.GAction.chartRes A (W₁ ⊓ W₂) W₁ (inf_le_left) hW₁i hinfi) g₁)
      = CategoryTheory.CategoryStruct.comp (W₁ ⊓ W₂).ι f := by
    rw [← CategoryTheory.Category.assoc,
      ← Work.SymQuot.Chart.chartRes_chartMap A (inf_le_left : W₁ ⊓ W₂ ≤ W₁) hW₁i hinfi,
      CategoryTheory.Category.assoc, hg₁, ← CategoryTheory.Category.assoc, AlgebraicGeometry.Scheme.homOfLE_ι]
  have key₂ : CategoryTheory.CategoryStruct.comp (A.chartMap (W₁ ⊓ W₂) hinfi)
      (CategoryTheory.CategoryStruct.comp
        (Work.SymQuot.GAction.chartRes A (W₁ ⊓ W₂) W₂ (inf_le_right) hW₂i hinfi) g₂)
      = CategoryTheory.CategoryStruct.comp (W₁ ⊓ W₂).ι f := by
    rw [← CategoryTheory.Category.assoc,
      ← Work.SymQuot.Chart.chartRes_chartMap A (inf_le_right : W₁ ⊓ W₂ ≤ W₂) hW₂i hinfi,
      CategoryTheory.Category.assoc, hg₂, ← CategoryTheory.Category.assoc, AlgebraicGeometry.Scheme.homOfLE_ι]
  rw [key₁, key₂]

end Work.SymQuot.Chart
