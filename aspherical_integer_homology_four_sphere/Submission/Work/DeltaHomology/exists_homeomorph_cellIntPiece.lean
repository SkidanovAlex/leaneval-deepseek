import Mathlib
import Submission.Work.DeltaHomology.openCoverInclPair
import Submission.Work.DeltaHomology.exists_homeomorph_intCell

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The open cell of a realized `Δ`-complex, inside the closed cell

For a realized `Δ`-complex `χ : DeltaSimplexMap K X`, the *open* `n`-cell of a simplex `σ` is
`χ.intCell n σ ⊆ X`.  In the skeleta induction one works with it viewed inside the *closed* cell,
i.e. with the set `cellIntPiece R n σ = {x : ↥(χ.cell n σ) | (x : X) ∈ χ.intCell n σ}`.

This file records that this piece is homeomorphic to the open standard simplex
`openSimplexSet n = {w | IsOpenSimplexPoint n w}`, by the characteristic map `χ.cls n σ`, and
that the homeomorphism carries the barycentre of the standard simplex to the barycentre of the
cell.

Route: `exists_homeomorph_intCell` already gives a homeomorphism
`↥(openSimplexSet n) ≃ₜ ↥(χ.intCell n σ)` whose underlying map is `χ.cls n σ`; the second factor is
then transported across the identification
`cellIntPiece R n σ = (Subtype.val : ↥(χ.cell n σ) → X) ⁻¹' χ.intCell n σ`
(the evident homeomorphism `↥(χ.intCell n σ) ≃ₜ ↥(cellIntPiece R n σ)` posting the two
subtype inclusions against each other).  The barycentre condition is the injectivity of
`χ.cls n σ` on interior points of the standard simplex, `eq_of_cls_eq_of_pos`.
-/

set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Convexity

namespace Work.DeltaHomology

noncomputable section

variable {K : DeltaCx} {X : TopCat}

/-- **The open cell of a simplex, viewed inside the closed cell, is homeomorphic to the open cell
viewed inside `X`.**  The homeomorphism merely re-associates the two subtype inclusions
`↥(χ.intCell n σ) ⊆ ↥(χ.cell n σ) ⊆ X`; both directions are continuous because they are built from
subtype inclusions. -/
def homeomorph_intCell_cellIntPiece (R : DeltaRealization K X) (n : ℕ) (σ : Fin (K.card n)) :
    ↥(R.toDeltaSimplexMap.intCell n σ) ≃ₜ ↥(cellIntPiece R n σ) where
  toFun x := ⟨⟨(x.1 : X), DeltaSimplexMap.intCell_subset_cell R.toDeltaSimplexMap n σ x.2⟩, x.2⟩
  invFun x := ⟨(x.1.1 : X), x.2⟩
  left_inv x := Subtype.ext rfl
  right_inv x := Subtype.ext (Subtype.ext rfl)
  continuous_toFun := Continuous.subtype_mk
    (Continuous.subtype_mk continuous_subtype_val fun _ => _) fun _ => _
  continuous_invFun := Continuous.subtype_mk
    (continuous_subtype_val.comp continuous_subtype_val) fun _ => _

@[simp]
theorem homeomorph_intCell_cellIntPiece_apply_coe (R : DeltaRealization K X) (n : ℕ)
    (σ : Fin (K.card n)) (x : ↥(R.toDeltaSimplexMap.intCell n σ)) :
    ((homeomorph_intCell_cellIntPiece R n σ x : ↥(R.toDeltaSimplexMap.cell n σ)) : X) =
      (x : X) := rfl

theorem exists_homeomorph_cellIntPiece {K : Work.DeltaHomology.DeltaCx} {X : TopCat}
    (R : Work.DeltaHomology.DeltaRealization K X) (n : ℕ) (σ : Fin (K.card n)) :
    ∃ e : ↥(Work.DeltaHomology.openSimplexSet n) ≃ₜ ↥(Work.DeltaHomology.cellIntPiece R n σ),
      (∀ w : ↥(Work.DeltaHomology.openSimplexSet n),
        ((e w : ↥(R.toDeltaSimplexMap.cell n σ)) : X) = R.toDeltaSimplexMap.cls n σ w) ∧
      (∀ w : ↥(Work.DeltaHomology.openSimplexSet n),
        (w : Convexity.StdSimplex ℝ (Fin (n + 1))) ≠ Work.DeltaHomology.simplexBarycenter n ↔
        ((e w : ↥(R.toDeltaSimplexMap.cell n σ)) : X) ≠
          R.toDeltaSimplexMap.cellBarycenter n σ) := by
  classical
  obtain ⟨h, hh⟩ := exists_homeomorph_intCell R n σ
  refine ⟨h.trans (homeomorph_intCell_cellIntPiece R n σ), ?_, ?_⟩
  · -- the composite is the characteristic map of `σ`
    intro w
    show ((h.trans (homeomorph_intCell_cellIntPiece R n σ) w
      : ↥(R.toDeltaSimplexMap.cell n σ)) : X) = R.toDeltaSimplexMap.cls n σ w
    rw [Homeomorph.trans_apply]
    exact hh w
  · intro w
    have hcoe : ((h.trans (homeomorph_intCell_cellIntPiece R n σ) w
        : ↥(R.toDeltaSimplexMap.cell n σ)) : X) = R.toDeltaSimplexMap.cls n σ w := by
      show ((h.trans (homeomorph_intCell_cellIntPiece R n σ) w
        : ↥(R.toDeltaSimplexMap.cell n σ)) : X) = R.toDeltaSimplexMap.cls n σ w
      rw [Homeomorph.trans_apply]
      exact hh w
    rw [hcoe]
    show (w : Convexity.StdSimplex ℝ (Fin (n + 1))) ≠ Work.DeltaHomology.simplexBarycenter n ↔
      R.toDeltaSimplexMap.cls n σ w ≠ R.toDeltaSimplexMap.cellBarycenter n σ
    constructor
    · -- `χ.cls n σ` is injective on the interior of the standard simplex
      intro hw heq
      exact hw (eq_of_cls_eq_of_pos R w.2 heq).2
    · intro hne hw
      exact hne (by rw [hw]; rfl)

end

end Work.DeltaHomology
