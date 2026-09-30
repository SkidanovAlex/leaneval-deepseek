import Mathlib
import Submission.Work.DeltaHomology.RealizationDefs
import Submission.Work.DeltaHomology.eq_of_cls_eq_of_pos
import Submission.Work.DeltaHomology.PunctSkelBasic
import Submission.Work.DeltaHomology.SkelSet

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.DeltaHomology

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Convexity Work.Homology

/-- **Distinct simplices have distinct characteristic maps.**  In a realization, if two
simplices of the same dimension have the same characteristic map (as continuous maps), then
they are equal.

Route: this is a two-line corollary of `eq_of_cls_eq_of_pos`
(`Submission.Work.DeltaHomology.eq_of_cls_eq_of_pos`): from `h : cls k σ = cls k τ`, evaluate
at the barycentre `simplexBarycenter k` (an interior point,
`isOpenSimplexPoint_simplexBarycenter`) and apply `eq_of_cls_eq_of_pos`, whose first conjunct
is `σ = τ`. -/
theorem chi_injective {K : DeltaCx} {X : TopCat} (R : DeltaRealization K X) (k : ℕ) :
    Function.Injective (fun σ : Fin (K.card k) => R.toDeltaSimplexMap.cls k σ) := by
  intro σ τ h
  exact (eq_of_cls_eq_of_pos (K := K) (X := X) R (n := k) (σ := σ) (σ' := τ)
    (y := simplexBarycenter k) (y' := simplexBarycenter k)
    (isOpenSimplexPoint_simplexBarycenter k)
    (congrArg (fun f : C(StdSimplex ℝ (Fin (k + 1)), X) => f (simplexBarycenter k)) h)).1

end Work.DeltaHomology
