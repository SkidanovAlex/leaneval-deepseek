import Mathlib
import Submission.Work.DeltaHomology.Realization
import Submission.Work.DeltaHomology.RealizationDefs
import Submission.Work.DeltaHomology.SkelSet
import Submission.Work.DeltaHomology.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.DeltaHomology

/-- The `0`-skeleton `χ.skelSet 0` of a realized `Δ`-complex is finite: unfolding
`χ.skelSet 0 = ⋃_{j ≤ 0} ⋃_{σ : Fin (K.card j)} Set.range (χ.cls j σ)`, a point of the skeleton is
`χ.cls j σ y` with `j ≤ 0`, so `j = 0`, and `y` may be replaced by any fixed point `b` of
`StdSimplex ℝ (Fin 1)` (a subsingleton, e.g. `simplexBarycenter 0`, whose interior-point property
is `isOpenSimplexPoint_simplexBarycenter`).  Hence `σ ↦ ⟨χ.cls 0 σ b, χ.cls_mem_skelSet le_rfl σ b⟩`
is surjective from `Fin (K.card 0)`, and `Finite.of_surjective` applies. -/
theorem finite_skelSet_zero {K : DeltaCx} {X : TopCat} (R : DeltaRealization K X) :
    Finite ↥(R.skelSet 0) := by
  classical
  refine Finite.of_surjective
    (fun σ : Fin (K.card 0) =>
      (⟨R.cls 0 σ (simplexBarycenter 0), R.cls_mem_skelSet le_rfl σ _⟩ : ↥(R.skelSet 0))) ?_
  rintro ⟨x, hx⟩
  simp only [DeltaSimplexMap.skelSet, Set.mem_iUnion, Set.mem_range] at hx
  obtain ⟨⟨j, hj⟩, σ, y, rfl⟩ := hx
  obtain rfl : j = 0 := Nat.eq_zero_of_le_zero hj
  exact ⟨σ, Subtype.ext (congrArg (R.cls 0 σ) (Subsingleton.elim (simplexBarycenter 0) y))⟩

end Work.DeltaHomology
