import Mathlib
import Submission.Work.DeltaHomology.Basic
import Submission.Work.DeltaHomology.RealizationDefs
import Submission.Work.DeltaHomology.SkelSet

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.DeltaHomology

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Convexity Work.Homology Work.DeltaHomology
open scoped Simplicial

set_option linter.style.haveILetI false

/-- The `k`-skeleton of a realized `Δ`-complex is closed in `X`: it is a finite
union of images of closed simplices, each of which is compact (a continuous image
of the compact standard simplex `StdSimplex ℝ (Fin (j+1))`) and hence closed
because `X` is Hausdorff.  (The index type of the union defining
`DeltaSimplexMap.skelSet` is finite; each `Set.range` is compact by
`isCompact_range`, hence closed by `IsCompact.isClosed` using the `T2Space X`
instance, which is the `DeltaRealization.t2` field and must be brought into scope
explicitly, e.g. `letI := R.t2`, since instance fields of a variable are not
synthesized automatically.) -/
theorem isClosed_skelSet {K : DeltaCx} {X : TopCat} (R : DeltaRealization K X) (k : ℕ) :
    IsClosed (R.toDeltaSimplexMap.skelSet k) := by
  letI : T2Space X := R.t2
  haveI : Finite {j : ℕ // j ≤ k} := Set.finite_Iic k
  rw [DeltaSimplexMap.skelSet]
  exact isClosed_iUnion_of_finite (fun j => isClosed_iUnion_of_finite (fun σ =>
    (isCompact_range (R.toDeltaSimplexMap.cls j.1 σ).continuous).isClosed))

end Work.DeltaHomology
