import Mathlib
import ChallengeDeps
import Submission.Work.DeltaHomology.Basic
import Submission.Work.DeltaHomology.RealizationDefs
import Submission.Work.DeltaHomology.SkelSet
import Submission.Work.DeltaHomology.mem_skelSet_iff
import Submission.Work.DeltaHomology.isClosed_skelSet
import Submission.Work.DeltaHomology.barycenter_not_mem_skelSet_of_lt

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The skeleta of a realized `Δ`-complex: basic properties

Collects the properties of `DeltaSimplexMap.skelSet` that use the realization: the
characterization `mem_skelSet_iff`, closedness `isClosed_skelSet`, the top skeleton
`skelSet_dim_eq_univ`, and the lemma that the barycentres of the `k`-simplices lie
outside the `(k-1)`-skeleton.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Convexity Work.Homology Work.DeltaHomology
open scoped Simplicial

set_option linter.unusedVariables false

namespace Work.DeltaHomology

noncomputable section

variable {K : DeltaCx} {X : TopCat}

/-- The `dim`-skeleton of a realized `Δ`-complex is the whole space: every point
lies in an open simplex whose dimension is at most `dim` (there are no simplices
above `dim`). -/
theorem skelSet_dim_eq_univ (R : DeltaRealization K X) :
    R.toDeltaSimplexMap.skelSet K.dim = Set.univ := by
  ext x
  refine ⟨fun _ => Set.mem_univ x, fun _ => ?_⟩
  obtain ⟨p, hp⟩ := (R.bij x).exists
  apply (mem_skelSet_iff R K.dim x).mpr
  refine ⟨p, hp, ?_⟩
  by_contra hlt
  have hk : K.dim < p.dim := Nat.lt_of_not_le hlt
  haveI : IsEmpty (Fin (K.card p.dim)) := K.isEmpty_fin_card hk
  exact isEmptyElim p.idx

/-- Every point of `X` is the realization of an open simplex of dimension `≤ dim`. -/
theorem exists_openSimplex_dim_le (R : DeltaRealization K X) (x : X) :
    ∃ p : OpenSimplex K, DeltaSimplexMap.real R.toDeltaSimplexMap p = x ∧ p.dim ≤ K.dim := by
  refine (mem_skelSet_iff R K.dim x).mp ?_
  rw [skelSet_dim_eq_univ]
  exact Set.mem_univ x

end

end Work.DeltaHomology
