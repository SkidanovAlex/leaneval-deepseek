import Mathlib
import Submission.Work.DeltaHomology.Basic
import Submission.Work.DeltaHomology.RealizationDefs
import Submission.Work.DeltaHomology.SkelSet
import Submission.Work.DeltaHomology.mem_skelSet_iff

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.DeltaHomology

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Convexity Work.Homology Work.DeltaHomology
open scoped Simplicial

/-- The barycentre of a `k`-simplex does not lie in the `j`-skeleton for `j < k`:
it is an interior point of (the realization of) that `k`-simplex, so its open
simplex has dimension exactly `k`.

Route: the barycentre is an interior point of the standard simplex
(`isOpenSimplexPoint_simplexBarycenter`), so `p := ⟨k, σ, simplexBarycenter k, _⟩`
is an `OpenSimplex K` with `DeltaSimplexMap.real R.toDeltaSimplexMap p` equal to the
point in question; the realization's bijection `R.bij` makes it the *unique* open
simplex representing that point, so if the point were in `skelSet j` its open
simplex would have dimension `≤ j < k` — contradiction (via the characterization
`mem_skelSet_iff`). -/
theorem barycenter_not_mem_skelSet_of_lt {K : DeltaCx} {X : TopCat} (R : DeltaRealization K X)
    {j k : ℕ} (h : j < k) (σ : Fin (K.card k)) :
    (R.toDeltaSimplexMap.cls k σ (simplexBarycenter k) : X) ∉
      R.toDeltaSimplexMap.skelSet j := by
  intro hx
  -- `x` lies in the `j`-skeleton, so its (unique) open simplex has dimension `≤ j`.
  obtain ⟨p, hp, hpk⟩ := (mem_skelSet_iff R j _).mp hx
  -- The barycentre itself is an open `k`-simplex representing `x`, hence equals `p`.
  have hq : DeltaSimplexMap.real R.toDeltaSimplexMap
      (⟨k, σ, simplexBarycenter k, isOpenSimplexPoint_simplexBarycenter k⟩ : OpenSimplex K) =
      DeltaSimplexMap.real R.toDeltaSimplexMap p := by
    rw [hp]; rfl
  have huniq := (R.bij (DeltaSimplexMap.real R.toDeltaSimplexMap p)).unique rfl hq
  have hdim : p.dim = k := by rw [huniq]
  omega

end Work.DeltaHomology
