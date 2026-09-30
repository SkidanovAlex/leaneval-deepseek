import Mathlib
import Submission.Work.DeltaHomology.CellData
import Submission.Work.DeltaHomology.isClosed_skelSet
import Submission.Work.DeltaHomology.barycenter_not_mem_skelSet_of_lt
import Submission.Work.DeltaHomology.PunctSkelBasic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The `k`-skeleton lies in the interior of the punctured `(k+1)`-skeleton

Working inside the `(k+1)`-skeleton `X^{k+1}` (as a subspace of `X`), the collar
`X^{k+1} ∖ {barycentres of (k+1)-simplices}` is open: the points removed form the
finite set of barycentres, hence are closed in the Hausdorff space `X^{k+1}`.  The
`k`-skeleton `X^k` is closed in `X`, hence closed (indeed equal to its closure) in
`X^{k+1}`, and it is contained in the collar.  Therefore the closure of `X^k`
inside `X^{k+1}` lies in the interior of the collar.
-/

set_option linter.style.haveILetI false

namespace Work.DeltaHomology

theorem closure_skelSet_interior_punctSkel {K : DeltaCx} {X : TopCat} (R : DeltaRealization K X)
    (k : ℕ) :
    closure {x : ↥(R.toDeltaSimplexMap.skelSet (k + 1)) |
        (x : X) ∈ R.toDeltaSimplexMap.skelSet k} ⊆
      interior {x : ↥(R.toDeltaSimplexMap.skelSet (k + 1)) |
        (x : X) ∈ R.toDeltaSimplexMap.punctSkel (k + 1)} := by
  letI : T2Space X := R.t2
  -- The collar, viewed inside the `(k+1)`-skeleton, is open: its complement is the
  -- preimage of the finite (hence closed) set of barycentres.
  have hTopen : IsOpen {x : ↥(R.toDeltaSimplexMap.skelSet (k + 1)) |
      (x : X) ∈ R.toDeltaSimplexMap.punctSkel (k + 1)} := by
    have hclosed : IsClosed ((Subtype.val ⁻¹' R.toDeltaSimplexMap.barycenterSet (k + 1)) :
        Set ↥(R.toDeltaSimplexMap.skelSet (k + 1))) :=
      IsClosed.preimage continuous_subtype_val
        ((R.toDeltaSimplexMap.barycenterSet_finite (k + 1)).isClosed)
    have hset : {x : ↥(R.toDeltaSimplexMap.skelSet (k + 1)) |
        (x : X) ∈ R.toDeltaSimplexMap.punctSkel (k + 1)} =
        (Subtype.val ⁻¹' R.toDeltaSimplexMap.barycenterSet (k + 1))ᶜ := by
      ext x
      simp [DeltaSimplexMap.punctSkel]
    rw [hset]
    exact hclosed.isOpen_compl
  rw [hTopen.interior_eq]
  -- The `k`-skeleton is closed in the `(k+1)`-skeleton, so equals its own closure.
  have hScl : IsClosed {x : ↥(R.toDeltaSimplexMap.skelSet (k + 1)) |
      (x : X) ∈ R.toDeltaSimplexMap.skelSet k} :=
    IsClosed.preimage continuous_subtype_val (isClosed_skelSet R k)
  rw [hScl.closure_eq]
  intro x hx
  exact DeltaSimplexMap.skelSet_subset_punctSkel_succ R k hx

end Work.DeltaHomology
