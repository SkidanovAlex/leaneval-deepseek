import Mathlib
import ChallengeDeps
import Submission.Work.DeltaHomology.Basic
import Submission.Work.DeltaHomology.SkeletonDefs
import Submission.Work.DeltaHomology.Skeleton
import Submission.Work.DeltaHomology.skelHomOfLe_face

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Inclusions between skeleta

For `n ≤ m` the `n`-skeleton of a `Δ`-complex is a subcomplex of the
`m`-skeleton: the inclusion `K.skel n ⟶ K.skel m` is the simplicial map whose
underlying map on simplices is `skelHomOfLe` (the identity when the dimension is
`≤ n`, the empty map above).  Its face compatibility is
`Submission.Work.DeltaHomology.skelHomOfLe_face`.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

set_option linter.unusedVariables false

namespace Work.DeltaHomology

noncomputable section

/-- The inclusion of the `n`-skeleton into the `m`-skeleton (`n ≤ m`) as a
simplicial map of `Δ`-complexes. -/
def DeltaCx.skelLE (K : DeltaCx) {n m : ℕ} (h : n ≤ m) : (K.skel n).Hom (K.skel m) where
  map := fun {_} σ => skelHomOfLe K h σ
  map_face := fun {_} σ i => skelHomOfLe_face K h σ i

@[simp]
theorem DeltaCx.skelLE_map (K : DeltaCx) {n m : ℕ} (h : n ≤ m) {j : ℕ}
    (σ : Fin ((K.skel n).card j)) :
    (K.skelLE h).map σ = skelHomOfLe K h σ := rfl

end

end Work.DeltaHomology
