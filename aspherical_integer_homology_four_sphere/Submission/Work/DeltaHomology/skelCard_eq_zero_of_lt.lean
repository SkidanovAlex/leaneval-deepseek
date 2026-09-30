import Mathlib
import Submission.Work.DeltaHomology.Basic
import Submission.Work.DeltaHomology.SkeletonDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.DeltaHomology

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Work.DeltaHomology

/-- The `card_eq_zero` obligation for the `n`-skeleton of a `Δ`-complex: above
`min K.dim n` there are no simplices of the truncation, i.e.
`skelCard K n k = 0` whenever `min K.dim n < k`.  Split on `k ≤ n`: in that case
`skelCard K n k = K.card k` and `K.dim < k` follows from the hypothesis, so
`K.card_eq_zero` gives the result; otherwise use `skelCard_eq_zero`. -/
theorem skelCard_eq_zero_of_lt (K : DeltaCx) (n : ℕ) {k : ℕ} (h : min K.dim n < k) :
    skelCard K n k = 0 := by
  by_cases hk : k ≤ n
  · rw [skelCard_eq K hk]
    exact K.card_eq_zero k (by omega)
  · exact skelCard_eq_zero K (by omega)

end Work.DeltaHomology
