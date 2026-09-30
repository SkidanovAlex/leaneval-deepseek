import Mathlib
import Submission.Work.Certificates.Sparse

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Certificates.SVec

/-- `toFun` is additive under concatenation of sparse vectors: the map
`v ↦ toFun v` is a monoid homomorphism from `(List (Fin n × ℤ), ++, [])` to the
pointwise additive monoid `(Fin n → ℤ, +, 0)`. -/
private theorem toFun_append_aux {n : ℕ} (a b : List (Fin n × ℤ)) :
    toFun (a ++ b) = toFun a + toFun b := by
  funext i
  simp [toFun, List.map_append]

/-- The semantics `toFun` of a sparse vector is additive over concatenation of lists of
sparse vectors: it turns `List.flatten` into a sum of the `toFun`s. -/
theorem toFun_flatten {n : ℕ} (L : List (List (Fin n × ℤ))) :
    toFun L.flatten = (L.map toFun).sum := by
  induction L with
  | nil => funext i; simp [toFun]
  | cons l L ih =>
    simp [List.flatten_cons, toFun_append_aux, ih, List.sum_cons]

end Work.Certificates.SVec
