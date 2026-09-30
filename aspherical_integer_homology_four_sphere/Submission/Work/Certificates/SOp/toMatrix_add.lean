import Mathlib
import Submission.Work.Certificates.Sparse

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Certificates

namespace SVec

/-- The semantic function of a concatenation of sparse vectors is the sum of the semantic
functions: `toFun` is additive in the list.

(Kept `private` here: the same fact is available publicly as
`Work.Certificates.SVec.toFun_append`, and importing both modules together must not produce a
name clash.) -/
private theorem toFun_append {n : ℕ} (a b : SVec n) :
    (a ++ b).toFun = a.toFun + b.toFun := by
  funext i
  simp [SVec.toFun, List.map_append, List.sum_append]

end SVec

namespace SOp

/-- `toMatrix` turns the sparse sum of operators into the sum of matrices. -/
theorem toMatrix_add {n m : ℕ} (A B : SOp n m) :
    toMatrix (add A B) = toMatrix A + toMatrix B := by
  ext i j
  simp [SOp.toMatrix, SOp.add, SVec.toFun, List.map_append, List.sum_append]

end SOp

end Work.Certificates
