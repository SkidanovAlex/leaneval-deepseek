import Mathlib
import Submission.Work.Certificates.Sparse
import Submission.Work.Certificates.SVec.toFun_append
import Submission.Work.Certificates.SVec.toFun_insert
import Submission.Work.Certificates.SVec.toFun_nil
import Submission.Work.Certificates.SVec.toFun_single

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Certificates.SVec

variable {n : ℕ}

/-- Pointwise-additive form of `toFun` on a cons, in the shape needed to compare with the
output of `insert`. -/
theorem toFun_cons (p : Fin n × ℤ) (l : SVec n) :
    toFun (p :: l) = toFun ([p] : SVec n) + toFun l := by
  rw [← List.singleton_append, toFun_append]

/-- `norm` is the fold of `insert` over the list, and `insert p` adds exactly `toFun [p]`
(`toFun_insert`), so `norm` does not change the represented function. -/
theorem toFun_norm {n : ℕ} (v : List (Fin n × ℤ)) : toFun (norm v) = toFun v := by
  induction v with
  | nil => rfl
  | cons p ps ih =>
    show toFun (insert p (norm ps)) = toFun (p :: ps)
    rw [toFun_insert, ih]
    exact (toFun_cons p ps).symm

end Work.Certificates.SVec
