import Mathlib
import Submission.Work.Certificates.Sparse

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Certificates.SVec

theorem toFun_single {n : ℕ} (p : Fin n × ℤ) :
    toFun ([p] : List (Fin n × ℤ)) = fun i => if p.1 = i then p.2 else 0 := by
  funext i
  simp [toFun]

end Work.Certificates.SVec
