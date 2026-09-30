import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.beta_pos
import Submission.Work.Cusp.collarHeight_one

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

theorem ThetaOuter_apply_one (v : Fin 5) (p y : E2) (hp : nrm p = 1) :
    ThetaOuter v p y = !₂[(cuspX v (u p) y) 0, (cuspX v (u p) y) 1, (cuspX v (u p) y) 2,
      beta (cuspX v (u p) y)] := by
  have hb : 0 < beta (cuspX v (u p) y) := beta_pos _
  have hs : collarS v p y = beta (cuspX v (u p) y) := by
    simp only [collarS]
    rw [hp]
    exact collarHeight_one _ hb
  simp only [ThetaOuter]
  rw [hs]

end Work.Cusp
