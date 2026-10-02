import Mathlib
import Submission.Work.Implosion.All

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

theorem norm_ecalPt_deriv (lam : ℝ) (w : ℂ) :
    ‖-(((lam : ℂ) ^ 2) / (Complex.sin ((lam : ℂ) * w)) ^ 2)‖
      = lam ^ 2 / ‖Complex.sin ((lam : ℂ) * w)‖ ^ 2 := by
  have h1 : ‖(lam : ℂ)‖ ^ 2 = lam ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_ofReal]
    ring
  rw [norm_neg, norm_div, norm_pow, norm_pow, h1]

end Work.PARIMPL2.Direct
