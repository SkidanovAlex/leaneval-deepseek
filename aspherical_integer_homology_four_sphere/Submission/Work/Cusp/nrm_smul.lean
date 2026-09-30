import Mathlib
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

theorem nrm_smul (c : ℝ) (p : E2) : nrm (c • p) = |c| * nrm p := by
  simp only [nrm, PiLp.smul_apply, smul_eq_mul, abs_mul]
  exact (mul_max_of_nonneg (|p 0|) (|p 1|) (abs_nonneg c)).symm

end Work.Cusp
