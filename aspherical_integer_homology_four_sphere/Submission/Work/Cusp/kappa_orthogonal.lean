import Mathlib
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Real InnerProductSpace

namespace Work.Cusp

/-- The three cusp lattice vectors `κ_{v,1}, κ_{v,2}, κ_{v,3}` (i.e. `kv v 0`, `kv v 1`,
`kv v 2`) are pairwise orthogonal in `ℝ³`.  They lie in the three coordinate axes (up to
sign) for every cusp `v : Fin 5`. -/
theorem kappa_orthogonal (v : Fin 5) :
    inner ℝ (kv v 0) (kv v 1) = 0 ∧ inner ℝ (kv v 0) (kv v 2) = 0 ∧
      inner ℝ (kv v 1) (kv v 2) = 0 := by
  fin_cases v <;> simp [kv, kappa, PiLp.inner_apply, Fin.sum_univ_three]

end Work.Cusp
