import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.Charts
import Submission.Work.Cusp.beta_continuous

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- The range of `tauCoord v = fun x ↦ (x, beta x)` is the graph of the ceiling function `beta`,
which is closed because `beta` is continuous. -/
theorem isClosed_range_tauCoord (v : Fin 5) : IsClosed (Set.range (tauCoord v)) := by
  have h : Set.range (tauCoord v) = {q : E3 × ℝ | q.2 = beta q.1} := by
    ext q
    constructor
    · rintro ⟨x, rfl⟩
      simp [tauCoord]
    · intro hq
      exact ⟨q.1, Prod.ext rfl hq.symm⟩
  rw [h]
  exact isClosed_eq continuous_snd (beta_continuous.comp continuous_fst)

end Work.Cusp
