import Mathlib
import Submission.Work.GATE2.Defs
import Submission.Work.NAKANE.BottcherJoint

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.GATE2

/-- **The `1024^m`-fold Böttcher equation along the high iterate `F_c = (T_c)^{10}`.**

`Work.EL.F c = (Tsq c)^[5]`, where `Tsq c = T_c ∘ T_c` is the holomorphic second iterate, hence
`F_c = (p_c)^5` for the monic quartic `p_c = pMap c = T_c ∘ T_c` of `Work.Bottcher`.  So the `m`-th
iterate of `F_c` is the `5m`-th iterate of `p_c`, and Nakane's iterated Böttcher equation
`(φ_c z)^(4^n) = φ_c ((p_c)^[n] z)` at `n = 5m` is the statement below, since `4^(5m) = 1024^m`. -/
theorem varphiCrit_F_iterate {c : ℂ} {z : ℂ} (hz : z ∈ Work.ParamRays.critDomain c) (m : ℕ) :
    (Work.Bottcher.varphiCrit c z) ^ (1024 ^ m) =
      Work.Bottcher.varphiCrit c ((Work.EL.F c)^[m] z) := by
  -- the iterate of the high return map `F_c` is the `5m`-th iterate of the second iterate `p_c`
  have hiter : (Work.EL.F c)^[m] z = (Work.Bottcher.pMap c)^[5 * m] z := by
    rw [show Work.EL.F c = (Work.Landing.Tsq c)^[5] from rfl,
      show Work.Landing.Tsq c = Work.Bottcher.pMap c from rfl, Function.iterate_mul]
  -- the iterated Böttcher equation of the critical coordinate, at `n = 5m`
  have hB := Work.NAKANE.varphiCrit_functional_iterate hz (5 * m)
  rw [hiter, ← hB]
  congr 1
  rw [pow_mul]
  norm_num

end Work.GATE2
