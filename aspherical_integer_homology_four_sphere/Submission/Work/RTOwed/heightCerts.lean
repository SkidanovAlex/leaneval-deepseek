import Mathlib
import Submission.Work.RTOwed.heightDel

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Work.RTOwed

noncomputable section

open scoped Matrix BigOperators
open Matrix Set Topology Function

/-- **Certificate**: the quadratic coefficient `tCp` of the height functional is positive. -/
theorem tCp_pos : ∀ (a b : Fin 48), a ≠ b → cubeBit a = cubeBit b → 0 < tCp a b := by
  decide +kernel

/-- **Certificate**: the quadratic coefficient dominates the scale factor. -/
theorem tCp_ge : ∀ (a b : Fin 48), a ≠ b → cubeBit a = cubeBit b →
    100 * chartScaleZ a * chartScaleZ b ≤ 121 * tCp a b := by
  decide +kernel

/-- **Certificate**: the height functional is positive on `cubeBox a × [11/10,∞)`. -/
theorem tcertD_pos : ∀ (a b : Fin 48), a ≠ b → cubeBit a = cubeBit b →
    0 < 121 * tCp a b ^ 2 + 100 * tCp a b * tEp a b - 100 * (∑ i : Fin 3, tLp a b i ^ 2) := by
  decide +kernel

/-- **Certificate**: `11 · tDel - 20 · (chartScale a)(chartScale b) · s` is positive on the
region. -/
theorem tcertG_pos : ∀ (a b : Fin 48), a ≠ b → cubeBit a = cubeBit b →
    0 < 1331 * tCp a b ^ 2 - 2200 * (chartScaleZ a * chartScaleZ b) * tCp a b
        - 1100 * (∑ i : Fin 3, tLp a b i ^ 2) + 1100 * tCp a b * tEp a b := by
  decide +kernel

end

end Work.RTOwed
