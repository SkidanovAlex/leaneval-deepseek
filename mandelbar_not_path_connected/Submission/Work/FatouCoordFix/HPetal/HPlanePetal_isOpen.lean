import Mathlib
import Submission.Work.FatouCoordFix.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Openness of the half-plane petal

`HPlanePetal M = {u : ℂ | u ≠ 0 ∧ M < Re (-1 / u)}` is the image in the dynamical plane of the
half-plane `{Re W > M}` under the parabolic chart `W = -1 / u`.  It is the intersection of the
open set `{u ≠ 0}` with the preimage of the open ray `(M, ∞)` under the function
`u ↦ Re (-1 / u)`, which is continuous at every `u ≠ 0`; hence it is open.
-/

namespace Work.FatouCoordFix.HPetal

open Set Filter

theorem HPlanePetal_isOpen (M : ℝ) : IsOpen (Work.FatouCoordFix.HPlanePetal M) := by
  rw [isOpen_iff_mem_nhds]
  rintro u ⟨hu0, hu⟩
  have hc : ContinuousAt (fun u : ℂ => (-1 / u).re) u :=
    Complex.continuous_re.continuousAt.comp (continuousAt_const.div continuousAt_id hu0)
  filter_upwards [hc.preimage_mem_nhds (isOpen_Ioi.mem_nhds hu),
                  isOpen_ne.mem_nhds hu0] with v hv hv0
  exact ⟨hv0, hv⟩

end Work.FatouCoordFix.HPetal
