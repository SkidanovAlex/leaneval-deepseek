import Mathlib
import Submission.Work.FatouCoordFix.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouCoordFix.HPetal

/-- For every level `M` the half-plane petal `HPlanePetal M = {u ≠ 0 | M < Re (-1/u)}` is
nonempty.  Explicitly, the chart point `W = max M 0 + 1` is real with `W ≥ 1 > 0` and
`Re W = max M 0 + 1 > M`, so that `u = -1/W` lies in `HPlanePetal M`, its chart coordinate
being `-1/u = W`. -/
theorem HPlanePetal_nonempty (M : ℝ) : (Work.FatouCoordFix.HPlanePetal M).Nonempty := by
  have hWpos : (0:ℝ) < max M 0 + 1 := by
    have h := le_max_right M (0:ℝ)
    linarith
  have hWne : (((max M 0 + 1 : ℝ)) : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  refine ⟨-1 / (((max M 0 + 1 : ℝ)) : ℂ), ?_, ?_⟩
  · exact div_ne_zero (by norm_num) hWne
  · show M < (-1 / (-1 / (((max M 0 + 1 : ℝ)) : ℂ))).re
    rw [Work.FatouCoordFix.neg_one_div_neg_one_div' hWne]
    simp
    have h := le_max_left M (0:ℝ)
    linarith

end Work.FatouCoordFix.HPetal
