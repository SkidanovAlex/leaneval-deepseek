import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Bottcher.Inverse.bottcherSeries_le_sharp
import Submission.Work.Bottcher.Contraction.norm_bottcherSeries_sub_le
import Submission.Work.NAKANE.FarInj.DiagFoundation
import Submission.Work.NAKANE.FarInj.DiagSeries
import Submission.Work.NAKANE.FarInj.orbit_diff_le

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.NAKANE.FarInj

/-- **A Lipschitz estimate for the Böttcher series along the diagonal.**  For large `‖x‖`, the diagonal function `x ↦ bottcherSeries x x` is Lipschitz with constant `C / ‖x‖ ^ 2`: together with the bound `‖bottcherSeries x x‖ ≤ 2/‖x‖ + 1/‖x‖² + 1/‖x‖³` (`Work.Bottcher.Critical.norm_bottcherSeries_self_le`) and the identity `Φ x = x * exp (bottcherSeries x x)` this makes `c ↦ w * exp (-(bottcherSeries c c))` a strict contraction for large `‖w‖`, which yields injectivity of `Φ` near infinity. -/
theorem exists_diagonal_lipschitz : ∃ r C : ℝ, 0 < r ∧ 0 < C ∧
    ∀ x y : ℂ, r ≤ ‖x‖ → ‖y - x‖ ≤ ‖x‖ / 2 →
      ‖Work.Bottcher.bottcherSeries x x - Work.Bottcher.bottcherSeries y y‖
        ≤ C * ‖x - y‖ / ‖x‖ ^ 2 := by
  refine ⟨256, 64, by norm_num, by norm_num, ?_⟩
  intro x y hA hδ
  exact bottcherSeries_diag_sub_le x y hA hδ (orbit_diff_le x y hA hδ)

end Work.NAKANE.FarInj
