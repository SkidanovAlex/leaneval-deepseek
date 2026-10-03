import Mathlib
import Submission.Work.Parab.leftCoord.levelData
import Submission.Work.Parab.leftCoord.wMap_large_estimates
import Submission.Work.Parab.leftCoord.wMap_orbit_facts
import Submission.Work.Parab.leftCoord.coordError_sector
import Submission.Work.FatouCoord.Exist.fatouCoordW_abel
import Submission.Work.FatouCoord.Exist.fatouCoordW_differentiable
import Submission.Work.FatouCoord.Exist.fatouCoordW_injOn
import Submission.Work.FatouCoord.Exist.fatouCoordW_deriv_close
import Submission.Work.FatouCoord.Exist.fatouCoordW_tsum_bound

namespace Work.Parab.leftCoord

open Work.FatouCoord

set_option linter.unusedVariables false

/-- All the estimates packaged in `LevelFacts` hold at some (large enough) level `N`: the
two-term asymptotic of `wMap f` together with its one-step growth of real parts
(`wMap_large_estimates` + `wMap_step_bound_norm`), differentiability and injectivity of `wMap f`
(`wMap_orbit_facts`), and the Abel equation, holomorphy, injectivity, derivative bound and
`O(1/Re w)` remainder for the Fatou coordinate `ψ = fatouCoordW f (1 - a)` (the `Exist` files of
the `FatouCoord` library). -/
theorem exists_levelFacts {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}
    (hb : Work.FatouCoord.ParabolicBounds f h a r A A') :
    ∃ N : ℝ, Work.Parab.leftCoord.LevelFacts f h a r N := by
  -- the two estimates for `wMap f`
  obtain ⟨R₁, K₁, hR₁pos, hR₁r, hK₁, hle₁⟩ := wMap_large_estimates hb
  obtain ⟨R₂, K₂, hR₂pos, hR₂r, hK₂, hle₂⟩ := wMap_step_bound_norm hb
  -- differentiability and injectivity of `wMap f`
  obtain ⟨N₃, hN₃pos, hN₃r, _, hgdiff, hginj, _⟩ := wMap_orbit_facts hb
  -- the Fatou coordinate facts
  obtain ⟨N₄, hN₄pos, hN₄r, habel⟩ := Work.FatouCoord.Exist.fatouCoordW_abel hb
  obtain ⟨N₅, hN₅pos, hN₅r, hψdiff⟩ := Work.FatouCoord.Exist.fatouCoordW_differentiable hb
  obtain ⟨N₆, hN₆pos, hN₆r, hψinj⟩ := Work.FatouCoord.Exist.fatouCoordW_injOn hb
  obtain ⟨N₇, hN₇pos, hN₇r, hderiv⟩ := Work.FatouCoord.Exist.fatouCoordW_deriv_close hb
  obtain ⟨N₈, K₈, hN₈pos, hN₈r, hK₈, hrem⟩ := Work.FatouCoord.Exist.fatouCoordW_tsum_bound hb
  -- a common level, dominating all the levels above
  set N : ℝ := R₁ + R₂ + N₃ + N₄ + N₅ + N₆ + N₇ + N₈ + 1 with hNdef
  have hR₁N : R₁ < N := by
    rw [hNdef]
    linarith [hR₂pos, hN₃pos, hN₄pos, hN₅pos, hN₆pos, hN₇pos, hN₈pos]
  have hR₂N : R₂ < N := by
    rw [hNdef]
    linarith [hR₁pos, hN₃pos, hN₄pos, hN₅pos, hN₆pos, hN₇pos, hN₈pos]
  have hN₃N : N₃ < N := by
    rw [hNdef]
    linarith [hR₁pos, hR₂pos, hN₄pos, hN₅pos, hN₆pos, hN₇pos, hN₈pos]
  have hN₄N : N₄ < N := by
    rw [hNdef]
    linarith [hR₁pos, hR₂pos, hN₃pos, hN₅pos, hN₆pos, hN₇pos, hN₈pos]
  have hN₅N : N₅ < N := by
    rw [hNdef]
    linarith [hR₁pos, hR₂pos, hN₃pos, hN₄pos, hN₆pos, hN₇pos, hN₈pos]
  have hN₆N : N₆ < N := by
    rw [hNdef]
    linarith [hR₁pos, hR₂pos, hN₃pos, hN₄pos, hN₅pos, hN₇pos, hN₈pos]
  have hN₇N : N₇ < N := by
    rw [hNdef]
    linarith [hR₁pos, hR₂pos, hN₃pos, hN₄pos, hN₅pos, hN₆pos, hN₈pos]
  have hN₈N : N₈ < N := by
    rw [hNdef]
    linarith [hR₁pos, hR₂pos, hN₃pos, hN₄pos, hN₅pos, hN₆pos, hN₇pos]
  refine ⟨N, { pos := by linarith [hR₁pos, hR₁N]
               hr := by linarith [hR₁r, hR₁N]
               step := ?_
               gdiff := fun x hx => hgdiff x (lt_trans hN₃N hx)
               ginj := hginj.mono fun x hx => lt_trans hN₃N hx
               abel := fun x hx => habel x (lt_trans hN₄N hx)
               ψdiff := hψdiff.mono fun x hx => lt_trans hN₅N hx
               ψinj := hψinj.mono fun x hx => lt_trans hN₆N hx
               deriv_close := fun x hx => hderiv x (lt_trans hN₇N hx)
               rem := ⟨K₈, hK₈, fun w hw => hrem w (lt_trans hN₈N hw)⟩ }⟩
  refine ⟨max K₁ K₂, le_trans hK₁ (le_max_left _ _), fun x hx => ?_⟩
  have hx₁ : R₁ < ‖x‖ := lt_trans hR₁N hx
  have hx₂ : R₂ < ‖x‖ := lt_trans hR₂N hx
  obtain ⟨ha, hb', hc⟩ := hle₁ x hx₁
  obtain ⟨_, he⟩ := hle₂ x hx₂
  have hKle : K₁ ≤ max K₁ K₂ := le_max_left _ _
  exact ⟨le_trans ha (div_le_div_of_nonneg_right hKle (norm_nonneg x)),
    le_trans hb' (div_le_div_of_nonneg_right hKle (by positivity)),
    le_trans hc (div_le_div_of_nonneg_right hKle (by positivity)),
    he⟩

end Work.Parab.leftCoord
