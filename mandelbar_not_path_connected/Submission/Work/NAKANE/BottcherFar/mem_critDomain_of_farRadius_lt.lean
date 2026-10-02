import Mathlib
import Submission.Work.NAKANE.Defs
import Submission.Work.Escape.log_half_le_green
import Submission.Work.Escape.green_le_log
import Submission.Work.Escape.greenParam_eq_paramPotential
import Submission.Work.Bottcher.Contraction.green_eq_greenFun

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.NAKANE.BottcherFar

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **The coarse far radius lies in the critical domain.**  If `‖z‖ > farRadius ‖c‖` where
`farRadius C = 2 * (max 2 (1 + C))^2 + 2` (`Work.NAKANE.farRadius`, in
`Submission/Work/NAKANE/Defs.lean`) then `z ∈ critDomain c`, i.e. `G_c z > G_c 0`.

Route (two Green-function bounds, both in `Submission/Work/Escape`).
* `‖z‖ > farRadius ‖c‖ ≥ 2 * (max 2 (1+‖c‖))^2 + 2` gives `‖z‖/2 > (max 2 (1+‖c‖))^2` and
  `max 2 ‖c‖ < ‖z‖`, so `Work.Escape.log_half_le_green` gives `Real.log (‖z‖/2) ≤ G_c z`.
* `Work.Escape.green_le_log` at `z = 0` (with `A = ‖c‖`, `d = 2`, `monicGrowth_Tantibar`) gives
  `G_c 0 ≤ 2 * Real.log (max 2 (max (‖c‖+1) 0)) = 2 * Real.log (max 2 (‖c‖+1))`, and
  `Real.log (‖z‖/2) > 2 * Real.log (max 2 (1+‖c‖))`.
* Hence `G_c 0 < log (‖z‖/2) ≤ G_c z`.  Bridge `Work.Escape.green` to
  `Work.ParamRays.greenFun`/`paramPotential` with `Work.Bottcher.Contraction.green_eq_greenFun`
  and `Work.Escape.greenParam_eq_paramPotential`.  The same computation is done in
  `Work.Bottcher.CritBasic.critFar_subset_CritDomain` for the sharper radius `critFarRadius`. -/
theorem mem_critDomain_of_farRadius_lt {c z : ℂ}
    (hz : Work.NAKANE.farRadius ‖c‖ < ‖z‖) : z ∈ Work.ParamRays.critDomain c := by
  rw [Work.ParamRays.mem_critDomain]
  set M : ℝ := max 2 (1 + ‖c‖) with hMdef
  have hM2 : (2 : ℝ) ≤ M := le_max_left _ _
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM2
  -- The hypothesis, rewritten with `M`.
  have hfar : Work.NAKANE.farRadius ‖c‖ = 2 * M ^ 2 + 2 := by
    rw [Work.NAKANE.farRadius, ← hMdef]
  have hz' : 2 * M ^ 2 + 2 < ‖z‖ := by rw [← hfar]; exact hz
  -- `z` lies in the escape region of `T_c`.
  have hMax : max 2 ‖c‖ < ‖z‖ := by
    have hcM : ‖c‖ ≤ M :=
      le_of_lt (lt_of_lt_of_le (by linarith [norm_nonneg c]) (le_max_right _ _))
    have hle : max 2 ‖c‖ ≤ M := max_le hM2 hcM
    have hMle : M ≤ 2 * M ^ 2 + 2 := by nlinarith [hM2]
    linarith
  -- The crucial inequality `M^2 < ‖z‖/2`.
  have hsq : M ^ 2 < ‖z‖ / 2 := by nlinarith [hz']
  -- Therefore `2 log M < log (‖z‖/2)`.
  have hlogM : 2 * Real.log M < Real.log (‖z‖ / 2) := by
    have hMsq_pos : 0 < M ^ 2 := pow_pos hMpos 2
    have hz2pos : 0 < ‖z‖ / 2 := by nlinarith [hsq, hMsq_pos]
    have hlogeq : 2 * Real.log M = Real.log (M ^ 2) := by
      rw [Real.log_pow]; push_cast; ring
    rw [hlogeq, Real.log_lt_log_iff (pow_pos hMpos 2) hz2pos]
    exact hsq
  -- Lower bound `log (‖z‖/2) ≤ G_c z`.
  have hlow : Real.log (‖z‖ / 2) ≤ Work.Escape.green (Tantibar c) 2 z :=
    Work.Escape.log_half_le_green (Tantibar c) 2 ‖c‖
      (Work.Escape.monicGrowth_Tantibar c) le_rfl
      (by rw [Work.Escape.mem_escapeRegion]; exact hMax)
  -- Upper bound `G_c 0 ≤ 2 log M`.
  have hup : Work.Escape.greenParam c ≤ 2 * Real.log M := by
    have hge := Work.Escape.green_le_log (Tantibar c) 2 ‖c‖
      (Work.Escape.monicGrowth_Tantibar c) le_rfl 0
    have hsimp : max 2 (max (‖c‖ + 1) ‖(0 : ℂ)‖) = M := by
      have h1 : ‖c‖ + 1 = 1 + ‖c‖ := by ring
      rw [hMdef, norm_zero, h1, max_eq_left (by linarith [norm_nonneg c] : (0 : ℝ) ≤ 1 + ‖c‖)]
    rw [hsimp] at hge
    simpa [Work.Escape.greenParam] using hge
  -- Combine, then bridge to the `ParamRays` vocabulary.
  have hbridge : Work.Escape.greenParam c < Work.Escape.green (Tantibar c) 2 z := by
    linarith [hup, hlogM, hlow]
  rw [← Work.Escape.greenParam_eq_paramPotential c,
    ← Work.Bottcher.Contraction.green_eq_greenFun c z]
  exact hbridge

end Work.NAKANE.BottcherFar
