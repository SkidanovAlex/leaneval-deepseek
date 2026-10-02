import Mathlib
import Submission.Work.NAKANE.Defs
import Submission.Work.NAKANE.GreenJoint

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.NAKANE.BottcherJoint

open Filter

/-- **Escape gap plus boundedness gives a far iterate.**  If `z` is bounded by `B`, `‖c‖ ≤ C`
and the potential of `z` exceeds `paramPotential c` by at least `s > 0`, then some fixed iterate of
`z` under the second return map `pMap c` is beyond `farRadius C`, uniformly in `(c,z)`.

Proof: `Work.Bottcher.CritBasic.green_pMap_four` gives `green c (pMap c w) = 4 * green c w` (for
*all* `c w`), so by induction `green c ((pMap c)^[N] z) = 4^N * green c z ≥ 4^N * s`; and
`Work.Escape.green_le_log` (chained through `Work.NAKANE.greenFun_eq_green` and
`Work.Escape.monicGrowth_Tantibar`) gives the upper bound
`green c w ≤ 2 * log (max 2 (max (‖c‖ + 1) ‖w‖))`.  Taking `N` with
`4^N * s > 2 * log (max 2 (max (C + 1) (farRadius C + 1)))` gives
`farRadius C < ‖(pMap c)^[N] z‖`. -/
theorem exists_far_iterate {C B s : ℝ} (hs : 0 < s) :
    ∃ N : ℕ, ∀ c z : ℂ, ‖c‖ ≤ C → ‖z‖ ≤ B →
      Work.ParamRays.paramPotential c + s ≤ Work.ParamRays.greenFun c z →
      Work.NAKANE.farRadius C < ‖(Work.Bottcher.pMap c)^[N] z‖ := by
  -- The threshold which certifies "far": any point `w` with `‖w‖ ≤ farRadius C` has Green
  -- value at most `M`.
  set M : ℝ := 2 * Real.log (max 2 (max (C + 1) (Work.NAKANE.farRadius C))) with hMdef
  -- Choose the iterate count `N` so that `4^N * s` beats that threshold.
  obtain ⟨N, hN⟩ : ∃ N : ℕ, M < (4 : ℝ) ^ N * s := by
    have h4 : Tendsto (fun n : ℕ => (4 : ℝ) ^ n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    have h4s : Tendsto (fun n : ℕ => (4 : ℝ) ^ n * s) atTop atTop :=
      h4.atTop_mul_const hs
    exact (h4s.eventually_gt_atTop M).exists
  refine ⟨N, fun c z hc _hB hgr => ?_⟩
  set w : ℂ := (Work.Bottcher.pMap c)^[N] z with hwdef
  -- The Green value of the initial point is at least `s`.
  have hsz : s ≤ Work.Bottcher.green c z := by
    rw [Work.Bottcher.CritBasic.green_eq]
    have hp := Work.ParamRays.paramPotential_nonneg c
    linarith
  -- `green` is multiplied by `4` under one application of `pMap c`, hence by `4^N` under `N`.
  have hiter : Work.Bottcher.green c w = (4 : ℝ) ^ N * Work.Bottcher.green c z := by
    have hall : ∀ k : ℕ, Work.Bottcher.green c ((Work.Bottcher.pMap c)^[k] z)
        = (4 : ℝ) ^ k * Work.Bottcher.green c z := by
      intro k
      induction k with
      | zero => simp
      | succ m ih =>
        rw [Function.iterate_succ_apply', Work.Bottcher.CritBasic.green_pMap_four, ih, pow_succ]
        ring
    rw [hwdef]
    exact hall N
  -- Consequently the Green value of `w` exceeds the threshold.
  have hbig : M < Work.Bottcher.green c w := by
    rw [hiter]
    calc M < (4 : ℝ) ^ N * s := hN
      _ ≤ (4 : ℝ) ^ N * Work.Bottcher.green c z :=
          mul_le_mul_of_nonneg_left hsz (by positivity)
  -- If `w` were not far, its Green value would be bounded by `M`, a contradiction.
  by_contra hcon
  have hcon' : ‖w‖ ≤ Work.NAKANE.farRadius C := le_of_not_gt hcon
  have hub : Work.Bottcher.green c w ≤ M := by
    change Work.Escape.green (LeanEval.ComplexAnalysis.Tantibar c) 2 w ≤ M
    have h := Work.Escape.green_le_log (LeanEval.ComplexAnalysis.Tantibar c) 2 ‖c‖
      (Work.Escape.monicGrowth_Tantibar c) le_rfl w
    refine h.trans ?_
    have hmax : max 2 (max (‖c‖ + 1) ‖w‖)
        ≤ max 2 (max (C + 1) (Work.NAKANE.farRadius C)) := by
      apply max_le_max le_rfl
      exact max_le_max (by linarith) hcon'
    have hpos : (0 : ℝ) < max 2 (max (‖c‖ + 1) ‖w‖) :=
      lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    have hlog := Real.log_le_log hpos hmax
    rw [hMdef]
    exact mul_le_mul_of_nonneg_left hlog (by norm_num)
  linarith [hub, hbig]

end Work.NAKANE.BottcherJoint
