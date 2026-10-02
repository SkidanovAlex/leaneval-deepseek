import Mathlib
import Submission.Work.FatouCoord.Setup
import Submission.Work.FatouCoord.Petal.reflected_inverse_germ

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouCoord.Repelling

open Set Metric

/-- For a parabolic germ `f z = z + z ^ 2 * h z` satisfying the quantitative hypotheses
`ParabolicBounds f h a r A A'`, the chart-conjugate dynamics `wMap f w = -1 / f (-1 / w)` is
injective on the complement of a large disc.  Indeed `f` is locally biholomorphic at `0`
(it has `f 0 = 0`, `f' 0 = 1`), so on a small disc `f` has a two-sided inverse `finv`; and for
`‖w‖` large the point `-1 / w` lies in that disc.  Since `wMap f w = chart (f (chart w))` and
`chart z = -1 / z` is injective, `wMap f w = wMap f w'` forces `f (chart w) = f (chart w')`,
hence `chart w = chart w'` and finally `w = w'`. -/
theorem wMap_injOn_large {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ} (hb : Work.FatouCoord.ParabolicBounds f h a r A A') : ∃ ρ : ℝ, 0 < ρ ∧ Set.InjOn (Work.FatouCoord.wMap f) {y : ℂ | ρ ≤ ‖y‖} := by
  obtain ⟨finv, F, hF, r', A'', A''', hb', hleft, hright, hFdef⟩ :=
    Work.FatouCoord.Petal.reflected_inverse_germ hb
  have hr' : 0 < r' := hb'.hr
  refine ⟨1 / r' + 1, by positivity, ?_⟩
  intro w hw w' hw' hww
  simp only [Set.mem_ofPred_eq] at hw hw'
  have h1 : (r')⁻¹ < ‖w‖ := by simpa [one_div] using (by linarith : 1 / r' < ‖w‖)
  have h1' : (r')⁻¹ < ‖w'‖ := by simpa [one_div] using (by linarith : 1 / r' < ‖w'‖)
  have hw0 : w ≠ 0 := by
    intro h; rw [h, norm_zero] at h1
    exact absurd h1 (not_lt.mpr (by positivity))
  have hw0' : w' ≠ 0 := by
    intro h; rw [h, norm_zero] at h1'
    exact absurd h1' (not_lt.mpr (by positivity))
  have hcw : chart w ∈ ball 0 r' := by
    rw [mem_ball_zero_iff, norm_chart hw0]
    exact inv_lt_of_inv_lt₀ hr' h1
  have hcw' : chart w' ∈ ball 0 r' := by
    rw [mem_ball_zero_iff, norm_chart hw0']
    exact inv_lt_of_inv_lt₀ hr' h1'
  have heq : f (chart w) = f (chart w') := chart_injective hww
  have hzz : finv (f (chart w)) = finv (f (chart w')) := by rw [heq]
  have hcw_eq : chart w = chart w' :=
    (hleft (chart w) hcw).symm.trans (hzz.trans (hleft (chart w') hcw'))
  exact chart_injective hcw_eq

end Work.FatouCoord.Repelling
