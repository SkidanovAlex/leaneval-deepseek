import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Cauchy

open MeasureTheory Metric

theorem radial_kernel_integrable (z : ℂ) (R : ℝ) {α : ℝ} (hα : α < 2) :
    MeasureTheory.Integrable (fun w : ℂ => if ‖w - z‖ ≤ R then ‖w - z‖ ^ (-α) else 0)
      (MeasureTheory.volume : MeasureTheory.Measure ℂ) := by
  -- Integrability of the version centred at the origin.
  have hG : Integrable (fun v : ℂ => if ‖v‖ ≤ R then ‖v‖ ^ (-α) else 0) volume := by
    -- `‖·‖ ^ (-α)` is integrable on a ball, since `α < 2 = finrank ℝ ℂ`.
    have hf_int : IntegrableOn (fun v : ℂ => ‖v‖ ^ (-α)) (ball 0 (R + 1)) volume := by
      have hα2 : α < (Module.finrank ℝ ℂ : ℝ) := by
        rw [Complex.finrank_real_complex]; exact hα
      refine integrableOn_ball_of_norm_le_rpow (E := ℂ) (F := ℝ) (μ := (volume : Measure ℂ))
        (C := 1) (α := α) (r := R + 1) ?_ hα2 ?_ ?_
      · rw [Complex.finrank_real_complex]; norm_num
      · filter_upwards with x
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), one_mul]
      · exact (Measurable.pow_const measurable_norm (-α)).aestronglyMeasurable
    have hf_on : IntegrableOn (fun v : ℂ => ‖v‖ ^ (-α)) (closedBall 0 R) volume :=
      hf_int.mono_set (fun x hx => by
        rw [mem_ball_zero_iff]
        have hx' := mem_closedBall_zero_iff.mp hx
        linarith)
    have h_ind : Integrable ((closedBall 0 R).indicator (fun v : ℂ => ‖v‖ ^ (-α))) volume :=
      hf_on.integrable_indicator (Metric.isClosed_closedBall.measurableSet)
    have hfun : (fun v : ℂ => if ‖v‖ ≤ R then ‖v‖ ^ (-α) else 0)
        = (closedBall 0 R).indicator (fun v : ℂ => ‖v‖ ^ (-α)) := by
      funext v
      simp [Set.indicator]
    rwa [hfun]
  -- Translate to the ball centred at `z`; `‖z - w‖ = ‖w - z‖`.
  have hmp := Measure.measurePreserving_sub_left (volume : Measure ℂ) z
  have hcomp := hmp.integrable_comp_of_integrable hG
  simpa only [Function.comp_def, norm_sub_rev] using hcomp

end Work.MRMT.Cauchy
