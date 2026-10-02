import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Finiteness of the Cauchy-type integral over a ball

We show that for every centre `ζ : ℂ` and radius `Λ : ℝ`, the Cauchy kernel
`w ↦ (ζ - w)⁻¹` has finite Lebesgue (lower) integral over the ball
`Metric.ball 0 Λ`.  This is a local-integrability statement: the function
`w ↦ w⁻¹` is locally integrable on `ℂ` (its singularity has codimension `2`
there), hence so is any translate of it, and a ball is contained in a compact
set, on which a locally integrable function is integrable.
-/

namespace Work.Koebe

open MeasureTheory Metric

theorem lintegral_cauchy_ball_lt_top (Λ : ℝ) (ζ : ℂ) :
    ∫⁻ w in Metric.ball (0 : ℂ) Λ, ENNReal.ofReal ‖(ζ - w)⁻¹‖ < ⊤ := by
  rw [← hasFiniteIntegral_iff_norm (μ := volume.restrict (Metric.ball (0 : ℂ) Λ))
      (fun w : ℂ => (ζ - w)⁻¹)]
  -- `w ↦ w⁻¹` is locally integrable on `ℂ`: it is dominated by `‖w‖ ^ (-1)`
  -- and the singularity has codimension `2 = finrank ℝ ℂ`.
  have hinv : LocallyIntegrable (fun v : ℂ => v⁻¹) volume := by
    refine locallyIntegrable_of_norm_le_rpow (E := ℂ) (F := ℂ) (μ := volume) (C := 1) (α := 1)
      (by rw [Complex.finrank_real_complex]; norm_num) ?_ ?_ ?_
    · norm_num [Complex.finrank_real_complex]
    · filter_upwards with x
      rw [one_mul, norm_inv, Real.rpow_neg_one]
    · exact measurable_inv.aestronglyMeasurable
  -- the measure is invariant under `w ↦ ζ - w`.
  have hmap : Measure.map (⇑(Homeomorph.subLeft ζ)) volume = volume := by
    rw [show (⇑(Homeomorph.subLeft ζ) : ℂ → ℂ) = (fun t => ζ - t) from
      funext (Homeomorph.subLeft_apply ζ)]
    exact Measure.map_sub_left_eq_self volume ζ
  -- hence `w ↦ (ζ - w)⁻¹` is locally integrable too.
  have hloc : LocallyIntegrable (fun w : ℂ => (ζ - w)⁻¹) volume := by
    have h1 := (locallyIntegrable_map_homeomorph (Homeomorph.subLeft ζ)
      (f := fun v : ℂ => v⁻¹) (μ := volume)).mp (by rw [hmap]; exact hinv)
    simpa [Function.comp_def, Homeomorph.subLeft_apply] using h1
  have hK : IsCompact (Metric.closedBall (0 : ℂ) Λ) := isCompact_closedBall 0 Λ
  exact ((hloc.integrableOn_isCompact hK).mono_set Metric.ball_subset_closedBall).hasFiniteIntegral

end Work.Koebe
