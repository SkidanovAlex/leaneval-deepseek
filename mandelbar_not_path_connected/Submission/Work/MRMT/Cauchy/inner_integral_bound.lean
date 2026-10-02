import Mathlib
import Submission.Work.MRMT.Cauchy.lintegral_ofReal_norm_inv_ball_uniform

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Cauchy

open MeasureTheory Set ENNReal
open scoped ENNReal

/-- **The kernel `z ↦ ‖ζ - z‖⁻¹` has uniformly bounded `lintegral` over a compact (bounded) set.**
For `K ⊆ Metric.ball (0 : ℂ) R` with `R ≥ 0`, and every `ζ : ℂ`,
`∫⁻ z in K, ENNReal.ofReal (‖ζ - z‖⁻¹) ≤ ENNReal.ofReal (8 * Real.pi * R)`.

Hints for the prover.  `MeasureTheory.lintegral_mono_set` with `hK : K ⊆ Metric.ball 0 R` reduces
the claim to the ball `Metric.ball 0 R`.  Then substitute `z ↦ z - ζ`: rewrite `‖ζ - z‖` to
`‖z - ζ‖` (`norm_sub_rev`), turn the set integral into `∫⁻ z, (Metric.ball 0 R).indicator G' z` with
`MeasureTheory.lintegral_indicator` where `G' z = ENNReal.ofReal (‖z - ζ‖⁻¹)`, and use the pointwise
identity `(Metric.ball (0:ℂ) R).indicator (fun z => G (z - ζ)) z = (Metric.ball (-ζ) R).indicator G (z - ζ)`
where `G w = ENNReal.ofReal (‖w‖⁻¹)` (the sets correspond under `z ↦ z - ζ`, and
`‖(z - ζ) - (-ζ)‖ = ‖z‖`).  Then `MeasureTheory.MeasurePreserving.lintegral_comp` for the
measure-preserving bijection `z ↦ z - ζ` (`MeasureTheory.measurePreserving_sub_right`, needs
`Measurable G` via `ENNReal.measurable_ofReal.comp measurable_norm`) gives
`∫⁻ w in Metric.ball (-ζ) R, G w`.  Finish with
`Work.MRMT.Cauchy.lintegral_ofReal_norm_inv_ball_uniform R hR (-ζ)`. -/
theorem inner_integral_bound (K : Set ℂ) (R : ℝ) (hR : 0 ≤ R) (hK : K ⊆ Metric.ball (0 : ℂ) R)
    (ζ : ℂ) :
    ∫⁻ z in K, ENNReal.ofReal (‖ζ - z‖⁻¹) ≤ ENNReal.ofReal (8 * Real.pi * R) := by
  classical
  set G : ℂ → ℝ≥0∞ := fun w => ENNReal.ofReal (‖w‖⁻¹) with hGdef
  have hGmeas : Measurable G := by
    rw [hGdef]
    exact ENNReal.measurable_ofReal.comp measurable_norm.inv
  have hmono : ∫⁻ z in K, ENNReal.ofReal (‖ζ - z‖⁻¹)
      ≤ ∫⁻ z in Metric.ball (0 : ℂ) R, ENNReal.ofReal (‖ζ - z‖⁻¹) :=
    lintegral_mono_set hK
  refine hmono.trans ?_
  have hshift : ∫⁻ z in Metric.ball (0 : ℂ) R, ENNReal.ofReal (‖ζ - z‖⁻¹)
      = ∫⁻ w in Metric.ball (-ζ) R, G w := by
    have e1 : ∫⁻ z in Metric.ball (0 : ℂ) R, ENNReal.ofReal (‖ζ - z‖⁻¹)
        = ∫⁻ z in Metric.ball (0 : ℂ) R, G (z - ζ) := by
      apply setLIntegral_congr_fun measurableSet_ball
      intro z _
      rw [hGdef]
      simp [norm_sub_rev]
    rw [e1]
    have hkey : ∀ z : ℂ, (Metric.ball (0 : ℂ) R).indicator (fun z => G (z - ζ)) z
        = (Metric.ball (-ζ) R).indicator G (z - ζ) := by
      intro z
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases hz : z ∈ Metric.ball (0 : ℂ) R
      · rw [ite_eq_left hz, ite_eq_left (by simpa [Metric.mem_ball, dist_eq_norm] using hz)]
      · rw [ite_eq_right hz, ite_eq_right (by simpa [Metric.mem_ball, dist_eq_norm] using hz)]
    calc ∫⁻ z in Metric.ball (0 : ℂ) R, G (z - ζ)
        = ∫⁻ z, (Metric.ball (0 : ℂ) R).indicator (fun z => G (z - ζ)) z :=
          (lintegral_indicator measurableSet_ball (fun z => G (z - ζ))).symm
      _ = ∫⁻ z, (Metric.ball (-ζ) R).indicator G (z - ζ) := lintegral_congr hkey
      _ = ∫⁻ w, (Metric.ball (-ζ) R).indicator G w :=
          (measurePreserving_sub_right volume ζ).lintegral_comp
            (hGmeas.indicator measurableSet_ball)
      _ = ∫⁻ w in Metric.ball (-ζ) R, G w :=
          lintegral_indicator measurableSet_ball G
  rw [hshift]
  simpa only [hGdef] using lintegral_ofReal_norm_inv_ball_uniform R hR (-ζ)

end Work.MRMT.Cauchy
