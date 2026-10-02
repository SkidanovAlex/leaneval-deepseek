import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Cauchy

open MeasureTheory Set ENNReal
open scoped ENNReal

/-- **Polar-coordinate computation of `∫⁻ ‖w‖⁻¹` over a ball centred at the origin.**

For `0 ≤ r`, `∫⁻ w in Metric.ball (0 : ℂ) r, ENNReal.ofReal (‖w‖⁻¹) = ENNReal.ofReal (2 * π * r)`.

This is the planar integral of the Newtonian-type kernel `1/‖w‖` over a disc of radius `r`; in
polar coordinates the integrand becomes `r⁻¹ · r = 1`, so the value is the area `2 π r`. -/
theorem lintegral_ofReal_norm_inv_ball_zero (r : ℝ) (hr : 0 ≤ r) :
    ∫⁻ w in Metric.ball (0 : ℂ) r, ENNReal.ofReal (‖w‖⁻¹) = ENNReal.ofReal (2 * Real.pi * r) := by
  have key := Complex.lintegral_comp_polarCoord_symm
    (Set.indicator (Metric.ball (0 : ℂ) r) (fun z => ENNReal.ofReal (‖z‖⁻¹)))
  rw [← MeasureTheory.lintegral_indicator Metric.isOpen_ball.measurableSet
    (fun z => ENNReal.ofReal (‖z‖⁻¹))]
  rw [← key]
  trans ∫⁻ p in Complex.polarCoord.target,
      (Set.Ioo (0:ℝ) r ×ˢ Set.Ioo (-Real.pi) Real.pi).indicator (fun _ => (1:ℝ≥0∞)) p
  · apply MeasureTheory.setLIntegral_congr_fun Complex.polarCoord.open_target.measurableSet
    intro p hp
    beta_reduce
    have hp1 : 0 < p.1 := hp.1
    have hp2 : p.2 ∈ Set.Ioo (-Real.pi) Real.pi := hp.2
    have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hp1]
    have hmem : Complex.polarCoord.symm p ∈ Metric.ball (0:ℂ) r ↔ p.1 < r := by
      rw [Metric.mem_ball, dist_zero_right, hnorm]
    by_cases hpr : p.1 < r
    · have h1 : Complex.polarCoord.symm p ∈ Metric.ball (0:ℂ) r := hmem.mpr hpr
      have h2 : p ∈ Set.Ioo (0:ℝ) r ×ˢ Set.Ioo (-Real.pi) Real.pi := by
        rw [Set.mem_prod]
        exact ⟨Set.mem_Ioo.mpr ⟨hp1, hpr⟩, hp2⟩
      rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2 (fun _ => (1:ℝ≥0∞)),
        smul_eq_mul, hnorm]
      rw [← ENNReal.ofReal_mul (le_of_lt hp1), mul_inv_cancel₀ (ne_of_gt hp1), ENNReal.ofReal_one]
    · have h1 : Complex.polarCoord.symm p ∉ Metric.ball (0:ℂ) r := fun h => hpr (hmem.mp h)
      have h2 : p ∉ Set.Ioo (0:ℝ) r ×ˢ Set.Ioo (-Real.pi) Real.pi := by
        intro h
        rw [Set.mem_prod] at h
        exact hpr (Set.mem_Ioo.mp h.1).2
      rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2, smul_eq_mul, mul_zero]
  · rw [MeasureTheory.setLIntegral_indicator (measurableSet_Ioo.prod measurableSet_Ioo)
      (fun _ => (1:ℝ≥0∞)), MeasureTheory.setLIntegral_one]
    have hAT : Set.Ioo (0:ℝ) r ×ˢ Set.Ioo (-Real.pi) Real.pi ⊆ Complex.polarCoord.target := by
      intro x hx
      exact ⟨Set.Ioo_subset_Ioi_self hx.1, hx.2⟩
    rw [inter_eq_left.mpr hAT, MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod,
      Real.volume_Ioo, Real.volume_Ioo, sub_zero, show Real.pi - -Real.pi = 2 * Real.pi by ring,
      ← ENNReal.ofReal_mul hr]
    congr 1
    ring

/-- **Uniform bound for `‖w‖⁻¹` over a ball of radius `R`, any centre.**  For `R ≥ 0` and any
`c : ℂ`, `∫⁻ w in Metric.ball c R, ENNReal.ofReal (‖w‖⁻¹) ≤ ENNReal.ofReal (8 * Real.pi * R)`.

The proof splits on whether the centre is close to the origin.  If `‖c‖ ≤ 3 R`, the ball lies in
the disc of radius `4 R` centred at the origin, and
`lintegral_ofReal_norm_inv_ball_zero` gives the exact value `2 π (4 R) = 8 π R`.  Otherwise every
`w` in the ball satisfies `‖w‖ ≥ ‖c‖ - R > 2 R`, so the integrand is bounded by `1/(2 R)`
pointwise and the integral is at most `volume (ball c R) / (2 R) = π R / 2 ≤ 8 π R`. -/
theorem lintegral_ofReal_norm_inv_ball_uniform (R : ℝ) (hR : 0 ≤ R) (c : ℂ) :
    ∫⁻ w in Metric.ball c R, ENNReal.ofReal (‖w‖⁻¹) ≤ ENNReal.ofReal (8 * Real.pi * R) := by
  rcases eq_or_lt_of_le hR with h0 | hpos
  · rw [← h0]
    simp [Metric.ball_zero]
  · rcases le_or_gt (‖c‖) (3 * R) with hc | hc
    · -- The centre is close to the origin: the ball is contained in the disc of radius `4 R`.
      have hsub : Metric.ball c R ⊆ Metric.ball (0:ℂ) (4 * R) := by
        intro w hw
        rw [Metric.mem_ball, dist_eq_norm] at hw
        rw [Metric.mem_ball, dist_zero_right]
        calc ‖w‖ = ‖(w - c) + c‖ := by rw [sub_add_cancel]
          _ ≤ ‖w - c‖ + ‖c‖ := norm_add_le _ _
          _ < R + 3 * R := by linarith
          _ = 4 * R := by ring
      calc ∫⁻ w in Metric.ball c R, ENNReal.ofReal (‖w‖⁻¹)
          ≤ ∫⁻ w in Metric.ball (0:ℂ) (4 * R), ENNReal.ofReal (‖w‖⁻¹) :=
            MeasureTheory.lintegral_mono_set hsub
        _ = ENNReal.ofReal (8 * Real.pi * R) := by
            rw [lintegral_ofReal_norm_inv_ball_zero (4 * R) (by linarith)]
            congr 1
            ring
    · -- The centre is far from the origin: `‖w‖ > 2 R` on the ball.
      have hpoint : ∀ w ∈ Metric.ball c R,
          ENNReal.ofReal (‖w‖⁻¹) ≤ ENNReal.ofReal (1 / (2 * R)) := by
        intro w hw
        rw [Metric.mem_ball, dist_eq_norm] at hw
        have hwc : ‖c - w‖ < R := by rwa [norm_sub_rev] at hw
        have h2 : 2 * R < ‖w‖ := by
          have h3 : ‖c‖ - ‖c - w‖ ≤ ‖w‖ := by simpa using norm_sub_norm_le c (c - w)
          linarith
        apply ENNReal.ofReal_le_ofReal
        have h4 := one_div_le_one_div_of_le (by linarith : (0:ℝ) < 2 * R) (le_of_lt h2)
        simpa [one_div] using h4
      calc ∫⁻ w in Metric.ball c R, ENNReal.ofReal (‖w‖⁻¹)
          ≤ ∫⁻ w in Metric.ball c R, ENNReal.ofReal (1 / (2 * R)) :=
            MeasureTheory.setLIntegral_mono measurable_const hpoint
        _ = ENNReal.ofReal (1 / (2 * R)) * volume (Metric.ball c R) :=
            MeasureTheory.setLIntegral_const _ _
        _ = ENNReal.ofReal (1 / (2 * R)) * (ENNReal.ofReal R ^ 2 * (↑NNReal.pi : ℝ≥0∞)) := by
            rw [Complex.volume_ball]
        _ ≤ ENNReal.ofReal (8 * Real.pi * R) := by
            have hpi : (↑NNReal.pi : ℝ≥0∞) = ENNReal.ofReal Real.pi := by
              rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi]
            rw [hpi]
            have h1 : ENNReal.ofReal (1 / (2 * R)) *
                  (ENNReal.ofReal R ^ 2 * ENNReal.ofReal Real.pi)
                = ENNReal.ofReal (1 / (2 * R) * (R ^ 2 * Real.pi)) := by
              rw [← ENNReal.ofReal_pow hR, ← ENNReal.ofReal_mul (sq_nonneg R),
                ← ENNReal.ofReal_mul (p := 1 / (2 * R)) (by positivity)]
            rw [h1]
            apply ENNReal.ofReal_le_ofReal
            have h : 1 / (2 * R) * (R ^ 2 * Real.pi) = Real.pi * R / 2 := by field_simp
            rw [h]
            nlinarith [Real.pi_pos, hpos]

end Work.MRMT.Cauchy
