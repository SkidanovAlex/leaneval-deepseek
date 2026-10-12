import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The integral of `1/‖x‖³` over a spherical shell in `ℝ³`

We compute, for `0 < a ≤ b`,

`∫_{a ≤ ‖x‖ < b} ‖x‖⁻³ dx = 4π (log b - log a)`,

which is the classical polar-coordinates computation: the shell
`{a ≤ ‖x‖ < b}` has volume element `4π r² dr` at radius `r`, so the integral is
`∫_a^b r^{-3} · 4π r² dr = 4π ∫_a^b dr/r = 4π (log b - log a)`.

The formal proof avoids `ENNReal`-valued "mass" distributions altogether: it
rewrites the set integral as the integral of `‖·‖` composed with the indicator of
the interval `Ico a b`, applies Mathlib's polar-coordinate formula
`MeasureTheory.integral_fun_norm_addHaar`, and evaluates the resulting one
dimensional integral with `intervalIntegral.integral_inv`.
-/

namespace Work.BoseFixB1B

open MeasureTheory MeasureTheory.Measure Set

theorem sphShellInv3Integral {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ x in {x : EuclideanSpace ℝ (Fin 3) | a ≤ ‖x‖ ∧ ‖x‖ < b}, (1 / ‖x‖ ^ 3)
      = 4 * Real.pi * (Real.log b - Real.log a) := by
  have hmeas : MeasurableSet {x : EuclideanSpace ℝ (Fin 3) | a ≤ ‖x‖ ∧ ‖x‖ < b} :=
    (measurableSet_Ici.preimage measurable_norm).inter
      (measurableSet_Iio.preimage measurable_norm)
  -- The shell integral is the integral over all of `E3` of the radial profile
  -- `1_{[a,b)} · r^{-3}` evaluated at `‖x‖`.
  have hA : ∫ x in {x : EuclideanSpace ℝ (Fin 3) | a ≤ ‖x‖ ∧ ‖x‖ < b}, (1 / ‖x‖ ^ 3)
      = ∫ x : EuclideanSpace ℝ (Fin 3), (Set.Ico a b).indicator (fun r : ℝ => (r ^ 3)⁻¹) ‖x‖ := by
    rw [← integral_indicator hmeas]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, Set.mem_Ico, one_div]
  -- The volume of the unit ball in `ℝ³` is `4π/3`.
  have hball : (volume : Measure (EuclideanSpace ℝ (Fin 3))).real (Metric.ball 0 1)
      = 4 * Real.pi / 3 := by
    rw [measureReal_def, EuclideanSpace.volume_ball_fin_three]
    simp
    rw [ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ Real.pi * 4 / 3)]
    ring
  -- The one dimensional radial integral: `∫_{r>0} r² · 1_{[a,b)}(r) r^{-3} dr = log b - log a`.
  have hX : ∫ y in Set.Ioi (0 : ℝ), y ^ 2 * (Set.Ico a b).indicator (fun r : ℝ => (r ^ 3)⁻¹) y
      = Real.log b - Real.log a := by
    have h1 : ∫ y in Set.Ioi (0 : ℝ), y ^ 2 * (Set.Ico a b).indicator (fun r : ℝ => (r ^ 3)⁻¹) y
        = ∫ y in Set.Ioi (0 : ℝ), (Set.Ico a b).indicator (fun r : ℝ => r⁻¹) y := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      by_cases hy : y ∈ Set.Ico a b
      · simp only [Set.indicator_of_mem hy]
        have hypos : y ≠ 0 := ne_of_gt (lt_of_lt_of_le ha hy.1)
        field_simp
      · simp [Set.indicator_of_notMem hy]
    rw [h1]
    rw [setIntegral_indicator measurableSet_Ico]
    have hset : Set.Ioi (0 : ℝ) ∩ Set.Ico a b = Set.Ico a b := by
      ext y; exact ⟨fun h => h.2, fun h => ⟨lt_of_lt_of_le ha h.1, h⟩⟩
    rw [hset]
    rw [setIntegral_congr_set Ico_ae_eq_Ioc]
    rw [← intervalIntegral.integral_of_le hab]
    have h0 : (0 : ℝ) ∉ Set.uIcc a b := by
      rw [Set.uIcc_of_le hab]
      exact fun h => absurd h.1 (not_le.mpr ha)
    rw [integral_inv h0, Real.log_div (ne_of_gt (lt_of_lt_of_le ha hab)) (ne_of_gt ha)]
  calc ∫ x in {x : EuclideanSpace ℝ (Fin 3) | a ≤ ‖x‖ ∧ ‖x‖ < b}, (1 / ‖x‖ ^ 3)
      = ∫ x : EuclideanSpace ℝ (Fin 3), (Set.Ico a b).indicator (fun r : ℝ => (r ^ 3)⁻¹) ‖x‖ := hA
    _ = Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) •
          (volume : Measure (EuclideanSpace ℝ (Fin 3))).real (Metric.ball 0 1) •
          ∫ y in Set.Ioi (0 : ℝ), y ^ (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1) •
            (Set.Ico a b).indicator (fun r : ℝ => (r ^ 3)⁻¹) y := by
          rw [MeasureTheory.integral_fun_norm_addHaar]
    _ = 4 * Real.pi * (Real.log b - Real.log a) := by
          rw [hball, finrank_euclideanSpace_fin]
          norm_num
          rw [hX]
          ring

end Work.BoseFixB1B
