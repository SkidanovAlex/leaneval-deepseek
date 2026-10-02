import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

open MeasureTheory ENNReal

theorem eLpNorm_le_of_support_measure {f : ℂ → ℂ} {S : Set ℂ} {M V : ℝ} (hM : 0 ≤ M) (hV : 0 ≤ V)
    (hf : MeasureTheory.AEStronglyMeasurable f (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    (hS : MeasureTheory.NullMeasurableSet S (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    (hzero : ∀ z, z ∉ S → f z = 0) (hbound : ∀ z, ‖f z‖ ≤ M)
    (hmeas : (MeasureTheory.volume : MeasureTheory.Measure ℂ) S ≤ ENNReal.ofReal V) :
    MeasureTheory.eLpNorm f 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ) ≤
      ENNReal.ofReal (M * Real.sqrt V) := by
  set μ : Measure ℂ := MeasureTheory.volume with hμ
  set g : ℂ → ℂ := (M : ℝ) • (S.indicator fun _ => (1 : ℂ)) with hg
  have hfg : ∀ z, ‖f z‖ ≤ ‖g z‖ := by
    intro z
    rw [hg]
    by_cases hz : z ∈ S
    · rw [Pi.smul_apply, Set.indicator_of_mem hz]
      simp only [norm_smul, Real.norm_of_nonneg hM, norm_one, mul_one]
      exact hbound z
    · rw [Pi.smul_apply, Set.indicator_of_notMem hz, smul_zero, norm_zero, hzero z hz, norm_zero]
  have hexp : (1 : ℝ) / (2:ℝ≥0∞).toReal = 1/2 := by
    rw [ENNReal.toReal_ofNat]
  calc MeasureTheory.eLpNorm f 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)
      = MeasureTheory.eLpNorm f 2 μ := by rw [hμ]
    _ ≤ MeasureTheory.eLpNorm g 2 μ := eLpNorm_mono hf hfg
    _ = ‖(M : ℝ)‖ₑ * MeasureTheory.eLpNorm (S.indicator fun _ => (1 : ℂ)) 2 μ := by
          rw [hg, eLpNorm_const_smul]
    _ = ENNReal.ofReal M * (μ S) ^ (1/2 : ℝ) := by
          rw [Real.enorm_eq_ofReal hM, eLpNorm_indicator_const hS (by norm_num) (by norm_num),
            hexp, enorm_one, one_mul]
    _ ≤ ENNReal.ofReal M * (ENNReal.ofReal V) ^ (1/2 : ℝ) := by
          exact mul_le_mul_right (ENNReal.rpow_le_rpow hmeas (by norm_num)) (ENNReal.ofReal M)
    _ = ENNReal.ofReal M * ENNReal.ofReal (Real.sqrt V) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hV (by norm_num), Real.sqrt_eq_rpow]
    _ = ENNReal.ofReal (M * Real.sqrt V) := by
          rw [ENNReal.ofReal_mul hM]

end Work.MRMT.Found
