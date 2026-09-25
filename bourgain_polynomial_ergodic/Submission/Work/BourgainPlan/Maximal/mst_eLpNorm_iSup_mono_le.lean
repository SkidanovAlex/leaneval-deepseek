import Mathlib

namespace Work.BourgainPlan.Maximal

open MeasureTheory ENNReal

/-- For a positive real exponent, `x ^ y` commutes with arbitrary suprema in `ℝ≥0∞`. -/
theorem iSup_rpow_of_pos {ι : Sort*} (a : ι → ENNReal) {y : ℝ} (hy : 0 < y) :
    (⨆ i, a i) ^ y = ⨆ i, (a i) ^ y := by
  have h := OrderIso.map_iSup (ENNReal.orderIsoRpow y hy) a
  rw [ENNReal.orderIsoRpow_apply] at h
  simp only [ENNReal.orderIsoRpow_apply] at h
  exact h

theorem mst_eLpNorm_iSup_mono_le {q : ℝ} (hq : 0 < q) {u : ℕ → ℤ → ENNReal}
    (hmono : Monotone u) {D : ENNReal}
    (h : ∀ n : ℕ, MeasureTheory.eLpNorm (u n) (ENNReal.ofReal q) MeasureTheory.Measure.count ≤ D) :
    MeasureTheory.eLpNorm (fun m : ℤ => ⨆ n : ℕ, u n m) (ENNReal.ofReal q) MeasureTheory.Measure.count ≤ D := by
  set p : ENNReal := ENNReal.ofReal q with hp_def
  have hq0 : p ≠ 0 := by rw [hp_def]; exact (ENNReal.ofReal_pos.mpr hq).ne'
  have hqt : p ≠ ⊤ := by rw [hp_def]; exact ENNReal.ofReal_ne_top
  have htr : p.toReal = q := by rw [hp_def]; exact ENNReal.toReal_ofReal hq.le
  have hqinv : 0 < 1 / q := one_div_pos.mpr hq
  have hmono' : Monotone (fun n : ℕ => fun m : ℤ => (u n m) ^ q) :=
    fun a b hab m => ENNReal.rpow_le_rpow (hmono hab m) hq.le
  have hL1 : eLpNorm (fun m : ℤ => ⨆ n : ℕ, u n m) p Measure.count
      = (∫⁻ m : ℤ, (⨆ n : ℕ, u n m) ^ q ∂Measure.count) ^ (1 / q) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqt .of_discrete, htr]
    congr 1
  have hL2 : (∫⁻ m : ℤ, (⨆ n : ℕ, u n m) ^ q ∂Measure.count)
      = ⨆ n : ℕ, ∫⁻ m : ℤ, (u n m) ^ q ∂Measure.count := by
    have hcongr : (∫⁻ m : ℤ, (⨆ n : ℕ, u n m) ^ q ∂Measure.count)
        = ∫⁻ m : ℤ, ⨆ n : ℕ, (u n m) ^ q ∂Measure.count := by
      apply lintegral_congr
      intro m
      exact iSup_rpow_of_pos (fun n => u n m) hq
    rw [hcongr, lintegral_iSup]
    · intro n
      measurability
    · exact hmono'
  have hAn : ∀ n : ℕ, eLpNorm (u n) p Measure.count
      = (∫⁻ m : ℤ, (u n m) ^ q ∂Measure.count) ^ (1 / q) := by
    intro n
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqt .of_discrete, htr]
    congr 1
  have key : eLpNorm (fun m : ℤ => ⨆ n : ℕ, u n m) p Measure.count
      = ⨆ n : ℕ, eLpNorm (u n) p Measure.count := by
    rw [hL1, hL2]
    simp_rw [hAn]
    exact iSup_rpow_of_pos (fun n => ∫⁻ m : ℤ, (u n m) ^ q ∂Measure.count) hqinv
  rw [key]
  exact iSup_le h

end Work.BourgainPlan.Maximal
