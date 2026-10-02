import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.unusedVariables false

namespace Work.MRMT.Found

open MeasureTheory Filter
open scoped ENNReal Topology

/-- Dominated convergence for `∫⁻_Ω ofReal (C * ‖ν n z‖ * ‖w z‖²)`.

The functions `ν n` converge to `0` almost everywhere and are a.e. bounded by the
constant `B`, while `‖w‖²` has finite `lintegral` over `Ω` (bounded by `K`).  Hence the
integrand is dominated by the *fixed* function `ofReal (C * B * ‖w z‖²)`, whose
`lintegral` is `ofReal (C * B) * ∫⁻_Ω ofReal (‖w z‖²) ≤ ofReal (C * B * K) < ∞`, and
Lebesgue's dominated convergence theorem (in its `AEMeasurable`/`lintegral` form) gives
the result. -/
theorem tendsto_lintegral_ofReal_mul_normSq_of_ae_tendsto_zero {Ω : Set ℂ}
    {ν : ℕ → ℂ → ℂ}
    (hνmeas : ∀ n, MeasureTheory.AEStronglyMeasurable (ν n) (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    (hν0 : Filter.Eventually (fun z => Filter.Tendsto (fun n => ν n z) Filter.atTop (nhds 0))
      (MeasureTheory.ae (MeasureTheory.volume : MeasureTheory.Measure ℂ)))
    {B : ℝ} (hB : 0 ≤ B)
    (hνb : ∀ n, Filter.Eventually (fun z => ‖ν n z‖ ≤ B)
      (MeasureTheory.ae (MeasureTheory.volume : MeasureTheory.Measure ℂ)))
    {C : ℝ} (hC : 0 ≤ C)
    {w : ℂ → ℂ} (hwmeas : AEMeasurable w (MeasureTheory.Measure.restrict MeasureTheory.volume Ω))
    {K : ℝ} (hK : 0 ≤ K)
    (hwbdd : ∫⁻ z in Ω, ENNReal.ofReal (‖w z‖ ^ 2) ≤ ENNReal.ofReal K) :
    Filter.Tendsto (fun n => ∫⁻ z in Ω, ENNReal.ofReal (C * ‖ν n z‖ * ‖w z‖ ^ 2))
      Filter.atTop (nhds 0) := by
  set μ : MeasureTheory.Measure ℂ := MeasureTheory.Measure.restrict MeasureTheory.volume Ω with hμ
  have hνμ : ∀ n, AEStronglyMeasurable (ν n) μ := fun n =>
    (hνmeas n).mono_measure (by rw [hμ]; exact MeasureTheory.Measure.restrict_le_self)
  have hνb_μ : ∀ n, ∀ᵐ z ∂μ, ‖ν n z‖ ≤ B := fun n =>
    MeasureTheory.ae_restrict_of_ae (μ := MeasureTheory.volume) (s := Ω) (hνb n)
  have hν0_μ : ∀ᵐ z ∂μ, Tendsto (fun n => ν n z) atTop (𝓝 0) :=
    MeasureTheory.ae_restrict_of_ae (μ := MeasureTheory.volume) (s := Ω) hν0
  -- Measurability of the integrand.
  have hFmeas : ∀ n, AEMeasurable (fun z => ENNReal.ofReal (C * ‖ν n z‖ * ‖w z‖ ^ 2)) μ := by
    intro n
    have hνR : AEMeasurable (fun z => ‖ν n z‖) μ := (hνμ n).aemeasurable.norm
    have hwR : AEMeasurable (fun z => ‖w z‖ ^ 2) μ := hwmeas.norm.pow_const 2
    have hreal : AEMeasurable (fun z => C * ‖ν n z‖ * ‖w z‖ ^ 2) μ :=
      (hνR.const_mul C).mul hwR
    exact ENNReal.measurable_ofReal.comp_aemeasurable hreal
  -- The dominating function has finite `lintegral`.
  have hbound : ∫⁻ z, ENNReal.ofReal (C * B * ‖w z‖ ^ 2) ∂μ ≠ ⊤ := by
    have hwmeas' : AEMeasurable (fun z => ENNReal.ofReal (‖w z‖ ^ 2)) μ :=
      ENNReal.measurable_ofReal.comp_aemeasurable (hwmeas.norm.pow_const 2)
    have heq : ∫⁻ z, ENNReal.ofReal (C * B * ‖w z‖ ^ 2) ∂μ
        = ENNReal.ofReal (C * B) * ∫⁻ z, ENNReal.ofReal (‖w z‖ ^ 2) ∂μ := by
      rw [← MeasureTheory.lintegral_const_mul'' (ENNReal.ofReal (C * B)) hwmeas']
      apply MeasureTheory.lintegral_congr
      intro z
      rw [ENNReal.ofReal_mul (by positivity)]
    rw [heq]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hwbdd)
  -- The a.e. domination.
  have hda : ∀ n, (fun z => ENNReal.ofReal (C * ‖ν n z‖ * ‖w z‖ ^ 2))
      ≤ᵐ[μ] (fun z => ENNReal.ofReal (C * B * ‖w z‖ ^ 2)) := by
    intro n
    filter_upwards [hνb_μ n] with z hz
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hz hC) (sq_nonneg _)
  -- The a.e. pointwise convergence to `0`.
  have hlim : ∀ᵐ z ∂μ, Tendsto (fun n => ENNReal.ofReal (C * ‖ν n z‖ * ‖w z‖ ^ 2)) atTop (𝓝 0) := by
    filter_upwards [hν0_μ] with z hz
    have hzr : Tendsto (fun n => ‖ν n z‖) atTop (𝓝 0) := by simpa using hz.norm
    have hreal : Tendsto (fun n => C * ‖ν n z‖ * ‖w z‖ ^ 2) atTop (𝓝 0) := by
      have h1 := (hzr.const_mul C).mul_const (‖w z‖ ^ 2)
      simpa using h1
    have h2 := (ENNReal.continuous_ofReal.tendsto 0).comp hreal
    simpa [Function.comp_def] using h2
  have h := MeasureTheory.tendsto_lintegral_of_dominated_convergence' (μ := μ)
      (F := fun n z => ENNReal.ofReal (C * ‖ν n z‖ * ‖w z‖ ^ 2))
      (f := fun _ => (0 : ℝ≥0∞)) (fun z => ENNReal.ofReal (C * B * ‖w z‖ ^ 2))
      hFmeas hda hbound hlim
  simpa using h

end Work.MRMT.Found
