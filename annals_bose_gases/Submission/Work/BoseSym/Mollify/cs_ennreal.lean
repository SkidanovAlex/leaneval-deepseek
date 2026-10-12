import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseSym.Mollify

open MeasureTheory ENNReal

/-- Cauchy–Schwarz / Hölder for the `ℒ²` seminorm: the (Bochner) integral of a product of two
functions is bounded in absolute value by the product of their `ℒ²` seminorms.  No integrability
hypothesis is needed: when `u * v` is not integrable the Bochner integral is `0`, and the
`lintegral` form of Hölder's inequality used below is valid for arbitrary functions. -/
theorem cs_ennreal {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α) {u v : α → ℝ}
    (hu : AEMeasurable u μ) (hv : AEMeasurable v μ) :
    ENNReal.ofReal ‖∫ t, u t * v t ∂μ‖
      ≤ MeasureTheory.eLpNorm u 2 μ * MeasureTheory.eLpNorm v 2 μ := by
  -- Rewrite the `lintegral` of the norm of the product as the product of the `enorm`s.
  have hY : (∫⁻ t, ENNReal.ofReal ‖u t * v t‖ ∂μ) = ∫⁻ t, ‖u t‖ₑ * ‖v t‖ₑ ∂μ := by
    refine lintegral_congr fun t => ?_
    simp only [ofReal_norm, enorm_mul]
  -- The integral is bounded by the `lintegral` of the norm.
  have h1 : ‖∫ t, u t * v t ∂μ‖ ≤ (∫⁻ t, ‖u t‖ₑ * ‖v t‖ₑ ∂μ).toReal := by
    rw [← hY]
    exact norm_integral_le_lintegral_norm _
  -- Hölder's inequality with the conjugate exponents `2` and `2`.
  have hH : ∫⁻ t, ‖u t‖ₑ * ‖v t‖ₑ ∂μ
      ≤ (∫⁻ t, ‖u t‖ₑ ^ (2:ℝ) ∂μ) ^ (1/2:ℝ) * (∫⁻ t, ‖v t‖ₑ ^ (2:ℝ) ∂μ) ^ (1/2:ℝ) :=
    ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hu.enorm hv.enorm
  -- Identify both factors with the corresponding `ℒ²` seminorms.
  have hu2 : MeasureTheory.eLpNorm u 2 μ = (∫⁻ t, ‖u t‖ₑ ^ (2:ℝ) ∂μ) ^ (1/2:ℝ) := by
    simp only [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) (by norm_num)
      (by norm_num) hu.aestronglyMeasurable, ENNReal.toReal_ofNat]
  have hv2 : MeasureTheory.eLpNorm v 2 μ = (∫⁻ t, ‖v t‖ₑ ^ (2:ℝ) ∂μ) ^ (1/2:ℝ) := by
    simp only [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) (by norm_num)
      (by norm_num) hv.aestronglyMeasurable, ENNReal.toReal_ofNat]
  have hH2 : (∫⁻ t, ‖u t‖ₑ * ‖v t‖ₑ ∂μ)
      ≤ MeasureTheory.eLpNorm u 2 μ * MeasureTheory.eLpNorm v 2 μ := by
    rw [hu2, hv2]
    exact hH
  by_cases htop : MeasureTheory.eLpNorm u 2 μ * MeasureTheory.eLpNorm v 2 μ = ⊤
  · rw [htop]
    exact le_top
  · have hle : ‖∫ t, u t * v t ∂μ‖
        ≤ (MeasureTheory.eLpNorm u 2 μ * MeasureTheory.eLpNorm v 2 μ).toReal :=
      h1.trans (ENNReal.toReal_mono htop hH2)
    calc ENNReal.ofReal ‖∫ t, u t * v t ∂μ‖
        ≤ ENNReal.ofReal ((MeasureTheory.eLpNorm u 2 μ * MeasureTheory.eLpNorm v 2 μ).toReal) :=
          ENNReal.ofReal_mono hle
      _ ≤ MeasureTheory.eLpNorm u 2 μ * MeasureTheory.eLpNorm v 2 μ := ENNReal.ofReal_toReal_le

end Work.BoseSym.Mollify
