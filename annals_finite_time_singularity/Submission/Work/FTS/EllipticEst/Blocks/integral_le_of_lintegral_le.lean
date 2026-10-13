import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Blocks

/-- Auxiliary form of `integral_le_of_lintegral_le` for an arbitrary measure `μ`.
If `g, h ≥ 0`, `h` is `μ`-integrable and the `ofReal`-`lintegral` of `g` is bounded by
`ofReal C` times that of `h`, then the Bochner integrals satisfy the same bound. -/
private theorem integral_le_of_lintegral_le_aux {μ : MeasureTheory.Measure ℝ} {C : ℝ} (hC : 0 ≤ C)
    {g h : ℝ → ℝ} (hg : ∀ z, 0 ≤ g z) (hh : ∀ z, 0 ≤ h z)
    (hhint : MeasureTheory.Integrable h μ)
    (hlin : (∫⁻ z, ENNReal.ofReal (g z) ∂μ)
            ≤ ENNReal.ofReal C * ∫⁻ z, ENNReal.ofReal (h z) ∂μ) :
    (∫ z, g z ∂μ) ≤ C * ∫ z, h z ∂μ := by
  -- the `ofReal`-`lintegral` of the nonnegative integrable function `h`
  have hAh : ENNReal.ofReal (∫ z, h z ∂μ) = ∫⁻ z, ENNReal.ofReal (h z) ∂μ :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hhint (Filter.Eventually.of_forall hh)
  have hIh : 0 ≤ ∫ z, h z ∂μ := MeasureTheory.integral_nonneg hh
  -- rewrite the hypothesis as a bound by `ofReal (C * ∫ h)`
  have hbnd : (∫⁻ z, ENNReal.ofReal (g z) ∂μ) ≤ ENNReal.ofReal (C * ∫ z, h z ∂μ) := by
    rw [← hAh, ← ENNReal.ofReal_mul hC] at hlin
    exact hlin
  by_cases hgi : MeasureTheory.Integrable g μ
  · -- `g` integrable: its Bochner integral is the `toReal` of its `ofReal`-`lintegral`
    have hgeq : ∫ z, g z ∂μ = (∫⁻ z, ENNReal.ofReal (g z) ∂μ).toReal :=
      MeasureTheory.integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hg)
        hgi.aestronglyMeasurable
    rw [hgeq]
    have hmono := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbnd
    rwa [ENNReal.toReal_ofReal (mul_nonneg hC hIh)] at hmono
  · -- `g` not integrable: the Bochner integral is `0`, and `C * ∫ h ≥ 0`
    rw [MeasureTheory.integral_undef hgi]
    exact mul_nonneg hC hIh

/-- The Bochner-integral form of a `lintegral` bound for nonnegative functions: if the `ofReal`-`lintegral` of `g` over `(0,∞)` is bounded by `ofReal C` times that of `h`, then the Bochner integrals satisfy the same bound. Note that no integrability of `g` is needed: when `g` is not integrable the left-hand Bochner integral is `0`, and `C * ∫ h ≥ 0` because `h ≥ 0`. -/
theorem integral_le_of_lintegral_le {C : ℝ} (hC : 0 ≤ C) {g h : ℝ → ℝ}
    (hg : ∀ z, 0 ≤ g z) (hh : ∀ z, 0 ≤ h z)
    (hhint : MeasureTheory.IntegrableOn h (Set.Ioi 0))
    (hlin : MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi 0))
              (fun z => ENNReal.ofReal (g z))
            ≤ ENNReal.ofReal C * MeasureTheory.lintegral
              (MeasureTheory.volume.restrict (Set.Ioi 0)) (fun z => ENNReal.ofReal (h z))) :
    (∫ z in Set.Ioi 0, g z) ≤ C * ∫ z in Set.Ioi 0, h z := by
  exact integral_le_of_lintegral_le_aux (μ := MeasureTheory.volume.restrict (Set.Ioi 0))
    hC hg hh hhint hlin

end Work.FTS.EllipticEst.Blocks
