import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Tactic.Have
import Submission.Work.EllipticEst.InteriorRegularity.young_l1_l2
import Submission.Work.EllipticEst.InteriorRegularity.lintegral_mul_sq_le
import Submission.Work.EllipticEst.InteriorRegularity.lintegral_lintegral_conv_sq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.InteriorRegularity

open MeasureTheory ENNReal

/-- Young's convolution inequality `L¹ * L² → L²` in `eLpNorm` form, for a function `f` whose
pointwise (extended) norm is dominated by the upper lintegral of `y ↦ F (x - y) * u y`.

The hypothesis `hpt` is exactly the *weak* (lintegral) form of `‖f x‖ ≤ (F * u) x`, which is
what the elliptic-estimate workflow produces; the conclusion is the sharp `L²` bound.

The two computational inputs are supplied by the workspace lemmas
`Work.EllipticEst.InteriorRegularity.lintegral_mul_sq_le` (the weighted Cauchy–Schwarz
`(∫ F u)² ≤ (∫ F)(∫ F u²)`, pointwise in `x`) and
`Work.EllipticEst.InteriorRegularity.lintegral_lintegral_conv_sq` (Tonelli plus translation
invariance of Lebesgue measure, computing `∫ x ∫ y, F (x-y) u y² = (∫ F)(∫ u²)`). -/
theorem young_l1_l2_eLpNorm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {F u : E → ℝ} {f : E → ℂ}
    (hF : ∀ x, 0 ≤ F x) (hu : ∀ x, 0 ≤ u x)
    (hFi : MeasureTheory.Integrable F MeasureTheory.volume)
    (huM : MeasureTheory.MemLp u 2 MeasureTheory.volume)
    (hfm : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume)
    (hpt : ∀ x, ‖f x‖ₑ ≤ ∫⁻ y, ENNReal.ofReal (F (x - y) * u y) ∂MeasureTheory.volume) :
    MeasureTheory.eLpNorm f 2 MeasureTheory.volume
      ≤ ENNReal.ofReal (∫ z, F z) * MeasureTheory.eLpNorm u 2 MeasureTheory.volume := by
  have hFm : AEMeasurable F (volume : Measure E) := hFi.aemeasurable
  have hum : AEMeasurable u (volume : Measure E) := huM.aemeasurable
  -- `∫⁻` of `ofReal F` is `ofReal` of the integral
  have hAeq : ENNReal.ofReal (∫ z, F z) = ∫⁻ z, ENNReal.ofReal (F z) :=
    ofReal_integral_eq_lintegral_ofReal hFi (ae_of_all _ hF)
  have hAlt : (∫⁻ z, ENNReal.ofReal (F z)) ≠ ∞ := by
    rw [← hAeq]; exact ENNReal.ofReal_ne_top
  -- weighted Cauchy–Schwarz in `y`, with weight `√(F (x - y))`, for each `x`
  have hcs : ∀ x : E, (∫⁻ y, ENNReal.ofReal (F (x - y) * u y)) ^ (2:ℝ)
      ≤ (∫⁻ y, ENNReal.ofReal (F (x - y)))
        * (∫⁻ y, ENNReal.ofReal (F (x - y) * u y ^ 2)) :=
    fun x => lintegral_mul_sq_le hF hu hFm hum x
  -- translation invariance in `x`
  have htrans : ∀ x : E, (∫⁻ y, ENNReal.ofReal (F (x - y))) = ∫⁻ z, ENNReal.ofReal (F z) := by
    intro x
    exact lintegral_sub_left_eq_self (μ := (volume : Measure E))
      (fun z : E => ENNReal.ofReal (F z)) x
  -- Tonelli + translation invariance, computing the double integral of the `u ^ 2`-term
  have hK : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (F (x - y) * u y ^ 2))
      = (∫⁻ z, ENNReal.ofReal (F z)) * (∫⁻ y, ENNReal.ofReal (u y ^ 2)) :=
    lintegral_lintegral_conv_sq hF hu hFm hum
  -- the bound on the `L²` (squared) mass of `f`
  have hkey1 : (∫⁻ x, ‖f x‖ₑ ^ (2:ℝ))
      ≤ (∫⁻ z, ENNReal.ofReal (F z))
        * ((∫⁻ z, ENNReal.ofReal (F z)) * ∫⁻ y, ENNReal.ofReal (u y ^ 2)) := by
    calc (∫⁻ x, ‖f x‖ₑ ^ (2:ℝ))
        ≤ ∫⁻ x, (∫⁻ y, ENNReal.ofReal (F (x - y) * u y)) ^ (2:ℝ) :=
          lintegral_mono (fun x => ENNReal.rpow_le_rpow (hpt x) (by norm_num))
      _ ≤ ∫⁻ x, (∫⁻ y, ENNReal.ofReal (F (x - y)))
            * (∫⁻ y, ENNReal.ofReal (F (x - y) * u y ^ 2)) :=
          lintegral_mono (fun x => hcs x)
      _ = ∫⁻ x, (∫⁻ z, ENNReal.ofReal (F z))
            * (∫⁻ y, ENNReal.ofReal (F (x - y) * u y ^ 2)) := by
          refine lintegral_congr (fun x => ?_)
          rw [htrans x]
      _ = (∫⁻ z, ENNReal.ofReal (F z)) * ∫⁻ x, ∫⁻ y, ENNReal.ofReal (F (x - y) * u y ^ 2) :=
          lintegral_const_mul' _ _ hAlt
      _ = (∫⁻ z, ENNReal.ofReal (F z))
            * ((∫⁻ z, ENNReal.ofReal (F z)) * ∫⁻ y, ENNReal.ofReal (u y ^ 2)) := by
          rw [hK]
  have hfnorm : eLpNorm f (2:ℝ≥0∞) (volume : Measure E)
      = (∫⁻ x, ‖f x‖ₑ ^ (2:ℝ)) ^ ((1:ℝ)/2) := by
    rw [eLpNorm_eq_eLpNorm' (p := (2:ℝ≥0∞)) (by norm_num) (by norm_num) hfm,
      eLpNorm'_eq_lintegral_enorm]
    norm_num
  have hunorm : eLpNorm u (2:ℝ≥0∞) (volume : Measure E)
      = (∫⁻ y, ENNReal.ofReal (u y ^ 2)) ^ ((1:ℝ)/2) := by
    rw [eLpNorm_eq_eLpNorm' (p := (2:ℝ≥0∞)) (by norm_num) (by norm_num)
        huM.aestronglyMeasurable,
      eLpNorm'_eq_lintegral_enorm]
    norm_num
    congr 1
    refine lintegral_congr (fun y => ?_)
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hu y)]
    exact (ENNReal.ofReal_pow (hu y) 2).symm
  have hfinal : eLpNorm f (2:ℝ≥0∞) (volume : Measure E)
      ≤ ENNReal.ofReal (∫ z, F z) * eLpNorm u (2:ℝ≥0∞) (volume : Measure E) := by
    rw [hfnorm, hunorm, hAeq]
    calc (∫⁻ x, ‖f x‖ₑ ^ (2:ℝ)) ^ ((1:ℝ)/2)
        ≤ ((∫⁻ z, ENNReal.ofReal (F z))
            * ((∫⁻ z, ENNReal.ofReal (F z)) * ∫⁻ y, ENNReal.ofReal (u y ^ 2))) ^ ((1:ℝ)/2) :=
          ENNReal.rpow_le_rpow hkey1 (by norm_num)
      _ = (∫⁻ z, ENNReal.ofReal (F z)) * (∫⁻ y, ENNReal.ofReal (u y ^ 2)) ^ ((1:ℝ)/2) := by
          rw [← mul_assoc, ← pow_two, ← ENNReal.rpow_natCast,
            ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ (1:ℝ)/2),
            ← ENNReal.rpow_mul]
          norm_num
  exact hfinal

end Work.EllipticEst.InteriorRegularity
