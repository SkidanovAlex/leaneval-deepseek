import Mathlib.MeasureTheory.Function.L2Space

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

open MeasureTheory

/-- Cauchy–Schwarz / Hölder for `L²`: if `u` and `v` are (a.e. strongly) measurable with
`u²` and `v²` integrable, then `u * v` is integrable and
`|∫ u·v| ≤ √(∫u²) · √(∫v²)`. -/
theorem holder_two_mul (μ : MeasureTheory.Measure ℝ) (u v : ℝ → ℝ)
    (hu : MeasureTheory.AEStronglyMeasurable u μ) (hv : MeasureTheory.AEStronglyMeasurable v μ)
    (hu2 : MeasureTheory.Integrable (fun x => u x ^ 2) μ)
    (hv2 : MeasureTheory.Integrable (fun x => v x ^ 2) μ) :
    MeasureTheory.Integrable (fun x => u x * v x) μ ∧
      |∫ x, u x * v x ∂μ| ≤ Real.sqrt (∫ x, u x ^ 2 ∂μ) * Real.sqrt (∫ x, v x ^ 2 ∂μ) := by
  constructor
  · -- Integrability of the product: `u, v ∈ L²` implies `u * v ∈ L¹`.
    have hu' : MemLp u 2 μ := (memLp_two_iff_integrable_sq hu).mpr hu2
    have hv' : MemLp v 2 μ := (memLp_two_iff_integrable_sq hv).mpr hv2
    have h : MemLp (fun x => u x * v x) 1 μ := hu'.mul hv'
    exact memLp_one_iff_integrable.mp h
  · -- The Cauchy–Schwarz bound, via Hölder with `p = q = 2` applied to `|u|`, `|v|`.
    have huabs : MeasureTheory.AEStronglyMeasurable (fun x => |u x|) μ := by
      simpa only [Real.norm_eq_abs] using hu.norm
    have hvabs : MeasureTheory.AEStronglyMeasurable (fun x => |v x|) μ := by
      simpa only [Real.norm_eq_abs] using hv.norm
    have hui : MeasureTheory.Integrable (fun x => |u x| ^ 2) μ :=
      hu2.congr (Filter.Eventually.of_forall fun x => (sq_abs (u x)).symm)
    have hvi : MeasureTheory.Integrable (fun x => |v x| ^ 2) μ :=
      hv2.congr (Filter.Eventually.of_forall fun x => (sq_abs (v x)).symm)
    have hu' : MeasureTheory.MemLp (fun x => |u x|) 2 μ :=
      (MeasureTheory.memLp_two_iff_integrable_sq huabs).mpr hui
    have hv' : MeasureTheory.MemLp (fun x => |v x|) 2 μ :=
      (MeasureTheory.memLp_two_iff_integrable_sq hvabs).mpr hvi
    have hpq : (2:ℝ).HolderConjugate 2 :=
      Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
    have hholder := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) hpq
      (Filter.Eventually.of_forall fun x => abs_nonneg (u x))
      (Filter.Eventually.of_forall fun x => abs_nonneg (v x))
      (by rw [ENNReal.ofReal_ofNat]; exact hu')
      (by rw [ENNReal.ofReal_ofNat]; exact hv')
    have hA2eq : (∫ x, |u x| ^ (2:ℝ) ∂μ) = ∫ x, u x ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [Real.rpow_ofNat, sq_abs]
    have hB2eq : (∫ x, |v x| ^ (2:ℝ) ∂μ) = ∫ x, v x ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [Real.rpow_ofNat, sq_abs]
    calc |∫ x, u x * v x ∂μ| ≤ ∫ x, |u x * v x| ∂μ := abs_integral_le_integral_abs
      _ = ∫ x, |u x| * |v x| ∂μ := by
            apply integral_congr_ae
            filter_upwards with x
            rw [abs_mul]
      _ ≤ (∫ x, |u x| ^ (2:ℝ) ∂μ) ^ (1/2:ℝ) * (∫ x, |v x| ^ (2:ℝ) ∂μ) ^ (1/2:ℝ) := hholder
      _ = Real.sqrt (∫ x, u x ^ 2 ∂μ) * Real.sqrt (∫ x, v x ^ 2 ∂μ) := by
            rw [hA2eq, hB2eq, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]

end Work.Coercivity
