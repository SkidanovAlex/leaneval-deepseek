import Mathlib.MeasureTheory.Function.L2Space

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

open MeasureTheory

/-- Cauchy–Schwarz in squared form for the Bochner integral of real-valued functions:
`(∫ A·B)² ≤ (∫ A²)·(∫ B²)`.  No sign hypothesis is needed since the proof bounds
`|∫ A·B|` by `∫ |A|·|B|` and applies Hölder with `p = q = 2`. -/
theorem sq_integral_mul_le (μ : MeasureTheory.Measure (ℝ × ℝ)) (A B : ℝ × ℝ → ℝ)
    (hA : MeasureTheory.AEStronglyMeasurable A μ) (hB : MeasureTheory.AEStronglyMeasurable B μ)
    (hA2 : MeasureTheory.Integrable (fun a => A a ^ 2) μ) (hB2 : MeasureTheory.Integrable (fun a => B a ^ 2) μ) :
    (∫ a, A a * B a ∂μ) ^ 2 ≤ (∫ a, A a ^ 2 ∂μ) * (∫ a, B a ^ 2 ∂μ) := by
  have hAabs : MeasureTheory.AEStronglyMeasurable (fun a => |A a|) μ := by
    simpa only [Real.norm_eq_abs] using hA.norm
  have hBabs : MeasureTheory.AEStronglyMeasurable (fun a => |B a|) μ := by
    simpa only [Real.norm_eq_abs] using hB.norm
  have hAi : MeasureTheory.Integrable (fun a => |A a| ^ 2) μ :=
    hA2.congr (Filter.Eventually.of_forall fun a => (sq_abs (A a)).symm)
  have hBi : MeasureTheory.Integrable (fun a => |B a| ^ 2) μ :=
    hB2.congr (Filter.Eventually.of_forall fun a => (sq_abs (B a)).symm)
  have hA' : MeasureTheory.MemLp (fun a => |A a|) 2 μ :=
    (MeasureTheory.memLp_two_iff_integrable_sq hAabs).mpr hAi
  have hB' : MeasureTheory.MemLp (fun a => |B a|) 2 μ :=
    (MeasureTheory.memLp_two_iff_integrable_sq hBabs).mpr hBi
  have hpq : (2:ℝ).HolderConjugate 2 := Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hholder := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) hpq
    (Filter.Eventually.of_forall fun a => abs_nonneg (A a))
    (Filter.Eventually.of_forall fun a => abs_nonneg (B a))
    (by rw [ENNReal.ofReal_ofNat]; exact hA')
    (by rw [ENNReal.ofReal_ofNat]; exact hB')
  have hA2eq : (∫ a, |A a| ^ (2:ℝ) ∂μ) = ∫ a, A a ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards with a
    rw [Real.rpow_ofNat, sq_abs]
  have hB2eq : (∫ a, |B a| ^ (2:ℝ) ∂μ) = ∫ a, B a ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards with a
    rw [Real.rpow_ofNat, sq_abs]
  rw [hA2eq, hB2eq] at hholder
  have hAB : |∫ a, A a * B a ∂μ| ≤ (∫ a, A a ^ 2 ∂μ) ^ (1/2:ℝ) * (∫ a, B a ^ 2 ∂μ) ^ (1/2:ℝ) := by
    calc |∫ a, A a * B a ∂μ| ≤ ∫ a, |A a * B a| ∂μ := MeasureTheory.abs_integral_le_integral_abs
      _ = ∫ a, |A a| * |B a| ∂μ := by
            apply integral_congr_ae
            filter_upwards with a
            rw [abs_mul]
      _ ≤ _ := hholder
  have hsq : ((∫ a, A a ^ 2 ∂μ) ^ (1/2:ℝ) * (∫ a, B a ^ 2 ∂μ) ^ (1/2:ℝ)) ^ 2
      = (∫ a, A a ^ 2 ∂μ) * (∫ a, B a ^ 2 ∂μ) := by
    have hAn : 0 ≤ ∫ a, A a ^ 2 ∂μ := integral_nonneg_of_ae (Filter.Eventually.of_forall fun a => sq_nonneg (A a))
    have hBn : 0 ≤ ∫ a, B a ^ 2 ∂μ := integral_nonneg_of_ae (Filter.Eventually.of_forall fun a => sq_nonneg (B a))
    rw [mul_pow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sq_sqrt hAn, Real.sq_sqrt hBn]
  calc (∫ a, A a * B a ∂μ) ^ 2 = |∫ a, A a * B a ∂μ| ^ 2 := (sq_abs _).symm
    _ ≤ ((∫ a, A a ^ 2 ∂μ) ^ (1/2:ℝ) * (∫ a, B a ^ 2 ∂μ) ^ (1/2:ℝ)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hAB 2
    _ = (∫ a, A a ^ 2 ∂μ) * (∫ a, B a ^ 2 ∂μ) := hsq

end Work.Coercivity
