import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

open MeasureTheory Filter

namespace Commons.Analysis.GaussianMeasure

/-- A weighted Cauchy--Schwarz inequality: for nonnegative functions `a`, `b` and a weight `w`,
if `a ^ 2 * w` and `b ^ 2 * w` are integrable then
`∫ a * b * w ≤ sqrt (∫ a ^ 2 * w) * sqrt (∫ b ^ 2 * w)`. -/
theorem weighted_cauchy_schwarz {α : Type*} [MeasurableSpace α] (μ : Measure α) (a b w : α → ℝ)
    (hw : 0 ≤ w) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hameas : AEMeasurable a μ) (hbmeas : AEMeasurable b μ) (hwmeas : AEMeasurable w μ)
    (hai : Integrable (fun x => a x ^ 2 * w x) μ)
    (hbi : Integrable (fun x => b x ^ 2 * w x) μ) :
    ∫ x, a x * b x * w x ∂μ ≤
      Real.sqrt (∫ x, a x ^ 2 * w x ∂μ) * Real.sqrt (∫ x, b x ^ 2 * w x ∂μ) := by
  let A : α → ℝ := fun x => a x * Real.sqrt (w x)
  let B : α → ℝ := fun x => b x * Real.sqrt (w x)
  have hA2 : ∀ x, A x ^ 2 = a x ^ 2 * w x := by
    intro x; simp only [A]; rw [mul_pow, Real.sq_sqrt (hw x)]
  have hB2 : ∀ x, B x ^ 2 = b x ^ 2 * w x := by
    intro x; simp only [B]; rw [mul_pow, Real.sq_sqrt (hw x)]
  have hAB : ∀ x, A x * B x = a x * b x * w x := by
    intro x
    simp only [A, B]
    have hs : Real.sqrt (w x) * Real.sqrt (w x) = w x := by
      rw [← sq, Real.sq_sqrt (hw x)]
    calc a x * Real.sqrt (w x) * (b x * Real.sqrt (w x))
        = a x * b x * (Real.sqrt (w x) * Real.sqrt (w x)) := by ring
      _ = a x * b x * w x := by rw [hs]
  have hAmeas : AEStronglyMeasurable A μ :=
    hameas.aestronglyMeasurable.mul hwmeas.sqrt.aestronglyMeasurable
  have hBmeas : AEStronglyMeasurable B μ :=
    hbmeas.aestronglyMeasurable.mul hwmeas.sqrt.aestronglyMeasurable
  have hAint : Integrable (fun x => A x ^ 2) μ :=
    hai.congr (Filter.Eventually.of_forall fun x => (hA2 x).symm)
  have hBint : Integrable (fun x => B x ^ 2) μ :=
    hbi.congr (Filter.Eventually.of_forall fun x => (hB2 x).symm)
  have hAmem : MemLp A (ENNReal.ofReal (2:ℝ)) μ := by
    rw [show ENNReal.ofReal (2:ℝ) = 2 by norm_num]
    exact (memLp_two_iff_integrable_sq hAmeas).2 hAint
  have hBmem : MemLp B (ENNReal.ofReal (2:ℝ)) μ := by
    rw [show ENNReal.ofReal (2:ℝ) = 2 by norm_num]
    exact (memLp_two_iff_integrable_sq hBmeas).2 hBint
  have hAnonneg : 0 ≤ᵐ[μ] A := Filter.Eventually.of_forall fun x => by
    simp only [A]; exact mul_nonneg (ha x) (Real.sqrt_nonneg _)
  have hBnonneg : 0 ≤ᵐ[μ] B := Filter.Eventually.of_forall fun x => by
    simp only [B]; exact mul_nonneg (hb x) (Real.sqrt_nonneg _)
  have hpq : (2:ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]; norm_num
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) hpq hAnonneg hBnonneg hAmem hBmem
  have hleft : ∫ x, A x * B x ∂μ = ∫ x, a x * b x * w x ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => hAB x)
  have hrightA : (∫ x, A x ^ (2:ℝ) ∂μ) ^ ((1:ℝ)/2) = Real.sqrt (∫ x, a x ^ 2 * w x ∂μ) := by
    calc (∫ x, A x ^ (2:ℝ) ∂μ) ^ ((1:ℝ)/2)
        = Real.sqrt (∫ x, A x ^ (2:ℝ) ∂μ) := (Real.sqrt_eq_rpow _).symm
      _ = Real.sqrt (∫ x, a x ^ 2 * w x ∂μ) := by
          congr 1
          apply integral_congr_ae
          filter_upwards with x
          rw [Real.rpow_two, hA2 x]
  have hrightB : (∫ x, B x ^ (2:ℝ) ∂μ) ^ ((1:ℝ)/2) = Real.sqrt (∫ x, b x ^ 2 * w x ∂μ) := by
    calc (∫ x, B x ^ (2:ℝ) ∂μ) ^ ((1:ℝ)/2)
        = Real.sqrt (∫ x, B x ^ (2:ℝ) ∂μ) := (Real.sqrt_eq_rpow _).symm
      _ = Real.sqrt (∫ x, b x ^ 2 * w x ∂μ) := by
          congr 1
          apply integral_congr_ae
          filter_upwards with x
          rw [Real.rpow_two, hB2 x]
  calc ∫ x, a x * b x * w x ∂μ = ∫ x, A x * B x ∂μ := hleft.symm
    _ ≤ (∫ x, A x ^ (2:ℝ) ∂μ) ^ ((1:ℝ)/2) * (∫ x, B x ^ (2:ℝ) ∂μ) ^ ((1:ℝ)/2) := hholder
    _ = Real.sqrt (∫ x, a x ^ 2 * w x ∂μ) * Real.sqrt (∫ x, b x ^ 2 * w x ∂μ) := by
        rw [hrightA, hrightB]

/-- The `L²` Cauchy--Schwarz inequality for gradients with weight `exp (-f)`. -/
theorem l2_cauchy_schwarz_grad {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (f u h : E → ℝ) (hf : ContDiff ℝ 1 f) (hu : ContDiff ℝ 1 u) (hh : ContDiff ℝ 1 h) (hgu : MeasureTheory.Integrable (fun x => ‖fderiv ℝ u x‖ ^ 2 * Real.exp (-(f x)))) (hgh : MeasureTheory.Integrable (fun x => ‖fderiv ℝ h x‖ ^ 2 * Real.exp (-(f x)))) : (∫ x, inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x)) ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ h x)) * Real.exp (-(f x))) ≤ Real.sqrt (∫ x, ‖fderiv ℝ u x‖ ^ 2 * Real.exp (-(f x))) * Real.sqrt (∫ x, ‖fderiv ℝ h x‖ ^ 2 * Real.exp (-(f x))) := by
  let W : E → ℝ := fun x => Real.exp (-(f x))
  let a : E → ℝ := fun x => ‖fderiv ℝ u x‖
  let b : E → ℝ := fun x => ‖fderiv ℝ h x‖
  let gu : E → E := fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x)
  let gh : E → E := fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ h x)
  change (∫ x, inner ℝ (gu x) (gh x) * W x) ≤
      Real.sqrt (∫ x, a x ^ 2 * W x) * Real.sqrt (∫ x, b x ^ 2 * W x)
  have hWnn : 0 ≤ W := fun x => (Real.exp_pos _).le
  have hann : 0 ≤ a := fun x => norm_nonneg _
  have hbnn : 0 ≤ b := fun x => norm_nonneg _
  have hameas : AEMeasurable a volume := ((hu.continuous_fderiv one_ne_zero).norm).aemeasurable
  have hbmeas : AEMeasurable b volume := ((hh.continuous_fderiv one_ne_zero).norm).aemeasurable
  have hwmeas : AEMeasurable W volume := (Real.continuous_exp.comp hf.continuous.neg).aemeasurable
  have hgu' : Integrable (fun x => a x ^ 2 * W x) volume := by simpa only [a, W] using hgu
  have hgh' : Integrable (fun x => b x ^ 2 * W x) volume := by simpa only [b, W] using hgh
  have hgint : Integrable (fun x => a x ^ 2 * W x + b x ^ 2 * W x) volume := hgu'.add hgh'
  have hgucont : Continuous gu :=
    (LinearIsometryEquiv.continuous (InnerProductSpace.toDual ℝ E).symm).comp (hu.continuous_fderiv one_ne_zero)
  have hghcont : Continuous gh :=
    (LinearIsometryEquiv.continuous (InnerProductSpace.toDual ℝ E).symm).comp (hh.continuous_fderiv one_ne_zero)
  have hpoint : ∀ x, inner ℝ (gu x) (gh x) ≤ a x * b x := by
    intro x
    simp only [gu, gh, a, b]
    calc inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x)) ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ h x))
        ≤ ‖(InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x)‖ * ‖(InnerProductSpace.toDual ℝ E).symm (fderiv ℝ h x)‖ := real_inner_le_norm _ _
      _ = ‖fderiv ℝ u x‖ * ‖fderiv ℝ h x‖ := by rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]
  have hab_le : ∀ x, a x * b x ≤ a x ^ 2 + b x ^ 2 := by
    intro x
    nlinarith [two_mul_le_add_sq (a x) (b x), sq_nonneg (a x), sq_nonneg (b x)]
  have hbnd1 : ∀ x, ‖a x * b x * W x‖ ≤ a x ^ 2 * W x + b x ^ 2 * W x := by
    intro x
    rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (hann x) (hbnn x)) (hWnn x))]
    calc a x * b x * W x ≤ (a x ^ 2 + b x ^ 2) * W x := mul_le_mul_of_nonneg_right (hab_le x) (hWnn x)
      _ = a x ^ 2 * W x + b x ^ 2 * W x := by ring
  have hbnd2 : ∀ x, ‖inner ℝ (gu x) (gh x) * W x‖ ≤ a x ^ 2 * W x + b x ^ 2 * W x := by
    intro x
    have hI : ‖inner ℝ (gu x) (gh x)‖ ≤ a x * b x := by
      calc ‖inner ℝ (gu x) (gh x)‖ ≤ ‖gu x‖ * ‖gh x‖ := norm_inner_le_norm _ _
        _ = a x * b x := by
            simp only [gu, gh, a, b]
            rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]
    rw [norm_mul, Real.norm_of_nonneg (hWnn x)]
    calc ‖inner ℝ (gu x) (gh x)‖ * W x ≤ (a x * b x) * W x := mul_le_mul_of_nonneg_right hI (hWnn x)
      _ ≤ (a x ^ 2 + b x ^ 2) * W x := mul_le_mul_of_nonneg_right (hab_le x) (hWnn x)
      _ = a x ^ 2 * W x + b x ^ 2 * W x := by ring
  have hasm1 : AEStronglyMeasurable (fun x => a x * b x * W x) volume :=
    ((hameas.mul hbmeas).mul hwmeas).aestronglyMeasurable
  have hasm2 : AEStronglyMeasurable (fun x => inner ℝ (gu x) (gh x) * W x) volume := by
    have h1 : AEStronglyMeasurable (fun x => inner ℝ (gu x) (gh x)) volume :=
      (hgucont.aestronglyMeasurable).inner (hghcont.aestronglyMeasurable)
    exact h1.mul (Real.continuous_exp.comp hf.continuous.neg).aestronglyMeasurable
  have hrhs_int : Integrable (fun x => a x * b x * W x) volume :=
    Integrable.mono' hgint hasm1 (Filter.Eventually.of_forall hbnd1)
  have hlhs_int : Integrable (fun x => inner ℝ (gu x) (gh x) * W x) volume :=
    Integrable.mono' hgint hasm2 (Filter.Eventually.of_forall hbnd2)
  have hmono : ∫ x, inner ℝ (gu x) (gh x) * W x ≤ ∫ x, a x * b x * W x :=
    integral_mono hlhs_int hrhs_int (fun x => mul_le_mul_of_nonneg_right (hpoint x) (hWnn x))
  have hcs := weighted_cauchy_schwarz volume a b W hWnn hann hbnn hameas hbmeas hwmeas hgu' hgh'
  exact hmono.trans hcs

end Commons.Analysis.GaussianMeasure