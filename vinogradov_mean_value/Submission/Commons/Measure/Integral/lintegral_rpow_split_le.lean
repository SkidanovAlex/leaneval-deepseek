import Mathlib.MeasureTheory.Integral.MeanInequalities

namespace Commons.Measure.Integral

/-- Cauchy--Schwarz (Hölder with exponents `1/2`, `1/2`) for `ℝ≥0∞`-valued functions:
`∫ A^{(a+b)/2} B^{(a+b)/2} ≤ (∫ A^a B^b)^{1/2} (∫ A^b B^a)^{1/2}`. -/
theorem lintegral_rpow_split_le {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    {A B : α → ENNReal} (hA : AEMeasurable A μ) (hB : AEMeasurable B μ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    MeasureTheory.lintegral μ (fun x => A x ^ ((a + b) / 2) * B x ^ ((a + b) / 2))
      ≤ (MeasureTheory.lintegral μ (fun x => A x ^ a * B x ^ b)) ^ (1 / 2 : ℝ)
        * (MeasureTheory.lintegral μ (fun x => A x ^ b * B x ^ a)) ^ (1 / 2 : ℝ) := by
  have hpt : ∀ x, A x ^ ((a + b) / 2) * B x ^ ((a + b) / 2)
      = (A x ^ a * B x ^ b) ^ (1 / 2 : ℝ) * (A x ^ b * B x ^ a) ^ (1 / 2 : ℝ) := by
    intro x
    rw [ENNReal.mul_rpow_of_nonneg _ _ (show (0:ℝ) ≤ 1/2 by norm_num),
        ENNReal.mul_rpow_of_nonneg _ _ (show (0:ℝ) ≤ 1/2 by norm_num)]
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
    rw [show a * (1/2:ℝ) = a/2 by ring, show b * (1/2:ℝ) = b/2 by ring]
    rw [show (a+b)/2 = a/2 + b/2 by ring]
    rw [ENNReal.rpow_add_of_nonneg _ _ (by linarith) (by linarith)]
    rw [ENNReal.rpow_add_of_nonneg _ _ (by linarith) (by linarith)]
    ring
  have hFm : AEMeasurable (fun x => A x ^ a * B x ^ b) μ := (hA.pow_const a).mul (hB.pow_const b)
  have hGm : AEMeasurable (fun x => A x ^ b * B x ^ a) μ := (hA.pow_const b).mul (hB.pow_const a)
  calc
    MeasureTheory.lintegral μ (fun x => A x ^ ((a + b) / 2) * B x ^ ((a + b) / 2))
        = MeasureTheory.lintegral μ
            (fun x => (A x ^ a * B x ^ b) ^ (1 / 2 : ℝ) * (A x ^ b * B x ^ a) ^ (1 / 2 : ℝ)) :=
          MeasureTheory.lintegral_congr hpt
    _ ≤ (MeasureTheory.lintegral μ (fun x => A x ^ a * B x ^ b)) ^ (1 / 2 : ℝ)
        * (MeasureTheory.lintegral μ (fun x => A x ^ b * B x ^ a)) ^ (1 / 2 : ℝ) :=
          ENNReal.lintegral_mul_norm_pow_le hFm hGm (by norm_num) (by norm_num) (by norm_num)

end Commons.Measure.Integral