import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxA0

lemma abs_integral_mul_le_sqrt {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsFiniteMeasure μ]
    {f g : α → ℝ} (hf : MeasureTheory.MemLp f 2 μ) (hg : MeasureTheory.MemLp g 2 μ) :
    |∫ x, f x * g x ∂μ| ≤ Real.sqrt (∫ x, (f x) ^ 2 ∂μ) * Real.sqrt (∫ x, (g x) ^ 2 ∂μ) := by
  -- Hölder's inequality with conjugate exponents `p = q = 2`.
  have hpq : (2:ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]; norm_num
  have hf' : MeasureTheory.MemLp f (ENNReal.ofReal (2:ℝ)) μ := by simpa using hf
  have hg' : MeasureTheory.MemLp g (ENNReal.ofReal (2:ℝ)) μ := by simpa using hg
  have hH := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq (μ := μ) (f := f) (g := g) hpq hf' hg'
  -- Rewrite the `‖f‖ ^ 2` appearing in Hölder's inequality as `f ^ 2`.
  have hA : (∫ x, ‖f x‖ ^ (2:ℝ) ∂μ) = ∫ x, (f x) ^ 2 ∂μ :=
    MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall (fun x => by simp [Real.norm_eq_abs, sq_abs]))
  have hB : (∫ x, ‖g x‖ ^ (2:ℝ) ∂μ) = ∫ x, (g x) ^ 2 ∂μ :=
    MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall (fun x => by simp [Real.norm_eq_abs, sq_abs]))
  rw [← Real.norm_eq_abs (∫ x, f x * g x ∂μ)]
  calc ‖∫ x, f x * g x ∂μ‖
      ≤ ∫ x, ‖f x * g x‖ ∂μ := MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ x, ‖f x‖ * ‖g x‖ ∂μ := by simp only [norm_mul]
    _ ≤ (∫ x, ‖f x‖ ^ (2:ℝ) ∂μ) ^ (1/2:ℝ) * (∫ x, ‖g x‖ ^ (2:ℝ) ∂μ) ^ (1/2:ℝ) := hH
    _ = Real.sqrt (∫ x, (f x) ^ 2 ∂μ) * Real.sqrt (∫ x, (g x) ^ 2 ∂μ) := by
        rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, hA, hB]

end Work.SmallBoxA0
