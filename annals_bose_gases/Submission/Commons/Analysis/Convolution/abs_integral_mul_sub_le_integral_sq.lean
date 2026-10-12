import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Analysis.Convolution

open MeasureTheory

theorem abs_integral_mul_sub_le_integral_sq {G : Type*} [MeasurableSpace G] [AddGroup G]
    [MeasurableAdd G] [MeasurableNeg G] {μ : Measure G} [μ.IsAddRightInvariant] [μ.IsNegInvariant]
    {f : G → ℝ} (hf : MemLp f 2 μ) (x : G) :
    |∫ y, f y * f (x - y) ∂μ| ≤ ∫ y, f y ^ 2 ∂μ := by
  have hφ : MeasurePreserving (fun y : G => x - y) μ μ := by
    have h1 : MeasurePreserving (fun z : G => z + (-x)) μ μ := measurePreserving_add_right μ (-x)
    have h2 : MeasurePreserving (fun z : G => -z) μ μ := Measure.measurePreserving_neg μ
    have h3 : MeasurePreserving (fun z : G => -(z + -x)) μ μ := h2.comp h1
    convert h3 using 1
    ext y
    rw [sub_eq_add_neg, neg_add_rev, neg_neg]
  have hg : MemLp (fun y : G => f (x - y)) 2 μ := hf.comp_measurePreserving hφ
  have hf' : MemLp f (ENNReal.ofReal 2) μ := by simpa using hf
  have hg' : MemLp (fun y : G => f (x - y)) (ENNReal.ofReal 2) μ := by simpa using hg
  have hA : (∫ y, ‖f y‖ ^ (2:ℝ) ∂μ) = ∫ y, f y ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards with y
    rw [Real.norm_eq_abs, Real.rpow_two, sq_abs]
  have hB : (∫ y, ‖f (x - y)‖ ^ (2:ℝ) ∂μ) = ∫ y, f y ^ 2 ∂μ := by
    have h1 : (∫ y, ‖f (x - y)‖ ^ (2:ℝ) ∂μ) = ∫ y, (fun z => f z ^ 2) (x - y) ∂μ := by
      apply integral_congr_ae
      filter_upwards with y
      rw [Real.norm_eq_abs, Real.rpow_two, sq_abs]
    rw [h1]
    exact MeasurePreserving.integral_comp hφ (measurableEmbedding_subLeft x) (fun z => f z ^ 2)
  have hnonneg : 0 ≤ ∫ y, f y ^ 2 ∂μ := integral_nonneg (fun y => sq_nonneg (f y))
  calc |∫ y, f y * f (x - y) ∂μ|
      ≤ ∫ y, |f y * f (x - y)| ∂μ := abs_integral_le_integral_abs
    _ = ∫ y, ‖f y‖ * ‖f (x - y)‖ ∂μ := by
        apply integral_congr_ae
        filter_upwards with y
        rw [abs_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ (∫ y, ‖f y‖ ^ (2:ℝ) ∂μ) ^ (1 / 2) *
          (∫ y, ‖f (x - y)‖ ^ (2:ℝ) ∂μ) ^ (1 / 2) :=
        integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hf' hg'
    _ = ∫ y, f y ^ 2 ∂μ := by
        rw [hA, hB, ← Real.sqrt_eq_rpow, ← sq, Real.sq_sqrt hnonneg]

end Commons.Analysis.Convolution