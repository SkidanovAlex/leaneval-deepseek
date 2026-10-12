import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

theorem absMulLeSqOfSqLe {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ]
    {f g : α → ℝ} {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hfm : Measurable f) (hfb : ∀ x, |f x| ≤ C)
    (hgm : Measurable g) (hgb : ∀ x, |g x| ≤ D)
    (h : ∫ x, g x ^ 2 ∂μ ≤ ∫ x, f x ^ 2 ∂μ) :
    ∫ x, |f x| * |g x| ∂μ ≤ ∫ x, f x ^ 2 ∂μ := by
  -- Both squares are integrable, since `f` and `g` are bounded and `μ` is a finite measure.
  have hfsq : MeasureTheory.Integrable (fun x => f x ^ 2) μ :=
    MeasureTheory.Integrable.of_bound (hfm.pow_const 2).aestronglyMeasurable (C ^ 2) (by
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact sq_le_sq' (abs_le.mp (hfb x)).1 (abs_le.mp (hfb x)).2)
  have hgsq : MeasureTheory.Integrable (fun x => g x ^ 2) μ :=
    MeasureTheory.Integrable.of_bound (hgm.pow_const 2).aestronglyMeasurable (D ^ 2) (by
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact sq_le_sq' (abs_le.mp (hgb x)).1 (abs_le.mp (hgb x)).2)
  have hfg : MeasureTheory.Integrable (fun x => |f x| * |g x|) μ :=
    MeasureTheory.Integrable.of_bound ((hfm.abs).mul (hgm.abs)).aestronglyMeasurable (C * D) (by
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))]
      exact mul_le_mul (hfb x) (hgb x) (abs_nonneg _) hC)
  -- Pointwise AM–GM: `|f x| * |g x| ≤ (f x ^ 2 + g x ^ 2) / 2`.
  have hpt : (fun x => |f x| * |g x|) ≤ fun x => (f x ^ 2 + g x ^ 2) / 2 := by
    intro x
    nlinarith [sq_nonneg (|f x| - |g x|), sq_abs (f x), sq_abs (g x)]
  have hsum : MeasureTheory.Integrable (fun x => (f x ^ 2 + g x ^ 2) / 2) μ :=
    (hfsq.add hgsq).div_const 2
  calc ∫ x, |f x| * |g x| ∂μ ≤ ∫ x, (f x ^ 2 + g x ^ 2) / 2 ∂μ :=
        MeasureTheory.integral_mono hfg hsum hpt
    _ = (∫ x, f x ^ 2 ∂μ + ∫ x, g x ^ 2 ∂μ) / 2 := by
        rw [MeasureTheory.integral_div, MeasureTheory.integral_add hfsq hgsq]
    _ ≤ ∫ x, f x ^ 2 ∂μ := by linarith

end Work.BoseBoxFock.PCFU
