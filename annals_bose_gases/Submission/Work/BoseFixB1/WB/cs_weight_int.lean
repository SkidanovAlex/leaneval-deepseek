import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Submission.Work.BoseFixB1.WB.cs_weight
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.WB.cs_weight_int`

Weighted Cauchy–Schwarz in integral form: for a.e. nonnegative `w : α → ℝ` and
`f, h : α → ℝ` such that `f²·w`, `h²·w` (and `f·h·w`) are integrable,

  `|∫ f·h·w| ≤ √(∫ f²·w) · √(∫ h²·w)`.

Proof: put `F := |f|·√w` and `H := |h|·√w`.  Both are pointwise nonnegative and
`F² = f²·w`, `H² = h²·w`, `F·H = |f·h·w|` almost everywhere, because `w ≥ 0`
a.e.  The abstract Cauchy–Schwarz inequality
`Work.BoseFixB1.WB.integral_mul_le_sqrt_mul_sqrt` applied to `F, H` then gives
`∫ F·H ≤ √(∫ F²)·√(∫ H²)`, and `|∫ f·h·w| ≤ ∫ |f·h·w| = ∫ F·H` finishes.
-/

open MeasureTheory Filter

namespace Work.BoseFixB1.WB

set_option linter.unusedVariables false

theorem cs_weight_int {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α) {w f h : α → ℝ}
    (hw : 0 ≤ᵐ[μ] w)
    (hf : MeasureTheory.Integrable (fun x => f x ^ 2 * w x) μ)
    (hh : MeasureTheory.Integrable (fun x => h x ^ 2 * w x) μ)
    (hfh : MeasureTheory.Integrable (fun x => f x * h x * w x) μ) :
    |∫ x, f x * h x * w x ∂μ| ≤
      Real.sqrt (∫ x, f x ^ 2 * w x ∂μ) * Real.sqrt (∫ x, h x ^ 2 * w x ∂μ) := by
  -- The two square roots of the weight, times `|f|` and `|h|` respectively.
  set F : α → ℝ := fun x => |f x| * Real.sqrt (w x) with hFdef
  set H : α → ℝ := fun x => |h x| * Real.sqrt (w x) with hHdef
  have hFsq : (fun x => F x ^ 2) =ᵐ[μ] (fun x => f x ^ 2 * w x) := by
    filter_upwards [hw] with x hx
    simp only [hFdef, mul_pow, sq_abs, Real.sq_sqrt hx]
  have hHsq : (fun x => H x ^ 2) =ᵐ[μ] (fun x => h x ^ 2 * w x) := by
    filter_upwards [hw] with x hx
    simp only [hHdef, mul_pow, sq_abs, Real.sq_sqrt hx]
  have hFi : Integrable (fun x => F x ^ 2) μ := hf.congr hFsq.symm
  have hHi : Integrable (fun x => H x ^ 2) μ := hh.congr hHsq.symm
  have hFnn : 0 ≤ᵐ[μ] F :=
    Eventually.of_forall fun _ => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  have hHnn : 0 ≤ᵐ[μ] H :=
    Eventually.of_forall fun _ => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  -- Cauchy–Schwarz for `F, H`.
  have hcs := integral_mul_le_sqrt_mul_sqrt μ hFnn hHnn hFi hHi
  rw [integral_congr_ae hFsq, integral_congr_ae hHsq] at hcs
  -- `F·H = |f·h·w|` a.e.
  have hFH : (fun x => F x * H x) =ᵐ[μ] (fun x => |f x * h x * w x|) := by
    filter_upwards [hw] with x hx
    have habs : |f x * h x * w x| = |f x| * |h x| * w x := by
      rw [abs_mul, abs_mul, abs_of_nonneg hx]
    simp only [hFdef, hHdef]
    rw [habs]
    calc (|f x| * Real.sqrt (w x)) * (|h x| * Real.sqrt (w x))
        = |f x| * |h x| * (Real.sqrt (w x) * Real.sqrt (w x)) := by ring
      _ = |f x| * |h x| * w x := by rw [Real.mul_self_sqrt hx]
  calc |∫ x, f x * h x * w x ∂μ|
      ≤ ∫ x, |f x * h x * w x| ∂μ := abs_integral_le_integral_abs
    _ = ∫ x, F x * H x ∂μ := (integral_congr_ae hFH).symm
    _ ≤ Real.sqrt (∫ x, f x ^ 2 * w x ∂μ) * Real.sqrt (∫ x, h x ^ 2 * w x ∂μ) := hcs

end Work.BoseFixB1.WB
