import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A complex function is AEStronglyMeasurable when three squared moduli are

If `‖f‖²`, `‖f - 1‖²` and `‖f - I‖²` are all AEStronglyMeasurable, then so is `f`.
The point is that the real and imaginary parts of `f` are recovered linearly from
these quantities:
`‖z‖² - ‖z - 1‖² = 2 * z.re - 1` and `‖z‖² - ‖z - I‖² = 2 * z.im - 1`.
-/

namespace Work.Diff.STE

open MeasureTheory

/-- Recovering the real part of `z` from `‖z‖²` and `‖z - 1‖²`. -/
private lemma re_eq (z : ℂ) : (‖z‖ ^ 2 - ‖z - 1‖ ^ 2 + 1) * (1/2) = z.re := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply,
      Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  ring

/-- Recovering the imaginary part of `z` from `‖z‖²` and `‖z - I‖²`. -/
private lemma im_eq (z : ℂ) : (‖z‖ ^ 2 - ‖z - Complex.I‖ ^ 2 + 1) * (1/2) = z.im := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply,
      Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im]
  ring

theorem aestronglyMeasurable_of_norm_sq_sub {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    (f : α → ℂ)
    (hf : MeasureTheory.AEStronglyMeasurable (fun x => ‖f x‖ ^ 2) μ)
    (h1 : MeasureTheory.AEStronglyMeasurable (fun x => ‖f x - 1‖ ^ 2) μ)
    (h2 : MeasureTheory.AEStronglyMeasurable (fun x => ‖f x - Complex.I‖ ^ 2) μ) :
    MeasureTheory.AEStronglyMeasurable f μ := by
  have hRe : AEStronglyMeasurable (fun x => (‖f x‖ ^ 2 - ‖f x - 1‖ ^ 2 + 1) * (1/2)) μ :=
    ((hf.sub h1).add_const 1).mul_const (1/2)
  have hIm : AEStronglyMeasurable (fun x => (‖f x‖ ^ 2 - ‖f x - Complex.I‖ ^ 2 + 1) * (1/2)) μ :=
    ((hf.sub h2).add_const 1).mul_const (1/2)
  have hReC : AEStronglyMeasurable (fun x => (((‖f x‖ ^ 2 - ‖f x - 1‖ ^ 2 + 1) * (1/2) : ℝ) : ℂ)) μ :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hRe
  have hImC : AEStronglyMeasurable (fun x => (((‖f x‖ ^ 2 - ‖f x - Complex.I‖ ^ 2 + 1) * (1/2) : ℝ) : ℂ)) μ :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hIm
  have hsum : AEStronglyMeasurable (fun x => (((‖f x‖ ^ 2 - ‖f x - 1‖ ^ 2 + 1) * (1/2) : ℝ) : ℂ)
        + (((‖f x‖ ^ 2 - ‖f x - Complex.I‖ ^ 2 + 1) * (1/2) : ℝ) : ℂ) * Complex.I) μ :=
    hReC.add (hImC.mul_const Complex.I)
  refine hsum.congr ?_
  filter_upwards with x
  rw [re_eq (f x), im_eq (f x), Complex.re_add_im]

end Work.Diff.STE
