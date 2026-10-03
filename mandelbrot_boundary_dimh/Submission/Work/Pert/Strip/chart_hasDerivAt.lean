import Mathlib
import Submission.Work.Pert.Strip.Defs

/-!
# Derivative of the strip chart

For `h > 0` the chart

    Work.Pert.stripChart h ζ = (E - 1)/(E + 1),   E = chartExp h ζ = exp (chartC h * ζ)

has, at any point `ζ` of the closed strip `|Re ζ| ≤ h`, the derivative

    2 * chartC h * chartExp h ζ / (chartExp h ζ + 1) ^ 2 .

The only point needing the strip hypothesis is the non-vanishing of `chartExp h ζ + 1`: on the
strip the real part of `chartExp h ζ` is `exp (-k Im ζ) * cos (k Re ζ)` with `k = π/(2h) > 0`,
and `|k Re ζ| ≤ π/2`, so this real part is `≥ 0` and `chartExp h ζ = -1` (whose real part is
`-1`) is impossible.
-/

namespace Work.Pert.Strip

noncomputable section

/-- `chartC h * ζ` as a real multiple of `Complex.I * ζ`. -/
private lemma chartDeriv_chartC_mul_eq (h : ℝ) (ζ : ℂ) :
    chartC h * ζ = ((chartK h : ℂ)) * (Complex.I * ζ) := by
  rw [chartC_eq_ofReal]; ring

/-- The real part of `chartExp h ζ` in terms of the real data `chartK`, `ζ.re`, `ζ.im`. -/
private lemma chartDeriv_chartExp_re (h : ℝ) (ζ : ℂ) :
    (chartExp h ζ).re = Real.exp (-(chartK h * ζ.im)) * Real.cos (chartK h * ζ.re) := by
  have h1 : (chartC h * ζ).re = -(chartK h * ζ.im) := by
    rw [chartDeriv_chartC_mul_eq]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.I_re, Complex.I_im, one_mul]
    ring
  have h2 : (chartC h * ζ).im = chartK h * ζ.re := by
    rw [chartDeriv_chartC_mul_eq]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      Complex.I_re, Complex.I_im, one_mul]
    ring
  rw [chartExp, Complex.exp_re, h1, h2]

/-- On the closed strip `|Re ζ| ≤ h` the argument `chartK h * ζ.re` lies in `[-π/2, π/2]`. -/
private lemma chartDeriv_chartK_mul_re_mem_Icc {h : ℝ} (hh : 0 < h) {ζ : ℂ}
    (hζ : |ζ.re| ≤ h) :
    chartK h * ζ.re ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
  have hk : 0 < chartK h := chartK_pos hh
  have hkabs : |chartK h * ζ.re| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos hk]
    calc chartK h * |ζ.re| ≤ chartK h * h := mul_le_mul_of_nonneg_left hζ (le_of_lt hk)
      _ = Real.pi / 2 := by rw [chartK]; field_simp
  rw [abs_le] at hkabs
  exact hkabs

/-- On the closed strip `|Re ζ| ≤ h` the denominator `chartExp h ζ + 1` does not vanish. -/
private lemma chartDeriv_chartExp_add_one_ne_zero {h : ℝ} (hh : 0 < h) {ζ : ℂ}
    (hζ : |ζ.re| ≤ h) :
    chartExp h ζ + 1 ≠ 0 := by
  intro hE
  have hre := chartDeriv_chartExp_re h ζ
  have hcos := Real.cos_nonneg_of_mem_Icc (chartDeriv_chartK_mul_re_mem_Icc hh hζ)
  have hnonneg : 0 ≤ (chartExp h ζ).re := by
    rw [hre]
    exact mul_nonneg (le_of_lt (Real.exp_pos _)) hcos
  have h1 : (chartExp h ζ).re = -1 := by
    have h2 : (chartExp h ζ + 1).re = (0 : ℂ).re := by rw [hE]
    simp at h2
    linarith
  linarith

theorem chart_hasDerivAt {h : ℝ} (hh : 0 < h) {ζ : ℂ} (hζ : |ζ.re| ≤ h) :
    HasDerivAt (Work.Pert.stripChart h)
      (2 * chartC h * chartExp h ζ / (chartExp h ζ + 1) ^ 2) ζ := by
  have hne : chartExp h ζ + 1 ≠ 0 := chartDeriv_chartExp_add_one_ne_zero hh hζ
  have hlin : HasDerivAt (fun w : ℂ => chartC h * w) (chartC h) ζ := by
    simpa using (hasDerivAt_id ζ).const_mul (chartC h)
  have hderiv : HasDerivAt (fun w : ℂ => chartExp h w) (chartC h * chartExp h ζ) ζ := by
    have h1 : HasDerivAt (fun w : ℂ => chartExp h w) (chartExp h ζ * chartC h) ζ := by
      simpa [chartExp] using hlin.cexp
    convert h1 using 1
    ring
  have hnum : HasDerivAt (fun w : ℂ => chartExp h w - 1) (chartC h * chartExp h ζ) ζ :=
    hderiv.sub_const 1
  have hden : HasDerivAt (fun w : ℂ => chartExp h w + 1) (chartC h * chartExp h ζ) ζ :=
    hderiv.add_const 1
  have hdiv := hnum.div hden hne
  have hfun : Work.Pert.stripChart h = fun w : ℂ => (chartExp h w - 1) / (chartExp h w + 1) :=
    funext (stripChart_eq_cayley h)
  rw [hfun]
  convert hdiv using 1
  field_simp
  ring

end

end Work.Pert.Strip
