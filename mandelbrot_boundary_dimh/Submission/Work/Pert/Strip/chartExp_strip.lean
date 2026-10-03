import Mathlib
import Submission.Work.Pert.Strip.Defs

/-!
# `Work.Pert.Strip.chartExp_strip`

Elementary facts about the exponential factor `chartExp h ζ = exp (i π ζ/(2h))` of the strip
chart, valid on the strip `|Re ζ| ≤ h` (`h > 0`):

* `chartP h ζ = (π/(2h)) · Re ζ` lies in `[-π/2, π/2]`, hence `cos (chartP h ζ) ≥ 0`;
* `chartExp h ζ + 1 ≠ 0`, because the real part of `chartExp h ζ + 1` is
  `exp (-(π/(2h)) · Im ζ) · cos (chartP h ζ) + 1 ≥ 1 > 0`.
-/

namespace Work.Pert.Strip

noncomputable section

/-- `chartK h · h = π/2` for `h > 0`. -/
lemma chartK_mul_self {h : ℝ} (hh : 0 < h) : chartK h * h = Real.pi / 2 := by
  rw [chartK]
  field_simp

/-- The real part of the exponent `chartC h * ζ`. -/
private lemma chartC_mul_re (h : ℝ) (ζ : ℂ) : (chartC h * ζ).re = -(chartK h * ζ.im) := by
  rw [chartC_eq_ofReal]
  simp [Complex.mul_re]

/-- The imaginary part of the exponent `chartC h * ζ` is `chartP h ζ`. -/
private lemma chartC_mul_im (h : ℝ) (ζ : ℂ) : (chartC h * ζ).im = chartP h ζ := by
  rw [chartC_eq_ofReal]
  simp [Complex.mul_im, chartP]

/-- On the strip `|Re ζ| ≤ h` the argument `chartP h ζ` lies in `[-π/2, π/2]`. -/
lemma chartP_mem_Icc {h : ℝ} (hh : 0 < h) {ζ : ℂ} (hζ : |ζ.re| ≤ h) :
    chartP h ζ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
  have hk : 0 < chartK h := chartK_pos hh
  have hx := (abs_le.mp hζ)
  have hup : chartP h ζ ≤ Real.pi / 2 := by
    calc chartP h ζ = chartK h * ζ.re := rfl
      _ ≤ chartK h * h := mul_le_mul_of_nonneg_left hx.2 (le_of_lt hk)
      _ = Real.pi / 2 := chartK_mul_self hh
  have hdown : -(Real.pi / 2) ≤ chartP h ζ := by
    have h1 : -(Real.pi / 2) = chartK h * (-h) := by
      rw [← chartK_mul_self hh]; ring
    calc -(Real.pi / 2) = chartK h * (-h) := h1
      _ ≤ chartK h * ζ.re := mul_le_mul_of_nonneg_left (by linarith [hx.1]) (le_of_lt hk)
      _ = chartP h ζ := rfl
  exact ⟨hdown, hup⟩

/-- Real part of `chartExp h ζ`. -/
lemma chartExp_re (h : ℝ) (ζ : ℂ) :
    (chartExp h ζ).re = Real.exp (-(chartK h * ζ.im)) * Real.cos (chartP h ζ) := by
  simp only [chartExp, Complex.exp_re]
  rw [chartC_mul_re, chartC_mul_im]

/-- Real part of `chartExp h ζ + 1`. -/
lemma chartExp_add_one_re (h : ℝ) (ζ : ℂ) :
    (chartExp h ζ + 1).re = Real.exp (-(chartK h * ζ.im)) * Real.cos (chartP h ζ) + 1 := by
  rw [Complex.add_re, chartExp_re h ζ, Complex.one_re]

theorem chartExp_strip {h : ℝ} (hh : 0 < h) {ζ : ℂ} (hζ : |ζ.re| ≤ h) :
    0 ≤ Real.cos (chartP h ζ) ∧ chartExp h ζ + 1 ≠ 0 := by
  have hcos : 0 ≤ Real.cos (chartP h ζ) :=
    Real.cos_nonneg_of_mem_Icc (chartP_mem_Icc hh hζ)
  refine ⟨hcos, ?_⟩
  intro hcontra
  have hzero : (chartExp h ζ + 1).re = 0 := by rw [hcontra]; rfl
  rw [chartExp_add_one_re h ζ] at hzero
  have hnonneg : 0 ≤ Real.exp (-(chartK h * ζ.im)) * Real.cos (chartP h ζ) :=
    mul_nonneg (le_of_lt (Real.exp_pos _)) hcos
  linarith

end

end Work.Pert.Strip
