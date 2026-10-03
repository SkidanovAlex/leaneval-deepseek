import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Interfaces.Parabolic

namespace Work.Pert.PinLogDev

/-!
# `Work.Pert.PinLogDev.tauC_axis_upper`

`InF1 α` (`|Im α| < Re α`) gives `Re α ≥ (7/10)‖α‖`.  On the upper axis `w = i s` (`s > 0`)

  `τ_f (i s) = σ / (1 - exp (2π s α))`,

and since `Re (2π s α) = 2π s Re α ≥ 0`,

  `‖1 - exp (2π s α)‖ ≥ ‖exp (2π s α)‖ - 1 = e^{2π s Re α} - 1 ≥ 2π s Re α`,

so with `‖σ‖ ≤ (9/7)‖2πiα‖ = (18/7)π‖α‖` we get

  `‖τ_f (i s)‖ ≤ (18/7)π‖α‖ / (2π s Re α) = (9/7)(‖α‖/Re α)/s ≤ (9/7)(10/7)/s = (90/49)/s ≤ 2/s`.
-/

/-- `InF1 α` gives `Re α ≥ (7/10)‖α‖`. -/
private lemma InF1_re_ge_seven_tenths {α : ℂ} (hInF1 : MandelDim.InF1 α) :
    (7 / 10 : ℝ) * ‖α‖ ≤ α.re := by
  have hInF1' : |α.im| < α.re := hInF1
  have hrepos : 0 < α.re := by linarith [abs_nonneg α.im]
  have him2 : α.im ^ 2 < α.re ^ 2 := by
    nlinarith [abs_nonneg α.im, sq_abs α.im, hInF1']
  have hnormsq : ‖α‖ ^ 2 = α.re ^ 2 + α.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hsq : ‖α‖ ^ 2 < 2 * α.re ^ 2 := by nlinarith [hnormsq, him2]
  have h67 : ((7 / 10 : ℝ) * ‖α‖) ^ 2 ≤ α.re ^ 2 := by nlinarith [hsq]
  have h := (sq_le_sq.mp h67)
  simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 7 / 10),
    abs_of_nonneg (norm_nonneg α), abs_of_nonneg (le_of_lt hrepos)] at h
  linarith [h]

/-- On the upper axis `w = i s` the universal cover `τ_f` is bounded by `2/s`, uniformly in the
data: `tauC σ α (i s) = σ / (1 - exp (2π s α))` and `𝓕₁ α` gives `Re α ≥ (7/10)‖α‖`, while
`‖σ‖ ≤ 9/7 ‖2πiα‖`; hence `‖τ_f (i s)‖ ≤ (18/7)/(2πs(7/10)) ≤ 2/s`. -/
theorem tauC_axis_upper {σ α : ℂ} {s : ℝ} (hInF1 : MandelDim.InF1 α) (hs : 0 < s)
    (hσ : ‖σ‖ ≤ 9 / 7 * ‖2 * Real.pi * Complex.I * α‖) :
    ‖Work.Pert.tauC σ α ((s : ℂ) * Complex.I)‖ ≤ 2 / s := by
  have hre : 0 < α.re := lt_of_le_of_lt (abs_nonneg α.im) hInF1
  have hre_ge : (7 / 10 : ℝ) * ‖α‖ ≤ α.re := InF1_re_ge_seven_tenths hInF1
  -- `‖2πiα‖ = 2π‖α‖`
  have hZnorm : ‖2 * Real.pi * Complex.I * α‖ = 2 * Real.pi * ‖α‖ := by
    rw [norm_mul, norm_mul, norm_mul]
    simp [Complex.norm_I]
  have hσ' : ‖σ‖ ≤ 9 / 7 * (2 * Real.pi * ‖α‖) := by
    rw [hZnorm] at hσ; exact hσ
  -- the exponent on the upper axis
  have harg : -(2 * Real.pi * Complex.I * α * ((s : ℂ) * Complex.I))
      = 2 * Real.pi * (s : ℂ) * α := by
    have h1 : 2 * Real.pi * Complex.I * α * ((s : ℂ) * Complex.I)
        = 2 * Real.pi * α * (s : ℂ) * (Complex.I * Complex.I) := by ring
    rw [h1, Complex.I_mul_I]
    ring
  rw [Work.Pert.tauC, harg]
  set E : ℂ := Complex.exp (2 * Real.pi * (s : ℂ) * α) with hE
  -- the modulus of the exponential
  have hnormE : ‖E‖ = Real.exp (2 * Real.pi * s * α.re) := by
    rw [hE, Complex.norm_exp]
    simp [Complex.mul_re]
  -- the denominator bound
  have hden : 2 * Real.pi * s * α.re ≤ ‖1 - E‖ := by
    have h1 : 2 * Real.pi * s * α.re ≤ Real.exp (2 * Real.pi * s * α.re) - 1 := by
      have h := Real.add_one_le_exp (2 * Real.pi * s * α.re)
      linarith
    have h3 : Real.exp (2 * Real.pi * s * α.re) - 1 ≤ ‖E - 1‖ := by
      have h := norm_sub_norm_le E (1 : ℂ)
      rw [hnormE] at h
      simpa using h
    have h4 : ‖E - 1‖ = ‖1 - E‖ := by rw [norm_sub_rev]
    linarith
  have hDpos : 0 < 2 * Real.pi * s * α.re := by positivity
  have hratio : ‖α‖ / α.re ≤ 10 / 7 := by
    rw [div_le_iff₀ hre]
    linarith
  calc ‖σ / (1 - E)‖ = ‖σ‖ / ‖1 - E‖ := norm_div _ _
    _ ≤ ‖σ‖ / (2 * Real.pi * s * α.re) :=
        div_le_div_of_nonneg_left (norm_nonneg σ) hDpos hden
    _ ≤ (9 / 7 * (2 * Real.pi * ‖α‖)) / (2 * Real.pi * s * α.re) :=
        div_le_div_of_nonneg_right hσ' (le_of_lt hDpos)
    _ = (9 / 7) * (‖α‖ / α.re) / s := by
        field_simp
    _ ≤ 2 / s := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hs)
        have h2 := mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℝ) ≤ 9 / 7)
        have h3 : (9 / 7 : ℝ) * (10 / 7) ≤ 2 := by norm_num
        linarith

end Work.Pert.PinLogDev
