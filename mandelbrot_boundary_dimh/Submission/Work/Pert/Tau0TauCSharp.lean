import Mathlib
import Submission.Work.Pert.tau0_tauC_close
import Submission.Work.Pert.one_sub_exp_ge_half

namespace Work.Pert

open Complex

noncomputable section

set_option linter.unusedVariables false

/-- Sharp chart comparison: `τ₀ (τ_f ζ) − ζ` bounded by the *first-order* terms only.

`Work.Pert.tau0_tauC_close` proves the exact identity `τ₀ (τ_f ζ) = u(0)(e^{−y}−1)/(1−e^{x})`
with `x = 2πiα`, `y = xζ` (its `hmain`), and its file contains the numerator estimate
`hnum : ‖u(0)(e^{−y}−1) − ζ(1−e^{x})‖ ≤ 2‖u0−1‖‖y‖ + ‖y‖² + ‖ζ‖‖x‖²` together with
`‖1 − e^{x}‖ ≥ ‖x‖/2`.  Dividing the first by the second and using `y = xζ` gives exactly

  `‖τ₀(τ_f ζ) − ζ‖ ≤ 4‖u(0)−1‖‖ζ‖ + 2‖x‖‖ζ‖² + 2‖x‖‖ζ‖`   (`x = 2πiα`),

i.e. the coefficients `4,2,2` (the file's own `hnum`, no new estimates needed: `2‖x‖²‖ζ‖/‖x‖`
for the middle term, `2‖ζ‖‖x‖` for the last). All Taylor inputs (`Complex.norm_exp_sub_one_le`,
`Complex.norm_exp_sub_one_sub_id_le`, `Work.Pert.norm_one_sub_exp_neg_ge`) only need
`‖x‖ ≤ 1`, `‖y‖ ≤ 1`, which is what the hypotheses give. This is the estimate the (4.2.5)
assembly needs, where `‖ζ‖ ≈ η` and `‖α‖η` is small — the constant `64` of `tau0_tauC_close`
(whose `ε‖ζ‖` term is overestimated by `1/(2π‖α‖)`) is unusable there. -/
theorem Tau0TauCSharp {u : ℂ → ℂ} {σ α ζ : ℂ}
    (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hα0 : α ≠ 0)
    (hx : ‖2 * Real.pi * Complex.I * α‖ ≤ 1)
    (hy : ‖2 * Real.pi * Complex.I * α * ζ‖ ≤ 1) :
    ‖MandelDim.tau0 (Work.Pert.tauC σ α ζ) - ζ‖ ≤
      4 * ‖u 0 - 1‖ * ‖ζ‖ + 2 * ‖2 * Real.pi * Complex.I * α‖ * ‖ζ‖ ^ 2 +
        2 * ‖2 * Real.pi * Complex.I * α‖ * ‖ζ‖ := by
  set x : ℂ := 2 * Real.pi * Complex.I * α with hxdef
  set y : ℂ := 2 * Real.pi * Complex.I * α * ζ with hydef
  have hxle : ‖x‖ ≤ 1 := hx
  have hyle : ‖y‖ ≤ 1 := hy
  have hx0 : x ≠ 0 := by
    rw [hxdef]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero) hα0
  have hxpos : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx0
  have hyx : y = ζ * x := by rw [hydef, hxdef]; ring
  have hynorm : ‖y‖ = ‖x‖ * ‖ζ‖ := by rw [hyx, norm_mul, mul_comm]
  have hσ : σ * u 0 = 1 - Complex.exp x := by linear_combination -hnorm
  have hq : 1 - Complex.exp x ≠ 0 := by
    intro h
    have h1 := one_sub_exp_ge_half x hxle
    rw [h, norm_zero] at h1
    linarith
  have hu0nz : u 0 ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hσ
    exact hq hσ.symm
  have hσeq : σ = (1 - Complex.exp x) / u 0 := (eq_div_iff hu0nz).mpr hσ
  have hτ : Work.Pert.tauC σ α ζ = σ / (1 - Complex.exp (-y)) := by
    rw [Work.Pert.tauC, hydef]
  -- the exact algebraic identity `τ₀ ∘ τ_f = u(0)(e^{-y}-1)/(1-e^{x})`
  have hmain : MandelDim.tau0 (Work.Pert.tauC σ α ζ)
      = u 0 * (Complex.exp (-y) - 1) / (1 - Complex.exp x) := by
    rw [hτ, MandelDim.tau0, hσeq]
    field_simp
    ring
  have hkey : MandelDim.tau0 (Work.Pert.tauC σ α ζ) - ζ
      = (u 0 * (Complex.exp (-y) - 1) - ζ * (1 - Complex.exp x)) / (1 - Complex.exp x) := by
    rw [hmain]
    field_simp
  -- numerator: only second order terms survive (`y = ζ x`)
  have hnum : ‖u 0 * (Complex.exp (-y) - 1) - ζ * (1 - Complex.exp x)‖
      ≤ 2 * ‖u 0 - 1‖ * ‖y‖ + ‖y‖ ^ 2 + ‖ζ‖ * ‖x‖ ^ 2 := by
    have hdec : u 0 * (Complex.exp (-y) - 1) - ζ * (1 - Complex.exp x)
        = (u 0 - 1) * (Complex.exp (-y) - 1)
          + (Complex.exp (-y) - 1 + y) + ζ * (Complex.exp x - 1 - x) := by
      rw [hyx]; ring
    rw [hdec]
    have h1 : ‖(u 0 - 1) * (Complex.exp (-y) - 1)‖ ≤ ‖u 0 - 1‖ * (2 * ‖y‖) := by
      have hexpy : ‖Complex.exp (-y) - 1‖ ≤ 2 * ‖y‖ := by
        have h := Complex.norm_exp_sub_one_le (x := -y) (by rw [norm_neg]; linarith)
        simpa using h
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hexpy (norm_nonneg _)
    have h2 : ‖Complex.exp (-y) - 1 + y‖ ≤ ‖y‖ ^ 2 := by
      have h := Complex.norm_exp_sub_one_sub_id_le (x := -y) (by rw [norm_neg]; linarith)
      simpa using h
    have h3 : ‖ζ * (Complex.exp x - 1 - x)‖ ≤ ‖ζ‖ * ‖x‖ ^ 2 := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (Complex.norm_exp_sub_one_sub_id_le hxle)
        (norm_nonneg ζ)
    calc ‖(u 0 - 1) * (Complex.exp (-y) - 1)
          + (Complex.exp (-y) - 1 + y) + ζ * (Complex.exp x - 1 - x)‖
        ≤ ‖(u 0 - 1) * (Complex.exp (-y) - 1) + (Complex.exp (-y) - 1 + y)‖
          + ‖ζ * (Complex.exp x - 1 - x)‖ := norm_add_le _ _
      _ ≤ (‖(u 0 - 1) * (Complex.exp (-y) - 1)‖ + ‖Complex.exp (-y) - 1 + y‖)
          + ‖ζ * (Complex.exp x - 1 - x)‖ := by
          gcongr
          exact norm_add_le _ _
      _ ≤ 2 * ‖u 0 - 1‖ * ‖y‖ + ‖y‖ ^ 2 + ‖ζ‖ * ‖x‖ ^ 2 := by linarith
  -- denominator: `‖1 - e^{x}‖ ≥ ‖x‖/2`
  have hden : ‖x‖ / 2 ≤ ‖1 - Complex.exp x‖ := one_sub_exp_ge_half x hxle
  have hdpos : (0 : ℝ) < ‖1 - Complex.exp x‖ := by linarith
  have hCnn : 0 ≤ 4 * ‖u 0 - 1‖ * ‖ζ‖ + 2 * ‖x‖ * ‖ζ‖ ^ 2 + 2 * ‖x‖ * ‖ζ‖ := by positivity
  rw [hkey, norm_div, div_le_iff₀ hdpos]
  rw [hynorm] at hnum
  have hCe : (4 * ‖u 0 - 1‖ * ‖ζ‖ + 2 * ‖x‖ * ‖ζ‖ ^ 2 + 2 * ‖x‖ * ‖ζ‖) * (‖x‖ / 2)
      = 2 * ‖u 0 - 1‖ * (‖x‖ * ‖ζ‖) + (‖x‖ * ‖ζ‖) ^ 2 + ‖ζ‖ * ‖x‖ ^ 2 := by ring
  have hstep : ‖u 0 * (Complex.exp (-y) - 1) - ζ * (1 - Complex.exp x)‖
      ≤ (4 * ‖u 0 - 1‖ * ‖ζ‖ + 2 * ‖x‖ * ‖ζ‖ ^ 2 + 2 * ‖x‖ * ‖ζ‖) * (‖x‖ / 2) := by
    rw [hCe]; exact hnum
  exact hstep.trans (mul_le_mul_of_nonneg_left hden hCnn)

end

end Work.Pert
