import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Pert.Basic
import Submission.Work.Pert.tauC_add_inv_le

/-!
# `τ₀ ∘ τ_f` is close to the identity (PERT area, Shishikura A.1.5 / (4.2.x))

Writing `x = 2πiα` and `y = 2πiαζ`, and using the normalisation `1 - σ u(0) = e^{x}` of
Lemma A.1.2, the two charts of the parabolic perturbation satisfy the EXACT identity

  `τ₀ (τ_f ζ) = u(0) · (e^{-y} - 1)/(1 - e^{x})`,   `τ_f w = σ/(1 - e^{-2πiαw})`,
  `τ₀ y = -1/y`.

Indeed `τ_f ζ = σ/(1 - e^{-y})`, so `τ₀(τ_f ζ) = -(1 - e^{-y})/σ`, and `σ = (1 - e^x)/u(0)`.

The estimate is then a two-term Taylor expansion around `0`:
`u(0)(e^{-y}-1) - ζ(1-e^{x}) = (u(0)-1)(e^{-y}-1) + [(e^{-y}-1+y) + ζ(e^{x}-1-x)]`
(the `O(y)`/`O(x)` terms cancel because `y = ζx`), while `‖1 - e^{x}‖ ≥ ‖x‖/2`.  Dividing,

  `‖τ₀(τ_f ζ) - ζ‖ ≤ 4ε‖ζ‖ + 2‖x‖‖ζ‖ + 2‖x‖‖ζ‖²`
  `              ≤ 64 (ε + ‖α‖ + ‖α‖‖ζ‖)‖ζ‖`   since `‖x‖ = 2π‖α‖` and `4π < 64`.

The constants are deliberately generous; no sharpness is claimed.
-/

namespace Work.Pert

open Complex

noncomputable section

set_option linter.unusedVariables false

/-- The perturbed chart `τ_f` (`Work.Pert.tauC`) and the unperturbed chart `τ₀ y = -1/y`
(`MandelDim.tau0`) are inverse to each other up to `O(ε + ‖α‖(1 + ‖ζ‖))`.

With the normalisation `1 - σ u(0) = e^{2πiα}`, `‖u(0) - 1‖ ≤ ε`, `‖α‖ ≤ 1/1024` and
`‖2πiαζ‖ ≤ 1/8`,

  `‖τ₀(τ_f ζ) - ζ‖ ≤ 64 (ε + ‖α‖ + ‖α‖‖ζ‖)‖ζ‖`.

This is the "return to the unperturbed chart" estimate used when propagating the perturbed
Fatou coordinate back to the `ζ`-coordinate of the horn map.

The hypothesis `ε ≤ 1/1024` fixes the regime of the contract; the proof only needs `ε ≥ 0`
(which follows from `‖u(0) - 1‖ ≤ ε`), the constant `64` absorbing the smallness. -/
theorem tau0_tauC_close {u : ℂ → ℂ} {σ α ζ : ℂ} {ε : ℝ}
    (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hu0 : ‖u 0 - 1‖ ≤ ε) (hε : ε ≤ 1 / 1024) (hαs : ‖α‖ ≤ 1 / 1024)
    (hα : 2 * Real.pi * ‖α‖ * ‖ζ‖ ≤ 1 / 8)
    (hα0 : α ≠ 0) (hζ : ζ ≠ 0) :
    ‖MandelDim.tau0 (Work.Pert.tauC σ α ζ) - ζ‖ ≤ 64 * (ε + ‖α‖ + ‖α‖ * ‖ζ‖) * ‖ζ‖ := by
  set x : ℂ := 2 * Real.pi * Complex.I * α with hxdef
  set y : ℂ := 2 * Real.pi * Complex.I * α * ζ with hydef
  have hε0 : 0 ≤ ε := le_trans (norm_nonneg _) hu0
  have hxnorm : ‖x‖ = 2 * Real.pi * ‖α‖ := by
    rw [hxdef, norm_mul, norm_mul, norm_mul]
    have hI : ‖Complex.I‖ = 1 := Complex.norm_I
    have hp : ‖(Real.pi : ℂ)‖ = Real.pi := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have h2c : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2c, hp, hI, mul_one]
  have hynorm : ‖y‖ = 2 * Real.pi * ‖α‖ * ‖ζ‖ := by
    rw [hydef, norm_mul, norm_mul, norm_mul, norm_mul]
    have hI : ‖Complex.I‖ = 1 := Complex.norm_I
    have hp : ‖(Real.pi : ℂ)‖ = Real.pi := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have h2c : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2c, hp, hI, mul_one]
  have hx0 : x ≠ 0 := by
    rw [hxdef]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero) hα0
  have hyx : y = ζ * x := by rw [hydef, hxdef]; ring
  have hxle : ‖x‖ ≤ 1 / 2 := by
    rw [hxnorm]; nlinarith [Real.pi_lt_four, norm_nonneg α, hαs]
  have hyle : ‖y‖ ≤ 1 / 8 := by rw [hynorm]; exact hα
  have hσ : σ * u 0 = 1 - Complex.exp x := by linear_combination -hnorm
  have hq : 1 - Complex.exp x ≠ 0 := by
    have h1 := Work.Pert.norm_one_sub_exp_neg_ge (-x) (by rw [norm_neg]; linarith)
    rw [neg_neg, norm_neg] at h1
    intro h
    rw [h, norm_zero] at h1
    have hxpos : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx0
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
      ≤ 2 * ε * ‖y‖ + ‖y‖ ^ 2 + ‖ζ‖ * ‖x‖ ^ 2 := by
    have hdec : u 0 * (Complex.exp (-y) - 1) - ζ * (1 - Complex.exp x)
        = (u 0 - 1) * (Complex.exp (-y) - 1)
          + (Complex.exp (-y) - 1 + y) + ζ * (Complex.exp x - 1 - x) := by
      rw [hyx]; ring
    rw [hdec]
    have h1 : ‖(u 0 - 1) * (Complex.exp (-y) - 1)‖ ≤ ε * (2 * ‖y‖) := by
      have hexpy : ‖Complex.exp (-y) - 1‖ ≤ 2 * ‖y‖ := by
        have h := Complex.norm_exp_sub_one_le (x := -y) (by rw [norm_neg]; linarith)
        simpa using h
      rw [norm_mul]
      exact mul_le_mul hu0 hexpy (by positivity) hε0
    have h2 : ‖Complex.exp (-y) - 1 + y‖ ≤ ‖y‖ ^ 2 := by
      have h := Complex.norm_exp_sub_one_sub_id_le (x := -y) (by rw [norm_neg]; linarith)
      simpa using h
    have h3 : ‖ζ * (Complex.exp x - 1 - x)‖ ≤ ‖ζ‖ * ‖x‖ ^ 2 := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (Complex.norm_exp_sub_one_sub_id_le (by linarith))
        (norm_nonneg ζ)
    calc ‖(u 0 - 1) * (Complex.exp (-y) - 1)
          + (Complex.exp (-y) - 1 + y) + ζ * (Complex.exp x - 1 - x)‖
        ≤ ‖(u 0 - 1) * (Complex.exp (-y) - 1) + (Complex.exp (-y) - 1 + y)‖
          + ‖ζ * (Complex.exp x - 1 - x)‖ := norm_add_le _ _
      _ ≤ (‖(u 0 - 1) * (Complex.exp (-y) - 1)‖ + ‖Complex.exp (-y) - 1 + y‖)
          + ‖ζ * (Complex.exp x - 1 - x)‖ := by
          gcongr
          exact norm_add_le _ _
      _ ≤ 2 * ε * ‖y‖ + ‖y‖ ^ 2 + ‖ζ‖ * ‖x‖ ^ 2 := by linarith
  -- denominator: `‖1 - e^{x}‖ ≥ ‖x‖/2`
  have hden : ‖x‖ / 2 ≤ ‖1 - Complex.exp x‖ := by
    have h1 := Work.Pert.norm_one_sub_exp_neg_ge (-x) (by rw [norm_neg]; linarith)
    simpa using h1
  have hxpos : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx0
  rw [hkey, norm_div]
  have hstep : ‖u 0 * (Complex.exp (-y) - 1) - ζ * (1 - Complex.exp x)‖ / ‖1 - Complex.exp x‖
      ≤ (2 * ε * ‖y‖ + ‖y‖ ^ 2 + ‖ζ‖ * ‖x‖ ^ 2) / (‖x‖ / 2) := by
    calc ‖u 0 * (Complex.exp (-y) - 1) - ζ * (1 - Complex.exp x)‖ / ‖1 - Complex.exp x‖
        ≤ (2 * ε * ‖y‖ + ‖y‖ ^ 2 + ‖ζ‖ * ‖x‖ ^ 2) / ‖1 - Complex.exp x‖ :=
          div_le_div_of_nonneg_right hnum (norm_nonneg _)
      _ ≤ (2 * ε * ‖y‖ + ‖y‖ ^ 2 + ‖ζ‖ * ‖x‖ ^ 2) / (‖x‖ / 2) :=
          div_le_div_of_nonneg_left (by positivity) (by linarith) hden
  refine hstep.trans ?_
  calc (2 * ε * ‖y‖ + ‖y‖ ^ 2 + ‖ζ‖ * ‖x‖ ^ 2) / (‖x‖ / 2)
      = 4 * ε * ‖ζ‖ + 2 * ‖x‖ * ‖ζ‖ ^ 2 + 2 * ‖x‖ * ‖ζ‖ := by
        rw [hynorm, hxnorm]
        field_simp
        ring
    _ ≤ 64 * (ε + ‖α‖ + ‖α‖ * ‖ζ‖) * ‖ζ‖ := by
        rw [hxnorm]
        nlinarith [Real.pi_lt_four, norm_nonneg α, norm_nonneg ζ, hε0,
          mul_nonneg (norm_nonneg α) (norm_nonneg ζ),
          mul_nonneg (norm_nonneg α) (sq_nonneg ‖ζ‖), Real.pi_pos]

end

end Work.Pert
