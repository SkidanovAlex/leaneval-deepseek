import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup

/-!
# PERT · `Work.Pert.tauC_upper_decay`

Shishikura (A.1.7)(ii) at the **upper end of the lower gate**: the universal cover

  `τ_f(z) = σ / (1 - exp (-2πi α z))`  (`Work.Pert.tauC`)

decays exponentially as `z.im → +∞` along the lower gate `Qm ξ α = Qreg (ξ - 1/α) (-ξ)`.

The region conditions read (`z = x + iy`, `w = 1/α`)

  (C1) `-|y + Im w| < x - ξ + Re w`   (from `b₁ = ξ - w`)
  (C2) `x + ξ < |y|`                  (from `b₂ = -ξ`)

so for `y > 0`: `x < y` and `x > ξ - Re w - |y + Im w| > -y - 2‖w‖`, i.e.

  `|x| < y + 2‖1/α‖`.

With `α.re > |α.im|` (`InF1`, so `λ := α.re - |α.im| > 0`) we get

  `Re (-(2πi α z)) = 2π (α.re·y + α.im·x) ≥ 2π (λ y - 2|α.im| ‖1/α‖) ≥ 2π λ y - 4π`,

and `|α.im| · ‖1/α‖ ≤ ‖α‖ · 1/‖α‖ = 1`.  Hence once `λ y ≥ 4`,

  `‖exp (-(2πi α z))‖ = exp (Re (-(2πi α z))) ≥ exp (π λ y)`,

so for `π λ y ≥ log 2` the denominator is bounded below by `exp (π λ y)/2` and

  `‖τ_f z‖ ≤ 2‖σ‖ · exp (-(π λ y))`.

Constants: `M = 2‖σ‖`, `κ = π λ`, `Y = max (max (4/λ) (log 2/κ)) 1`.
-/

namespace Work.Pert

open Complex

noncomputable section

theorem tauC_upper_decay {σ α : ℂ} {ξ : ℝ} (hξ : 0 < ξ) (hα : MandelDim.InF1 α)
    (hσ : σ ≠ 0) :
    ∃ M κ Y : ℝ, 0 < M ∧ 0 < κ ∧
      ∀ z ∈ Work.Pert.Qm ξ α, Y < z.im →
        ‖Work.Pert.tauC σ α z‖ ≤ M * Real.exp (-(κ * z.im)) := by
  -- `InF1 α` is `|α.im| < α.re`, hence `α ≠ 0` and `λ := α.re - |α.im| > 0`
  have hlpos : 0 < α.re - |α.im| := by
    have h : |α.im| < α.re := hα
    linarith
  have hκpos : 0 < Real.pi * (α.re - |α.im|) := mul_pos Real.pi_pos hlpos
  refine ⟨2 * ‖σ‖, Real.pi * (α.re - |α.im|),
      max (max (4 / (α.re - |α.im|)) (Real.log 2 / (Real.pi * (α.re - |α.im|)))) 1,
      by linarith [norm_pos_iff.mpr hσ], hκpos, ?_⟩
  have hY1 : (1 : ℝ) ≤
      max (max (4 / (α.re - |α.im|)) (Real.log 2 / (Real.pi * (α.re - |α.im|)))) 1 :=
    le_max_right _ _
  have hYA : 4 / (α.re - |α.im|) ≤
      max (max (4 / (α.re - |α.im|)) (Real.log 2 / (Real.pi * (α.re - |α.im|)))) 1 :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have hYB : Real.log 2 / (Real.pi * (α.re - |α.im|)) ≤
      max (max (4 / (α.re - |α.im|)) (Real.log 2 / (Real.pi * (α.re - |α.im|)))) 1 :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  intro z hz hY
  have hy0 : 0 < z.im := by linarith
  have hy4 : 4 ≤ (α.re - |α.im|) * z.im := by
    have h1 : 4 / (α.re - |α.im|) ≤ z.im := le_of_lt (lt_of_le_of_lt hYA hY)
    rw [div_le_iff₀ hlpos] at h1
    linarith
  have hy2 : Real.log 2 ≤ Real.pi * (α.re - |α.im|) * z.im := by
    have h1 : Real.log 2 / (Real.pi * (α.re - |α.im|)) ≤ z.im := le_of_lt (lt_of_le_of_lt hYB hY)
    rw [div_le_iff₀ hκpos] at h1
    linarith
  -- (C2): `z.re + ξ < z.im`
  have h2 : z.re + ξ < z.im := by
    have h := hz.2 (-(ξ : ℂ)) (by simp)
    have him : (z - (-(ξ : ℂ))).im = z.im := by simp
    have hre : (z - (-(ξ : ℂ))).re = z.re + ξ := by simp
    rw [him, hre, abs_of_pos hy0] at h
    exact h
  -- (C1): `-(z.im + 2‖1/α‖) < z.re`
  have h1 : -(z.im + 2 * ‖(1 : ℂ) / α‖) < z.re := by
    have h := hz.1 ((ξ : ℂ) - 1 / α) (by simp)
    have him : (z - ((ξ : ℂ) - 1 / α)).im = z.im + (1 / α).im := by simp
    have hre : (z - ((ξ : ℂ) - 1 / α)).re = z.re - ξ + (1 / α).re := by simp; ring
    rw [him, hre] at h
    have hb : |z.im + (1 / α).im| ≤ z.im + ‖(1 : ℂ) / α‖ := by
      calc |z.im + (1 / α).im| ≤ |z.im| + |(1 / α).im| := abs_add_le _ _
        _ = z.im + |(1 / α).im| := by rw [abs_of_pos hy0]
        _ ≤ z.im + ‖(1 : ℂ) / α‖ := by
            have := abs_im_le_norm ((1 : ℂ) / α); linarith
    have hb2 : ((1 : ℂ) / α).re ≤ ‖(1 : ℂ) / α‖ := by
      have hh := abs_re_le_norm ((1 : ℂ) / α); linarith [le_abs_self (((1 : ℂ) / α).re)]
    linarith
  have hL : 0 ≤ ‖(1 : ℂ) / α‖ := norm_nonneg _
  have hxub : z.re < z.im + 2 * ‖(1 : ℂ) / α‖ := by linarith
  have hxabs : |z.re| < z.im + 2 * ‖(1 : ℂ) / α‖ := abs_lt.mpr ⟨h1, hxub⟩
  -- `|α.im| · ‖1/α‖ ≤ 1`
  have hbnd : |α.im| * ‖(1 : ℂ) / α‖ ≤ 1 := by
    have h1 : ‖α‖ * ‖(1 : ℂ) / α‖ ≤ 1 := by
      by_cases hα0 : α = 0
      · subst hα0; simp
      · rw [norm_div, norm_one, mul_one_div, div_self (ne_of_gt (norm_pos_iff.mpr hα0))]
    calc |α.im| * ‖(1 : ℂ) / α‖ ≤ ‖α‖ * ‖(1 : ℂ) / α‖ :=
          mul_le_mul_of_nonneg_right (abs_im_le_norm α) (norm_nonneg _)
      _ ≤ 1 := h1
  have himl : -|α.im| * (z.im + 2 * ‖(1 : ℂ) / α‖) ≤ α.im * z.re := by
    have h1 : -(|α.im * z.re|) ≤ α.im * z.re := neg_abs_le _
    have h2 : |α.im * z.re| = |α.im| * |z.re| := abs_mul _ _
    have h3 : |α.im| * |z.re| ≤ |α.im| * (z.im + 2 * ‖(1 : ℂ) / α‖) :=
      mul_le_mul_of_nonneg_left hxabs.le (abs_nonneg _)
    linarith
  -- `α.re z.im + α.im z.re ≥ λ z.im / 2`
  have hkey : (α.re - |α.im|) * z.im / 2 ≤ α.re * z.im + α.im * z.re := by
    have h4 : (α.re - |α.im|) * z.im - 2 ≤ α.re * z.im + α.im * z.re := by
      nlinarith [himl, hbnd]
    linarith [h4, hy4]
  have hre : (-(2 * Real.pi * I * α * z)).re =
      2 * Real.pi * (α.re * z.im + α.im * z.re) := by
    simp [Complex.mul_re, Complex.mul_im]
    ring
  have hexp_ge : Real.exp (Real.pi * (α.re - |α.im|) * z.im) ≤
      ‖Complex.exp (-(2 * Real.pi * I * α * z))‖ := by
    rw [Complex.norm_exp, hre]
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_left hkey (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    have he : 2 * Real.pi * ((α.re - |α.im|) * z.im / 2) =
        Real.pi * (α.re - |α.im|) * z.im := by ring
    linarith [hmul, he]
  have hexp2 : (2 : ℝ) ≤ ‖Complex.exp (-(2 * Real.pi * I * α * z))‖ := by
    have h := (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 2)).mp hy2
    linarith
  have hden : Real.exp (Real.pi * (α.re - |α.im|) * z.im) / 2 ≤
      ‖1 - Complex.exp (-(2 * Real.pi * I * α * z))‖ := by
    have h1 : ‖Complex.exp (-(2 * Real.pi * I * α * z))‖ ≤
        ‖1 - Complex.exp (-(2 * Real.pi * I * α * z))‖ + 1 := by
      have h := norm_add_le (Complex.exp (-(2 * Real.pi * I * α * z)) - 1) (1 : ℂ)
      have he : (Complex.exp (-(2 * Real.pi * I * α * z)) - 1) + 1 =
          Complex.exp (-(2 * Real.pi * I * α * z)) := by ring
      rw [he, norm_one] at h
      have h2 : ‖Complex.exp (-(2 * Real.pi * I * α * z)) - 1‖ =
          ‖1 - Complex.exp (-(2 * Real.pi * I * α * z))‖ :=
        norm_sub_rev (Complex.exp (-(2 * Real.pi * I * α * z))) 1
      linarith
    linarith
  rw [Work.Pert.tauC, norm_div]
  calc ‖σ‖ / ‖1 - Complex.exp (-(2 * Real.pi * I * α * z))‖
      ≤ ‖σ‖ / (Real.exp (Real.pi * (α.re - |α.im|) * z.im) / 2) :=
        div_le_div_of_nonneg_left (norm_nonneg σ) (by positivity) hden
    _ = 2 * ‖σ‖ * (Real.exp (Real.pi * (α.re - |α.im|) * z.im))⁻¹ := by
        field_simp
    _ = 2 * ‖σ‖ * Real.exp (-(Real.pi * (α.re - |α.im|) * z.im)) := by
        rw [Real.exp_neg]

end

end Work.Pert
