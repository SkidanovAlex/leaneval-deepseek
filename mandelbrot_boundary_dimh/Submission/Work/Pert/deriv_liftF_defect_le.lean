import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup
import Submission.Work.Pert.gate_derivF
import Submission.Work.Pert.scale_cauchy
import Submission.Work.Pert.scale_tau

/-!
# PERT · `Work.Pert.deriv_liftF_defect_le`

The pointwise defect estimate for the derivative of the lift `F_f = liftF u σ α` of Shishikura's
perturbed Fatou coordinate (A.1.7)(ii) / §4.2, in the form needed to feed the L1 near-translation
condition: with `E = exp (-(2πiαz))` and `τ = τ_f z = σ/(1 - E)`,

  `‖F_f'(z) - 1‖ ≤ (32/ρmin + 16) ‖σ‖² ‖E‖/‖1 - E‖²`.

The exact formula `F_f'(z) - 1 = τ(τ-σ)(u'(τ) - u(τ)²)/((1 + τu(τ) - σu(τ))(1 + τu(τ)))`
(`Work.Pert.gate_derivF`) splits the bound into
* `‖τ(τ-σ)‖ = ‖σ‖²‖E‖/‖1 - E‖²` (`τ - σ = τE`), and
* `‖u'(τ) - u(τ)²‖/(‖1 + τu(τ) - σu(τ)‖ ‖1 + τu(τ)‖) ≤ 32/ρmin + 16`,

the second from the Cauchy estimate `Work.Pert.scale_cauchy` (`‖u'‖ ≤ 8/ρmin`), `1/2 ≤ ‖u‖ ≤ 2`,
and the normalisation `1 - σ u 0 = exp (2πiα)` which keeps both denominator factors `≥ 1/2`.
-/

namespace Work.Pert

open Complex

theorem deriv_liftF_defect_le {u : ℂ → ℂ} {σ α : ℂ} {ρ ρmin : ℝ} {z : ℂ}
    (hρmin : 0 < ρmin) (hρ : ρmin ≤ ρ)
    (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) ρ))
    (hub : ∀ w ∈ Metric.ball (0 : ℂ) ρ, 1 / 2 ≤ ‖u w‖ ∧ ‖u w‖ ≤ 2)
    (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hσ8 : ‖σ‖ ≤ 8 * Real.pi * ‖α‖)
    (hαs : ‖α‖ ≤ 1 / 10 ^ 6) (hαne : α ≠ 0)
    (hτ1 : ‖Work.Pert.tauC σ α z‖ ≤ 1 / 16) (hτ2 : ‖Work.Pert.tauC σ α z‖ ≤ ρmin / 2)
    (hE : Complex.exp (-(2 * Real.pi * Complex.I * α * z)) ≠ 1) :
    ‖deriv (Work.Pert.liftF u σ α) z - 1‖
      ≤ (32 / ρmin + 16) * ‖σ‖ ^ 2
        * (‖Complex.exp (-(2 * Real.pi * Complex.I * α * z))‖
            / ‖1 - Complex.exp (-(2 * Real.pi * Complex.I * α * z))‖ ^ 2) := by
  -- ## Step 1: `exp (2πiα) ≠ 1`, hence `σ ≠ 0`
  have hexp_ne_one : Complex.exp (2 * Real.pi * Complex.I * α) ≠ 1 := by
    intro h
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
    have h2 : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Complex.ext_iff, Real.pi_ne_zero]
    have hαn : α = (n : ℂ) := by
      have h3 : (2 * Real.pi * I) * α = (2 * Real.pi * I) * (n : ℂ) := by
        linear_combination hn
      exact mul_left_cancel₀ h2 h3
    apply hαne
    have hnle : ‖(n : ℂ)‖ ≤ 1 / 10 ^ 6 := by rw [← hαn]; exact hαs
    simp only [Complex.norm_intCast] at hnle
    have h5 : (|n| : ℤ) = 0 := by
      have h4 : ((|n| : ℤ) : ℝ) < 1 := by
        rw [Int.cast_abs]; linarith [hnle, abs_nonneg (n : ℝ)]
      have h6 : (|n| : ℤ) < 1 := by exact_mod_cast h4
      have h7 : (0 : ℤ) ≤ |n| := abs_nonneg n
      omega
    rw [hαn]
    have : n = 0 := abs_eq_zero.mp (by exact_mod_cast h5)
    rw [this]; simp
  have hσne : σ ≠ 0 := by
    intro hσ0
    refine hexp_ne_one ?_
    rw [← hnorm, hσ0]; ring
  -- ## Step 2: smallness of `σ` and closeness of `exp (2πiα)` to `1`
  have hσ_le : ‖σ‖ ≤ 8 * Real.pi * (1 / 10 ^ 6) := by
    have h := mul_le_mul_of_nonneg_left hαs (by positivity : (0:ℝ) ≤ 8 * Real.pi)
    linarith [hσ8, h]
  have hσsmall : ‖σ‖ ≤ 1 / 64 := by
    have h : 8 * Real.pi * (1 / 10 ^ 6) ≤ 1 / 64 := by
      have := Real.pi_lt_four; nlinarith
    linarith
  have h4σ : 4 * ‖σ‖ ≤ 1 / 16 := by linarith
  have hexp_ge : (3 / 4 : ℝ) ≤ ‖Complex.exp (2 * Real.pi * Complex.I * α)‖ := by
    rw [Complex.norm_exp]
    have him : (2 * Real.pi * Complex.I * α).re = -(2 * Real.pi * α.im) := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [him]
    set t : ℝ := 2 * Real.pi * α.im with ht
    have ht_le : t ≤ 2 * Real.pi * (1 / 10 ^ 6) := by
      rw [ht]
      have h := Complex.im_le_norm α
      nlinarith [Real.pi_pos, h, hαs]
    have hsub : 1 - t ≤ Real.exp (-t) := by
      have h := Real.add_one_le_exp (-t); linarith
    have h34 : (3 / 4 : ℝ) ≤ 1 - 2 * Real.pi * (1 / 10 ^ 6) := by
      have := Real.pi_lt_four; linarith
    linarith
  have hEne : (1 : ℂ) - Complex.exp (-(2 * Real.pi * Complex.I * α * z)) ≠ 0 := by
    intro h; exact hE (sub_eq_zero.mp h).symm
  -- ## Step 3: the point `τ = τ_f z` and the Cauchy estimates
  set τ : ℂ := Work.Pert.tauC σ α z with hτdef
  have hτa : ‖τ‖ ≤ 1 / 16 := by rw [hτdef]; exact hτ1
  have hτb : ‖τ‖ ≤ ρmin / 2 := by rw [hτdef]; exact hτ2
  have hρpos : 0 < ρ := lt_of_lt_of_le hρmin hρ
  have hτmem : τ ∈ Metric.ball (0 : ℂ) ρ := by
    rw [Metric.mem_ball, dist_zero_right]; linarith
  have h0mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) ρ := by
    rw [Metric.mem_ball, dist_zero_right, norm_zero]; exact hρpos
  have huτ2 : ‖u τ‖ ≤ 2 := (hub τ hτmem).2
  have huτ_at : DifferentiableAt ℂ u τ := hu.differentiableAt (Metric.isOpen_ball.mem_nhds hτmem)
  have hsc := Work.Pert.scale_cauchy hρmin hρ hu (fun w hw => (hub w hw).2)
  have hdu : ‖deriv u τ‖ ≤ 8 / ρmin := hsc.1 τ hτb
  have hmvt : ‖u 0 - u τ‖ ≤ (8 / ρmin) * ‖τ‖ := hsc.2 τ hτb
  -- ## Step 4: `1 - σ u τ` is close to `exp (2πiα)`
  have hσu : ‖σ * (u 0 - u τ)‖ ≤ 1 / 16 := by
    rw [norm_mul]
    calc ‖σ‖ * ‖u 0 - u τ‖ ≤ ‖σ‖ * ((8 / ρmin) * ‖τ‖) :=
          mul_le_mul_of_nonneg_left hmvt (norm_nonneg σ)
      _ ≤ ‖σ‖ * ((8 / ρmin) * (ρmin / 2)) := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg σ)
          exact mul_le_mul_of_nonneg_left hτb (by positivity)
      _ = 4 * ‖σ‖ := by field_simp; ring
      _ ≤ 1 / 16 := h4σ
  have h1σu : (11 / 16 : ℝ) ≤ ‖1 - σ * u τ‖ := by
    have heq : 1 - σ * u τ = Complex.exp (2 * Real.pi * I * α) + σ * (u 0 - u τ) := by
      rw [← hnorm]; ring
    rw [heq]
    have h := norm_sub_le (Complex.exp (2 * Real.pi * I * α) + σ * (u 0 - u τ))
      (σ * (u 0 - u τ))
    rw [add_sub_cancel_right] at h
    linarith
  -- ## Step 5: the two denominator factors are `≥ 1/2`, hence their product `≥ 1/4`
  have hτu : ‖τ * u τ‖ ≤ 1 / 8 := by
    rw [norm_mul]
    calc ‖τ‖ * ‖u τ‖ ≤ (1/16) * 2 := mul_le_mul hτa huτ2 (norm_nonneg _) (by norm_num)
      _ = 1/8 := by norm_num
  have h1τu : (7 / 8 : ℝ) ≤ ‖1 + τ * u τ‖ := by
    have h := norm_sub_le ((1 : ℂ) + τ * u τ) (τ * u τ)
    rw [add_sub_cancel_right, norm_one] at h
    linarith
  have h1τuσu : (1 / 2 : ℝ) ≤ ‖1 + τ * u τ - σ * u τ‖ := by
    have heq : 1 + τ * u τ - σ * u τ = (1 - σ * u τ) + τ * u τ := by ring
    rw [heq]
    have h := norm_sub_le ((1 - σ * u τ) + τ * u τ) (τ * u τ)
    rw [add_sub_cancel_right] at h
    linarith
  have hAne : 1 + τ * u τ ≠ 0 := by
    intro h; rw [h, norm_zero] at h1τu; norm_num at h1τu
  have hBne : 1 + τ * u τ - σ * u τ ≠ 0 := by
    intro h; rw [h, norm_zero] at h1τuσu; norm_num at h1τuσu
  have hden : (1 / 4 : ℝ) ≤ ‖1 + τ * u τ - σ * u τ‖ * ‖1 + τ * u τ‖ := by
    have h := mul_le_mul h1τuσu h1τu (by norm_num : (0:ℝ) ≤ 7/8) (norm_nonneg _)
    linarith [h]
  -- ## Step 6: the numerator `u' - u²` is `O(1/ρmin)`
  have hnum : ‖deriv u τ - u τ ^ 2‖ ≤ 8 / ρmin + 4 := by
    have h2 : ‖u τ ^ 2‖ ≤ 4 := by
      rw [norm_pow]; nlinarith [huτ2, norm_nonneg (u τ)]
    linarith [norm_sub_le (deriv u τ) (u τ ^ 2), hdu, h2]
  -- ## Step 7: `1 - sfun ∈ slitPlane` (so that `Complex.log` is differentiable there)
  have hsfun_eq : Work.Pert.sfun u σ α z = σ * u τ / (1 + τ * u τ) := by
    simp only [Work.Pert.sfun]
    rw [← hτdef]
  have hsfun_le : ‖Work.Pert.sfun u σ α z‖ ≤ 1 / 28 := by
    rw [hsfun_eq, norm_div, norm_mul]
    rw [div_le_iff₀ (by linarith : (0:ℝ) < ‖1 + τ * u τ‖)]
    have h1 : ‖σ‖ * ‖u τ‖ ≤ 1 / 32 := by
      calc ‖σ‖ * ‖u τ‖ ≤ (1/64) * 2 := mul_le_mul hσsmall huτ2 (norm_nonneg _) (by norm_num)
        _ = 1/32 := by norm_num
    have h2 : (1/32 : ℝ) ≤ 1 / 28 * ‖1 + τ * u τ‖ := by
      have hh : (1/28 : ℝ) * (7/8) ≤ (1/28) * ‖1 + τ * u τ‖ :=
        mul_le_mul_of_nonneg_left h1τu (by norm_num)
      have : (1:ℝ)/28 * (7/8) = 1/32 := by norm_num
      linarith
    linarith
  have hslit : 1 - Work.Pert.sfun u σ α z ∈ Complex.slitPlane := by
    refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
    have h := Complex.abs_re_le_norm (Work.Pert.sfun u σ α z)
    rw [abs_le] at h
    simp only [Complex.sub_re, Complex.one_re]
    linarith [h.1, hsfun_le]
  -- ## Step 8: the exact derivative formula `Work.Pert.gate_derivF`
  have hzne' : Work.Pert.tauC σ α z ≠ 0 := by
    rw [Work.Pert.tauC]
    exact div_ne_zero hσne hEne
  have huτ_at' : DifferentiableAt ℂ u (Work.Pert.tauC σ α z) := by rw [← hτdef]; exact huτ_at
  have hAne' : (1 : ℂ) + Work.Pert.tauC σ α z * u (Work.Pert.tauC σ α z) ≠ 0 := by
    rw [← hτdef]; exact hAne
  have hBne' : 1 + Work.Pert.tauC σ α z * u (Work.Pert.tauC σ α z)
      - σ * u (Work.Pert.tauC σ α z) ≠ 0 := by rw [← hτdef]; exact hBne
  have hderiv0 := Work.Pert.gate_derivF hαne hσne hzne' huτ_at' hslit hE hAne' hBne'
  have hderiv : deriv (Work.Pert.liftF u σ α) z - 1
      = τ * (τ - σ) * (deriv u τ - u τ ^ 2) / ((1 + τ * u τ - σ * u τ) * (1 + τ * u τ)) := by
    rw [hderiv0.deriv]
    rw [← hτdef]
    ring
  -- ## Step 9: `τ(τ-σ) = σ²E/(1-E)²`
  set E : ℂ := Complex.exp (-(2 * Real.pi * Complex.I * α * z)) with hEdef
  have hτE : τ = σ / (1 - E) := by rw [hτdef, Work.Pert.tauC, ← hEdef]
  have hττσ : τ * (τ - σ) = σ ^ 2 * E / (1 - E) ^ 2 := by
    rw [hτE]; field_simp; ring
  have hnorm_ττσ : ‖τ * (τ - σ)‖ = ‖σ‖ ^ 2 * ‖E‖ / ‖1 - E‖ ^ 2 := by
    rw [hττσ, norm_div, norm_mul, norm_pow, norm_pow]
  have hratio : ‖deriv u τ - u τ ^ 2‖ / (‖1 + τ * u τ - σ * u τ‖ * ‖1 + τ * u τ‖)
      ≤ 32 / ρmin + 16 := by
    rw [div_le_iff₀ (by linarith [hden] : (0:ℝ) < ‖1 + τ * u τ - σ * u τ‖ * ‖1 + τ * u τ‖)]
    have hc : (32 / ρmin + 16) * (1/4) = 8 / ρmin + 4 := by ring
    have hh := mul_le_mul_of_nonneg_left hden (by positivity : (0:ℝ) ≤ 32 / ρmin + 16)
    linarith [hnum, hh, hc]
  -- ## Step 10: assembly
  calc ‖deriv (Work.Pert.liftF u σ α) z - 1‖
      = ‖τ * (τ - σ) * (deriv u τ - u τ ^ 2)
          / ((1 + τ * u τ - σ * u τ) * (1 + τ * u τ))‖ := by rw [hderiv]
    _ = ‖τ * (τ - σ)‖ * ‖deriv u τ - u τ ^ 2‖
          / (‖1 + τ * u τ - σ * u τ‖ * ‖1 + τ * u τ‖) := by
          simp only [norm_div, norm_mul]
    _ = ‖τ * (τ - σ)‖ * (‖deriv u τ - u τ ^ 2‖
          / (‖1 + τ * u τ - σ * u τ‖ * ‖1 + τ * u τ‖)) := by ring_nf
    _ ≤ ‖τ * (τ - σ)‖ * (32 / ρmin + 16) :=
          mul_le_mul_of_nonneg_left hratio (norm_nonneg _)
    _ = (32 / ρmin + 16) * ‖σ‖ ^ 2 * (‖E‖ / ‖1 - E‖ ^ 2) := by
          rw [hnorm_ττσ]; ring_nf
    _ = (32 / ρmin + 16) * ‖σ‖ ^ 2
          * (‖Complex.exp (-(2 * Real.pi * Complex.I * α * z))‖
              / ‖1 - Complex.exp (-(2 * Real.pi * Complex.I * α * z))‖ ^ 2) := by
          rw [hEdef]

end Work.Pert
