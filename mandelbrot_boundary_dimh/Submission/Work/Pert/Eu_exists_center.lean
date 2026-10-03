import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Pert.deriv_tau0_tauC_exact
import Submission.Work.Pert.norm_exp_sub_one_sub_id_le_sharp
import Submission.Work.Pert.exp_inv_64_le
import Submission.Work.Pert.norm_sinh_sub_id_le
import Submission.Work.Pert.norm_psi_sub_one_le

/-!
# PERT · `Work.Pert.Eu_exists_center`

Shishikura, Lemma A.4 / (4.2.x): the composite chart `τ₀ ∘ τ_f` (where `τ_f = tauC σ α` is the
universal cover `ℂ → ℂ ∖ {0, σ}` of (A.1.5) and `τ₀ w = -1/w`) differs from the identity by an
additive constant, uniformly on the two discs `closedBall (±iη) (33η/100)`, up to `η/115`.

The exact identity is

  `τ₀ (τ_f ζ) = (e^{-2πiαζ} - 1)/σ`,

and the normalisation `1 - σ u₀ = e^{2πiα}` gives `σ = (1 - e^{x})/u₀`, `x = 2πiα`.  Writing
`ψ = (e^{x} - 1)/x` one has `σ = -xψ/u₀`, so for `zc` one of the two centres and `w = x·zc`:

  `τ₀ (τ_f ζ) - (e^{-x·zc} + e^{x·zc} - 2)/(2σ)
      = (-r·((x/σ)e^{-x·zc} + 1) + e^{-x·zc}·ρ/σ) + (zc·(u₀ sinh(w)/w/ψ - 1))`

with `r = ζ - zc` and `ρ = e^{-x r} - 1 + x r`.  Both bracketed pieces are `O(η)·(≤1/64)`
(the first because the two `O(1)` terms of `e^{-xζ}` cancel, the second because `sinh(w)/w = 1+O(w²)`
and `u₀ ≈ ψ`), and the arithmetic `33/100·171/10000 + 1/940 + 1/840 ≤ 1/115` closes the estimate.
-/

namespace Work.Pert

open Complex

noncomputable section

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem Eu_exists_center {σ α u₀ : ℂ} {η : ℝ}
    (hη : 0 < η) (hη100 : 100 ≤ η) (hσ : σ ≠ 0) (hα : α ≠ 0)
    (hu₀ : ‖u₀ - 1‖ ≤ 1 / 1024)
    (hαη : 2 * Real.pi * ‖α‖ * η ≤ 1 / 64)
    (heq : 1 - σ * u₀ = Complex.exp (2 * Real.pi * Complex.I * α)) :
    ∃ c : ℂ, ∀ ζ ∈ Metric.closedBall (Complex.I * (η : ℂ)) (33 * η / 100) ∪
                          Metric.closedBall (-(Complex.I * (η : ℂ))) (33 * η / 100),
      ‖MandelDim.tau0 (Work.Pert.tauC σ α ζ) - ζ - c‖ ≤ η / 115 := by
  set x : ℂ := 2 * Real.pi * Complex.I * α with hxdef
  set z0 : ℂ := Complex.I * (η : ℂ) with hz0def
  -- ## facts about `x`
  have hxnz : x ≠ 0 := by
    rw [hxdef]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ?_) ?_) hα
    · exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    · exact Complex.I_ne_zero
  have hxnorm : ‖x‖ = 2 * Real.pi * ‖α‖ := by
    rw [hxdef, norm_mul, norm_mul, norm_mul]
    have hI : ‖Complex.I‖ = 1 := Complex.norm_I
    have hp : ‖(Real.pi : ℂ)‖ = Real.pi := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have h2c : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2c, hp, hI, mul_one]
  have hxeta : ‖x‖ * η ≤ 1 / 64 := by rw [hxnorm]; exact hαη
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hxnz
  have hx6400 : ‖x‖ ≤ 1 / 6400 := by nlinarith [hxeta, hη100, hxpos]
  have hxhalf : ‖x‖ ≤ 1 / 2 := by linarith
  -- ## facts about `z0`
  have hz0nz : z0 ≠ 0 := by
    rw [hz0def]
    exact mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hη))
  have hz0norm : ‖z0‖ = η := by
    rw [hz0def, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hη]
  -- ## facts about `u₀`
  have hu0nz : u₀ ≠ 0 := by
    intro h
    rw [h] at hu₀
    norm_num at hu₀
  have hu0le : ‖u₀‖ ≤ 1 + 1 / 1024 := by
    have h3 : (u₀ - 1) + 1 = u₀ := by ring
    have h2 : ‖(u₀ - 1) + 1‖ ≤ ‖u₀ - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    rw [h3, norm_one] at h2
    linarith
  -- ## facts about `σ`, `ψ`
  have hσu0 : σ * u₀ = 1 - Complex.exp x := by
    have h := heq
    rw [hxdef] at h
    linear_combination -h
  have h1expnz : 1 - Complex.exp x ≠ 0 := by
    rw [← hσu0]; exact mul_ne_zero hσ hu0nz
  set ψ : ℂ := (Complex.exp x - 1) / x with hψdef
  have hψ1 : ‖ψ - 1‖ ≤ 29 / 48 * ‖x‖ := by
    rw [hψdef]; exact norm_psi_sub_one_le hxnz hxhalf
  have hψ1b : ‖ψ - 1‖ ≤ 1 / 10000 := by
    have h : (29 / 48 : ℝ) * ‖x‖ ≤ 1 / 10000 := by nlinarith [hx6400]
    linarith [hψ1, h]
  have hψge : (9999 / 10000 : ℝ) ≤ ‖ψ‖ := by
    have h : (1 : ℂ) = ψ - (ψ - 1) := by ring
    have h2 : ‖(1 : ℂ)‖ ≤ ‖ψ - (ψ - 1)‖ := by rw [← h]
    rw [norm_one] at h2
    have h3 := norm_sub_le ψ (ψ - 1)
    linarith [hψ1b]
  have hψne : ψ ≠ 0 := by
    intro h
    have h2 := hψge
    rw [h, norm_zero] at h2
    norm_num at h2
  have hψeq : x * ψ = Complex.exp x - 1 := by
    rw [hψdef]; field_simp
  have hσ_eq : σ = -(x * ψ) / u₀ := by
    rw [eq_div_iff hu0nz, hσu0, hψeq]; ring
  have hxσ : x / σ = -u₀ / ψ := by
    rw [hσ_eq]; field_simp
  have hinvσ : (1 : ℂ) / σ = -u₀ / (x * ψ) := by
    rw [hσ_eq]; field_simp
  have hσnorm : (998 / 1000 : ℝ) * ‖x‖ ≤ ‖σ‖ := by
    have hu0p : 0 < ‖u₀‖ := norm_pos_iff.mpr hu0nz
    have hσval : ‖σ‖ = ‖x‖ * ‖ψ‖ / ‖u₀‖ := by
      rw [hσ_eq, norm_div, norm_neg, norm_mul]
    have h2 : (998 / 1000 : ℝ) * ‖u₀‖ ≤ ‖ψ‖ := by nlinarith [hψge, hu0le]
    rw [hσval, le_div_iff₀ hu0p]
    nlinarith [mul_le_mul_of_nonneg_left h2 (norm_nonneg x)]
  -- ## the constant and the key estimate
  refine ⟨(Complex.exp (-(x * z0)) + Complex.exp (x * z0) - 2) / (2 * σ), ?_⟩
  have key : ∀ (zc z : ℂ), (zc = z0 ∨ zc = -z0) → ‖z - zc‖ ≤ 33 * η / 100 →
      ‖MandelDim.tau0 (Work.Pert.tauC σ α z) - z
        - (Complex.exp (-(x * zc)) + Complex.exp (x * zc) - 2) / (2 * σ)‖ ≤ η / 115 := by
    intro zc z hzc hz
    have hznorm : ‖zc‖ = η := by
      rcases hzc with h | h
      · rw [h]; exact hz0norm
      · rw [h, norm_neg]; exact hz0norm
    have hznz : zc ≠ 0 := by
      intro h
      have h2 := hznorm
      rw [h, norm_zero] at h2
      linarith [hη]
    have hxzc : ‖x * zc‖ ≤ 1 / 64 := by rw [norm_mul, hznorm]; exact hxeta
    have hxzc_half : ‖x * zc‖ ≤ 1 / 2 := by linarith
    have hexp_norm : ‖Complex.exp (-(x * zc))‖ ≤ 51 / 50 := by
      have h102 : (1.02 : ℝ) = 51 / 50 := by norm_num
      have h1 : (-(x * zc)).re ≤ 1 / 64 := by
        calc (-(x * zc)).re ≤ ‖-(x * zc)‖ := Complex.re_le_norm _
          _ = ‖x * zc‖ := by rw [norm_neg]
          _ ≤ 1 / 64 := hxzc
      rw [Complex.norm_exp]
      calc Real.exp ((-(x * zc)).re) ≤ Real.exp (1 / 64) := Real.exp_le_exp.mpr h1
        _ ≤ 1.02 := exp_inv_64_le
        _ = 51 / 50 := h102
    set r : ℂ := z - zc with hrdef
    have hrnorm : ‖r‖ ≤ 33 * η / 100 := by rw [hrdef]; exact hz
    have hzdecomp : z = zc + r := by rw [hrdef]; ring
    have hxr_half : ‖x * r‖ ≤ 1 / 2 := by
      rw [norm_mul]
      have h2 : ‖x‖ * (33 * η / 100) ≤ 1 / 2 := by nlinarith [hxeta, hη, hxpos]
      exact le_trans (mul_le_mul_of_nonneg_left hrnorm (norm_nonneg x)) h2
    -- exact decomposition
    have hexpz : Complex.exp (-(x * z)) = Complex.exp (-(x * zc)) * Complex.exp (-(x * r)) := by
      rw [← Complex.exp_add]
      congr 1
      rw [hrdef]; ring
    have hdecomp : MandelDim.tau0 (Work.Pert.tauC σ α z) - z
        - (Complex.exp (-(x * zc)) + Complex.exp (x * zc) - 2) / (2 * σ)
        = (-r * ((x / σ) * Complex.exp (-(x * zc)) + 1)
            + Complex.exp (-(x * zc)) * (Complex.exp (-(x * r)) - 1 + x * r) / σ)
          + ((Complex.exp (-(x * zc)) - Complex.exp (x * zc)) / (2 * σ) - zc) := by
      have htau : MandelDim.tau0 (Work.Pert.tauC σ α z)
          = (Complex.exp (-(x * z)) - 1) / σ := by
        rw [Work.Pert.tau0_tauC_eq σ α z]
      rw [htau, hexpz, hzdecomp]
      field_simp
      ring
    -- ### the `C₁` bound
    have hC1 : ‖(x / σ) * Complex.exp (-(x * zc)) + 1‖ ≤ 171 / 10000 := by
      have hE : (x / σ) * Complex.exp (-(x * zc)) + 1
          = (ψ - u₀ * Complex.exp (-(x * zc))) / ψ := by
        rw [hxσ]; field_simp; ring
      rw [hE, norm_div]
      have hnum : ‖ψ - u₀ * Complex.exp (-(x * zc))‖ ≤ 17 / 1000 := by
        have hsplit : ψ - u₀ * Complex.exp (-(x * zc))
            = (ψ - 1) + (1 - Complex.exp (-(x * zc)))
              + (1 - u₀) * Complex.exp (-(x * zc)) := by ring
        rw [hsplit]
        have h1 : ‖ψ - 1‖ ≤ 29 / 48 * (1 / 6400) := by nlinarith [hψ1, hx6400]
        have h2 : ‖1 - Complex.exp (-(x * zc))‖ ≤ 1 / 64 + (1 / 64) ^ 2 := by
          have hw : ‖-(x * zc)‖ ≤ 1 := by rw [norm_neg]; linarith [hxzc]
          have hb := Complex.norm_exp_sub_one_sub_id_le (x := -(x * zc)) hw
          have hb2 : ‖Complex.exp (-(x * zc)) - 1 + x * zc‖ ≤ ‖x * zc‖ ^ 2 := by
            simpa only [norm_neg, sub_neg_eq_add] using hb
          have hb3 : ‖Complex.exp (-(x * zc)) - 1‖ ≤ ‖x * zc‖ + ‖x * zc‖ ^ 2 := by
            have hs : Complex.exp (-(x * zc)) - 1
                = (Complex.exp (-(x * zc)) - 1 + x * zc) - (x * zc) := by ring
            rw [hs]
            have hle := norm_sub_le (Complex.exp (-(x * zc)) - 1 + x * zc) (x * zc)
            linarith
          rw [norm_sub_rev]
          nlinarith [hb3, hxzc, norm_nonneg (x * zc)]
        have h3 : ‖(1 - u₀) * Complex.exp (-(x * zc))‖ ≤ (1 / 1024) * (51 / 50) := by
          rw [norm_mul, norm_sub_rev]
          exact mul_le_mul hu₀ hexp_norm (norm_nonneg _) (by norm_num)
        calc ‖(ψ - 1) + (1 - Complex.exp (-(x * zc)))
              + (1 - u₀) * Complex.exp (-(x * zc))‖
            ≤ ‖(ψ - 1) + (1 - Complex.exp (-(x * zc)))‖
              + ‖(1 - u₀) * Complex.exp (-(x * zc))‖ := norm_add_le _ _
          _ ≤ (‖ψ - 1‖ + ‖1 - Complex.exp (-(x * zc))‖)
              + ‖(1 - u₀) * Complex.exp (-(x * zc))‖ := by
              gcongr
              exact norm_add_le _ _
          _ ≤ 17 / 1000 := by linarith [h1, h2, h3]
      calc ‖ψ - u₀ * Complex.exp (-(x * zc))‖ / ‖ψ‖ ≤ (17 / 1000) / ‖ψ‖ :=
            div_le_div_of_nonneg_right hnum (norm_nonneg ψ)
        _ ≤ (17 / 1000) / (9999 / 10000) :=
            div_le_div_of_nonneg_left (by norm_num) (by norm_num) hψge
        _ ≤ 171 / 10000 := by norm_num
    have b1 : ‖-r * ((x / σ) * Complex.exp (-(x * zc)) + 1)‖
        ≤ (33 * η / 100) * (171 / 10000) := by
      rw [norm_mul, norm_neg]
      exact mul_le_mul hrnorm hC1 (norm_nonneg _) (by positivity)
    -- ### the `ρ` (second-order) bound
    have b2 : ‖Complex.exp (-(x * zc)) * (Complex.exp (-(x * r)) - 1 + x * r) / σ‖
        ≤ η / 940 := by
      have hρ : ‖Complex.exp (-(x * r)) - 1 + x * r‖ ≤ 29 / 48 * ‖x * r‖ ^ 2 := by
        have hb := norm_exp_sub_one_sub_id_le_sharp (z := -(x * r))
          (by rw [norm_neg]; exact hxr_half)
        simpa only [norm_neg, sub_neg_eq_add] using hb
      have hxr2 : ‖x‖ * ‖r‖ ^ 2 ≤ (1089 / 10000) * (η / 64) := by
        have hr2 : ‖r‖ ^ 2 ≤ (33 * η / 100) ^ 2 := by nlinarith [hrnorm, norm_nonneg r, hη]
        calc ‖x‖ * ‖r‖ ^ 2 ≤ ‖x‖ * (33 * η / 100) ^ 2 :=
              mul_le_mul_of_nonneg_left hr2 (norm_nonneg x)
          _ = (1089 / 10000) * (‖x‖ * η ^ 2) := by ring
          _ ≤ (1089 / 10000) * (η / 64) := by
              have h2 : ‖x‖ * η ^ 2 ≤ η / 64 := by nlinarith [hxeta, hη]
              exact mul_le_mul_of_nonneg_left h2 (by norm_num)
      rw [norm_div, norm_mul]
      have hstep : ‖Complex.exp (-(x * zc))‖ * ‖Complex.exp (-(x * r)) - 1 + x * r‖ / ‖σ‖
          ≤ (51 / 50) * (29 / 48 * ‖x * r‖ ^ 2) / ((998 / 1000) * ‖x‖) := by
        apply div_le_div₀ (by positivity)
        · exact mul_le_mul hexp_norm hρ (norm_nonneg _) (by norm_num)
        · positivity
        · exact hσnorm
      calc ‖Complex.exp (-(x * zc))‖ * ‖Complex.exp (-(x * r)) - 1 + x * r‖ / ‖σ‖
          ≤ (51 / 50) * (29 / 48 * ‖x * r‖ ^ 2) / ((998 / 1000) * ‖x‖) := hstep
        _ = (51 / 50) * (29 / 48) * (1000 / 998) * (‖x‖ * ‖r‖ ^ 2) := by
            rw [norm_mul, norm_mul]
            field_simp
        _ ≤ (51 / 50) * (29 / 48) * (1000 / 998) * ((1089 / 10000) * (η / 64)) := by
            have hc : (0 : ℝ) ≤ (51 / 50) * (29 / 48) * (1000 / 998) := by norm_num
            exact mul_le_mul_of_nonneg_left hxr2 hc
        _ ≤ η / 940 := by
            have h1 : (51 / 50) * (29 / 48) * (1000 / 998) * ((1089 / 10000) * (1 / 64)) ≤ 1 / 940 := by
              norm_num
            nlinarith [h1, hη]
    -- ### the centre-mismatch bound
    have b3 : ‖(Complex.exp (-(x * zc)) - Complex.exp (x * zc)) / (2 * σ) - zc‖ ≤ η / 840 := by
      have hsinh : Complex.sinh (x * zc) = (Complex.exp (x * zc) - Complex.exp (-(x * zc))) / 2 := by
        rw [Complex.sinh]
      have hw : x * zc ≠ 0 := mul_ne_zero hxnz hznz
      have hform : (Complex.exp (-(x * zc)) - Complex.exp (x * zc)) / (2 * σ) - zc
          = zc * (u₀ * (Complex.sinh (x * zc) / (x * zc)) / ψ - 1) := by
        rw [hsinh]
        have hstep : (Complex.exp (-(x * zc)) - Complex.exp (x * zc)) / (2 * σ)
            = (Complex.exp (-(x * zc)) - Complex.exp (x * zc)) / 2 * (1 / σ) := by ring
        rw [hstep, hinvσ]
        field_simp
        ring
      have hsinhle : ‖Complex.sinh (x * zc) / (x * zc) - 1‖ ≤ (1 / 64) ^ 2 / 3 := by
        have h1 : Complex.sinh (x * zc) / (x * zc) - 1
            = (Complex.sinh (x * zc) - x * zc) / (x * zc) := by
          field_simp
        rw [h1, norm_div]
        have hb := norm_sinh_sub_id_le (w := x * zc) hxzc_half
        have hwpos : 0 < ‖x * zc‖ := norm_pos_iff.mpr hw
        rw [div_le_iff₀ hwpos]
        calc ‖Complex.sinh (x * zc) - x * zc‖ ≤ ‖x * zc‖ ^ 3 / 3 := hb
          _ ≤ ((1 / 64 : ℝ) ^ 2 / 3) * ‖x * zc‖ := by
              have h0 : (0:ℝ) ≤ ‖x * zc‖ := norm_nonneg _
              have hsq : ‖x * zc‖ ^ 2 ≤ (1 / 64 : ℝ) ^ 2 := by nlinarith [hxzc, h0]
              nlinarith [hsq, h0]
      have hsinhnorm : ‖Complex.sinh (x * zc) / (x * zc)‖ ≤ 1 + (1 / 64) ^ 2 / 3 := by
        have h := norm_add_le (Complex.sinh (x * zc) / (x * zc) - 1) 1
        rw [sub_add_cancel, norm_one] at h
        linarith [hsinhle]
      have hnum2 : ‖u₀ * (Complex.sinh (x * zc) / (x * zc)) - ψ‖ ≤ 116 / 100000 := by
        have hsplit : u₀ * (Complex.sinh (x * zc) / (x * zc)) - ψ
            = (u₀ - 1) * (Complex.sinh (x * zc) / (x * zc))
              + (Complex.sinh (x * zc) / (x * zc) - 1) + (1 - ψ) := by ring
        rw [hsplit]
        have h1 : ‖(u₀ - 1) * (Complex.sinh (x * zc) / (x * zc))‖
            ≤ (1 / 1024) * (1 + (1 / 64) ^ 2 / 3) := by
          rw [norm_mul]
          exact mul_le_mul hu₀ hsinhnorm (norm_nonneg _) (by norm_num)
        have h2 : ‖Complex.sinh (x * zc) / (x * zc) - 1‖ ≤ (1 / 64) ^ 2 / 3 := hsinhle
        have h3 : ‖1 - ψ‖ ≤ 1 / 10000 := by rw [norm_sub_rev]; exact hψ1b
        calc ‖(u₀ - 1) * (Complex.sinh (x * zc) / (x * zc))
              + (Complex.sinh (x * zc) / (x * zc) - 1) + (1 - ψ)‖
            ≤ ‖(u₀ - 1) * (Complex.sinh (x * zc) / (x * zc))
                + (Complex.sinh (x * zc) / (x * zc) - 1)‖ + ‖1 - ψ‖ := norm_add_le _ _
          _ ≤ (‖(u₀ - 1) * (Complex.sinh (x * zc) / (x * zc))‖
                + ‖Complex.sinh (x * zc) / (x * zc) - 1‖) + ‖1 - ψ‖ := by
              gcongr
              exact norm_add_le _ _
          _ ≤ 116 / 100000 := by linarith [h1, h2, h3]
      have hfin : ‖u₀ * (Complex.sinh (x * zc) / (x * zc)) / ψ - 1‖ ≤ 1 / 840 := by
        have hform2 : u₀ * (Complex.sinh (x * zc) / (x * zc)) / ψ - 1
            = (u₀ * (Complex.sinh (x * zc) / (x * zc)) - ψ) / ψ := by
          field_simp
        rw [hform2, norm_div]
        calc ‖u₀ * (Complex.sinh (x * zc) / (x * zc)) - ψ‖ / ‖ψ‖ ≤ (116 / 100000) / ‖ψ‖ :=
              div_le_div_of_nonneg_right hnum2 (norm_nonneg ψ)
          _ ≤ (116 / 100000) / (9999 / 10000) :=
              div_le_div_of_nonneg_left (by norm_num) (by norm_num) hψge
          _ ≤ 1 / 840 := by norm_num
      rw [hform, norm_mul]
      calc ‖zc‖ * ‖u₀ * (Complex.sinh (x * zc) / (x * zc)) / ψ - 1‖ ≤ η * (1 / 840) := by
            rw [hznorm]
            exact mul_le_mul_of_nonneg_left hfin (by positivity)
        _ = η / 840 := by ring
    -- ### assemble
    have hsum : (33 * η / 100) * (171 / 10000) + η / 940 + η / 840 ≤ η / 115 := by
      have hcoef : (33 / 100 : ℝ) * (171 / 10000) + 1 / 940 + 1 / 840 ≤ 1 / 115 := by norm_num
      have he : (33 * η / 100) * (171 / 10000) + η / 940 + η / 840
          = ((33 / 100 : ℝ) * (171 / 10000) + 1 / 940 + 1 / 840) * η := by ring
      have he2 : η / 115 = (1 / 115 : ℝ) * η := by ring
      rw [he, he2]
      exact mul_le_mul_of_nonneg_right hcoef (le_of_lt hη)
    rw [hdecomp]
    calc ‖(-r * ((x / σ) * Complex.exp (-(x * zc)) + 1)
            + Complex.exp (-(x * zc)) * (Complex.exp (-(x * r)) - 1 + x * r) / σ)
          + ((Complex.exp (-(x * zc)) - Complex.exp (x * zc)) / (2 * σ) - zc)‖
        ≤ (33 * η / 100) * (171 / 10000) + η / 940 + η / 840 := by
          refine (norm_add_le _ _).trans ?_
          have hinner : ‖-r * ((x / σ) * Complex.exp (-(x * zc)) + 1)
              + Complex.exp (-(x * zc)) * (Complex.exp (-(x * r)) - 1 + x * r) / σ‖
              ≤ (33 * η / 100) * (171 / 10000) + η / 940 := by
            refine (norm_add_le _ _).trans ?_
            linarith [b1, b2]
          linarith [hinner, b3]
      _ ≤ η / 115 := hsum
  intro ζ hζ
  rcases hζ with h | h
  · rw [Metric.mem_closedBall, dist_eq_norm] at h
    exact key z0 ζ (Or.inl rfl) h
  · rw [Metric.mem_closedBall, dist_eq_norm] at h
    have h' : ‖ζ - (-z0)‖ ≤ 33 * η / 100 := by
      simpa using h
    have hcinv : (Complex.exp (-(x * (-z0))) + Complex.exp (x * (-z0)) - 2) / (2 * σ)
        = (Complex.exp (-(x * z0)) + Complex.exp (x * z0) - 2) / (2 * σ) := by
      rw [show x * (-z0) = -(x * z0) by ring]
      simp only [neg_neg]
      ring
    rw [← hcinv]
    exact key (-z0) ζ (Or.inr rfl) h'

end

end Work.Pert
