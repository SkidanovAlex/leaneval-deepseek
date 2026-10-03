import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup
import Submission.Work.Pert.tauC_gate_bound
import Submission.Work.Pert.liftF_lower_zeta_bound

/-!
# PERT · `Work.Pert.liftF_lower_translation`

Shishikura §4.2, the **lower end** of the lower gate `Qm ξ α`: as `z.im → -∞` inside the gate the
universal cover `τ_f z = σ/(1 - exp(-2πiαz))` tends to `σ`, hence the lift
`F_f z = liftF u σ α z` of the perturbed germ, instead of being the translation by `1`, is the
translation by

  `ρ = -log (1 + σ u σ)/(2πi α)`   (note `1 + σ u σ = f'(σ)`, so `ρ = -log f'(σ)/(2πiα)`),

up to an exponentially small error: `‖F_f z - (z + ρ)‖ ≤ M exp (κ z.im)`.  Moreover the
normalisation `1 - σ u 0 = exp (2πiα)` together with the smallness hypothesis
`(2π + 32 C)‖α‖ ≤ 1/128` forces `‖ρ - 1‖ ≤ 1/32`, which is the hypothesis of the lower branch of
`MandelDim.FatouEndsL1`/`PertData.R_close_dn` (see `NOTES_PERT_assembly.md` §14).

The proof is assembled from four independent estimates, proved in this file:

* `log_mul_re_pos_bound` — `log (A*B) = log A + log B` for `Re A, Re B > 0` together with the
  bound `‖log (1 + ζ)‖ ≤ (3/2)‖ζ‖` (`Complex.norm_log_one_add_half_le_self`);
* `tauC_lower_decay` — `‖τ_f z - σ‖ ≤ M exp (κ z.im)` on the gate at the lower end (pure
  two-cone geometry, as in `tauC_upper_decay`);
* `liftF_lower_rho_close` — the numerical bound `‖ρ - 1‖ ≤ 1/32`;
* `liftF_lower_zeta_bound` — the algebraic identity `(1 - sfun) (1 + σuσ) = 1 + ζ` with
  `‖ζ‖ ≤ K₀ ‖τ_f z - σ‖`, together with the positivity of the real parts needed for `log_mul`.
-/

namespace Work.Pert

open MandelDim Complex

noncomputable section

set_option maxHeartbeats 1000000

/-- For `A, B` in the open right half-plane, `A * B = 1 + ζ` and `‖ζ‖ ≤ 1/2`,
`‖(log A + log B)/x‖ ≤ (3/2)‖ζ‖/‖x‖`. -/
theorem log_mul_re_pos_bound {A B ζ x : ℂ}
    (hA : 0 < A.re) (hB : 0 < B.re) (hx : x ≠ 0)
    (hAB : A * B = 1 + ζ) (hζ : ‖ζ‖ ≤ 1 / 2) :
    ‖(Complex.log A + Complex.log B) / x‖ ≤ 3 / 2 * ‖ζ‖ / ‖x‖ := by
  have hAne : A ≠ 0 := fun h => by rw [h] at hA; simp at hA
  have hBne : B ≠ 0 := fun h => by rw [h] at hB; simp at hB
  have harg : Complex.arg A + Complex.arg B ∈ Set.Ioc (-Real.pi) Real.pi := by
    have h1 : |Complex.arg A| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hA)
    have h2 : |Complex.arg B| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hB)
    obtain ⟨ha1, ha2⟩ := abs_lt.mp h1
    obtain ⟨hb1, hb2⟩ := abs_lt.mp h2
    exact ⟨by linarith, by linarith⟩
  have hlog : Complex.log (A * B) = Complex.log A + Complex.log B := Complex.log_mul hAne hBne harg
  rw [← hlog, hAB, norm_div]
  rw [div_le_div_iff_of_pos_right (norm_pos_iff.mpr hx)]
  exact Complex.norm_log_one_add_half_le_self hζ

/-- On the lower gate `Qm ξ α` the covering map decays exponentially at the lower end:
`‖τ_f z - σ‖ ≤ M exp (κ z.im)` for `z.im < -Y`. -/
theorem tauC_lower_decay {σ α : ℂ} {ξ : ℝ} (hξ : 0 < ξ) (hα : MandelDim.InF1 α) :
    ∃ M κ Y : ℝ, 0 < M ∧ 0 < κ ∧
      ∀ z ∈ Work.Pert.Qm ξ α, z.im < -Y →
        ‖Work.Pert.tauC σ α z - σ‖ ≤ M * Real.exp (κ * z.im) := by
  have hα' : |α.im| < α.re := hα
  have hαre : 0 < α.re := by linarith [abs_nonneg α.im]
  have hαne : α ≠ 0 := by intro h; rw [h] at hαre; simp at hαre
  set lam : ℝ := α.re - |α.im| with hlamdef
  have hlampos : 0 < lam := by rw [hlamdef]; linarith
  refine ⟨2 * ‖σ‖ * Real.exp (4 * Real.pi) + 1, 2 * Real.pi * lam,
    (Real.log 2 + 4 * Real.pi) / (2 * Real.pi * lam), by positivity,
    mul_pos (by positivity) hlampos, ?_⟩
  intro z hz hY
  set y : ℝ := z.im with hydef
  set x : ℝ := z.re with hxdef
  have hYpos : 0 < (Real.log 2 + 4 * Real.pi) / (2 * Real.pi * lam) := by positivity
  have hy : y < 0 := by rw [hydef]; linarith
  have hw1 := hz.1 ((ξ : ℂ) - 1 / α) (by simp)
  have hw2 := hz.2 (-(ξ : ℂ)) (by simp)
  have him1 : (z - ((ξ : ℂ) - 1 / α)).im = y + (1 / α).im := by
    rw [hydef]; simp [Complex.sub_im]
  have hre1 : (z - ((ξ : ℂ) - 1 / α)).re = x - ξ + (1 / α).re := by
    rw [hxdef]; simp [Complex.sub_re]; ring
  have hb1 : -|y + (1 / α).im| < x - ξ + (1 / α).re := by rw [him1, hre1] at hw1; exact hw1
  have hb2 : x + ξ < |y| := by
    have h1 : (z - (-(ξ : ℂ))).re = x + ξ := by rw [hxdef]; simp
    have h2 : (z - (-(ξ : ℂ))).im = y := by rw [hydef]; simp
    rw [h1, h2] at hw2; exact hw2
  set c : ℝ := ‖(1 / α : ℂ)‖ with hcdef
  have hcnonneg : 0 ≤ c := by rw [hcdef]; positivity
  have hcre : (1 / α).re ≤ c := by rw [hcdef]; exact Complex.re_le_norm _
  have hcim : |(1 / α).im| ≤ c := by rw [hcdef]; exact Complex.abs_im_le_norm _
  have hcval : c = 1 / ‖α‖ := by rw [hcdef, Complex.norm_div, norm_one, one_div]
  have himc : |α.im| * c ≤ 1 := by
    have h1 : |α.im| ≤ ‖α‖ := Complex.abs_im_le_norm α
    have h2 : 0 < ‖α‖ := norm_pos_iff.mpr hαne
    rw [hcval, mul_one_div, div_le_iff₀ h2]; simpa using h1
  have hyabs : |y| = -y := abs_of_neg hy
  have hlow : y - 2 * c < x := by
    have h3 : |y + (1 / α).im| ≤ -y + c := by
      calc |y + (1 / α).im| ≤ |y| + |(1 / α).im| := abs_add_le _ _
        _ = -y + |(1 / α).im| := by rw [hyabs]
        _ ≤ -y + c := by linarith
    linarith [hb1, h3, hcre, hξ]
  have hhigh : x < -y := by linarith [hb2, hξ, hyabs]
  have hxabs : |x| ≤ -y + 2 * c := by
    rw [abs_le]
    exact ⟨by linarith [hhigh, hyabs, hcnonneg], by linarith [hlow, hyabs]⟩
  have hEre : (-(2 * Real.pi * I * α * z)).re = 2 * Real.pi * (α.re * y + α.im * x) := by
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, hxdef, hydef]
    ring
  have hexp_le : α.re * y + α.im * x ≤ lam * y + 2 := by
    have h1 : α.im * x ≤ |α.im| * |x| := by
      have hh := le_abs_self (α.im * x)
      rwa [abs_mul] at hh
    have h2 : |α.im| * |x| ≤ |α.im| * (-y + 2 * c) :=
      mul_le_mul_of_nonneg_left hxabs (abs_nonneg _)
    have h3 : |α.im| * (-y + 2 * c) ≤ -(|α.im| * y) + 2 := by
      have h4 : |α.im| * c ≤ 1 := himc
      nlinarith [abs_nonneg α.im]
    rw [hlamdef]
    nlinarith [h1, h2, h3]
  have hEnorm : ‖Complex.exp (-(2 * Real.pi * I * α * z))‖
      ≤ Real.exp (4 * Real.pi) * Real.exp ((2 * Real.pi * lam) * y) := by
    rw [Complex.norm_exp, hEre, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [hexp_le, Real.pi_pos]
  have hBpos : 0 < 2 * Real.pi * lam := mul_pos (by positivity) hlampos
  have hyY : y < -((Real.log 2 + 4 * Real.pi) / (2 * Real.pi * lam)) := by rw [hydef]; exact hY
  have hexp2 : Real.exp (4 * Real.pi) * Real.exp ((2 * Real.pi * lam) * y) < 1 / 2 := by
    have hmul : (2 * Real.pi * lam) * y < -(Real.log 2 + 4 * Real.pi) := by
      have h := mul_lt_mul_of_pos_left hyY hBpos
      rwa [mul_neg, mul_div_cancel₀ _ (ne_of_gt hBpos)] at h
    calc Real.exp (4 * Real.pi) * Real.exp ((2 * Real.pi * lam) * y)
        = Real.exp (4 * Real.pi + (2 * Real.pi * lam) * y) := (Real.exp_add _ _).symm
      _ < Real.exp (-(Real.log 2)) := by
          apply Real.exp_lt_exp.mpr; linarith
      _ = 1 / 2 := by
          rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]; norm_num
  have hEsmall : ‖Complex.exp (-(2 * Real.pi * I * α * z))‖ < 1 / 2 := by linarith [hEnorm, hexp2]
  have hnorm1E : 1 / 2 ≤ ‖(1 : ℂ) - Complex.exp (-(2 * Real.pi * I * α * z))‖ := by
    have h2 : |‖(1 : ℂ)‖ - ‖Complex.exp (-(2 * Real.pi * I * α * z))‖|
        ≤ ‖(1 : ℂ) - Complex.exp (-(2 * Real.pi * I * α * z))‖ := abs_norm_sub_norm_le _ _
    rw [norm_one] at h2
    have h3 : |1 - ‖Complex.exp (-(2 * Real.pi * I * α * z))‖|
        = 1 - ‖Complex.exp (-(2 * Real.pi * I * α * z))‖ :=
      abs_of_nonneg (by linarith [hEsmall])
    rw [h3] at h2
    linarith [hEsmall]
  have hE1ne : (1 : ℂ) - Complex.exp (-(2 * Real.pi * I * α * z)) ≠ 0 := by
    intro h
    have h1 : ‖(1 : ℂ) - Complex.exp (-(2 * Real.pi * I * α * z))‖ = 0 := by rw [h, norm_zero]
    linarith [hnorm1E]
  have hτeq : Work.Pert.tauC σ α z - σ
      = σ * Complex.exp (-(2 * Real.pi * I * α * z))
          / (1 - Complex.exp (-(2 * Real.pi * I * α * z))) := by
    rw [Work.Pert.tauC]
    field_simp
    ring
  calc ‖Work.Pert.tauC σ α z - σ‖
      = ‖σ‖ * ‖Complex.exp (-(2 * Real.pi * I * α * z))‖
          / ‖(1 : ℂ) - Complex.exp (-(2 * Real.pi * I * α * z))‖ := by
        rw [hτeq, norm_div, norm_mul]
    _ ≤ ‖σ‖ * ‖Complex.exp (-(2 * Real.pi * I * α * z))‖ / (1 / 2) :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) hnorm1E
    _ = 2 * ‖σ‖ * ‖Complex.exp (-(2 * Real.pi * I * α * z))‖ := by ring
    _ ≤ 2 * ‖σ‖ * (Real.exp (4 * Real.pi) * Real.exp ((2 * Real.pi * lam) * y)) :=
        mul_le_mul_of_nonneg_left hEnorm (by positivity)
    _ = (2 * ‖σ‖ * Real.exp (4 * Real.pi)) * Real.exp ((2 * Real.pi * lam) * y) := by ring
    _ ≤ (2 * ‖σ‖ * Real.exp (4 * Real.pi) + 1) * Real.exp ((2 * Real.pi * lam) * y) :=
        mul_le_mul_of_nonneg_right (by linarith) (le_of_lt (Real.exp_pos _))

/-- The numerical core of the lower end: with `x = 2πiα` and `P = 1 + σ u σ` one has
`P · e^x = 1 + ζ` with `ζ = -(e^x - 1)^2 + e^x σ (u σ - u 0)` and `‖ζ‖ ≤ ‖x‖/48`, whence
`‖ρ - 1‖ = ‖log (1+ζ)/x‖ ≤ 1/32` for `ρ = -log P/x`. -/
theorem liftF_lower_rho_close_aux {u : ℂ → ℂ} {σ α : ℂ} {r C : ℝ}
    (hr : 0 < r) (hC : 0 ≤ C)
    (hu2 : ∀ z ∈ Metric.ball 0 r, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (huL : ∀ z ∈ Metric.ball 0 r, ∀ w ∈ Metric.ball 0 r, ‖u z - u w‖ ≤ C * ‖z - w‖)
    (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hσr : ‖σ‖ < r) (hαne : α ≠ 0)
    (hsmall : (2 * Real.pi + 32 * C) * ‖α‖ ≤ 1 / 128) :
    ‖-Complex.log (1 + σ * u σ) / (2 * Real.pi * Complex.I * α) - 1‖ ≤ 1 / 32 := by
  set x : ℂ := 2 * Real.pi * Complex.I * α with hxdef
  set e1 : ℂ := Complex.exp x with he1def
  set t : ℝ := ‖x‖ with htdef
  have ht0 : 0 ≤ t := by rw [htdef]; positivity
  have hxnorm : t = 2 * Real.pi * ‖α‖ := by
    rw [htdef, hxdef]
    simp [Complex.norm_I, Real.norm_of_nonneg Real.pi_pos.le]
  have htpos : 0 < t := by
    rw [hxnorm]; exact mul_pos (mul_pos (by norm_num) Real.pi_pos) (norm_pos_iff.mpr hαne)
  have ht128 : t ≤ 1 / 128 := by
    rw [hxnorm]; nlinarith [hsmall, Real.pi_pos, norm_nonneg α]
  have ht1 : t ≤ 1 := by linarith
  have hCt : C * t ≤ 1 / 512 := by
    rw [hxnorm]; nlinarith [hsmall, Real.pi_pos, Real.pi_lt_four, norm_nonneg α, hC]
  have hxne : x ≠ 0 := by
    rw [hxdef]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero) hαne
  have h0mem : (0 : ℂ) ∈ Metric.ball 0 r := by rw [Metric.mem_ball, dist_self]; exact hr
  have hu0a : 1 / 2 ≤ ‖u 0‖ := (hu2 0 h0mem).1
  have hσu0 : σ * u 0 = 1 - e1 := by linear_combination (-1 : ℂ) * hnorm
  have he1b : ‖e1 - 1‖ ≤ t + t ^ 2 := by
    have h := Complex.norm_exp_sub_one_sub_id_le (x := x) ht1
    have h4 : ‖Complex.exp x - 1 - x‖ ≤ t ^ 2 := by rw [htdef]; exact h
    have h2 : ‖e1 - 1‖ ≤ ‖e1 - 1 - x‖ + ‖x‖ := by
      calc ‖e1 - 1‖ = ‖(e1 - 1 - x) + x‖ := by ring_nf
        _ ≤ ‖e1 - 1 - x‖ + ‖x‖ := norm_add_le _ _
    rw [he1def, ← htdef] at h2
    linarith
  have h1e1 : ‖1 - e1‖ ≤ t + t ^ 2 := by
    rw [show (1 : ℂ) - e1 = -(e1 - 1) by ring, norm_neg]; exact he1b
  have hσu0n : ‖σ‖ * ‖u 0‖ = ‖1 - e1‖ := by rw [← hσu0, norm_mul]
  have hσbound : ‖σ‖ ≤ 2 * (t + t ^ 2) := by nlinarith [hσu0n, hu0a, h1e1, norm_nonneg σ]
  have hσmem : σ ∈ Metric.ball 0 r := by rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hσr
  have hσd : ‖u σ - u 0‖ ≤ C * ‖σ‖ := by
    have h := huL σ hσmem 0 h0mem
    simpa using h
  have hζal : e1 * (1 + σ * u σ) - 1 = -(e1 - 1) ^ 2 + e1 * (σ * (u σ - u 0)) := by
    linear_combination e1 * hσu0
  have hdec : 1 + σ * u σ = (2 - e1) + σ * (u σ - u 0) := by linear_combination hσu0
  have hexp : Real.exp t ≤ 33 / 32 := by
    have h := Real.exp_bound' ht0 ht1 (n := 2) (by norm_num)
    have h2 : (∑ m ∈ Finset.range 2, t ^ m / (m.factorial : ℝ)) = 1 + t := by
      simp [Finset.sum_range_succ]
    rw [h2] at h
    nlinarith [h, ht128, ht0]
  have hsqt : t * t ≤ (1 / 128) * t := by nlinarith [ht128, ht0]
  have hCt2 : C * (t * t) ≤ (1 / 512) * t := by nlinarith [hCt, ht0]
  have he1re : 0 < e1.re := by
    rw [he1def, Complex.exp_re]
    refine mul_pos (Real.exp_pos _) ?_
    apply Real.cos_pos_of_mem_Ioo
    have h := Complex.abs_im_le_norm x
    rw [abs_le, ← htdef] at h
    constructor <;> linarith [h.1, h.2, ht128, Real.pi_gt_three]
  have hPre : 0 < (1 + σ * u σ).re := by
    have h1 : e1.re ≤ Real.exp t := by
      calc e1.re ≤ ‖e1‖ := Complex.re_le_norm e1
        _ ≤ Real.exp t := by rw [he1def]; simpa [← htdef] using Complex.norm_exp_le_exp_norm x
    have hbb : (2 * (t + t ^ 2)) ^ 2 ≤ (33 / 16 * t) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by nlinarith [hσbound, ht128, ht0]) 2
    have hbb2 : C * (2 * (t + t ^ 2)) ^ 2 ≤ 1 / 8 := by
      have h2 : C * (2 * (t + t ^ 2))^2 ≤ C * (33/16 * t)^2 := mul_le_mul_of_nonneg_left hbb hC
      have h3 : C * (33/16 * t)^2 = (33/16)^2 * (C * (t*t)) := by ring
      nlinarith [h2, h3, hCt2]
    have h4 : ‖σ * (u σ - u 0)‖ ≤ 1 / 8 := by
      rw [norm_mul]
      have h5 : ‖σ‖ * ‖u σ - u 0‖ ≤ ‖σ‖ * (C * ‖σ‖) := mul_le_mul_of_nonneg_left hσd (norm_nonneg _)
      have h6 : ‖σ‖ * (C * ‖σ‖) = C * ‖σ‖^2 := by ring
      have h7 : ‖σ‖^2 ≤ (2 * (t + t^2))^2 := pow_le_pow_left₀ (norm_nonneg σ) hσbound 2
      have h8 : C * ‖σ‖^2 ≤ C * (2 * (t + t^2))^2 := mul_le_mul_of_nonneg_left h7 hC
      linarith
    have h7 : -‖σ * (u σ - u 0)‖ ≤ (σ * (u σ - u 0)).re := by
      have h := Complex.abs_re_le_norm (σ * (u σ - u 0))
      rw [abs_le] at h; linarith [h.2]
    rw [hdec, Complex.add_re, Complex.sub_re]
    have h8 : (2 : ℂ).re = 2 := rfl
    rw [h8]
    linarith [h1, h7, h4, hexp]
  have hPne : (1 + σ * u σ) ≠ 0 := by
    intro h; rw [h] at hPre; simp at hPre
  have harg : (1 + σ * u σ).arg + e1.arg ∈ Set.Ioc (-Real.pi) Real.pi := by
    have h1 : |(1 + σ * u σ).arg| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hPre)
    have h2 : |e1.arg| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl he1re)
    obtain ⟨a1, a2⟩ := abs_lt.mp h1
    obtain ⟨b1, b2⟩ := abs_lt.mp h2
    exact ⟨by linarith, by linarith⟩
  have hloge1 : Complex.log e1 = x := by
    rw [he1def]
    apply Complex.log_exp
    · have h := Complex.abs_im_le_norm x
      rw [abs_le, ← htdef] at h
      linarith [h.2, ht128, Real.pi_gt_three]
    · have h := Complex.abs_im_le_norm x
      rw [abs_le, ← htdef] at h
      linarith [h.1, ht128, Real.pi_gt_three]
  have hlogmul : Complex.log ((1 + σ * u σ) * e1)
      = Complex.log (1 + σ * u σ) + Complex.log e1 :=
    Complex.log_mul hPne (Complex.exp_ne_zero x) harg
  have hlogP : Complex.log (1 + σ * u σ) + x
      = Complex.log (1 + (e1 * (1 + σ * u σ) - 1)) := by
    rw [← hloge1, ← hlogmul]
    congr 1
    ring
  have hρeq : -Complex.log (1 + σ * u σ) / x - 1
      = -(Complex.log (1 + (e1 * (1 + σ * u σ) - 1)) / x) := by
    rw [← hlogP]
    field_simp
    ring
  have he1n : ‖e1‖ ≤ Real.exp t := by
    rw [he1def]; simpa [← htdef] using Complex.norm_exp_le_exp_norm x
  have hσsq : ‖σ‖^2 ≤ (2 * (t + t^2))^2 := pow_le_pow_left₀ (norm_nonneg σ) hσbound 2
  have hsdn : ‖σ * (u σ - u 0)‖ ≤ C * (2 * (t + t^2))^2 := by
    rw [norm_mul]
    calc ‖σ‖ * ‖u σ - u 0‖ ≤ ‖σ‖ * (C * ‖σ‖) := mul_le_mul_of_nonneg_left hσd (norm_nonneg _)
      _ = C * ‖σ‖^2 := by ring
      _ ≤ C * (2 * (t + t^2))^2 := mul_le_mul_of_nonneg_left hσsq hC
  have h2 : ‖e1 * (σ * (u σ - u 0))‖ ≤ Real.exp t * C * (2 * (t + t ^ 2)) ^ 2 := by
    calc ‖e1 * (σ * (u σ - u 0))‖ = ‖e1‖ * ‖σ * (u σ - u 0)‖ := norm_mul _ _
      _ ≤ Real.exp t * (C * (2 * (t + t^2))^2) :=
          mul_le_mul he1n hsdn (norm_nonneg _) (Real.exp_pos t).le
      _ = Real.exp t * C * (2 * (t + t^2))^2 := by ring
  have h1 : ‖(e1 - 1) ^ 2‖ ≤ (t + t ^ 2) ^ 2 := by
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) he1b 2
  have hζb : ‖e1 * (1 + σ * u σ) - 1‖
      ≤ (t + t ^ 2) ^ 2 + Real.exp t * C * (2 * (t + t ^ 2)) ^ 2 := by
    rw [hζal]
    calc ‖-(e1 - 1) ^ 2 + e1 * (σ * (u σ - u 0))‖
        ≤ ‖-(e1 - 1) ^ 2‖ + ‖e1 * (σ * (u σ - u 0))‖ := norm_add_le _ _
      _ = ‖(e1 - 1) ^ 2‖ + ‖e1 * (σ * (u σ - u 0))‖ := by rw [norm_neg]
      _ ≤ (t + t ^ 2) ^ 2 + Real.exp t * C * (2 * (t + t ^ 2)) ^ 2 := add_le_add h1 h2
  have hζ48 : ‖e1 * (1 + σ * u σ) - 1‖ ≤ t / 48 := by
    have hb1 : (t + t ^ 2) ^ 2 ≤ t / 112 := by nlinarith [hsqt, ht128, ht0]
    have hb2 : Real.exp t * C * (2 * (t + t ^ 2)) ^ 2 ≤ t / 112 := by
      have hbb : (2 * (t + t ^ 2)) ^ 2 ≤ (33 / 16 * t) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by nlinarith [ht128, ht0]) 2
      have hCbb : C * (2 * (t + t ^ 2)) ^ 2 ≤ (33/16)^2 * (1/512) * t := by
        have h2 : C * (2 * (t + t ^ 2))^2 ≤ C * (33/16 * t)^2 := mul_le_mul_of_nonneg_left hbb hC
        have h3 : C * (33/16 * t)^2 = (33/16)^2 * (C * (t*t)) := by ring
        rw [h3] at h2
        exact h2.trans (by nlinarith [hCt2])
      have h4 : Real.exp t * C * (2 * (t + t ^ 2))^2 ≤ (33/32) * (C * (2 * (t + t^2))^2) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right hexp (by positivity)
      nlinarith [h4, hCbb]
    linarith [hζb, hb1, hb2]
  have hζhalf : ‖e1 * (1 + σ * u σ) - 1‖ ≤ 1 / 2 := by linarith [hζ48, ht128, ht0]
  calc ‖-Complex.log (1 + σ * u σ) / x - 1‖
      = ‖Complex.log (1 + (e1 * (1 + σ * u σ) - 1)) / x‖ := by rw [hρeq, norm_neg]
    _ = ‖Complex.log (1 + (e1 * (1 + σ * u σ) - 1))‖ / ‖x‖ := norm_div _ _
    _ ≤ (3 / 2 * ‖e1 * (1 + σ * u σ) - 1‖) / t := by
        rw [← htdef]
        exact div_le_div_of_nonneg_right (Complex.norm_log_one_add_half_le_self hζhalf) (norm_nonneg x)
    _ ≤ (3 / 2 * (t / 48)) / t := by
        apply div_le_div_of_nonneg_right _ (le_of_lt htpos)
        linarith
    _ = 1 / 32 := by field_simp; norm_num


theorem liftF_lower_translation {u : ℂ → ℂ} {σ α : ℂ} {r C ξ : ℝ}
    (hξ : 0 < ξ) (hα : MandelDim.InF1 α) (hσ : σ ≠ 0) (hr : 0 < r) (hC : 0 ≤ C)
    (hu : DifferentiableOn ℂ u (Metric.ball 0 r))
    (hu2 : ∀ z ∈ Metric.ball 0 r, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (huL : ∀ z ∈ Metric.ball 0 r, ∀ w ∈ Metric.ball 0 r, ‖u z - u w‖ ≤ C * ‖z - w‖)
    (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hσr : ‖σ‖ < r) (hαξ : ‖α‖ * ξ ≤ 1)
    (hsmall : (2 * Real.pi + 32 * C) * ‖α‖ ≤ 1 / 128) :
    ∃ M κ Y : ℝ, 0 < M ∧ 0 < κ ∧
      ‖-Complex.log (1 + σ * u σ) / (2 * Real.pi * Complex.I * α) - 1‖ ≤ 1 / 32 ∧
      ∀ z ∈ Work.Pert.Qm ξ α, z.im < -Y →
        ‖Work.Pert.liftF u σ α z - (z + (-Complex.log (1 + σ * u σ) / (2 * Real.pi * Complex.I * α)))‖
          ≤ M * Real.exp (κ * z.im) := by
  have hαre : 0 < α.re := by
    have h : |α.im| < α.re := hα
    linarith [abs_nonneg α.im]
  have hαne : α ≠ 0 := by intro h; rw [h] at hαre; simp at hαre
  have hρ := liftF_lower_rho_close_aux hr hC hu2 huL hnorm hσr hαne hsmall
  obtain ⟨hPre, hPne, ε, K₀, hεpos, hK₀pos, hεr, hzeta⟩ :=
    liftF_lower_zeta_bound hr hC hu2 huL hnorm hσr hαne hsmall
  obtain ⟨M₁, κ, Y₁, hM₁, hκpos, hdec⟩ := tauC_lower_decay (σ := σ) hξ hα
  set ε' : ℝ := min ε (1 / (2 * K₀)) with hε'def
  have hε'pos : 0 < ε' := lt_min hεpos (by positivity)
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hε'K : K₀ * ε' ≤ 1 / 2 := by
    have h := min_le_right ε (1 / (2 * K₀))
    calc K₀ * ε' ≤ K₀ * (1 / (2 * K₀)) := mul_le_mul_of_nonneg_left h (le_of_lt hK₀pos)
      _ = 1 / 2 := by field_simp
  set Kf : ℝ := 3 / 2 * K₀ / (2 * Real.pi * ‖α‖) with hKfdef
  have hKfpos : 0 < Kf := by
    rw [hKfdef]
    exact div_pos (mul_pos (by norm_num) hK₀pos) (mul_pos (by positivity) (norm_pos_iff.mpr hαne))
  refine ⟨Kf * M₁, κ, max Y₁ (max 0 (-(Real.log (ε' / (2 * M₁)) / κ))),
    mul_pos hKfpos hM₁, hκpos, hρ, ?_⟩
  intro z hz hY
  have hY1 : z.im < -Y₁ := by
    have hle : Y₁ ≤ max Y₁ (max 0 (-(Real.log (ε' / (2 * M₁)) / κ))) := le_max_left _ _
    linarith
  have hzY : z.im < Real.log (ε' / (2 * M₁)) / κ := by
    have h1 : -(Real.log (ε' / (2 * M₁)) / κ)
        ≤ max Y₁ (max 0 (-(Real.log (ε' / (2 * M₁)) / κ))) :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    linarith
  have hzsmall : Real.exp (κ * z.im) ≤ ε' / (2 * M₁) := by
    have h3 : κ * z.im < Real.log (ε' / (2 * M₁)) := by
      have h := mul_lt_mul_of_pos_left hzY hκpos
      rwa [mul_div_cancel₀ _ (ne_of_gt hκpos)] at h
    calc Real.exp (κ * z.im) ≤ Real.exp (Real.log (ε' / (2 * M₁))) :=
          le_of_lt (Real.exp_lt_exp.mpr h3)
      _ = ε' / (2 * M₁) := Real.exp_log (by positivity)
  have hT1 : ‖Work.Pert.tauC σ α z - σ‖ ≤ ε' := by
    have h1 := hdec z hz hY1
    have h2 : M₁ * Real.exp (κ * z.im) ≤ ε' / 2 := by
      calc M₁ * Real.exp (κ * z.im) ≤ M₁ * (ε' / (2 * M₁)) :=
            mul_le_mul_of_nonneg_left hzsmall (le_of_lt hM₁)
        _ = ε' / 2 := by field_simp
    linarith
  have hT : ‖Work.Pert.tauC σ α z - σ‖ ≤ ε := le_trans hT1 hε'ε
  obtain ⟨hAsre, hAne, hζ⟩ := hzeta z hT
  have hζ2 : ‖(1 - Work.Pert.sfun u σ α z) * (1 + σ * u σ) - 1‖ ≤ 1 / 2 := by
    have h1 : K₀ * ‖Work.Pert.tauC σ α z - σ‖ ≤ K₀ * ε' :=
      mul_le_mul_of_nonneg_left hT1 (le_of_lt hK₀pos)
    linarith [hζ, h1, hε'K]
  have hxne : 2 * Real.pi * Complex.I * α ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero) hαne
  have hlog := log_mul_re_pos_bound (A := 1 - Work.Pert.sfun u σ α z) (B := 1 + σ * u σ)
    (ζ := (1 - Work.Pert.sfun u σ α z) * (1 + σ * u σ) - 1) (x := 2 * Real.pi * Complex.I * α)
    hAsre hPre hxne (by ring) hζ2
  have hxnorm : ‖2 * Real.pi * Complex.I * α‖ = 2 * Real.pi * ‖α‖ := by
    simp [Complex.norm_I, Real.norm_of_nonneg Real.pi_pos.le]
  have hstep : 3 / 2 * ‖(1 - Work.Pert.sfun u σ α z) * (1 + σ * u σ) - 1‖
      / ‖2 * Real.pi * Complex.I * α‖ ≤ Kf * ‖Work.Pert.tauC σ α z - σ‖ := by
    rw [hxnorm, hKfdef]
    have h1 : 3 / 2 * ‖(1 - Work.Pert.sfun u σ α z) * (1 + σ * u σ) - 1‖
        ≤ 3 / 2 * (K₀ * ‖Work.Pert.tauC σ α z - σ‖) := by linarith [hζ]
    have h2 : 0 < 2 * Real.pi * ‖α‖ :=
      mul_pos (mul_pos (by norm_num) Real.pi_pos) (norm_pos_iff.mpr hαne)
    calc 3 / 2 * ‖(1 - Work.Pert.sfun u σ α z) * (1 + σ * u σ) - 1‖ / (2 * Real.pi * ‖α‖)
        ≤ (3 / 2 * (K₀ * ‖Work.Pert.tauC σ α z - σ‖)) / (2 * Real.pi * ‖α‖) :=
          div_le_div_of_nonneg_right h1 (le_of_lt h2)
      _ = 3 / 2 * K₀ / (2 * Real.pi * ‖α‖) * ‖Work.Pert.tauC σ α z - σ‖ := by ring
  have hsplit : Work.Pert.liftF u σ α z
      - (z + (-Complex.log (1 + σ * u σ) / (2 * Real.pi * Complex.I * α)))
      = (Complex.log (1 - Work.Pert.sfun u σ α z) + Complex.log (1 + σ * u σ))
          / (2 * Real.pi * Complex.I * α) := by
    rw [Work.Pert.liftF, add_div]
    ring
  calc ‖Work.Pert.liftF u σ α z
        - (z + (-Complex.log (1 + σ * u σ) / (2 * Real.pi * Complex.I * α)))‖
      = ‖(Complex.log (1 - Work.Pert.sfun u σ α z) + Complex.log (1 + σ * u σ))
          / (2 * Real.pi * Complex.I * α)‖ := by rw [hsplit]
    _ ≤ 3 / 2 * ‖(1 - Work.Pert.sfun u σ α z) * (1 + σ * u σ) - 1‖
        / ‖2 * Real.pi * Complex.I * α‖ := hlog
    _ ≤ Kf * ‖Work.Pert.tauC σ α z - σ‖ := hstep
    _ ≤ Kf * (M₁ * Real.exp (κ * z.im)) :=
        mul_le_mul_of_nonneg_left (hdec z hz hY1) (le_of_lt hKfpos)
    _ = Kf * M₁ * Real.exp (κ * z.im) := by ring

end

end Work.Pert
