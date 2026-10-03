import Mathlib
import Submission.Work.Pert.EndDefect
import Submission.Work.Pert.norm_log_sub_log_le
import Submission.Work.Pert.norm_inv_u_sub_sigma_le
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup
import Submission.Work.Pert.u_lipschitz_halfball_le
import Submission.Work.Pert.log_close_one_le

/-!
# PERT · `Work.Pert.defect_sub_endDefect_le`

The defect `d(w) = liftF u σ α w - (w+1)` of the lifted perturbed Fatou coordinate differs from
its lower-end value `endDefect u σ α = (1/(2πiα)) log (1/(1+σ u σ)) - 1` by a term which is
Lipschitz in the displacement `δ = τ_f w - σ` of the coordinate `τ_f w = tauC σ α w`:

    ‖d(w) - endDefect u σ α‖ ≤ 2^11 (1 + 1/rr) ‖τ_f w - σ‖ .

## The argument (the constants are generous on purpose)

Write `A2 = 2πiα`, `τ = τ_f w`, `δ = τ - σ`, `Ω = 1 + σ u σ`, `Δ = 1 + τ u τ` and
`H = Ω (1 - sfun u σ α w)`.  The exact algebra (`liftF_sub_one_eq'`, `one_sub_sfun_eq'`,
`A_mul_one_sub_sfun_sub_one'`) gives

* `d(w) - D(σ) = (1/A2) (log (1 - sfun) - log (1/Ω)) = (1/A2) log H`;
* `H - 1 = (σ (u σ - u τ) + σ u σ u τ δ)/Δ`.

The hypothesis `hd` (`‖d(w)‖ ≤ 1/32`) says `log (1 - sfun) = A2 + ρ` with `‖ρ‖ ≤ ‖A2‖/32`, i.e.
`1 - sfun = exp (A2 + ρ)`; this gives `Δ = (1 + u τ δ) exp (-(A2 + ρ))`, hence `‖Δ‖ ≥ 4/9`.
Writing `s = sfun = 1 - exp (A2 + ρ)` one gets `‖s‖ ≤ 7.5 ‖α‖`, whence `‖σ u τ‖ = ‖s‖ ‖Δ‖` and
`‖σ‖ ≤ 26 ‖α‖` — this is the only place where the smallness of `α` enters: `hd` forces the second
fixed point `σ` to be `O(α)`.  Consequently `1/8 ≤ ‖Ω‖ ≤ 2`.

Finally `‖H - 1‖ ≤ 1000 ‖α‖ (1 + 1/rr) ‖δ‖`, and the logarithmic step is split:

* if `‖H - 1‖ ≤ 1/2` then `1/4 ≤ ‖H‖ ≤ 2` and the elementary estimate
  `Work.Pert.log_close_one_le` gives `‖log H‖ ≤ 2π 2^11 ‖α‖ (1+1/rr) ‖δ‖`;
* otherwise `‖δ‖ ≥ 1/(2000 ‖α‖ (1+1/rr))`, and since `log H = log Ω + (A2 + ρ)` with
  `‖log Ω‖ ≤ 3.7` one gets `‖log H‖ ≤ 3.81 ≤ 2π 2^11 ‖α‖(1+1/rr)‖δ‖` as well.
-/

set_option maxHeartbeats 1000000

namespace Work.Pert

open MandelDim Complex

noncomputable section

/-! ## Exact algebra of the defect (private, self-contained copies) -/

/-- The defect in terms of `sfun`: `d w = (1/(2πiα))·(log (1 - sfun) - 2πiα)`. -/
private theorem liftF_sub_one_eq' {u : ℂ → ℂ} {σ α w : ℂ} (hα : α ≠ 0) :
    liftF u σ α w - (w + 1)
      = (1 / (2 * Real.pi * Complex.I * α)) *
        (Complex.log (1 - sfun u σ α w) - 2 * Real.pi * Complex.I * α) := by
  have h2 : (2 * Real.pi * Complex.I * α) ≠ 0 := by
    simp [hα, Real.pi_ne_zero, Complex.I_ne_zero]
  unfold liftF
  field_simp
  ring

/-- `1 - sfun` as a rational function of `τ = tauC σ α w`. -/
private theorem one_sub_sfun_eq' {u : ℂ → ℂ} {σ α w : ℂ}
    (h : 1 + tauC σ α w * u (tauC σ α w) ≠ 0) :
    1 - sfun u σ α w
      = (1 + u (tauC σ α w) * (tauC σ α w - σ)) / (1 + tauC σ α w * u (tauC σ α w)) := by
  have h' : 1 + u (tauC σ α w) * tauC σ α w ≠ 0 := by simpa [mul_comm] using h
  unfold sfun
  rw [eq_div_iff h]
  field_simp
  ring

/-- `(1 + σ u σ)(1 - sfun) - 1` in terms of `τ - σ` and `1 + τ u τ`. -/
private theorem A_mul_one_sub_sfun_sub_one' {u : ℂ → ℂ} {σ α w : ℂ}
    (h : 1 + tauC σ α w * u (tauC σ α w) ≠ 0) :
    (1 + σ * u σ) * (1 - sfun u σ α w) - 1
      = (σ * (u σ - u (tauC σ α w))
          + σ * u σ * u (tauC σ α w) * (tauC σ α w - σ))
        / (1 + tauC σ α w * u (tauC σ α w)) := by
  have h' : 1 + u (tauC σ α w) * tauC σ α w ≠ 0 := by simpa [mul_comm] using h
  rw [one_sub_sfun_eq' h]
  field_simp
  ring

/-! ## Elementary real/complex estimates (small contexts) -/

/-- `‖exp z - 1‖ ≤ exp ‖z‖ - 1`. -/
private theorem norm_exp_sub_one_le_exp_norm_sub_one' (z : ℂ) :
    ‖Complex.exp z - 1‖ ≤ Real.exp ‖z‖ - 1 := by
  simpa using Complex.norm_exp_sub_sum_le_exp_norm_sub_sum z 1

/-- `exp x ≤ 1 + x + (3/4) x ^ 2` for `0 ≤ x ≤ 1`. -/
private theorem exp_le_one_add_add' (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Real.exp x ≤ 1 + x + (3 / 4) * x ^ 2 := by
  have h := Real.exp_bound' (x := x) h0 h1 (n := 2) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `exp t - 1 ≤ t * exp t` for `t ≥ 0`. -/
private theorem exp_sub_one_le_mul_exp (t : ℝ) :
    Real.exp t - 1 ≤ t * Real.exp t := by
  have h := Real.one_sub_le_exp_neg t
  have h2 : Real.exp t * (1 - t) ≤ 1 := by
    calc Real.exp t * (1 - t) ≤ Real.exp t * Real.exp (-t) :=
          mul_le_mul_of_nonneg_left h (le_of_lt (Real.exp_pos t))
      _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  nlinarith [h2, Real.exp_pos t]

/-- `2 π (1/64) ≤ 1/10`. -/
private lemma two_pi_div64_le : 2 * Real.pi * (1 / 64 : ℝ) ≤ 1 / 10 := by
  nlinarith [Real.pi_lt_d4, Real.pi_pos]

/-- `exp 0.104 ≤ 1.12`. -/
private lemma exp_104_le : Real.exp (0.104 : ℝ) ≤ 1.12 := by
  have h := exp_le_one_add_add' (0.104 : ℝ) (by norm_num) (by norm_num)
  nlinarith [h]

/-- `2 π (33/32) 1.12 ≤ 7.5`. -/
private lemma mul_33_le : 2 * Real.pi * (33 / 32 : ℝ) * 1.12 ≤ 7.5 := by
  nlinarith [Real.pi_lt_d4, Real.pi_pos]

/-- `3.81 / (2π) ≤ 2048/2000`. -/
private lemma arith_381 : (3.81 : ℝ) / (2 * Real.pi) ≤ 2048 / 2000 := by
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [Real.pi_pos, Real.pi_gt_three]

/-- `16/rr + 4 ≤ 16 (1 + 1/rr)` for `rr > 0`. -/
private lemma sixteen_div_add_four {rr : ℝ} : 16 / rr + 4 ≤ 16 * (1 + 1 / rr) := by
  rw [show 16 * (1 + 1 / rr) = 16 + 16 * (1 / rr) from by ring,
    show (16 : ℝ) / rr = 16 * (1 / rr) from by ring]
  linarith

/-- The size of `log z` for `1/8 ≤ ‖z‖ ≤ 2` and `|arg z| < π/2`. -/
private lemma log_norm_le_of_bounds {z : ℂ} (hlo : (1 : ℝ) / 8 ≤ ‖z‖) (hhi : ‖z‖ ≤ 2)
    (harg : |z.arg| < Real.pi / 2) : ‖Complex.log z‖ ≤ 3.7 := by
  have h1 : |(Complex.log z).re| ≤ 2.1 := by
    rw [Complex.log_re, abs_le]
    have hp : 0 < ‖z‖ := lt_of_lt_of_le (by norm_num) hlo
    constructor
    · have hlog8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
        have h8 : (8 : ℝ) = 2 ^ 3 := by norm_num
        rw [h8, Real.log_pow]; norm_num
      have hle : Real.log ((1 : ℝ) / 8) ≤ Real.log ‖z‖ :=
        Real.log_le_log (by norm_num) hlo
      rw [one_div, Real.log_inv, hlog8] at hle
      have := Real.log_two_lt_d9
      linarith
    · have hle := Real.log_le_log hp hhi
      have := Real.log_two_lt_d9
      linarith
  have h2 : |(Complex.log z).im| ≤ 1.58 := by
    rw [Complex.log_im, abs_le]
    rw [abs_lt] at harg
    have hpi := Real.pi_lt_d4
    constructor <;> linarith
  calc ‖Complex.log z‖ ≤ |(Complex.log z).re| + |(Complex.log z).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 2.1 + 1.58 := by linarith
    _ ≤ 3.7 := by norm_num

/-! ## The main estimate -/

theorem defect_sub_endDefect_le {rr : ℝ} {α σ : ℂ} {u : ℂ → ℂ} {w : ℂ}
    (hrr : 0 < rr) (hα64 : ‖α‖ ≤ 1 / 64) (hα : α ≠ 0)
    (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr))
    (hu2 : ∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (huσ : ‖σ‖ ≤ rr / 2)
    (hτ : Work.Pert.tauC σ α w ∈ Metric.ball (0 : ℂ) rr)
    (hd : ‖Work.Pert.liftF u σ α w - (w + 1)‖ ≤ 1 / 32)
    (hy : ‖Work.Pert.tauC σ α w - σ‖ ≤ 1 / 4)
    (hA : 0 < (1 + σ * u σ).re) :
    ‖Work.Pert.liftF u σ α w - (w + 1) - Work.Pert.endDefect u σ α‖
      ≤ 2 ^ 11 * (1 + 1 / rr) * ‖Work.Pert.tauC σ α w - σ‖ := by
  have hαpos : 0 < ‖α‖ := norm_pos_iff.mpr hα
  -- ## notation
  set A2 : ℂ := 2 * Real.pi * Complex.I * α with hA2def
  set τ : ℂ := tauC σ α w with hτabbr
  set δ : ℂ := τ - σ with hδabbr
  set Ω : ℂ := 1 + σ * u σ with hΩabbr
  set Δ : ℂ := 1 + τ * u τ with hΔabbr
  -- ## elementary facts about `A2`
  have hA2ne : A2 ≠ 0 := by
    rw [hA2def]
    simp [hα, Real.pi_ne_zero, Complex.I_ne_zero]
  have hA2norm : ‖A2‖ = 2 * Real.pi * ‖α‖ := by
    rw [hA2def, norm_mul, norm_mul, norm_mul]
    simp [Complex.norm_I, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hA2pos : 0 < ‖A2‖ := by
    rw [hA2norm]; exact mul_pos (by positivity) hαpos
  have hA2le : ‖A2‖ ≤ 1 / 10 := by
    rw [hA2norm]
    calc 2 * Real.pi * ‖α‖ = (2 * Real.pi) * ‖α‖ := by ring
      _ ≤ (2 * Real.pi) * (1 / 64) := mul_le_mul_of_nonneg_left hα64 (by positivity)
      _ ≤ 1 / 10 := two_pi_div64_le
  -- ## the level `τ` and its displacement
  have hτmem : τ ∈ Metric.ball (0 : ℂ) rr := hτ
  have hδle : ‖δ‖ ≤ 1 / 4 := hy
  have hσmem : σ ∈ Metric.ball (0 : ℂ) rr := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    linarith [huσ, hrr]
  have huτlo : 1 / 2 ≤ ‖u τ‖ := (hu2 τ hτmem).1
  have huτhi : ‖u τ‖ ≤ 2 := (hu2 τ hτmem).2
  have huσlo : 1 / 2 ≤ ‖u σ‖ := (hu2 σ hσmem).1
  have huσhi : ‖u σ‖ ≤ 2 := (hu2 σ hσmem).2
  -- the Lipschitz bound for `u` on the segment from `σ` to `τ` (delegated lemma)
  have hulip : ‖u τ - u σ‖ ≤ 16 / rr * ‖δ‖ := by
    simpa [hδabbr] using
      u_lipschitz_halfball_le hrr hu (fun z hz => (hu2 z hz).2) huσ hτmem hδle
  -- ## the denominator `Δ` is nonzero
  have hΔne : Δ ≠ 0 := by
    intro h0
    have hs0 : sfun u σ α w = 0 := by
      have h1 : sfun u σ α w = σ * u τ / Δ := rfl
      rw [h1, h0, div_zero]
    have hid := liftF_sub_one_eq' (u := u) (σ := σ) (α := α) (w := w) hα
    rw [hs0, sub_zero, Complex.log_one, ← hA2def] at hid
    have hval : (1 / A2) * (0 - A2) = -1 := by
      rw [zero_sub, mul_neg, one_div_mul_cancel hA2ne]
    rw [hid, hval, norm_neg, norm_one] at hd
    norm_num at hd
  -- ## `hd` as a statement about the principal logarithm
  have hρbound : ‖Complex.log (1 - sfun u σ α w) - A2‖ ≤ ‖A2‖ / 32 := by
    have h := hd
    rw [liftF_sub_one_eq' (u := u) (σ := σ) (α := α) (w := w) hα, ← hA2def] at h
    rw [norm_mul, norm_div, norm_one] at h
    rw [div_mul_eq_mul_div, one_mul] at h
    rw [div_le_iff₀ hA2pos, hA2norm] at h
    have h' : (1 / 32) * (2 * Real.pi * ‖α‖) = (2 * Real.pi * ‖α‖) / 32 := by ring
    linarith [h, h']
  have h1s_ne : 1 - sfun u σ α w ≠ 0 := by
    intro h0
    have h1 : ‖Complex.log (1 - sfun u σ α w) - A2‖ = ‖A2‖ := by
      rw [h0, Complex.log_zero, zero_sub, norm_neg]
    rw [h1] at hρbound
    linarith [hA2pos, hρbound]
  set ρ : ℂ := Complex.log (1 - sfun u σ α w) - A2 with hρdef
  have hρle : ‖ρ‖ ≤ ‖A2‖ / 32 := hρbound
  have hlog1s : Complex.log (1 - sfun u σ α w) = A2 + ρ := by
    rw [hρdef]; ring
  have hexp : Complex.exp (A2 + ρ) = 1 - sfun u σ α w := by
    rw [← hlog1s]
    exact Complex.exp_log h1s_ne
  have hzle : ‖A2 + ρ‖ ≤ 0.104 := by
    have h1 : ‖A2 + ρ‖ ≤ ‖A2‖ + ‖ρ‖ := norm_add_le _ _
    have h2 : ‖ρ‖ ≤ 1 / 320 := by
      have h := hρle
      rw [hA2norm] at h
      have h3 : 2 * Real.pi * ‖α‖ ≤ 2 * Real.pi * (1 / 64) :=
        mul_le_mul_of_nonneg_left hα64 (by positivity)
      linarith [h, h3, two_pi_div64_le]
    linarith [h1, h2, hA2le]
  have hexpz_le : Real.exp ‖A2 + ρ‖ ≤ 1.12 := by
    have h1 : Real.exp ‖A2 + ρ‖ ≤ Real.exp (0.104 : ℝ) := Real.exp_le_exp.mpr hzle
    exact le_trans h1 exp_104_le
  have hzre : |(A2 + ρ).re| ≤ ‖A2 + ρ‖ := Complex.abs_re_le_norm _
  have h1s_re : 0 < (1 - sfun u σ α w).re := by
    rw [← hexp, Complex.exp_re]
    have him : |(A2 + ρ).im| ≤ ‖A2 + ρ‖ := Complex.abs_im_le_norm _
    rw [abs_le] at him
    have hpi := Real.pi_gt_three
    have hcos : 0 < Real.cos (A2 + ρ).im := by
      refine Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩ <;> linarith [him.1, him.2, hzle, hpi]
    positivity
  -- ## facts about `Ω`
  have hΩne : Ω ≠ 0 := by
    intro h0
    rw [h0] at hA
    simp at hA
  have hΩarg : |Ω.arg| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hA)
  have hΩarg_ne : Ω.arg ≠ Real.pi := by
    intro hpi
    rw [hpi, abs_of_pos Real.pi_pos] at hΩarg
    linarith [Real.pi_pos, hΩarg]
  -- ## the `H` of the logarithmic step, and the two logarithmic identities
  set H : ℂ := Ω * (1 - sfun u σ α w) with hHabbr
  have hargcond : Ω.arg + (1 - sfun u σ α w).arg ∈ Set.Ioc (-Real.pi) Real.pi := by
    have h1 := hΩarg
    have h2 : |(1 - sfun u σ α w).arg| < Real.pi / 2 :=
      Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl h1s_re)
    rw [abs_lt] at h1 h2
    exact ⟨by linarith [h1.1, h2.1, Real.pi_pos],
      by linarith [h1.2, h2.2, Real.pi_pos]⟩
  have hlogH : Complex.log H = Complex.log Ω + (A2 + ρ) := by
    rw [hHabbr, Complex.log_mul hΩne h1s_ne hargcond, hlog1s]
  have hlogdiff : Complex.log (1 - sfun u σ α w) - Complex.log (1 / Ω) = Complex.log H := by
    have hinv : Complex.log (1 / Ω) = -Complex.log Ω := by
      rw [one_div, Complex.log_inv Ω hΩarg_ne]
    rw [hlog1s, hinv, hlogH]
    ring
  have hLHS : ‖liftF u σ α w - (w + 1) - endDefect u σ α‖ = ‖Complex.log H‖ / ‖A2‖ := by
    have heq : liftF u σ α w - (w + 1) - endDefect u σ α = (1 / A2) * Complex.log H := by
      rw [liftF_sub_one_eq' (u := u) (σ := σ) (α := α) (w := w) hα, ← hA2def]
      rw [endDefect, ← hΩabbr]
      have h1 : (1 / A2) * (Complex.log (1 - sfun u σ α w) - A2)
            - ((1 / A2) * Complex.log (1 / Ω) - 1)
          = (1 / A2) * (Complex.log (1 - sfun u σ α w) - Complex.log (1 / Ω)) := by
        field_simp
        ring
      rw [h1, hlogdiff]
    rw [heq, norm_mul, norm_div, norm_one]
    ring
  -- ## the size of `Δ`
  have hΔeq : Δ = (1 + u τ * δ) * Complex.exp (-(A2 + ρ)) := by
    have h1 : 1 - sfun u σ α w = (1 + u τ * δ) / Δ :=
      one_sub_sfun_eq' (u := u) (σ := σ) (α := α) (w := w) hΔne
    have h2 : Complex.exp (A2 + ρ) = (1 + u τ * δ) / Δ := by rw [hexp, h1]
    have h3 : Δ * Complex.exp (A2 + ρ) = 1 + u τ * δ := by
      rw [h2]
      field_simp
    rw [show Δ = (1 + u τ * δ) / Complex.exp (A2 + ρ) from by
        rw [eq_div_iff (Complex.exp_ne_zero _)]; exact h3]
    rw [div_eq_mul_inv, ← Complex.exp_neg]
  have huτδ_lo : 1 / 2 ≤ ‖1 + u τ * δ‖ := by
    have hx : ‖u τ * δ‖ ≤ 1 / 2 := by
      rw [norm_mul]
      nlinarith [huτhi, hδle, norm_nonneg (u τ)]
    have h := abs_norm_sub_norm_le (1 : ℂ) (-(u τ * δ))
    rw [norm_neg, norm_one, sub_neg_eq_add] at h
    have h' : (1 : ℝ) - ‖u τ * δ‖ ≤ |1 - ‖u τ * δ‖| := le_abs_self _
    linarith [h, h']
  have huτδ_hi : ‖1 + u τ * δ‖ ≤ 3 / 2 := by
    have hx : ‖u τ * δ‖ ≤ 1 / 2 := by
      rw [norm_mul]
      nlinarith [huτhi, hδle, norm_nonneg (u τ)]
    have h := norm_add_le (1 : ℂ) (u τ * δ)
    rw [norm_one] at h
    linarith [h, hx]
  have hΔ_ge : (4 / 9 : ℝ) ≤ ‖Δ‖ := by
    rw [hΔeq, norm_mul, Complex.norm_exp]
    have hre : -(‖A2 + ρ‖) ≤ (-(A2 + ρ)).re := by
      have h := Complex.abs_re_le_norm (A2 + ρ)
      rw [abs_le] at h
      simp only [Complex.neg_re]
      linarith [h.1]
    have h1 : (0.89 : ℝ) ≤ Real.exp (-(A2 + ρ)).re := by
      have h2 : Real.exp (-(‖A2 + ρ‖)) ≤ Real.exp (-(A2 + ρ)).re := Real.exp_le_exp.mpr hre
      have h3 : (1 : ℝ) - ‖A2 + ρ‖ ≤ Real.exp (-(‖A2 + ρ‖)) := Real.one_sub_le_exp_neg _
      linarith [h2, h3, hzle]
    have h4 : (1 / 2 : ℝ) * 0.89 ≤ ‖1 + u τ * δ‖ * Real.exp (-(A2 + ρ)).re :=
      mul_le_mul huτδ_lo h1 (by norm_num) (norm_nonneg _)
    linarith [h4, norm_nonneg (1 + u τ * δ)]
  have hΔ_le : ‖Δ‖ ≤ 17 / 10 := by
    rw [hΔeq, norm_mul, Complex.norm_exp]
    have hre : (-(A2 + ρ)).re ≤ ‖A2 + ρ‖ := by
      have h := Complex.abs_re_le_norm (A2 + ρ)
      rw [abs_le] at h
      simp only [Complex.neg_re]
      linarith [h.1]
    have h1 : Real.exp (-(A2 + ρ)).re ≤ 1.12 :=
      le_trans (Real.exp_le_exp.mpr hre) hexpz_le
    have h4 : ‖1 + u τ * δ‖ * Real.exp (-(A2 + ρ)).re ≤ (3 / 2) * 1.12 :=
      mul_le_mul huτδ_hi h1 (Real.exp_pos _).le (by norm_num)
    linarith [h4, norm_nonneg (1 + u τ * δ)]
  -- ## `σ` is of size `O(‖α‖)`
  have hs_eq : sfun u σ α w = 1 - Complex.exp (A2 + ρ) := by rw [hexp]; ring
  have hs_bound : ‖sfun u σ α w‖ ≤ 7.5 * ‖α‖ := by
    rw [hs_eq, norm_sub_rev]
    have h1 : ‖Complex.exp (A2 + ρ) - 1‖ ≤ Real.exp ‖A2 + ρ‖ - 1 :=
      norm_exp_sub_one_le_exp_norm_sub_one' _
    have h2 : Real.exp ‖A2 + ρ‖ - 1 ≤ ‖A2 + ρ‖ * 1.12 := by
      have h := exp_sub_one_le_mul_exp ‖A2 + ρ‖
      have h' : ‖A2 + ρ‖ * Real.exp ‖A2 + ρ‖ ≤ ‖A2 + ρ‖ * 1.12 :=
        mul_le_mul_of_nonneg_left hexpz_le (norm_nonneg _)
      linarith [h, h']
    have h3 : ‖A2 + ρ‖ ≤ 2 * Real.pi * ‖α‖ * (33 / 32) := by
      have h := norm_add_le A2 ρ
      have h4 : ‖A2‖ + ‖A2‖ / 32 = ‖A2‖ * (33 / 32) := by ring
      have h5 : ‖A2‖ + ‖ρ‖ ≤ ‖A2‖ * (33 / 32) := by linarith [hρle, h4]
      have h6 : ‖A2‖ * (33 / 32) = 2 * Real.pi * ‖α‖ * (33 / 32) := by rw [hA2norm]
      linarith [h, h5, h6]
    have h4 : 2 * Real.pi * ‖α‖ * (33 / 32) * 1.12 ≤ 7.5 * ‖α‖ := by
      rw [show 2 * Real.pi * ‖α‖ * (33 / 32) * 1.12
          = (2 * Real.pi * (33 / 32) * 1.12) * ‖α‖ from by ring]
      exact mul_le_mul_of_nonneg_right mul_33_le (norm_nonneg α)
    linarith [h1, h2, h3, h4]
  have hσuτ_bound : ‖σ * u τ‖ ≤ 7.5 * ‖α‖ * (17 / 10) := by
    have h1 : sfun u σ α w = σ * u τ / Δ := rfl
    have h2 : ‖σ * u τ‖ / ‖Δ‖ ≤ 7.5 * ‖α‖ := by
      have h := hs_bound
      rwa [h1, norm_div] at h
    have hΔpos : 0 < ‖Δ‖ := lt_of_lt_of_le (by norm_num) hΔ_ge
    rw [div_le_iff₀ hΔpos] at h2
    calc ‖σ * u τ‖ ≤ 7.5 * ‖α‖ * ‖Δ‖ := h2
      _ ≤ 7.5 * ‖α‖ * (17 / 10) := mul_le_mul_of_nonneg_left hΔ_le (by positivity)
  have hσ_bound : ‖σ‖ ≤ 26 * ‖α‖ := by
    have h1 : ‖σ‖ * ‖u τ‖ ≤ 7.5 * ‖α‖ * (17 / 10) := by
      rw [← norm_mul]; exact hσuτ_bound
    have h2 : ‖σ‖ * (1 / 2) ≤ ‖σ‖ * ‖u τ‖ :=
      mul_le_mul_of_nonneg_left huτlo (norm_nonneg σ)
    have h3 : (7.5 : ℝ) * ‖α‖ * (17 / 10) = 7.5 * (17 / 10) * ‖α‖ := by ring
    linarith [h1, h2, h3, norm_nonneg σ, hαpos]
  have hΩ_lo : (1 / 8 : ℝ) ≤ ‖Ω‖ := by
    have h1 : ‖Ω - 1‖ = ‖σ * u σ‖ := by
      congr 1
      rw [hΩabbr]; ring
    have h2 : ‖σ * u σ‖ ≤ 2 * ‖σ‖ := by
      rw [norm_mul]; nlinarith [huσhi, norm_nonneg σ]
    have h3 : ‖(1 : ℂ)‖ - ‖Ω‖ ≤ ‖(1 : ℂ) - Ω‖ := by
      have h := abs_norm_sub_norm_le (1 : ℂ) Ω
      rw [abs_le] at h
      linarith [h.1]
    rw [norm_one, norm_sub_rev, h1] at h3
    have h4 : 2 * ‖σ‖ ≤ 2 * (26 * ‖α‖) := mul_le_mul_of_nonneg_left hσ_bound (by norm_num)
    have h5 : 2 * (26 * (1 / 64 : ℝ)) ≤ 7 / 8 := by norm_num
    linarith [h3, h2, h4, h5, hα64]
  have hΩ_hi : ‖Ω‖ ≤ 2 := by
    have h1 : ‖Ω - 1‖ = ‖σ * u σ‖ := by
      congr 1
      rw [hΩabbr]; ring
    have h2 : ‖σ * u σ‖ ≤ 2 * ‖σ‖ := by
      rw [norm_mul]; nlinarith [huσhi, norm_nonneg σ]
    have h3 : ‖Ω‖ - ‖(1 : ℂ)‖ ≤ ‖Ω - 1‖ := by
      have h := abs_norm_sub_norm_le Ω (1 : ℂ)
      rw [abs_le] at h
      linarith [h.2]
    rw [norm_one, h1] at h3
    have h4 : 2 * ‖σ‖ ≤ 2 * (26 * ‖α‖) := mul_le_mul_of_nonneg_left hσ_bound (by norm_num)
    have h5 : 2 * (26 * (1 / 64 : ℝ)) ≤ 7 / 8 := by norm_num
    linarith [h3, h2, h4, h5, hα64]
  -- ## the size of `H - 1`
  have hH1 : ‖H - 1‖ ≤ 1000 * ‖α‖ * (1 + 1 / rr) * ‖δ‖ := by
    have halg := A_mul_one_sub_sfun_sub_one' (u := u) (σ := σ) (α := α) (w := w) hΔne
    have hHeq : H - 1 = (σ * (u σ - u τ) + σ * u σ * u τ * δ) / Δ := by
      rw [hHabbr]
      exact halg
    have hnum : ‖σ * (u σ - u τ) + σ * u σ * u τ * δ‖
        ≤ 26 * ‖α‖ * (16 / rr) * ‖δ‖ + 26 * ‖α‖ * 4 * ‖δ‖ := by
      have h1 : ‖σ * (u σ - u τ)‖ ≤ 26 * ‖α‖ * (16 / rr) * ‖δ‖ := by
        have h := hulip
        rw [norm_sub_rev] at h
        rw [norm_mul]
        calc ‖σ‖ * ‖u σ - u τ‖ ≤ (26 * ‖α‖) * (16 / rr * ‖δ‖) :=
              mul_le_mul hσ_bound h (norm_nonneg _) (by positivity)
          _ = 26 * ‖α‖ * (16 / rr) * ‖δ‖ := by ring
      have h2 : ‖σ * u σ * u τ * δ‖ ≤ 26 * ‖α‖ * 4 * ‖δ‖ := by
        rw [norm_mul, norm_mul, norm_mul]
        have h3 : ‖σ‖ * ‖u σ‖ ≤ (26 * ‖α‖) * 2 :=
          mul_le_mul hσ_bound huσhi (norm_nonneg _) (by positivity)
        have h4 : ‖u τ‖ * ‖δ‖ ≤ 2 * ‖δ‖ := mul_le_mul_of_nonneg_right huτhi (norm_nonneg δ)
        calc ‖σ‖ * ‖u σ‖ * ‖u τ‖ * ‖δ‖ = (‖σ‖ * ‖u σ‖) * (‖u τ‖ * ‖δ‖) := by ring
          _ ≤ ((26 * ‖α‖) * 2) * (2 * ‖δ‖) :=
              mul_le_mul h3 h4 (by positivity) (by positivity)
          _ = 26 * ‖α‖ * 4 * ‖δ‖ := by ring
      exact le_trans (norm_add_le _ _) (add_le_add h1 h2)
    have hΔpos : 0 < ‖Δ‖ := lt_of_lt_of_le (by norm_num) hΔ_ge
    have hkey : 26 * ‖α‖ * (16 / rr) * ‖δ‖ + 26 * ‖α‖ * 4 * ‖δ‖
        ≤ 1000 * ‖α‖ * (1 + 1 / rr) * ‖δ‖ * ‖Δ‖ := by
      have hk := sixteen_div_add_four (rr := rr)
      calc 26 * ‖α‖ * (16 / rr) * ‖δ‖ + 26 * ‖α‖ * 4 * ‖δ‖
          = 26 * ‖α‖ * ‖δ‖ * (16 / rr + 4) := by ring
        _ ≤ 26 * ‖α‖ * ‖δ‖ * (16 * (1 + 1 / rr)) :=
            mul_le_mul_of_nonneg_left hk (by positivity)
        _ = 416 * ‖α‖ * (1 + 1 / rr) * ‖δ‖ := by ring
        _ ≤ 1000 * ‖α‖ * (1 + 1 / rr) * ‖δ‖ * ‖Δ‖ := by
            have h1 : (416 : ℝ) ≤ 1000 * ‖Δ‖ := by
              linarith [hΔ_ge]
            have h2 : (0 : ℝ) ≤ ‖α‖ * (1 + 1 / rr) * ‖δ‖ := by positivity
            have h3 : 416 * ‖α‖ * (1 + 1 / rr) * ‖δ‖
                = 416 * (‖α‖ * (1 + 1 / rr) * ‖δ‖) := by ring
            have h4 : 1000 * ‖α‖ * (1 + 1 / rr) * ‖δ‖ * ‖Δ‖
                = (1000 * ‖Δ‖) * (‖α‖ * (1 + 1 / rr) * ‖δ‖) := by ring
            rw [h3, h4]
            exact mul_le_mul_of_nonneg_right h1 h2
    calc ‖H - 1‖ = ‖(σ * (u σ - u τ) + σ * u σ * u τ * δ) / Δ‖ := by rw [hHeq]
      _ = ‖σ * (u σ - u τ) + σ * u σ * u τ * δ‖ / ‖Δ‖ := norm_div _ _
      _ ≤ (26 * ‖α‖ * (16 / rr) * ‖δ‖ + 26 * ‖α‖ * 4 * ‖δ‖) / ‖Δ‖ :=
          div_le_div_of_nonneg_right hnum (le_of_lt hΔpos)
      _ ≤ 1000 * ‖α‖ * (1 + 1 / rr) * ‖δ‖ := by
          rw [div_le_iff₀ hΔpos]
          exact hkey
  -- ## the two logarithmic cases
  by_cases hcase : ‖H - 1‖ ≤ 1 / 2
  · have hHlo : 1 / 4 ≤ ‖H‖ := by
      have h := abs_norm_sub_norm_le H (1 : ℂ)
      rw [abs_le, norm_one] at h
      linarith [h.1, hcase]
    have hHhi : ‖H‖ ≤ 2 := by
      have h := abs_norm_sub_norm_le H (1 : ℂ)
      rw [abs_le, norm_one] at h
      linarith [h.2, hcase]
    have hchild : ‖Complex.log H‖ ≤ 2 * Real.pi * 2 ^ 11 * ‖α‖ * (1 + 1 / rr) * ‖δ‖ :=
      log_close_one_le (norm_nonneg α) (norm_nonneg δ) (by positivity) hHlo hHhi hH1
    rw [hLHS, hA2norm, div_le_iff₀ (by positivity)]
    have h'' : 2 * Real.pi * 2 ^ 11 * ‖α‖ * (1 + 1 / rr) * ‖δ‖
        = 2 ^ 11 * (1 + 1 / rr) * ‖δ‖ * (2 * Real.pi * ‖α‖) := by ring
    linarith [hchild, h'']
  · push_neg at hcase
    have hδge : 1 / (2000 * (‖α‖ * (1 + 1 / rr))) ≤ ‖δ‖ := by
      have hpos : 0 < 2000 * (‖α‖ * (1 + 1 / rr)) := by positivity
      rw [div_le_iff₀ hpos]
      have h : 1000 * ‖α‖ * (1 + 1 / rr) * ‖δ‖ = 1000 * (‖α‖ * (1 + 1 / rr)) * ‖δ‖ := by ring
      rw [h] at hH1
      nlinarith [hH1, hcase]
    have hlogΩ : ‖Complex.log Ω‖ ≤ 3.7 := log_norm_le_of_bounds hΩ_lo hΩ_hi hΩarg
    have hlogH_le : ‖Complex.log H‖ ≤ 3.81 := by
      rw [hlogH]
      have h1 := norm_add_le (Complex.log Ω) (A2 + ρ)
      linarith [h1, hlogΩ, hzle]
    rw [hLHS, hA2norm]
    have hstep1 : ‖Complex.log H‖ / (2 * Real.pi * ‖α‖) ≤ 3.81 / (2 * Real.pi * ‖α‖) :=
      div_le_div_of_nonneg_right hlogH_le (by positivity)
    have hR1 : 2 ^ 11 * (1 + 1 / rr) * (1 / (2000 * (‖α‖ * (1 + 1 / rr))))
        = 2048 / (2000 * ‖α‖) := by
      field_simp
      ring
    have htarget : 2 ^ 11 * (1 + 1 / rr) * ‖δ‖
        ≥ 2 ^ 11 * (1 + 1 / rr) * (1 / (2000 * (‖α‖ * (1 + 1 / rr)))) := by
      have hfac : (0 : ℝ) ≤ 2 ^ 11 * (1 + 1 / rr) := by positivity
      exact mul_le_mul_of_nonneg_left hδge hfac
    have hmid : (3.81 : ℝ) / (2 * Real.pi * ‖α‖) ≤ 2048 / (2000 * ‖α‖) := by
      rw [show (3.81 : ℝ) / (2 * Real.pi * ‖α‖) = (3.81 / (2 * Real.pi)) * (1 / ‖α‖) from by ring,
        show (2048 : ℝ) / (2000 * ‖α‖) = (2048 / 2000) * (1 / ‖α‖) from by ring]
      exact mul_le_mul_of_nonneg_right arith_381 (by positivity)
    linarith [hstep1, hmid, htarget, hR1]

end

end Work.Pert
