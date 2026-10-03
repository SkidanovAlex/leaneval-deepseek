import Mathlib
import Submission.Work.Pert.Basic

/-!
# The gate value bound `‖sfun w - σ u 0‖ ≤ ‖α‖/4`

`F_f w = w + log (1 - sfun w)/(2πi α)`, so the near-translation hypothesis
`‖F_f w - (w + 1)‖ ≤ 1/32` says exactly that

  `‖log (1 - sfun w) - 2πi α‖ ≤ 2π‖α‖/32 = π‖α‖/16`.

Writing `s = sfun u σ α w` and `c = log (1 - s)` we have `1 - s = exp c` (whence
`1 - s ≠ 0` automatically) and, with `1 - σ u 0 = exp (2πi α)`,

  `s - σ u 0 = exp (2πi α) - exp c = exp (2πi α) · (1 - exp (c - 2πi α))`.

Since `‖exp (2πi α)‖ ≤ exp ‖2πi α‖ = exp (2π‖α‖) ≤ exp (π/32)` and, for small `δ`,
`‖1 - exp δ‖ ≤ ‖δ‖ + ‖δ‖²`, this gives

  `‖s - σ u 0‖ ≤ exp (π/32) · (π‖α‖/16) · (1 + π/1024) ≤ ‖α‖/4`,

the last step being the elementary constant bound
`(π/16)(1 + π/1024) exp (π/32) ≤ 1/4`.  The hypotheses `‖α‖ ≤ 1/64` and the constant
`1/32` in the near-translation are exactly what make this hold.
-/

namespace Work.Pert.TauCGate

/-- The numerical constant behind the gate estimate:
`(π/16)·(1 + π/1024)·exp (π/32) ≤ 1/4`.  Proved from `π < 3.15` and
`exp x ≤ 1/(1 - x)` on `[0,1)`. -/
lemma pi_div_sixteen_mul_exp_pi_div_32_le :
    (Real.pi / 16) * (1 + Real.pi / 1024) * Real.exp (Real.pi / 32) ≤ 1 / 4 := by
  have hπ : Real.pi < 3.15 := Real.pi_lt_d2
  have hexp : Real.exp (Real.pi / 32) ≤ 1 / (1 - Real.pi / 32) :=
    Real.exp_bound_div_one_sub_of_interval (by positivity) (by nlinarith)
  have h1 : 0 < 1 - Real.pi / 32 := by nlinarith
  have hmul : (Real.pi / 16) * (1 + Real.pi / 1024) * Real.exp (Real.pi / 32)
      ≤ (Real.pi / 16) * (1 + Real.pi / 1024) * (1 / (1 - Real.pi / 32)) :=
    mul_le_mul_of_nonneg_left hexp (by positivity)
  have h2 : (Real.pi / 16) * (1 + Real.pi / 1024) * (1 / (1 - Real.pi / 32)) ≤ 1 / 4 := by
    rw [show (Real.pi / 16) * (1 + Real.pi / 1024) * (1 / (1 - Real.pi / 32))
        = ((Real.pi / 16) * (1 + Real.pi / 1024)) / (1 - Real.pi / 32) from by ring]
    rw [div_le_iff₀ h1]
    nlinarith [hπ, Real.pi_pos]
  linarith

/-- **The gate value bound.**  If the lift of the perturbed germ satisfies the near-translation
hypothesis `‖F_f w - (w + 1)‖ ≤ 1/32` at `w`, if `1 - σ u 0 = exp (2πi α)` and
`‖α‖ ≤ 1/64`, `α ≠ 0`, then the value `s = σ u(τ w)/(1 + τ w u(τ w))` is within `‖α‖/4` of its
nominal value `σ u 0`. -/
theorem sfun_sub_sigma_u0_le {α σ : ℂ} {u : ℂ → ℂ} {w : ℂ}
    (hα64 : ‖α‖ ≤ 1 / 64) (hαne : α ≠ 0)
    (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hD : ‖Work.Pert.liftF u σ α w - (w + 1)‖ ≤ 1 / 32) :
    ‖Work.Pert.sfun u σ α w - σ * u 0‖ ≤ ‖α‖ / 4 := by
  have ha : 0 < ‖α‖ := norm_pos_iff.mpr hαne
  set z : ℂ := 2 * Real.pi * Complex.I * α with hzdef
  have hzn : ‖z‖ = 2 * Real.pi * ‖α‖ := by
    rw [hzdef, norm_mul, norm_mul, norm_mul]
    rw [show ‖(2 : ℂ)‖ = 2 by norm_num,
        show ‖(Real.pi : ℂ)‖ = Real.pi by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos],
        Complex.norm_I, mul_one]
  have hz0 : z ≠ 0 := by
    rw [hzdef]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero) hαne
  set s : ℂ := Work.Pert.sfun u σ α w with hsdef
  have hL : Work.Pert.liftF u σ α w - (w + 1) = (1 / z) * Complex.log (1 - s) - 1 := by
    rw [Work.Pert.liftF, hzdef, hsdef]; ring
  -- ## the near-translation hypothesis, rewritten for the logarithm
  have hlogbound : ‖Complex.log (1 - s) - z‖ ≤ Real.pi * ‖α‖ / 16 := by
    have hkey : (1 / z) * Complex.log (1 - s) - 1 = (Complex.log (1 - s) - z) / z := by
      field_simp
    have h1 : ‖(Complex.log (1 - s) - z) / z‖ ≤ 1 / 32 := by
      rw [← hkey, ← hL]; exact hD
    rw [norm_div] at h1
    have hzp : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    rw [div_le_iff₀ hzp] at h1
    rw [hzn] at h1
    linarith
  have hsne : 1 - s ≠ 0 := by
    intro h0
    have hzx : Complex.log (1 - s) = 0 := by rw [h0, Complex.log_zero]
    rw [hzx, zero_sub, norm_neg, hzn] at hlogbound
    nlinarith [ha, Real.pi_pos]
  have hexpXlog : Complex.exp (Complex.log (1 - s)) = 1 - s := Complex.exp_log hsne
  have hσu : σ * u 0 = 1 - Complex.exp z := by
    rw [hzdef] at hnorm ⊢
    rw [← hnorm]; ring
  have hsdiff : s - σ * u 0 = Complex.exp z - Complex.exp (Complex.log (1 - s)) := by
    have h1 : s = 1 - Complex.exp (Complex.log (1 - s)) := by rw [hexpXlog]; ring
    linear_combination h1 - hσu
  have hfac : Complex.exp z - Complex.exp (Complex.log (1 - s))
      = Complex.exp z * (1 - Complex.exp (Complex.log (1 - s) - z)) := by
    rw [Complex.exp_sub]
    have hz : Complex.exp z ≠ 0 := Complex.exp_ne_zero z
    field_simp
  -- ## the second factor of the product is `≤ ‖δ‖ + ‖δ‖²`
  have hδle1 : ‖Complex.log (1 - s) - z‖ ≤ 1 := by
    nlinarith [hlogbound, hα64, Real.pi_lt_four, norm_nonneg α]
  have hdv : ‖1 - Complex.exp (Complex.log (1 - s) - z)‖
      ≤ ‖Complex.log (1 - s) - z‖ + ‖Complex.log (1 - s) - z‖ ^ 2 := by
    have h := Complex.norm_exp_sub_one_sub_id_le (x := Complex.log (1 - s) - z) hδle1
    calc ‖1 - Complex.exp (Complex.log (1 - s) - z)‖
        = ‖Complex.exp (Complex.log (1 - s) - z) - 1‖ := norm_sub_rev _ _
      _ = ‖(Complex.exp (Complex.log (1 - s) - z) - 1 - (Complex.log (1 - s) - z))
            + (Complex.log (1 - s) - z)‖ := by ring_nf
      _ ≤ ‖Complex.exp (Complex.log (1 - s) - z) - 1 - (Complex.log (1 - s) - z)‖
            + ‖Complex.log (1 - s) - z‖ := norm_add_le _ _
      _ ≤ ‖Complex.log (1 - s) - z‖ ^ 2 + ‖Complex.log (1 - s) - z‖ := by linarith
      _ = ‖Complex.log (1 - s) - z‖ + ‖Complex.log (1 - s) - z‖ ^ 2 := by ring
  -- ## the final numerical estimate
  have hfinal :
      Real.exp (Real.pi / 32)
        * (‖Complex.log (1 - s) - z‖ + ‖Complex.log (1 - s) - z‖ ^ 2) ≤ ‖α‖ / 4 := by
    have hsq : ‖Complex.log (1 - s) - z‖ + ‖Complex.log (1 - s) - z‖ ^ 2
        ≤ (Real.pi * ‖α‖ / 16) * (1 + Real.pi / 1024) := by
      have h1 : 1 + ‖Complex.log (1 - s) - z‖ ≤ 1 + Real.pi / 1024 := by
        have h2 : ‖Complex.log (1 - s) - z‖ ≤ Real.pi / 1024 := by
          calc ‖Complex.log (1 - s) - z‖ ≤ Real.pi * ‖α‖ / 16 := hlogbound
            _ ≤ Real.pi * (1 / 64) / 16 := by
                  have h3 := mul_le_mul_of_nonneg_left hα64 Real.pi_pos.le
                  linarith
            _ = Real.pi / 1024 := by ring
        linarith
      calc ‖Complex.log (1 - s) - z‖ + ‖Complex.log (1 - s) - z‖ ^ 2
          = ‖Complex.log (1 - s) - z‖ * (1 + ‖Complex.log (1 - s) - z‖) := by ring
        _ ≤ (Real.pi * ‖α‖ / 16) * (1 + Real.pi / 1024) :=
              mul_le_mul hlogbound h1 (by positivity) (by positivity)
    calc Real.exp (Real.pi / 32)
          * (‖Complex.log (1 - s) - z‖ + ‖Complex.log (1 - s) - z‖ ^ 2)
        ≤ Real.exp (Real.pi / 32)
            * ((Real.pi * ‖α‖ / 16) * (1 + Real.pi / 1024)) :=
            mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le
      _ = ‖α‖ * ((Real.pi / 16) * (1 + Real.pi / 1024) * Real.exp (Real.pi / 32)) := by ring
      _ ≤ ‖α‖ * (1 / 4) :=
            mul_le_mul_of_nonneg_left pi_div_sixteen_mul_exp_pi_div_32_le (norm_nonneg α)
      _ = ‖α‖ / 4 := by ring
  calc ‖s - σ * u 0‖
      = ‖Complex.exp z - Complex.exp (Complex.log (1 - s))‖ := by rw [hsdiff]
    _ = ‖Complex.exp z‖ * ‖1 - Complex.exp (Complex.log (1 - s) - z)‖ := by
          rw [hfac, norm_mul]
    _ ≤ Real.exp (Real.pi / 32)
          * (‖Complex.log (1 - s) - z‖ + ‖Complex.log (1 - s) - z‖ ^ 2) := by
          apply mul_le_mul _ hdv (by positivity) (Real.exp_pos _).le
          calc ‖Complex.exp z‖ ≤ Real.exp ‖z‖ := Complex.norm_exp_le_exp_norm z
            _ ≤ Real.exp (Real.pi / 32) := by
                apply Real.exp_le_exp.mpr
                rw [hzn]; nlinarith [hα64, Real.pi_pos]
    _ ≤ ‖α‖ / 4 := hfinal

end Work.Pert.TauCGate
