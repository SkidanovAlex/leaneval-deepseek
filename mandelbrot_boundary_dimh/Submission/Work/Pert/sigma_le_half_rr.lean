import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Basic
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Pert.scale_lattice
import Submission.Work.Pert.norm_one_sub_exp_pole_witness
import Submission.Work.Pert.mem_Qm_neg_fifteen_sixteenth

/-!
# PERT · `Work.Pert.sigma_le_half_rr`

`‖σ‖ ≤ rr/2` whenever `τ_f` maps the lower gate `Qm Ξ α` into the ball of radius `rr`.

The point is that `τ_f w = σ / (1 - exp (-2πi α w))` for **every** `w`, so

  `‖σ‖ = ‖τ_f w‖ · ‖1 - exp (-2πi α w)‖ < rr · ‖1 - exp (-2πi α w)‖`

and it suffices to exhibit one point of the gate on which the exponential denominator is small:
the pole line `w_λ = λ/α` (`λ` real) has `α w_λ = λ`, so there
`‖1 - exp (-2πi α w_λ)‖ = 2 |sin (π λ)|`, which is `≤ 1/2` as soon as `λ` is within `1/12` of an
integer.

The gate keeps `λ ∈ (-1, 0)`-points of the pole line away from the poles `0`, `-1` by the
two cone inequalities: writing `A = Re(1/α) + |Im(1/α)| > 0`, the `w_λ` with
`λ ∈ (Ξ/A - 1, -Ξ/A)` all lie in `Qm Ξ α`.  We take the explicit `λ = -15/16`, which is admissible
as soon as `16 Ξ < A`; at it the denominator is the fixed number `2 sin (π/16) < 1/2`.

`A ≥ 1/‖α‖ ≥ 32 (M + 2 + Ξ) ≥ 32 Ξ` by the smallness hypothesis `‖α‖ ≤ 1/(32 (M+2+Ξ))`, so
`16 Ξ < A` holds.  No smallness of `σ` is needed, and `σ = 0` is allowed.
-/

namespace Work.Pert

open MandelDim Complex

noncomputable section

theorem sigma_le_half_rr {Ξ rr M : ℝ} {α σ : ℂ}
    (hΞ : 0 < Ξ) (hrr : 0 < rr) (hM : 2 ^ 10 ≤ M) (hInF1 : MandelDim.InF1 α)
    (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ)))
    (hτQ : ∀ w ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α w ∈ Metric.ball (0 : ℂ) rr) :
    ‖σ‖ ≤ rr / 2 := by
  -- `InF1 α` says `|Im α| < Re α`, so `α ≠ 0`
  have hF1 : |α.im| < α.re := hInF1
  have hre : 0 < α.re := lt_of_le_of_lt (abs_nonneg α.im) hF1
  have hαne : α ≠ 0 := by intro h; rw [h] at hre; simp at hre
  have hαpos : 0 < ‖α‖ := norm_pos_iff.mpr hαne
  -- `A = Re(1/α) + |Im(1/α)|`
  set A : ℝ := (1 / α).re + |(1 / α).im| with hAdef
  have hPpos : 0 < (1 / α).re := by
    rw [one_div, Complex.inv_re, Complex.normSq_eq_norm_sq]
    exact div_pos hre (pow_pos hαpos 2)
  have hAge : 1 / ‖α‖ ≤ A := by
    have h1 : ‖(1 / α : ℂ)‖ ≤ |(1 / α).re| + |(1 / α).im| := Complex.norm_le_abs_re_add_abs_im _
    have h2 : ‖(1 / α : ℂ)‖ = 1 / ‖α‖ := by rw [norm_div, norm_one]
    have h3 : |(1 / α).re| = (1 / α).re := abs_of_pos hPpos
    rw [hAdef]
    linarith
  have hApos : 0 < A := lt_of_lt_of_le (by positivity) hAge
  -- `A ≥ 32 Ξ` from the smallness of `‖α‖`
  have hM2 : (0 : ℝ) ≤ M + 2 := by
    have h1024 : (1024 : ℝ) ≤ M := by norm_num at hM; exact hM
    linarith
  have hden : 0 < 32 * (M + 2 + Ξ) := by linarith
  have hmul : 32 * (M + 2 + Ξ) * ‖α‖ ≤ 1 := by
    have h1 := mul_le_mul_of_nonneg_left hα hden.le
    rwa [mul_one_div, div_self (ne_of_gt hden)] at h1
  have h32 : 32 * Ξ ≤ A := by
    have h2 : 32 * (M + 2 + Ξ) ≤ 1 / ‖α‖ := by
      rw [le_div_iff₀ hαpos]
      linarith
    have h3 : 32 * Ξ ≤ 32 * (M + 2 + Ξ) := by linarith
    linarith
  have h16 : 16 * Ξ < A := by linarith
  -- the pole-line witness and the gate hypothesis at it
  have hwQ : ((-15 / 16 : ℝ) : ℂ) / α ∈ Work.Pert.Qm Ξ α := mem_Qm_neg_fifteen_sixteenth hΞ h16
  have hmem : ‖Work.Pert.tauC σ α (((-15 / 16 : ℝ) : ℂ) / α)‖ < rr := by
    have h := hτQ _ hwQ
    rwa [Metric.mem_ball, dist_zero_right] at h
  have hnorm := norm_one_sub_exp_pole_witness hαne
  -- the denominator does not vanish, so `σ = τ_f w · (1 - exp (…))`
  have hsinpos : 0 < Real.sin (Real.pi / 16) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  have hEne : (1 : ℂ)
      - Complex.exp (-(2 * Real.pi * Complex.I * α * (((-15 / 16 : ℝ) : ℂ) / α))) ≠ 0 := by
    intro h0
    have h1 : ‖(1 : ℂ)
        - Complex.exp (-(2 * Real.pi * Complex.I * α * (((-15 / 16 : ℝ) : ℂ) / α)))‖ = 0 := by
      rw [h0, norm_zero]
    rw [hnorm] at h1
    linarith
  have hσeq : σ = Work.Pert.tauC σ α (((-15 / 16 : ℝ) : ℂ) / α)
      * (1 - Complex.exp (-(2 * Real.pi * Complex.I * α * (((-15 / 16 : ℝ) : ℂ) / α)))) := by
    rw [Work.Pert.tauC, div_mul_cancel₀ _ hEne]
  have hbound : ‖σ‖ < rr * (2 * Real.sin (Real.pi / 16)) := by
    rw [hσeq, norm_mul, hnorm]
    exact mul_lt_mul_of_pos_right hmem (by linarith [hsinpos])
  -- `2 sin (π/16) ≤ 1/2`
  have hsmall : 2 * Real.sin (Real.pi / 16) ≤ 1 / 2 := by
    have h1 : Real.sin (Real.pi / 16) < Real.pi / 16 := Real.sin_lt (by positivity)
    have h2 : (2 : ℝ) * (Real.pi / 16) < 1 / 2 := by linarith [Real.pi_lt_four]
    linarith
  have hle : rr * (2 * Real.sin (Real.pi / 16)) ≤ rr / 2 := by
    nlinarith [hsmall, hrr]
  linarith

end

end Work.Pert
