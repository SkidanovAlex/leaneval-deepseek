import Mathlib
import Submission.Work.CNum.Basic
import Submission.Work.CNum.exp_phi_eq
import Submission.Work.CNum.Wfun_exp
import Submission.Work.CNum.log_norm_hauptH
import Submission.Work.CNum.sqrt_Ra_circle

/-! # `circleLog phiC = Hfun ∘ phiR` on the cusp arc

On the first arc `C₁` of the unit circle, parametrised by `θ ∈ (-α, α)`, the boundary value of
the Theorem C map is

`φ_C(e^{iθ}) = h(ψ_C(e^{iθ})) = h((3/4) W(e^{iθ})) = h((3/4) e^{iφ_R(θ)})`,

because `ψ_C = (3/4) W` (`psiC_eq_smul_Wfun`) and `W(e^{iθ}) = e^{iφ_R(θ)}`
(`Work.CNum.exp_phi_eq`).  Applying the series expansion `log ‖h(q)‖ = log 256 + log ‖q‖ +
Σ' n, 24 log ‖1 + q^{n+1}‖` at `q = (3/4) e^{iφ_R(θ)}` (radius exactly `3/4`) turns the
circle logarithm into the cosine-form series `Hfun (φ_R θ)`.

This is the identification used by `rearrInt_bridge`/`blk_le_doubleSum_indicator`: the block of
`circleLog phiC` covering the arc `C₁` is bounded by `max (Hfun (φ_R θ)) (Hfun (φ_R θ'))`.
-/

namespace Work.CNum

open scoped BigOperators

/-- The `circleLog` parametrisation: `circleLog φ (θ/(2π)) = log ‖φ (e^{iθ})‖`. -/
lemma circleLog_param (φ : ℂ → ℂ) (θ : ℝ) :
    Submission.CDTPlan.circleLog φ (θ / (2 * Real.pi)) =
      Real.log ‖φ (Complex.exp (Complex.I * (θ : ℂ)))‖ := by
  rw [Submission.CDTPlan.circleLog]
  congr 2
  push_cast
  field_simp

/-- `ψ_C = (3/4) · W`: the definitional identity `√ = (·)^{1/2}` and `ring`. -/
lemma psiC_eq_smul_Wfun (z : ℂ) : Submission.CDTPlan.psiC z = (3 / 4) * Wfun z := by
  unfold Submission.CDTPlan.psiC Submission.CDTPlan.lune Wfun Ra AR BR dR cR
  rw [Complex.sqrt]
  push_cast
  ring_nf

/-- The modulus of the evaluation point: `‖(3/4) e^{iφ}‖ = 3/4`. -/
lemma norm_three_quarters_exp (φ : ℝ) :
    ‖(3 / 4 : ℂ) * Complex.exp (Complex.I * (φ : ℂ))‖ = 3 / 4 := by
  rw [norm_mul, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero, Real.exp_zero, mul_one]
  norm_num

/-- The series expansion of `log ‖h‖` at the radius-`3/4` circle: `log ‖h((3/4) e^{iφ})‖ = Hfun φ`. -/
lemma log_norm_hauptH_circle (φ : ℝ) :
    Real.log ‖Submission.CDTPlan.hauptH ((3 / 4 : ℂ) * Complex.exp (Complex.I * (φ : ℂ)))‖ =
      Hfun φ := by
  have hnorm := norm_three_quarters_exp φ
  have hne : (3 / 4 : ℂ) * Complex.exp (Complex.I * (φ : ℂ)) ≠ 0 :=
    mul_ne_zero (by norm_num) (Complex.exp_ne_zero _)
  have hpow : ∀ n : ℕ, ((3 / 4 : ℂ) * Complex.exp (Complex.I * (φ : ℂ))) ^ (n + 1) =
      (((3 / 4 : ℝ)) : ℂ) ^ (n + 1) * Complex.exp (Complex.I * ((n + 1 : ℝ) : ℂ) * (φ : ℂ)) := by
    intro n
    rw [mul_pow, ← Complex.exp_nat_mul]
    congr 1
    · push_cast; norm_num
    · push_cast; ring_nf
  rw [log_norm_hauptH hnorm.le hne, hnorm, Hfun, tsum_congr (fun n => by rw [hpow n])]
  have : Real.log 256 + Real.log (3 / 4) = Real.log 192 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  linarith [this]

theorem circleLog_eq_Hfun {θ : ℝ} (h : θ ∈ Set.Ioo (-alpR) alpR) :
    Submission.CDTPlan.circleLog Submission.CDTPlan.phiC (θ / (2 * Real.pi)) = Hfun (phiR θ) := by
  have harg : Submission.CDTPlan.phiC (Complex.exp (Complex.I * (θ : ℂ))) =
      Submission.CDTPlan.hauptH ((3 / 4 : ℂ) * Complex.exp (Complex.I * (phiR θ : ℂ))) := by
    rw [Submission.CDTPlan.phiC, psiC_eq_smul_Wfun, ← exp_phi_eq h]
  rw [circleLog_param, harg, log_norm_hauptH_circle]

end Work.CNum
