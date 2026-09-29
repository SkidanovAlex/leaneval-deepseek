import Mathlib
import Submission.Work.CNum.Basic
import Submission.Work.CNum.log_norm_hauptH
import Submission.Work.CNum.C2_mem
import Submission.Work.CPsi.psiC_facts

/-!
# `circleLog phiC (θ/2π) = Jfun (arg (Vof θ))` on the second arc

On the "large" arc `C₂` of the unit circle, parametrised by
`θ ∈ (α, 2π - α)` (`α = alpR`, the cusp angle), the boundary value of the Theorem C map is

  `φ_C(e^{iθ}) = h(ψ_C(e^{iθ}))`,  `ψ_C = (3/4)·W`,

so with `z = e^{iθ}` and `Q = ψ_C z`,

  `circleLog φ_C (θ/2π) = log ‖h(Q)‖ = log 256 + log ‖Q‖ + Σ' n, 24 log ‖1 + Qⁿ⁺¹‖`
  (`log_norm_hauptH`; `‖Q‖ ≤ 3/4` on the closed disc, `Q ≠ 0`),

while on this arc `Q` runs on the circle `C₂` of centre `c₂ = cenC2 = a/b` and radius
`ρ = √rho2sq`: `Vof θ = (Q - c₂)/ρ` has `‖Vof θ‖ = 1` (`C2_mem`), so
`Q = c₂ + ρ e^{i·arg (Vof θ)}` and the expansion above is exactly `Jfun (Vof θ).arg`.

This is the `C₂`-arc counterpart of `circleLog_eq_Hfun` (the `C₁` arc `(-α, α)`), and the
identification used by the chord bound `Jfun_chord` on the complementary blocks of
`rearrInt (fun _ => 1) (fun _ => phiC)`.
-/

namespace Work.CNum

open Complex Metric Filter Topology
open scoped BigOperators

/-- The `circleLog` parametrisation: `circleLog φ (θ/(2π)) = log ‖φ (e^{iθ})‖`. -/
private lemma circleLog_param' (φ : ℂ → ℂ) (θ : ℝ) :
    Submission.CDTPlan.circleLog φ (θ / (2 * Real.pi)) =
      Real.log ‖φ (Complex.exp (Complex.I * (θ : ℂ)))‖ := by
  rw [Submission.CDTPlan.circleLog]
  congr 2
  push_cast
  field_simp

/-- `ψ_C = (3/4)·W`: the definitional identity `√ = (·)^{1/2}` and `ring`. -/
private lemma psiC_eq_quarter_Wfun (z : ℂ) : Submission.CDTPlan.psiC z = (3 / 4) * Wfun z := by
  unfold Submission.CDTPlan.psiC Submission.CDTPlan.lune Wfun Ra AR BR dR cR
  rw [Complex.sqrt]
  push_cast
  ring_nf

/-- `Vof` in terms of `ψ_C`: `Vof θ = (ψ_C(e^{iθ}) - c₂)/ρ`. -/
private lemma Vof_eq_psiC' (θ : ℝ) :
    Vof θ = (Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ : ℂ))) - (cenC2 : ℂ)) /
      ((Real.sqrt rho2sq : ℝ) : ℂ) := by
  rw [Vof, psiC_eq_quarter_Wfun]

private lemma rho2sq_eq' : rho2sq = (3 * cR / (2 * (cR ^ 2 - 1))) ^ 2 := by
  rw [rho2sq, aR, bR, c0R, kR, cR]; norm_num

private lemma sqrt_rho2sq_ne_zero' : Real.sqrt rho2sq ≠ 0 := by
  rw [rho2sq_eq', Real.sqrt_sq (by norm_num [cR])]; norm_num [cR]

private lemma sqrt_rho2sq_ne_zero'' : ((Real.sqrt rho2sq : ℝ) : ℂ) ≠ 0 := by
  simp only [ne_eq, Complex.ofReal_eq_zero]
  exact sqrt_rho2sq_ne_zero'

private lemma norm_exp_I (θ : ℝ) : ‖Complex.exp (Complex.I * (θ : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero, Real.exp_zero]

theorem circleLog_eq_Jfun {θ : ℝ} (h : θ ∈ Set.Ioo alpR (2 * Real.pi - alpR)) :
    Submission.CDTPlan.circleLog Submission.CDTPlan.phiC (θ / (2 * Real.pi)) = Jfun (Vof θ).arg := by
  have hQ : Vof θ = (Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ : ℂ))) - (cenC2 : ℂ)) /
      ((Real.sqrt rho2sq : ℝ) : ℂ) := Vof_eq_psiC' θ
  have hnorm : ‖Vof θ‖ = 1 := C2_mem h
  -- the unit parameter is the exponential of its argument
  have hexp : Complex.exp (Complex.I * (((Vof θ).arg : ℝ) : ℂ)) = Vof θ := by
    have h1 := Complex.norm_mul_exp_arg_mul_I (Vof θ)
    rw [hnorm] at h1
    simpa [mul_comm] using h1
  -- the evaluation point of `h` is the point of `C₂` of parameter `arg (Vof θ)`
  have hQeq : (cenC2 : ℂ) + ((Real.sqrt rho2sq : ℝ) : ℂ) *
      Complex.exp (Complex.I * (((Vof θ).arg : ℝ) : ℂ)) =
      Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ : ℂ))) := by
    have hρ : ((Real.sqrt rho2sq : ℝ) : ℂ) ≠ 0 := sqrt_rho2sq_ne_zero''
    rw [hexp, hQ, ← mul_div_assoc, mul_div_cancel_left₀ _ hρ]
    ring
  have hnormQ : ‖Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ : ℂ)))‖ ≤ 3 / 4 :=
    Work.CPsi.psiC_norm_le (le_of_eq (norm_exp_I θ))
  have hneQ : Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ : ℂ))) ≠ 0 := by
    intro h0
    exact Complex.exp_ne_zero (Complex.I * (θ : ℂ)) (Work.CPsi.psiC_eq_zero h0)
  rw [circleLog_param' _ θ]
  simp only [Submission.CDTPlan.phiC]
  rw [log_norm_hauptH hnormQ hneQ, Jfun, hQeq]

end Work.CNum
