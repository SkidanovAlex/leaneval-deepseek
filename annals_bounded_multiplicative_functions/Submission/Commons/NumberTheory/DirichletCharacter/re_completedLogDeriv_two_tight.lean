import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.completedLogDeriv_two_tight
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_logRem_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Complex DirichletCharacter
open scoped Real Topology
set_option autoImplicit false
noncomputable section

namespace Commons.NumberTheory.DirichletCharacter

/-! ### The real part of `Λ'/Λ` on the line `Re s = 2`

For the standard tight one-sided bound on the real part of the logarithmic derivative of the
completed Dirichlet L-function on the line `Re s = 2`, we split
`logDeriv Λ = logDeriv L + logDeriv (gammaFactor χ)` and bound the two pieces separately:

* `Re logDeriv L(2+iT) ≤ 1` (the twisted von Mangoldt series, `norm_logDeriv_L_two_le_one`);
* `Re logDeriv (gammaFactor χ)(2+iT) ≤ (1/2)·log(2+|T|) - 1/4`
  (the even/odd case split of `re_logDeriv_Gammaℝ_le_two_three`).

Adding gives exactly `Re(Λ'/Λ)(2+iT) ≤ (1/2)·log(2+|T|) + 3/4`. -/

/-- **Real part of the log-derivative of `Γℝ` on the lines `Re s = 2`, `Re s = 3`.**

For `x ∈ {2, 3}` and any real `y`,

    Re logDeriv Γℝ (x + iy) ≤ (1/2)·log(2 + |y|) − 1/4.

Proof: `logDeriv Γℝ s = −(log π)/2 + ψ(s/2)/2` (`logDeriv_Gammaℝ_formula`), and the Binet
remainder bound `digamma_logRem_le` gives `Re ψ(w) ≤ log ‖w‖ + 1/2` for `1/2 ≤ Re w ≤ 8`
(the remainder has real part at most its modulus, and `Re w > 0` makes `Re (w⁻¹) ≥ 0`).
At `w = s/2 = x/2 + iy/2` one has `‖w‖ ≤ 2 + |y|` when `2 ≤ x ≤ 3`, and `log π ≥ 1`
finishes the estimate. -/
lemma re_logDeriv_Gammaℝ_le_two_three {x : ℝ} (hx : x = 2 ∨ x = 3) (y : ℝ) :
    (logDeriv Complex.Gammaℝ ((x : ℂ) + Complex.I * (y : ℂ))).re ≤
      (1 / 2) * Real.log (2 + |y|) - 1 / 4 := by
  have hx2 : (2 : ℝ) ≤ x := by rcases hx with h | h <;> linarith
  have hx3 : x ≤ 3 := by rcases hx with h | h <;> linarith
  set s : ℂ := (x : ℂ) + Complex.I * (y : ℂ) with hs
  have hsre : 0 < s.re := by
    simp [hs]
    linarith
  have hformula := logDeriv_Gammaℝ_formula s hsre
  set z : ℂ := ((x / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * Complex.I with hz
  have hs2z : s / 2 = z := by
    rw [hs, hz]
    push_cast
    ring
  have hdg := Commons.Analysis.SpecialFunctions.Gamma.digamma_logRem_le (x / 2) (y / 2)
    (by linarith : (1 : ℝ) / 2 ≤ x / 2) (by linarith : x / 2 ≤ 8)
  have hzre : z.re = x / 2 := by
    rw [hz]
    simp
  have hznormpos : 0 < ‖z‖ := by
    rw [norm_pos_iff]
    intro h0
    have h1 : z.re = 0 := by rw [h0]; simp
    rw [hzre] at h1
    linarith
  have hznorm : ‖z‖ ≤ 2 + |y| := by
    have hzim : z.im = y / 2 := by rw [hz]; simp
    have h1 : ‖z‖ ^ 2 = (x / 2) ^ 2 + (y / 2) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, hzre, hzim]
      ring
    have h2 : ‖z‖ ^ 2 ≤ (2 + |y|) ^ 2 := by
      rw [h1, add_sq, sq_abs]
      have hxq : (x / 2) ^ 2 ≤ 9 / 4 := by nlinarith [hx2, hx3]
      have hyq : (y / 2) ^ 2 = y ^ 2 / 4 := by ring
      rw [hyq]
      nlinarith [abs_nonneg y, sq_nonneg y]
    nlinarith [norm_nonneg z, abs_nonneg y]
  have hpsi : (Complex.digamma z).re ≤ Real.log ‖z‖ + 1 / 2 := by
    have h1 : (Complex.digamma z - Complex.log z + ((2 : ℂ)⁻¹) * z⁻¹).re ≤ 1 / 2 :=
      le_trans (Complex.re_le_norm _) hdg
    rw [Complex.add_re, Complex.sub_re] at h1
    have hzren : 0 ≤ z.re := by rw [hzre]; linarith
    have hznormsq : 0 < Complex.normSq z := by
      rw [← Complex.sq_norm]
      exact pow_pos hznormpos 2
    have hinvnn : 0 ≤ z⁻¹.re := by
      rw [Complex.inv_re]
      exact div_nonneg hzren hznormsq.le
    have h3 : 0 ≤ (((2 : ℂ)⁻¹) * z⁻¹).re := by
      have h2c : ((2 : ℂ)⁻¹) = ((1 / 2 : ℝ) : ℂ) := by norm_num
      rw [h2c, Complex.mul_re]
      simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      linarith
    have hlog : (Complex.log z).re = Real.log ‖z‖ := Complex.log_re z
    rw [hlog] at h1
    linarith
  have hlogpi : 1 ≤ Real.log Real.pi := by
    have hlt : Real.exp 1 < Real.pi := lt_trans Real.exp_one_lt_three Real.pi_gt_three
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hlt.le
  have hlogz : Real.log ‖z‖ ≤ Real.log (2 + |y|) := Real.log_le_log hznormpos hznorm
  have hlogpi_eq : Complex.log (Real.pi : ℂ) = (Real.log Real.pi : ℂ) :=
    (Complex.ofReal_log (by positivity : (0 : ℝ) ≤ Real.pi)).symm
  have hA : (-(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma z / 2).re =
      -(Real.log Real.pi) / 2 + (Complex.digamma z).re / 2 := by
    rw [Complex.add_re, Complex.div_ofNat_re, Complex.div_ofNat_re, Complex.neg_re, hlogpi_eq]
    simp
  rw [hformula, hs2z, hA]
  linarith [hpsi, hlogz, hlogpi]

/-- Sharp one-sided bound for the real part of the logarithmic derivative of `Λ` on the
line `Re s = 2`: `Re(Λ′/Λ)(2+iT) ≤ (1/2)·log(2+|T|) + 3/4`.

`Λ = Γℝ · L` (resp. `Γℝ(·+1) · L`) and on `Re s = 2` one has
`Re logDeriv L(2+iT) ≤ 1` while `Re logDeriv (gammaFactor χ)(2+iT) ≤ (1/2)log(2+|T|) - 1/4`
(`re_logDeriv_Gammaℝ_le_two_three`, even/odd case split). -/
theorem re_completedLogDeriv_two_tight {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (T : ℝ) :
    (logDeriv (DirichletCharacter.completedLFunction χ) ((2 : ℂ) + Complex.I * (T : ℂ))).re ≤
      (1 / 2) * Real.log (2 + |T|) + 3 / 4 := by
  set s : ℂ := (2 : ℂ) + Complex.I * (T : ℂ) with hs
  have hsre : 0 < s.re := by
    simp [hs]
  have hLs0 : DirichletCharacter.LFunction χ s ≠ 0 := by
    have hlow : (1 : ℝ) / 4 ≤ ‖DirichletCharacter.LFunction χ s‖ := by
      simpa [hs] using L_lower_re_two_explicit χ hχ T
    exact norm_ne_zero_iff.mp (ne_of_gt (by linarith))
  have hdec := logDeriv_completedLFunction_eq_add χ hχ s hsre hLs0
  have hL : (logDeriv (DirichletCharacter.LFunction χ) s).re ≤ 1 :=
    le_trans (Complex.re_le_norm _) (by simpa [hs] using norm_logDeriv_L_two_le_one χ T)
  have hG : (logDeriv (DirichletCharacter.gammaFactor χ) s).re ≤
      (1 / 2) * Real.log (2 + |T|) - 1 / 4 := by
    rcases χ.even_or_odd with hE | hO
    · have hfun : gammaFactor χ = Complex.Gammaℝ := funext fun z => hE.gammaFactor_def z
      rw [hfun]
      simpa [hs] using re_logDeriv_Gammaℝ_le_two_three (Or.inl rfl) T
    · have hfun : gammaFactor χ = (fun z : ℂ => Complex.Gammaℝ (z + 1)) :=
        funext fun z => hO.gammaFactor_def z
      have hs1b : 0 < (s + 1).re := by
        have hre : (s + 1).re = s.re + 1 := by simp
        rw [hre, hs]
        norm_num
      have hldcomp : logDeriv (fun z : ℂ => Complex.Gammaℝ (z + 1)) s =
          logDeriv Complex.Gammaℝ (s + 1) := by
        have hf : DifferentiableAt ℂ Complex.Gammaℝ (s + 1) :=
          differentiableAt_Gammaℝ (s + 1) hs1b
        have hg : DifferentiableAt ℂ (fun z : ℂ => z + 1) s := by fun_prop
        have h := logDeriv_comp (f := Complex.Gammaℝ) (g := fun z : ℂ => z + 1) (x := s) hf hg
        have hder : deriv (fun z : ℂ => z + 1) s = 1 := by simp
        rw [hder] at h
        simpa [Function.comp_def, mul_comm] using h
      rw [hfun, hldcomp]
      have hS : s + 1 = (3 : ℂ) + Complex.I * (T : ℂ) := by
        rw [hs]
        ring
      rw [hS]
      exact re_logDeriv_Gammaℝ_le_two_three (Or.inr rfl) T
  rw [hdec, Complex.add_re]
  linarith

end Commons.NumberTheory.DirichletCharacter
