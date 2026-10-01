import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.logDeriv_completedLFunction_one_sub
import Submission.Commons.NumberTheory.DirichletCharacter.chebyshevPsiChi_explicit_formula_mult
import Submission.Commons.NumberTheory.Linnik.tentMellin_bridge_scale
import Submission.Commons.NumberTheory.DirichletCharacter.logDeriv_LFunction_norm_le_re_ge_three_halves
import Submission.Commons.NumberTheory.DirichletCharacter.leftEdge_logDeriv_bound

namespace Commons.NumberTheory.DirichletCharacter

theorem norm_logDeriv_LFunction_leftEdge_add_logN_le {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (t : ℝ) :
    ‖logDeriv (DirichletCharacter.LFunction χ)
        ((((-1/2:ℝ):ℂ) + (t:ℂ) * Complex.I)) + ((Real.log (N:ℝ)) : ℂ)‖
      ≤ 100 * (Real.log (2 + |t|) + 1) := by
  set s : ℂ := ((-1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I with hsdef
  have hsre : s.re = (-1/2 : ℝ) := by
    rw [hsdef]; simp [Complex.add_re, Complex.mul_re]
  have hs1 : (1 - s).re = (3/2 : ℝ) := by
    rw [Complex.sub_re, Complex.one_re, hsre]; norm_num
  have hN1 : N ≠ 1 := by rintro rfl; exact hχ (Subsingleton.elim χ 1)
  have hlog2 : 0 ≤ Real.log (2 + |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hχinv : χ⁻¹ ≠ 1 := by
    intro h
    apply hχ
    calc χ = (χ⁻¹)⁻¹ := by simp
      _ = (1 : DirichletCharacter ℂ N)⁻¹ := by rw [h]
      _ = 1 := by simp
  have hχpinv : (χ⁻¹).IsPrimitive := isPrimitive_inv hχprim
  have hLs : DirichletCharacter.LFunction χ s ≠ 0 := by
    rw [hsdef]
    exact LFunction_ne_zero_of_re_eq_neg_half χ hχ hχprim t
  have hγs : DirichletCharacter.gammaFactor χ s ≠ 0 :=
    Commons.NumberTheory.Linnik.gammaFactor_ne_zero_of_re_eq_neg_half χ hsre
  have hγdiff : DifferentiableAt ℂ (DirichletCharacter.gammaFactor χ) s := by
    rw [hsdef]
    exact Commons.NumberTheory.Linnik.differentiableAt_gammaFactor_at_neg_half χ t
  have hΛs : DirichletCharacter.completedLFunction χ s ≠ 0 := by
    intro h
    exact hLs (by
      rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inr hN1), h, zero_div])
  have hΛcs : DirichletCharacter.completedLFunction (χ⁻¹) (1 - s) ≠ 0 := by
    intro h
    have hL : DirichletCharacter.LFunction (χ⁻¹) (1 - s) ≠ 0 :=
      DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ⁻¹) (Or.inl hχinv) (by rw [hs1]; norm_num)
    exact hL (by
      rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor (χ⁻¹) (1 - s) (Or.inr hN1), h,
        zero_div])
  have hLsplit : logDeriv (DirichletCharacter.LFunction χ) s =
      logDeriv (DirichletCharacter.completedLFunction χ) s -
        logDeriv (DirichletCharacter.gammaFactor χ) s := by
    have hfun : DirichletCharacter.LFunction χ =
        (fun z => DirichletCharacter.completedLFunction χ z / DirichletCharacter.gammaFactor χ z) :=
      funext (fun z => DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ z (Or.inr hN1))
    rw [hfun]
    exact logDeriv_div s hΛs hγs ((DirichletCharacter.differentiable_completedLFunction hχ) s) hγdiff
  have hFE : logDeriv (DirichletCharacter.completedLFunction χ) s =
      -(Real.log (N : ℝ) : ℂ) -
        logDeriv (DirichletCharacter.completedLFunction (χ⁻¹)) (1 - s) :=
    logDeriv_completedLFunction_one_sub χ hχprim hΛs hΛcs
  have hsplit : logDeriv (DirichletCharacter.completedLFunction (χ⁻¹)) (1 - s) =
      logDeriv (DirichletCharacter.LFunction (χ⁻¹)) (1 - s) +
        logDeriv (DirichletCharacter.gammaFactor (χ⁻¹)) (1 - s) :=
    Commons.NumberTheory.DirichletCharacter.leftHalf_avg.logDeriv_completedL_eq_add_re_ge_one
      (χ⁻¹) hχinv hχpinv (1 - s) (by rw [hs1]; norm_num)
  have hL1 : ‖logDeriv (DirichletCharacter.LFunction (χ⁻¹)) (1 - s)‖ ≤ 20 :=
    logDeriv_LFunction_norm_le_re_ge_three_halves (χ⁻¹) (s := 1 - s) (by rw [hs1])
  have hγ1 : ‖logDeriv (DirichletCharacter.gammaFactor (χ⁻¹)) (1 - s)‖ ≤
      Real.log (2 + |t|) / 2 + 14 := by
    have h := Commons.NumberTheory.Linnik.norm_logDeriv_gammaFactor_at_three_halves (χ := χ⁻¹) t
    have heq : (1 : ℂ) - s = ((3/2 : ℝ) : ℂ) - (t : ℂ) * Complex.I := by
      rw [hsdef]; push_cast; ring
    rwa [heq]
  have hγ0 : ‖logDeriv (DirichletCharacter.gammaFactor χ) s‖ ≤
      13 * (Real.log (2 + |t|) + 1) := by
    rw [hsdef]
    exact Commons.NumberTheory.Linnik.norm_logDeriv_gammaFactor_left χ t
  have hkey : logDeriv (DirichletCharacter.LFunction χ) s + (Real.log (N : ℝ) : ℂ) =
      -(logDeriv (DirichletCharacter.LFunction (χ⁻¹)) (1 - s) +
        logDeriv (DirichletCharacter.gammaFactor (χ⁻¹)) (1 - s)) -
        logDeriv (DirichletCharacter.gammaFactor χ) s := by
    rw [hLsplit, hFE, hsplit]; ring
  rw [hkey]
  calc ‖-(logDeriv (DirichletCharacter.LFunction (χ⁻¹)) (1 - s) +
            logDeriv (DirichletCharacter.gammaFactor (χ⁻¹)) (1 - s)) -
            logDeriv (DirichletCharacter.gammaFactor χ) s‖
      ≤ ‖-(logDeriv (DirichletCharacter.LFunction (χ⁻¹)) (1 - s) +
            logDeriv (DirichletCharacter.gammaFactor (χ⁻¹)) (1 - s))‖ +
          ‖logDeriv (DirichletCharacter.gammaFactor χ) s‖ := norm_sub_le _ _
    _ = ‖logDeriv (DirichletCharacter.LFunction (χ⁻¹)) (1 - s) +
            logDeriv (DirichletCharacter.gammaFactor (χ⁻¹)) (1 - s)‖ +
          ‖logDeriv (DirichletCharacter.gammaFactor χ) s‖ := by rw [norm_neg]
    _ ≤ (20 + (Real.log (2 + |t|) / 2 + 14)) + 13 * (Real.log (2 + |t|) + 1) := by
        refine add_le_add ?_ hγ0
        calc ‖logDeriv (DirichletCharacter.LFunction (χ⁻¹)) (1 - s) +
              logDeriv (DirichletCharacter.gammaFactor (χ⁻¹)) (1 - s)‖
            ≤ ‖logDeriv (DirichletCharacter.LFunction (χ⁻¹)) (1 - s)‖ +
              ‖logDeriv (DirichletCharacter.gammaFactor (χ⁻¹)) (1 - s)‖ := norm_add_le _ _
          _ ≤ 20 + (Real.log (2 + |t|) / 2 + 14) := add_le_add hL1 hγ1
    _ ≤ 100 * (Real.log (2 + |t|) + 1) := by nlinarith [hlog2]

end Commons.NumberTheory.DirichletCharacter
