import Mathlib

namespace Work.NumberTheory.Chen.APSwitchUpper

open MeasureTheory intervalIntegral Set

theorem integral_L2lo_mul_u4 :
    ∫ u in (2 : ℝ)..4,
        (u - 4) * (2 * ((u - 2) / (u + 4)) + (2 / 3 : ℝ) * ((u - 2) / (u + 4)) ^ 3) / u
      = 97 / 12 - (221 / 3 : ℝ) * Real.log 2 + 39 * Real.log 3 := by
  -- Antiderivative used: the substitution `t = (u-2)/(u+4)` turns the integrand into a
  -- rational function of `t` with partial fraction decomposition
  -- `4*(2t + 5/2 + (26/3)/(t-1) + 4/(t-1)^2 + (13/6)/(2t+1))`, whence
  -- `F(u) = 4*((u-2)/(u+4))^2 + 10*((u-2)/(u+4)) + (8/3)*(u+4) - 39*log(u+4) + (13/3)*log u`.
  have hderiv : ∀ x ∈ Set.uIcc (2:ℝ) 4,
      HasDerivAt ((((fun u : ℝ => 4 * ((u - 2) / (u + 4)) ^ 2) + (fun u : ℝ => 10 * ((u - 2) / (u + 4))))
        + (fun u : ℝ => (8 / 3) * (u + 4)) - (fun u : ℝ => 39 * Real.log (u + 4)))
        + (fun u : ℝ => (13 / 3) * Real.log u))
      ((x - 4) * (2 * ((x - 2) / (x + 4)) + (2 / 3 : ℝ) * ((x - 2) / (x + 4)) ^ 3) / x) x := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (2:ℝ) ≤ 4)] at hx
    have hxne : x ≠ 0 := by linarith [hx.1]
    have hx4ne : x + 4 ≠ 0 := by linarith [hx.1]
    have ht : HasDerivAt (fun u : ℝ => (u - 2) / (u + 4)) (6 / (x + 4) ^ 2) x := by
      have h := ((hasDerivAt_id' x).sub_const 2).div ((hasDerivAt_id' x).add_const 4) hx4ne
      refine h.congr_deriv ?_
      field_simp
      ring
    have hp : HasDerivAt (fun u : ℝ => ((u - 2) / (u + 4)) ^ 2)
        (2 * ((x - 2) / (x + 4)) * (6 / (x + 4) ^ 2)) x := by
      have h := ht.pow 2
      refine h.congr_deriv ?_
      ring
    have hp4 : HasDerivAt (fun u : ℝ => 4 * ((u - 2) / (u + 4)) ^ 2)
        (4 * (2 * ((x - 2) / (x + 4)) * (6 / (x + 4) ^ 2))) x :=
      hp.const_mul 4
    have ht10 : HasDerivAt (fun u : ℝ => 10 * ((u - 2) / (u + 4)))
        (10 * (6 / (x + 4) ^ 2)) x :=
      ht.const_mul 10
    have hlin : HasDerivAt (fun u : ℝ => (8 / 3) * (u + 4)) (8 / 3) x := by
      have h := ((hasDerivAt_id' x).add_const 4).const_mul (8 / 3 : ℝ)
      refine h.congr_deriv ?_
      ring
    have hlog4 : HasDerivAt (fun u : ℝ => 39 * Real.log (u + 4)) (39 * (1 / (x + 4))) x := by
      have h := ((hasDerivAt_id' x).add_const 4).log hx4ne
      refine (h.const_mul 39).congr_deriv ?_
      ring
    have hlogu : HasDerivAt (fun u : ℝ => (13 / 3) * Real.log u) ((13 / 3) * x⁻¹) x :=
      (Real.hasDerivAt_log hxne).const_mul (13 / 3)
    have hcomb := (((hp4.add ht10).add hlin).sub hlog4).add hlogu
    refine hcomb.congr_deriv ?_
    field_simp
    ring
  have hint : IntervalIntegrable
      (fun u : ℝ => (u - 4) * (2 * ((u - 2) / (u + 4)) + (2 / 3 : ℝ) * ((u - 2) / (u + 4)) ^ 3) / u)
      volume 2 4 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (2:ℝ) ≤ 4)]
    have h1 : ∀ x ∈ Set.Icc (2:ℝ) 4, x + 4 ≠ 0 := fun x hx => by have := hx.1; linarith
    have h2 : ∀ x ∈ Set.Icc (2:ℝ) 4, x ≠ 0 := fun x hx => by have := hx.1; linarith
    fun_prop (disch := first | assumption | norm_num)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [Pi.add_apply, Pi.sub_apply]
  norm_num
  rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]
  rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
  rw [show (6:ℝ) = 2*3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  push_cast
  ring

end Work.NumberTheory.Chen.APSwitchUpper
