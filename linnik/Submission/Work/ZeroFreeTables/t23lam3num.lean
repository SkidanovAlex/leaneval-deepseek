import Mathlib
import Submission.Work.ZeroFreeTables.t23Defs
import Submission.Work.ZeroFreeTables.integral_pow_mul_exp

open scoped BigOperators
noncomputable section

namespace Work.ZeroFreeTables

/-! ## A rigorous upper bound for `Real.exp (8/3)`

Only a crude rational upper bound `exp (8/3) ≤ 15` is needed: the exactly-computed value of the
integral is `8505/1024 - (77553/1024)·exp (-(8/3))`, and `exp (-(8/3)) ≥ 1/15`. -/

private theorem lam3_exp_le_taylor9 (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    Real.exp r ≤ 1 + r + r ^ 2 / 2 + r ^ 3 / 6 + r ^ 4 / 24 + r ^ 5 / 120 + r ^ 6 / 720
      + r ^ 7 / 5040 + r ^ 8 / 40320 + r ^ 9 * (10 / 3265920) := by
  have h := Real.exp_bound' h0 h1 (n := 9) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  linarith

private theorem lam3_exp_two_thirds_le : Real.exp ((2 : ℝ) / 3) ≤ 1.95 := by
  have h := lam3_exp_le_taylor9 ((2 : ℝ) / 3) (by norm_num) (by norm_num)
  norm_num at h
  linarith

private theorem lam3_exp_eight_thirds_le : Real.exp ((8 : ℝ) / 3) ≤ 15 := by
  have hpow : Real.exp ((8 : ℝ) / 3) = (Real.exp ((2 : ℝ) / 3)) ^ 4 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [hpow]
  calc (Real.exp ((2 : ℝ) / 3)) ^ 4 ≤ (1.95 : ℝ) ^ 4 :=
        pow_le_pow_left₀ (le_of_lt (Real.exp_pos _)) lam3_exp_two_thirds_le 4
    _ ≤ 15 := by norm_num

/-! ## The value of the integral -/

private theorem lam3_integral_unshifted :
    (∫ u in (0 : ℝ)..2, u * hb72g u * Real.exp ((4 : ℝ) / 3 * u))
      = (8505 : ℝ) / 1024 * Real.exp (8 / 3) - 77553 / 1024 := by
  have hx : (4 : ℝ) / 3 ≠ 0 := by norm_num
  have hcongr : (fun u : ℝ => u * hb72g u * Real.exp ((4 : ℝ) / 3 * u))
      = (fun u : ℝ => 32 * (u ^ 1 * Real.exp ((4 : ℝ) / 3 * u))
          - 40 * (u ^ 3 * Real.exp ((4 : ℝ) / 3 * u))
          + 20 * (u ^ 4 * Real.exp ((4 : ℝ) / 3 * u))
          - (u ^ 6 * Real.exp ((4 : ℝ) / 3 * u))) := by
    funext u
    unfold hb72g
    ring
  rw [hcongr]
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_add, intervalIntegral.integral_sub,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  · rw [integral_pow_mul_exp 1 hx, integral_pow_mul_exp 3 hx, integral_pow_mul_exp 4 hx,
      integral_pow_mul_exp 6 hx]
    norm_num
    ring
  all_goals exact (by fun_prop : Continuous _).intervalIntegrable 0 2

private theorem lam3_integral_shift :
    (∫ u in (0 : ℝ)..2, u * hb72g u * Real.exp ((4 : ℝ) / 3 * (u - 2)))
      = Real.exp (-(8 / 3)) * (∫ u in (0 : ℝ)..2, u * hb72g u * Real.exp ((4 : ℝ) / 3 * u)) := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  have harg : (4 : ℝ) / 3 * (u - 2) = (4 : ℝ) / 3 * u + (-(8 / 3)) := by ring
  rw [harg, Real.exp_add]
  ring

theorem t23lam3num : Work.ZeroFreeTables.GlueLam3Num := by
  unfold Work.ZeroFreeTables.GlueLam3Num
  rw [lam3_integral_shift, lam3_integral_unshifted]
  have hE : (0 : ℝ) < Real.exp (8 / 3) := Real.exp_pos _
  rw [Real.exp_neg]
  have hcomb : (Real.exp (8 / 3))⁻¹ * ((8505 : ℝ) / 1024 * Real.exp (8 / 3) - 77553 / 1024)
      = 8505 / 1024 - 77553 / 1024 * (Real.exp (8 / 3))⁻¹ := by
    field_simp
  rw [hcomb]
  have hlb : (1 : ℝ) / 15 ≤ (Real.exp (8 / 3))⁻¹ := by
    have h := one_div_le_one_div_of_le hE lam3_exp_eight_thirds_le
    simpa [one_div] using h
  linarith [hlb]

end Work.ZeroFreeTables
