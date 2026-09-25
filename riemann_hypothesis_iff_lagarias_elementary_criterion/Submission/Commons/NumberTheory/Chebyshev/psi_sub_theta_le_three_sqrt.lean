import Mathlib
import Submission.Commons.NumberTheory.Chebyshev.psi_sub_theta_eventually_le

/-!
# An explicit global bound `ψ x - θ x ≤ 3 √x`

We prove that the difference of the Chebyshev `ψ`- and `θ`-functions is bounded by
`3 √x` for every real `x ≥ 1`.  The proof combines

* the Costa–Pereira upper bound `ψ x - θ x ≤ ψ(x^{1/2}) + ψ(x^{1/3}) + ψ(x^{1/5})`,
* the linear bound `ψ y ≤ (log 3) · y` (Hanson's bound on `lcm(1,…,n)`),
* the elementary estimates `x^{1/3} ≤ (4/5) x^{1/2}` and `x^{1/5} ≤ (2/3) x^{1/2}`
  valid for `x ≥ 4`.

For `1 ≤ x < 4` all three arguments `x^{1/2}, x^{1/3}, x^{1/5}` are `< 2`, so `ψ`
vanishes on them and the difference is `0`.
-/

namespace Commons.NumberTheory.Chebyshev

/-- `4^{-1/6} ≤ 4/5`. -/
private lemma four_rpow_neg_sixth_le : (4 : ℝ) ^ (-(1 / 6) : ℝ) ≤ 4 / 5 := by
  have key : ((4 : ℝ) ^ (-(1 / 6) : ℝ)) ^ (6 : ℝ) ≤ ((4 : ℝ) / 5) ^ (6 : ℝ) := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
    rw [show (-(1 / 6 : ℝ)) * 6 = -1 by norm_num, Real.rpow_neg_one]
    norm_num
  exact (Real.rpow_le_rpow_iff (by positivity) (by norm_num) (by norm_num : (0 : ℝ) < 6)).mp key

/-- `4^{-3/10} ≤ 2/3`. -/
private lemma four_rpow_neg_three_tenths_le : (4 : ℝ) ^ (-(3 / 10) : ℝ) ≤ 2 / 3 := by
  have key : ((4 : ℝ) ^ (-(3 / 10) : ℝ)) ^ (10 : ℝ) ≤ ((2 : ℝ) / 3) ^ (10 : ℝ) := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
    rw [show (-(3 / 10 : ℝ)) * 10 = -3 by norm_num, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  exact (Real.rpow_le_rpow_iff (by positivity) (by norm_num) (by norm_num : (0 : ℝ) < 10)).mp key

/-- For `x ≥ 4`, `x^{1/3} ≤ (4/5) x^{1/2}`. -/
private lemma rpow_third_le {x : ℝ} (hx : 4 ≤ x) :
    x ^ (1 / 3 : ℝ) ≤ (4 / 5) * x ^ (1 / 2 : ℝ) := by
  have hxpos : 0 < x := by linarith
  have hhalf : 0 < x ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hxpos _
  rw [← div_le_iff₀ hhalf]
  rw [← Real.rpow_sub hxpos]
  rw [show (1 / 3 : ℝ) - 1 / 2 = -(1 / 6) by norm_num]
  calc x ^ (-(1 / 6) : ℝ) ≤ (4 : ℝ) ^ (-(1 / 6) : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hx (by norm_num)
    _ ≤ 4 / 5 := four_rpow_neg_sixth_le

/-- For `x ≥ 4`, `x^{1/5} ≤ (2/3) x^{1/2}`. -/
private lemma rpow_fifth_le {x : ℝ} (hx : 4 ≤ x) :
    x ^ (1 / 5 : ℝ) ≤ (2 / 3) * x ^ (1 / 2 : ℝ) := by
  have hxpos : 0 < x := by linarith
  have hhalf : 0 < x ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hxpos _
  rw [← div_le_iff₀ hhalf]
  rw [← Real.rpow_sub hxpos]
  rw [show (1 / 5 : ℝ) - 1 / 2 = -(3 / 10) by norm_num]
  calc x ^ (-(3 / 10) : ℝ) ≤ (4 : ℝ) ^ (-(3 / 10) : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hx (by norm_num)
    _ ≤ 2 / 3 := four_rpow_neg_three_tenths_le

/-- For `1 ≤ x < 4`, `x^{1/2} < 2`. -/
private lemma rpow_half_lt_two {x : ℝ} (hx : 1 ≤ x) (hx4 : x < 4) :
    x ^ (1 / 2 : ℝ) < 2 := by
  have h := Real.rpow_lt_rpow (by linarith : (0 : ℝ) ≤ x) hx4 (by norm_num : (0 : ℝ) < (1 / 2 : ℝ))
  have h4 : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by norm_num
  rwa [h4] at h

theorem psi_sub_theta_le_three_sqrt (x : ℝ) (hx : 1 ≤ x) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 3 * Real.sqrt x := by
  have hxpos : 0 < x := by linarith
  have hCP := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  rw [show (2 : ℝ)⁻¹ = (1 / 2 : ℝ) by norm_num,
      show (3 : ℝ)⁻¹ = (1 / 3 : ℝ) by norm_num,
      show (5 : ℝ)⁻¹ = (1 / 5 : ℝ) by norm_num] at hCP
  rcases lt_or_ge x 4 with hlt | hge
  · -- `1 ≤ x < 4`: all three arguments of `ψ` are `< 2`, so `ψ` vanishes.
    have hhalf_lt : x ^ (1 / 2 : ℝ) < 2 := rpow_half_lt_two hx hlt
    have hthird_lt : x ^ (1 / 3 : ℝ) < 2 :=
      lt_of_le_of_lt (Real.rpow_le_rpow_of_exponent_le hx (by norm_num)) hhalf_lt
    have hfifth_lt : x ^ (1 / 5 : ℝ) < 2 :=
      lt_of_le_of_lt (Real.rpow_le_rpow_of_exponent_le hx (by norm_num)) hhalf_lt
    have hA := Chebyshev.psi_eq_zero_of_lt_two hhalf_lt
    have hB := Chebyshev.psi_eq_zero_of_lt_two hthird_lt
    have hC := Chebyshev.psi_eq_zero_of_lt_two hfifth_lt
    have hle0 : Chebyshev.psi x - Chebyshev.theta x ≤ 0 := by
      calc Chebyshev.psi x - Chebyshev.theta x
          ≤ Chebyshev.psi (x ^ (1 / 2 : ℝ)) + Chebyshev.psi (x ^ (1 / 3 : ℝ))
              + Chebyshev.psi (x ^ (1 / 5 : ℝ)) := hCP
        _ = 0 := by rw [hA, hB, hC]; ring
    nlinarith [Real.sqrt_nonneg x]
  · -- `x ≥ 4`: bound each `ψ` term linearly and compare the resulting powers.
    have hlog3pos : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
    have hxhalf_nn : (0 : ℝ) ≤ x ^ (1 / 2 : ℝ) := Real.rpow_nonneg hxpos.le _
    have b1 : Chebyshev.psi (x ^ (1 / 2 : ℝ)) ≤ Real.log 3 * x ^ (1 / 2 : ℝ) :=
      psi_le_log3_mul_real _ (Real.rpow_nonneg hxpos.le _)
    have b3 : Chebyshev.psi (x ^ (1 / 3 : ℝ)) ≤ Real.log 3 * x ^ (1 / 3 : ℝ) :=
      psi_le_log3_mul_real _ (Real.rpow_nonneg hxpos.le _)
    have b5 : Chebyshev.psi (x ^ (1 / 5 : ℝ)) ≤ Real.log 3 * x ^ (1 / 5 : ℝ) :=
      psi_le_log3_mul_real _ (Real.rpow_nonneg hxpos.le _)
    have e3 := rpow_third_le hge
    have e5 := rpow_fifth_le hge
    have hlog3le : Real.log 3 ≤ 6 / 5 := by linarith [Real.log_three_lt_d9]
    have hnum : Real.log 3 * (x ^ (1 / 2 : ℝ) + x ^ (1 / 3 : ℝ) + x ^ (1 / 5 : ℝ))
        ≤ 3 * x ^ (1 / 2 : ℝ) := by
      calc Real.log 3 * (x ^ (1 / 2 : ℝ) + x ^ (1 / 3 : ℝ) + x ^ (1 / 5 : ℝ))
          ≤ Real.log 3 * (x ^ (1 / 2 : ℝ) + (4 / 5) * x ^ (1 / 2 : ℝ)
              + (2 / 3) * x ^ (1 / 2 : ℝ)) := by
            apply mul_le_mul_of_nonneg_left _ hlog3pos.le
            linarith [e3, e5]
        _ = Real.log 3 * ((37 / 15) * x ^ (1 / 2 : ℝ)) := by ring
        _ ≤ (6 / 5) * ((37 / 15) * x ^ (1 / 2 : ℝ)) := by
            apply mul_le_mul_of_nonneg_right hlog3le
            positivity
        _ = (222 / 75 : ℝ) * x ^ (1 / 2 : ℝ) := by ring
        _ ≤ 3 * x ^ (1 / 2 : ℝ) := by
            apply mul_le_mul_of_nonneg_right _ hxhalf_nn
            norm_num
    have hsqrt : x ^ (1 / 2 : ℝ) = Real.sqrt x := (Real.sqrt_eq_rpow x).symm
    calc Chebyshev.psi x - Chebyshev.theta x
        ≤ Chebyshev.psi (x ^ (1 / 2 : ℝ)) + Chebyshev.psi (x ^ (1 / 3 : ℝ))
            + Chebyshev.psi (x ^ (1 / 5 : ℝ)) := hCP
      _ ≤ Real.log 3 * (x ^ (1 / 2 : ℝ) + x ^ (1 / 3 : ℝ) + x ^ (1 / 5 : ℝ)) := by
            linarith [b1, b3, b5]
      _ ≤ 3 * x ^ (1 / 2 : ℝ) := hnum
      _ = 3 * Real.sqrt x := by rw [hsqrt]

end Commons.NumberTheory.Chebyshev
