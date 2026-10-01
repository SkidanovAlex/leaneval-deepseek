import Mathlib

set_option linter.unusedVariables false

namespace Work.LinnikAreas

open Filter Real

theorem ratio_convex_const (C6 : ℝ) (hC6 : 0 < C6) :
    ∃ N : ℕ, 3 ≤ N ∧ 3 * C6 * (400001 : ℝ) ^ ((4 : ℝ) / 3 - (N : ℝ) / 2)
      * Real.exp ((N : ℝ) / 10) ≤ 1 / 4 := by
  set r : ℝ := Real.exp (1/10) * (Real.sqrt 400001)⁻¹ with hrdef
  have hsqrt_pos : 0 < Real.sqrt 400001 := Real.sqrt_pos.mpr (by norm_num)
  have hexp_lt : Real.exp (1/10) < 3 := by
    calc Real.exp (1/10) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
      _ < 3 := Real.exp_one_lt_three
  have hsqrt_gt : 3 < Real.sqrt 400001 := by
    rw [Real.lt_sqrt (by norm_num : (0:ℝ) ≤ 3)]
    norm_num
  have hrpos : 0 < r := by
    rw [hrdef]; positivity
  have hrlt1 : r < 1 := by
    rw [hrdef, ← div_eq_mul_inv, div_lt_one hsqrt_pos]
    linarith
  have key : ∀ n : ℕ,
      3 * C6 * (400001 : ℝ) ^ ((4 : ℝ) / 3 - (n : ℝ) / 2) * Real.exp ((n : ℝ) / 10)
        = (3 * C6 * (400001:ℝ)^((4:ℝ)/3)) * r^n := by
    intro n
    have h1 : (400001 : ℝ) ^ ((4 : ℝ) / 3 - (n : ℝ) / 2)
        = (400001 : ℝ) ^ ((4:ℝ)/3) * ((Real.sqrt 400001)⁻¹)^n := by
      rw [show (4:ℝ)/3 - (n:ℝ)/2 = (4:ℝ)/3 + (-(1:ℝ)/2 * (n:ℝ)) by ring]
      rw [Real.rpow_add (by norm_num : (0:ℝ) < 400001)]
      congr 1
      rw [show (-(1:ℝ)/2 * (n:ℝ)) = (-(1/2)) * (n:ℝ) by ring]
      rw [Real.rpow_mul (by norm_num : (0:ℝ) ≤ 400001)]
      rw [Real.rpow_natCast]
      congr 1
      rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 400001), Real.sqrt_eq_rpow]
    have h2 : Real.exp ((n:ℝ)/10) = (Real.exp (1/10))^n := by
      rw [show (n:ℝ)/10 = (n:ℝ) * (1/10) by ring, Real.exp_nat_mul]
    rw [h1, h2, hrdef]
    rw [show (Real.exp (1/10) * (Real.sqrt 400001)⁻¹)^n
          = (Real.sqrt 400001)⁻¹^n * (Real.exp (1/10))^n by rw [mul_pow, mul_comm]]
    ring
  have hlim : Tendsto (fun n : ℕ => (3 * C6 * (400001:ℝ)^((4:ℝ)/3)) * r^n) atTop (nhds 0) := by
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (le_of_lt hrpos) hrlt1
    have := hp.const_mul (3 * C6 * (400001:ℝ)^((4:ℝ)/3))
    simpa using this
  have hev : ∀ᶠ n in atTop, (3 * C6 * (400001:ℝ)^((4:ℝ)/3)) * r^n < 1/4 :=
    hlim.eventually (eventually_lt_nhds (by norm_num : (0:ℝ) < 1/4))
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hev
  refine ⟨max 3 N0, le_max_left 3 N0, ?_⟩
  have hkey := hN0 (max 3 N0) (le_max_right 3 N0)
  have hid := key (max 3 N0)
  linarith [hkey, hid]

end Work.LinnikAreas
