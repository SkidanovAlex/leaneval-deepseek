import Mathlib

namespace Work.LinnikAreas.JMAux

/-- `exp (-(49/10) m) * exp ((2 + 1/1000) (m+1)) ≤ 25 * (1/2)^m`, so summing over any
finset of naturals against a geometric series of ratio `1/2` gives at most `50`. -/
lemma ExpSumLe (s : Finset ℕ) :
    (∑ m ∈ s, Real.exp (-(49/10) * (m:ℝ)) * Real.exp ((2 + 1/1000) * ((m:ℝ)+1)))
      ≤ 50 := by
  -- Numeric bound on the constant factor: `exp (2001/1000) ≤ 25`.
  have h1 : Real.exp (2001/1000) ≤ 25 := by
    have hlt : Real.exp (2001/1000) < Real.exp 3 := Real.exp_lt_exp.mpr (by norm_num)
    have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by
      rw [show (3:ℝ) = (3:ℕ) * 1 by norm_num, Real.exp_nat_mul]
    rw [h3] at hlt
    have hx : Real.exp 1 ^ 3 < (2.7182818286:ℝ)^3 :=
      pow_lt_pow_left₀ Real.exp_one_lt_d9 (le_of_lt (Real.exp_pos 1)) (by norm_num)
    have hc : (2.7182818286:ℝ)^3 < 25 := by norm_num
    linarith
  -- Numeric bound on the decay ratio: `exp (-(2899/1000)) ≤ 1/2`.
  have h2 : Real.exp (-(2899/1000)) ≤ 1/2 := by
    have hle1 : Real.exp 1 ≤ Real.exp (2899/1000) := Real.exp_le_exp.mpr (by norm_num)
    have hinv : (Real.exp (2899/1000))⁻¹ ≤ (Real.exp 1)⁻¹ := by
      rw [inv_le_inv₀ (Real.exp_pos (2899/1000)) (Real.exp_pos 1)]
      exact hle1
    calc Real.exp (-(2899/1000)) = (Real.exp (2899/1000))⁻¹ := Real.exp_neg _
      _ ≤ (Real.exp 1)⁻¹ := hinv
      _ ≤ 1/2 := by
          rw [one_div, inv_le_inv₀ (Real.exp_pos 1) (by norm_num)]
          exact le_of_lt Real.exp_one_gt_two
  -- Each summand is at most `25 * (1/2)^m`.
  have hbound : ∀ m : ℕ,
      Real.exp (-(49/10) * (m:ℝ)) * Real.exp ((2 + 1/1000) * ((m:ℝ)+1)) ≤ 25 * (1/2)^m := by
    intro m
    rw [← Real.exp_add]
    have hexp : -(49/10)*(m:ℝ) + (2+1/1000)*((m:ℝ)+1)
        = 2001/1000 + (m:ℝ) * (-(2899/1000)) := by ring
    rw [hexp, Real.exp_add, Real.exp_nat_mul]
    exact mul_le_mul h1 (pow_le_pow_left₀ (le_of_lt (Real.exp_pos _)) h2 m)
      (by positivity) (by norm_num)
  calc ∑ m ∈ s, Real.exp (-(49/10) * (m:ℝ)) * Real.exp ((2 + 1/1000) * ((m:ℝ)+1))
      ≤ ∑ m ∈ s, 25 * (1/2:ℝ)^m := Finset.sum_le_sum (fun m _ => hbound m)
    _ = 25 * ∑ m ∈ s, (1/2:ℝ)^m := by rw [Finset.mul_sum]
    _ ≤ 25 * 2 := by
        have hsum : ∑ m ∈ s, (1/2:ℝ)^m ≤ 2 := by
          calc ∑ m ∈ s, (1/2:ℝ)^m ≤ ∑' m, (1/2:ℝ)^m :=
                Summable.sum_le_tsum s (fun i _ => by positivity) summable_geometric_two
            _ = 2 := tsum_geometric_two
        linarith
    _ = 50 := by norm_num

end Work.LinnikAreas.JMAux
