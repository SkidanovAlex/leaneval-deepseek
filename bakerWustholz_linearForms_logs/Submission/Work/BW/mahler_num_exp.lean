import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Upper bound for `exp (5/24)` from the second-order Taylor expansion:
`exp (5/24) ≤ 1 + 5/24 + (5/24)^2 * 3/(2! * 2) = 953/768`. -/
theorem exp_five_twentyfourths_le : Real.exp ((5:ℝ)/24) ≤ 953/768 := by
  have h := Real.exp_bound' (x := (5/24:ℝ)) (by norm_num) (by norm_num) (n := 2) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

/-- Lower bound for `exp (-(5/24))`: since `exp (5/24) ≤ 953/768`, taking
reciprocals gives `exp (-(5/24)) = (exp (5/24))⁻¹ ≥ 768/953 ≥ 4/5`. -/
theorem exp_neg_five_twentyfourths_ge : (4:ℝ)/5 ≤ Real.exp (-(5/24)) := by
  rw [Real.exp_neg]
  have hpos : (0:ℝ) < Real.exp (5/24) := Real.exp_pos _
  have hinv : (953/768:ℝ)⁻¹ ≤ (Real.exp (5/24))⁻¹ := inv_anti₀ hpos exp_five_twentyfourths_le
  have hnum : ((953/768:ℝ)⁻¹) = 768/953 := by norm_num
  rw [hnum] at hinv
  linarith

/-- Upper bound for `exp (-(5/48))`: `exp (5/48) ≥ 1 + 5/48 = 53/48`, so
`exp (-(5/48)) = (exp (5/48))⁻¹ ≤ 48/53 ≤ 23/24`. -/
theorem exp_neg_five_fortyeighths_le : Real.exp (-(5/48)) ≤ 23/24 := by
  rw [Real.exp_neg]
  have hle : (5/48:ℝ) + 1 ≤ Real.exp (5/48) := Real.add_one_le_exp _
  have hpos : (0:ℝ) < (5/48:ℝ) + 1 := by norm_num
  have hinv : (Real.exp (5/48))⁻¹ ≤ ((5/48:ℝ) + 1)⁻¹ := inv_anti₀ hpos hle
  have hnum : (((5/48:ℝ) + 1)⁻¹) = 48/53 := by norm_num
  rw [hnum] at hinv
  linarith

theorem mahler_num_exp : (4:ℝ)/5 ≤ Real.exp (-(5/24)) ∧ Real.exp (-(5/48)) ≤ 23/24 :=
  ⟨exp_neg_five_twentyfourths_ge, exp_neg_five_fortyeighths_le⟩

end Work.BW
