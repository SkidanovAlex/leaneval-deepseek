import Mathlib

namespace Work.ResMath

/-- `exp (-π/2) ≤ 209/1000`, from `π > 3.14` and a Taylor lower bound for
`exp (1.57)`: the partial sum `∑_{i<7} 1.57^i / i!` already exceeds `1000/209`. -/
private lemma exp_neg_half_pi_le : Real.exp (-(Real.pi / 2)) ≤ 209 / 1000 := by
  have h157 : (1.57 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_gt_d2]
  have hsum : (1000 : ℝ) / 209 ≤ ∑ i ∈ Finset.range 7, (1.57 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    norm_num [Finset.sum_range_succ]
  have hle : (1000 : ℝ) / 209 ≤ Real.exp (Real.pi / 2) :=
    le_trans hsum (le_trans (Real.sum_le_exp_of_nonneg (by norm_num) 7) (Real.exp_le_exp.mpr h157))
  have h1 := one_div_le_one_div_of_le (show (0:ℝ) < 1000/209 by norm_num) hle
  rw [Real.exp_neg]
  calc (Real.exp (Real.pi / 2))⁻¹ = 1 / Real.exp (Real.pi / 2) := by rw [one_div]
    _ ≤ 1 / ((1000:ℝ)/209) := h1
    _ = 209 / 1000 := by norm_num

/-- `2.000008 ≤ exp (π/2 - log 2)`, since `exp (π/2) ≥ 4.000016` (Taylor partial sum) -/
private lemma exp_half_pi_sub_log2_ge : (2.000008 : ℝ) ≤ Real.exp (Real.pi / 2 - Real.log 2) := by
  rw [Real.exp_sub, Real.exp_log (by norm_num : (0:ℝ) < 2)]
  have h157 : (1.57 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_gt_d2]
  have hsum : (4.000016 : ℝ) ≤ ∑ i ∈ Finset.range 5, (1.57 : ℝ)^i / (Nat.factorial i : ℝ) := by
    norm_num [Finset.sum_range_succ]
  have h4 : (4.000016 : ℝ) ≤ Real.exp (Real.pi / 2) :=
    le_trans hsum (le_trans (Real.sum_le_exp_of_nonneg (by norm_num) 5) (Real.exp_le_exp.mpr h157))
  linarith

theorem expGaussBounds (x : ℝ) (hx : 1 ≤ x) :
    2.000008 * Real.exp (-(Real.pi * x / 2)) ≤ 21 / 50 ∧
    2.000008 * Real.exp (-(Real.pi * x / 2)) ≤ (2 : ℝ) ^ (-x) := by
  have h2 : (0:ℝ) ≤ Real.pi / 2 := by positivity
  have harg : -(Real.pi * x / 2) ≤ -(Real.pi / 2) := by
    have h := mul_le_mul_of_nonneg_left hx h2
    nlinarith [h]
  have hexp_le : Real.exp (-(Real.pi * x / 2)) ≤ 209 / 1000 :=
    le_trans (Real.exp_le_exp.mpr harg) exp_neg_half_pi_le
  constructor
  · have h1 : 2.000008 * Real.exp (-(Real.pi * x / 2)) ≤ 2.000008 * (209/1000) :=
      mul_le_mul_of_nonneg_left hexp_le (by norm_num)
    linarith [h1]
  · have hc : (0:ℝ) ≤ Real.pi / 2 - Real.log 2 := by
      have h1 : (1:ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_d2]
      have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
      linarith
    have hmul : (1:ℝ) * (Real.pi / 2 - Real.log 2) ≤ x * (Real.pi / 2 - Real.log 2) :=
      mul_le_mul_of_nonneg_right hx hc
    have hexp_le2 : Real.exp (Real.pi / 2 - Real.log 2) ≤
        Real.exp (x * (Real.pi / 2 - Real.log 2)) :=
      Real.exp_le_exp.mpr (by simpa using hmul)
    have hkey : (2.000008 : ℝ) ≤ Real.exp (x * (Real.pi / 2 - Real.log 2)) :=
      le_trans exp_half_pi_sub_log2_ge hexp_le2
    have hpos : (0:ℝ) < Real.exp (-(Real.pi * x / 2)) := Real.exp_pos _
    calc 2.000008 * Real.exp (-(Real.pi * x / 2))
        ≤ Real.exp (x * (Real.pi / 2 - Real.log 2)) * Real.exp (-(Real.pi * x / 2)) :=
          mul_le_mul_of_nonneg_right hkey hpos.le
      _ = Real.exp (x * (Real.pi / 2 - Real.log 2) + -(Real.pi * x / 2)) := by rw [← Real.exp_add]
      _ = Real.exp (-(x * Real.log 2)) := by congr 1; ring
      _ = (2:ℝ)^(-x) := by
            rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
            congr 1; ring

end Work.ResMath
