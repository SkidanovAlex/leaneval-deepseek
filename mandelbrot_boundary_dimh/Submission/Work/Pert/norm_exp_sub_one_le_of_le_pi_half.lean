import Mathlib

namespace Work.Pert

/-- Numerical estimate: `exp (π/6) ≤ 1.691`, via the Taylor bound `Real.exp_bound'` at
`x = π/6 ≤ 21/40 = 0.525` with `n = 5`. -/
lemma exp_pi_div_six_le : Real.exp (Real.pi / 6) ≤ 1.691 := by
  have hx0 : 0 ≤ Real.pi / 6 := by positivity
  have hx : Real.pi / 6 ≤ (21 / 40 : ℝ) := by linarith [Real.pi_lt_d2]
  have hb := Real.exp_bound' (x := Real.pi / 6) hx0 (by linarith : Real.pi / 6 ≤ 1)
    (n := 5) (by norm_num)
  have h2 :
      (∑ m ∈ Finset.range 5, (Real.pi / 6) ^ m / (m.factorial : ℝ)) +
          (Real.pi / 6) ^ 5 * (5 + 1) / ((Nat.factorial 5 : ℝ) * 5)
        ≤ (∑ m ∈ Finset.range 5, (21 / 40 : ℝ) ^ m / (m.factorial : ℝ)) +
          (21 / 40 : ℝ) ^ 5 * (5 + 1) / ((Nat.factorial 5 : ℝ) * 5) := by
    gcongr
  have h3 :
      (∑ m ∈ Finset.range 5, (21 / 40 : ℝ) ^ m / (m.factorial : ℝ)) +
          (21 / 40 : ℝ) ^ 5 * (5 + 1) / ((Nat.factorial 5 : ℝ) * 5) ≤ 1.691 := by
    simp [Finset.sum_range_succ]
    norm_num
  linarith

/-- Numerical estimate: `exp (π/2) ≤ 5`, since `π/2 = 3 · (π/6)` and `exp (π/6) ≤ 1.691`,
`1.691^3 ≤ 5`. -/
lemma exp_pi_div_two_le_five : Real.exp (Real.pi / 2) ≤ 5 := by
  have h3 : Real.exp (Real.pi / 2) = (Real.exp (Real.pi / 6)) ^ 3 := by
    have hpi : Real.pi / 2 = 3 * (Real.pi / 6) := by ring
    rw [hpi]
    exact Real.exp_nat_mul (Real.pi / 6) 3
  rw [h3]
  calc (Real.exp (Real.pi / 6)) ^ 3 ≤ (1.691 : ℝ) ^ 3 := by
        gcongr
        exact exp_pi_div_six_le
    _ ≤ 5 := by norm_num

/-- Convexity of `exp` on `[0, π/2]`: `exp t - 1 ≤ ((exp (π/2) - 1)/(π/2)) · t`. -/
lemma exp_sub_one_le_ratio_mul {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ Real.pi / 2) :
    Real.exp t - 1 ≤ ((Real.exp (Real.pi / 2) - 1) / (Real.pi / 2)) * t := by
  rcases eq_or_lt_of_le h0 with h | ht
  · rw [← h]; norm_num
  have hne : Real.pi / 2 ≠ 0 := by positivity
  have hsec := convexOn_exp.secant_mono (a := 0) (x := t) (y := Real.pi / 2)
    (Set.mem_univ 0) (Set.mem_univ t) (Set.mem_univ (Real.pi / 2)) ht.ne' hne h1
  simp only [Real.exp_zero, sub_zero] at hsec
  have h' := (div_le_iff₀ ht).mp hsec
  linarith

/-- The optimal constant for the ratio bound on the disc of radius `π/2` is `≤ 27/10`. -/
lemma exp_ratio_le : ((Real.exp (Real.pi / 2) - 1) / (Real.pi / 2)) ≤ 27 / 10 := by
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < Real.pi / 2)]
  nlinarith [Real.pi_gt_three, exp_pi_div_two_le_five]

/-- **Ratio bound for the exponential on the disc of radius `π/2`.** For `‖z‖ ≤ π/2`,
`‖exp z - 1‖ ≤ 2.7 ‖z‖`. (The optimal constant is `(e^{π/2}-1)/(π/2) ≈ 2.426`.)

Proof sketch: `‖exp z - 1‖ ≤ exp ‖z‖ - 1` (`Complex.norm_exp_sub_sum_le_exp_norm_sub_sum z 1`).
For `0 ≤ t ≤ π/2`, convexity of `exp` (`convexOn_exp`, or `ConvexOn.le_max_of_mem_Icc`) gives
`exp t ≤ 1 + (2t/π)(exp (π/2) - 1)`, i.e. `exp t - 1 ≤ ((2/π)(exp (π/2)-1)) t`, and
`(2/π)(exp (π/2) - 1) ≤ 2.7` because `exp (π/2) ≤ 5` and `Real.pi_gt_three`. For `exp (π/2) ≤ 5`,
use `Real.exp_bound' (x := π/6) (n := 5)` (valid as `0 ≤ π/6 ≤ 1` and `Real.pi_lt_d2` gives
`π/6 ≤ 0.525`) to get `exp (π/6) ≤ 1 + 0.525 + 0.525²/2 + ... + 0.525^5·6/120 ≤ 1.6921`, and
`exp (π/2) = (exp (π/6))^3 ≤ 1.6921^3 ≤ 4.845`. -/
theorem norm_exp_sub_one_le_of_le_pi_half {z : ℂ} (hz : ‖z‖ ≤ Real.pi / 2) :
    ‖Complex.exp z - 1‖ ≤ (27 / 10) * ‖z‖ := by
  have h1 : ‖Complex.exp z - 1‖ ≤ Real.exp ‖z‖ - 1 := by
    simpa using Complex.norm_exp_sub_sum_le_exp_norm_sub_sum z 1
  have h2 : Real.exp ‖z‖ - 1 ≤ (27 / 10) * ‖z‖ := by
    have h := exp_sub_one_le_ratio_mul (norm_nonneg z) hz
    nlinarith [h, exp_ratio_le, norm_nonneg z]
  linarith

end Work.Pert
