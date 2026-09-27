import Mathlib

namespace Work.EKLComp

theorem summable_exp_neg :
    Summable (fun i : ℕ => Real.exp (-(i : ℝ))) ∧
      (∑' i : ℕ, Real.exp (-(i : ℝ))) ≤ 2 ∧
      Summable (fun i : ℕ => (i : ℝ) * Real.exp (-(i : ℝ))) := by
  -- Rewrite the exponential sequence as a geometric sequence with ratio `exp (-1)`.
  have hpow : ∀ i : ℕ, Real.exp (-(i : ℝ)) = (Real.exp (-1)) ^ i := by
    intro i
    simpa using Real.exp_nat_mul (-1) i
  have hr_pos : 0 < Real.exp (-1) := Real.exp_pos _
  have hr_lt : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hnorm : ‖Real.exp (-1)‖ < 1 := by
    rwa [Real.norm_eq_abs, abs_of_pos hr_pos]
  -- `exp (-1) ≤ 1/2` since `exp 1 > 2`.
  have hr_le : Real.exp (-1) ≤ 1 / 2 := by
    have h := (inv_le_inv₀ (Real.exp_pos 1) (by norm_num : (0 : ℝ) < 2)).mpr
      (le_of_lt Real.exp_one_gt_two)
    rw [Real.exp_neg]
    simpa using h
  have hsum_exp : Summable (fun i : ℕ => Real.exp (-(i : ℝ))) :=
    (summable_geometric_of_norm_lt_one hnorm).congr (fun i => (hpow i).symm)
  have hsum_half : Summable (fun i : ℕ => (1 / 2 : ℝ) ^ i) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  have hsum_mul : Summable (fun i : ℕ => (i : ℝ) * Real.exp (-(i : ℝ))) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).summable.congr
      (fun i => by rw [hpow i])
  refine ⟨hsum_exp, ?_, hsum_mul⟩
  calc (∑' i : ℕ, Real.exp (-(i : ℝ)))
      ≤ ∑' i : ℕ, (1 / 2 : ℝ) ^ i :=
        Summable.tsum_le_tsum
          (fun i => by rw [hpow i]; exact pow_le_pow_left₀ hr_pos.le hr_le i)
          hsum_exp hsum_half
    _ = 2 := by
        rw [tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)]
        norm_num

end Work.EKLComp
