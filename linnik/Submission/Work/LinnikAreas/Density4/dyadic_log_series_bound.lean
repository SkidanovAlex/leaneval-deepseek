import Mathlib
import Submission.Work.LinnikAreas.Density4.sum_range_inv_succ_sq_le_two

namespace Work.LinnikAreas.Density4

/-!
# A convergent dyadic logarithmic series

We bound the partial sums `∑_{j ≤ n} (log (2 + 2^j))⁻²` by the absolute constant `9`.

The key observations are:

* `log (2 + 2^j) ≥ log (2^j) = j * log 2` for `j ≥ 1`, while the `j = 0` term is
  `(log 3)⁻² ≤ (log 2)⁻²`;
* `∑_{k=1}^{n} 1 / k² ≤ 2` (see `sum_range_inv_succ_sq_le_two`);
* `log 2 > 0.693 > 1/√3`, so `3 (log 2)⁻² ≤ 9`.

Hence the whole sum is at most `(log 2)⁻² · 2 + (log 2)⁻² = 3 (log 2)⁻² ≤ 9`.
-/

/-- `x ^ (-2 : ℝ) = (x ^ 2)⁻¹` for `x > 0`. -/
lemma rpow_neg_two_eq_inv_sq {x : ℝ} (hx : 0 < x) : x ^ (-2 : ℝ) = (x ^ 2)⁻¹ := by
  rw [Real.rpow_neg (le_of_lt hx)]
  norm_num

theorem dyadic_log_series_bound (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), (Real.log (2 + (2 : ℝ) ^ j)) ^ (-2 : ℝ) ≤ 9 := by
  have hc : 0 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hc2inv : (Real.log 2) ^ (-2 : ℝ) = ((Real.log 2) ^ 2)⁻¹ := by
    rw [Real.rpow_neg (le_of_lt hc)]; norm_num
  -- Pointwise bound `(log (2 + 2^(j+1)))⁻² ≤ ((j+1) log 2)⁻²`.
  have hstep : ∀ j : ℕ,
      (Real.log (2 + (2 : ℝ) ^ (j+1))) ^ (-2 : ℝ)
        ≤ (((j+1:ℕ):ℝ) * Real.log 2) ^ (-2 : ℝ) := by
    intro j
    apply Real.rpow_le_rpow_of_nonpos
    · exact mul_pos (by positivity) hc
    · calc (((j+1:ℕ):ℝ) * Real.log 2) = Real.log ((2:ℝ)^(j+1)) := by rw [Real.log_pow]
        _ ≤ Real.log (2 + (2:ℝ)^(j+1)) := by
              apply Real.log_le_log (by positivity)
              linarith [show (0:ℝ) ≤ (2:ℝ)^(j+1) by positivity]
    · norm_num
  -- Bound the sum over the indices `j ≥ 1`.
  have htail : (∑ j ∈ Finset.range n, (Real.log (2 + (2:ℝ)^(j+1))) ^ (-2:ℝ))
      ≤ (Real.log 2) ^ (-2:ℝ) * 2 := by
    calc (∑ j ∈ Finset.range n, (Real.log (2 + (2:ℝ)^(j+1))) ^ (-2:ℝ))
        ≤ ∑ j ∈ Finset.range n, ((((j+1:ℕ):ℝ) * Real.log 2) ^ (-2:ℝ)) :=
          Finset.sum_le_sum (fun j _ => hstep j)
      _ = ∑ j ∈ Finset.range n, ((Real.log 2) ^ (-2:ℝ) * (((j+1:ℕ):ℝ)^2)⁻¹) := by
          apply Finset.sum_congr rfl
          intro j _
          calc ((((j+1:ℕ):ℝ) * Real.log 2) ^ (-2:ℝ))
              = ((((j+1:ℕ):ℝ) * Real.log 2)^2)⁻¹ := by
                rw [Real.rpow_neg (le_of_lt (mul_pos (by positivity) hc))]; norm_num
            _ = (((j+1:ℕ):ℝ)^2 * (Real.log 2)^2)⁻¹ := by rw [mul_pow]
            _ = (((j+1:ℕ):ℝ)^2)⁻¹ * ((Real.log 2)^2)⁻¹ := by rw [mul_inv]
            _ = ((Real.log 2)^2)⁻¹ * (((j+1:ℕ):ℝ)^2)⁻¹ := by rw [mul_comm]
            _ = (Real.log 2)^(-2:ℝ) * (((j+1:ℕ):ℝ)^2)⁻¹ := by rw [hc2inv]
      _ = (Real.log 2) ^ (-2:ℝ) * ∑ j ∈ Finset.range n, (((j+1:ℕ):ℝ)^2)⁻¹ := by
          rw [Finset.mul_sum]
      _ ≤ (Real.log 2) ^ (-2:ℝ) * 2 := by
          apply mul_le_mul_of_nonneg_left (sum_range_inv_succ_sq_le_two n)
          rw [hc2inv]; positivity
  -- The `j = 0` term.
  have hf0 : (Real.log (2 + (2:ℝ)^0)) ^ (-2:ℝ) ≤ (Real.log 2) ^ (-2:ℝ) := by
    refine Real.rpow_le_rpow_of_nonpos hc ?_ (by norm_num : (-2:ℝ) ≤ 0)
    apply Real.log_le_log (by norm_num)
    norm_num
  rw [Finset.sum_range_succ']
  calc (∑ j ∈ Finset.range n, (Real.log (2 + (2:ℝ)^(j+1))) ^ (-2:ℝ))
        + (Real.log (2 + (2:ℝ)^0)) ^ (-2:ℝ)
      ≤ (Real.log 2)^(-2:ℝ) * 2 + (Real.log 2)^(-2:ℝ) := add_le_add htail hf0
    _ = 3 * (Real.log 2)^(-2:ℝ) := by ring
    _ ≤ 9 := by
        rw [hc2inv]
        have hx : 0 < (Real.log 2)^2 := by positivity
        have h1 : ((Real.log 2)^2)⁻¹ ≤ 3 := by
          rw [inv_le_iff_one_le_mul₀ hx]
          nlinarith [Real.log_two_gt_d9]
        linarith

end Work.LinnikAreas.Density4
