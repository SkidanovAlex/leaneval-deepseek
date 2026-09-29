import Mathlib

namespace Work.A14D

theorem summable_add_one_pow_mul_geometric (j : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ j * s ^ n) := by
  have hs : ‖s‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hs0]; exact hs1
  refine (summable_sum (f := fun i n : ℕ => (j.choose i : ℝ) * ((n : ℝ) ^ i * s ^ n))
    (s := Finset.range (j + 1)) (fun i _ => ?_)).congr (fun n => ?_)
  · exact (summable_pow_mul_geometric_of_norm_lt_one i hs).mul_left _
  · rw [add_pow]
    simp only [one_pow, mul_one]
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring

end Work.A14D
