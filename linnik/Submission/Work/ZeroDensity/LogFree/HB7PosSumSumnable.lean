import Mathlib

namespace Work.ZeroDensity.LogFree

/-- `min 1 (exp ((c - n) * L))` is summable in `n : ℕ` for any `L > 0`:
it is dominated by the geometric series `exp (c * L) * (exp (-L)) ^ n`. -/
theorem HB7PosSumSumnable (c L : ℝ) (hL : 0 < L) :
    Summable (fun n : ℕ => min 1 (Real.exp ((c - (n : ℝ)) * L))) := by
  have hr : ‖Real.exp (-L)‖ < 1 := by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_lt_one_iff]
    linarith
  have hgeom : Summable (fun n : ℕ => Real.exp (-L) ^ n) :=
    summable_geometric_of_norm_lt_one hr
  have hf : Summable (fun n : ℕ => Real.exp (c * L) * Real.exp (-L) ^ n) :=
    Summable.mul_left (Real.exp (c * L)) hgeom
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hf
  · exact le_min (by norm_num) (Real.exp_pos _).le
  · have heq : Real.exp ((c - (n : ℝ)) * L) = Real.exp (c * L) * Real.exp (-L) ^ n := by
      have h : (c - (n : ℝ)) * L = c * L + (n : ℝ) * (-L) := by ring
      rw [h, Real.exp_add, Real.exp_nat_mul]
    exact (min_le_right 1 _).trans (le_of_eq heq)

end Work.ZeroDensity.LogFree
