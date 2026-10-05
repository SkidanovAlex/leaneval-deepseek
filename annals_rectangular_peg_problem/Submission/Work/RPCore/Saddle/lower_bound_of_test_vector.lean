import Mathlib

namespace Work.RPCore.Saddle

/-- If a linear functional `T` is uniformly close to a "test function" `S` at a point `w`
of norm `≤ 1`, and `S w` is at least `a`, then the operator norm of `T` is at least `a - C`. -/
theorem lower_bound_of_test_vector {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (T : W →L[ℝ] ℝ) (S : W → ℝ) {a C : ℝ} (hC : 0 ≤ C) (w : W) (hw : ‖w‖ ≤ 1)
    (hw2 : a ≤ S w) (hdev : |T w - S w| ≤ C * ‖w‖) :
    a - C ≤ ‖T‖ := by
  -- `S w ≤ T w + C * ‖w‖`
  have hS : S w ≤ T w + C * ‖w‖ := by
    have h := neg_le_abs (T w - S w)
    linarith [h, hdev]
  -- `T w ≤ ‖T‖ * ‖w‖`
  have hT : T w ≤ ‖T‖ * ‖w‖ := by
    have h1 : T w ≤ ‖T w‖ := le_abs_self _
    have h2 : ‖T w‖ ≤ ‖T‖ * ‖w‖ := T.le_opNorm w
    linarith
  -- `‖T‖ * ‖w‖ ≤ ‖T‖`
  have hT1 : ‖T‖ * ‖w‖ ≤ ‖T‖ := by
    have h := mul_le_mul_of_nonneg_left hw (norm_nonneg T)
    simpa using h
  -- `C * ‖w‖ ≤ C`
  have hC1 : C * ‖w‖ ≤ C := by
    have h := mul_le_mul_of_nonneg_left hw hC
    simpa using h
  linarith

end Work.RPCore.Saddle
