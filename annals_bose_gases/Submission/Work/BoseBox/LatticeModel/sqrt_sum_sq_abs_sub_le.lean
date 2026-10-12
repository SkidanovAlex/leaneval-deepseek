import Mathlib.Analysis.InnerProductSpace.PiL2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBox.LatticeModel

/-- If two points of `ℝ³` differ by at most `h/2` in every coordinate, then their
Euclidean norms differ by at most `h √3 / 2`. This is the triangle inequality
`|‖x‖ - ‖c‖| ≤ ‖x - c‖` combined with the coordinatewise bound. -/
theorem sqrt_sum_sq_abs_sub_le {x c : Fin 3 → ℝ} {h : ℝ} (hh : 0 ≤ h)
    (hcoord : ∀ j : Fin 3, |x j - c j| ≤ h / 2) :
    |Real.sqrt (∑ j : Fin 3, x j ^ 2) - Real.sqrt (∑ j : Fin 3, c j ^ 2)|
      ≤ h * Real.sqrt 3 / 2 := by
  -- Identify the sums of squares with Euclidean norms.
  have hnormx : ‖((EuclideanSpace.equiv (Fin 3) ℝ).symm x)‖
      = Real.sqrt (∑ j : Fin 3, x j ^ 2) := by
    rw [EuclideanSpace.norm_eq]; simp
  have hnormc : ‖((EuclideanSpace.equiv (Fin 3) ℝ).symm c)‖
      = Real.sqrt (∑ j : Fin 3, c j ^ 2) := by
    rw [EuclideanSpace.norm_eq]; simp
  have hnormd : ‖((EuclideanSpace.equiv (Fin 3) ℝ).symm x)
        - ((EuclideanSpace.equiv (Fin 3) ℝ).symm c)‖
      = Real.sqrt (∑ j : Fin 3, (x j - c j) ^ 2) := by
    rw [show ((EuclideanSpace.equiv (Fin 3) ℝ).symm x)
          - ((EuclideanSpace.equiv (Fin 3) ℝ).symm c)
          = ((EuclideanSpace.equiv (Fin 3) ℝ).symm (x - c)) from by simp]
    rw [EuclideanSpace.norm_eq]; simp
  rw [← hnormx, ← hnormc]
  refine le_trans (abs_norm_sub_norm_le _ _) ?_
  rw [hnormd]
  -- Bound the difference vector coordinatewise.
  have hd : (∑ j : Fin 3, (x j - c j) ^ 2) ≤ 3 * (h / 2) ^ 2 := by
    calc (∑ j : Fin 3, (x j - c j) ^ 2) ≤ ∑ _j : Fin 3, (h / 2) ^ 2 := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [← sq_abs (x j - c j)]
          exact pow_le_pow_left₀ (abs_nonneg _) (hcoord j) 2
      _ = 3 * (h / 2) ^ 2 := by simp [Finset.sum_const]
  have hval : Real.sqrt (3 * (h / 2) ^ 2) = h * Real.sqrt 3 / 2 := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_sq_eq_abs,
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ h / 2)]
    ring
  calc Real.sqrt (∑ j : Fin 3, (x j - c j) ^ 2)
      ≤ Real.sqrt (3 * (h / 2) ^ 2) := Real.sqrt_le_sqrt hd
    _ = h * Real.sqrt 3 / 2 := hval

end Work.BoseBox.LatticeModel
