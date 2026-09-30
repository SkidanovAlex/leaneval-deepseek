import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW.LiouvilleAux

/-- For a nonnegative real number `x`, `log⁺ (max x 1) = log⁺ x`. -/
private lemma posLog_max_one_eq {x : ℝ} (hx : 0 ≤ x) :
    Real.posLog (max x 1) = Real.posLog x := by
  rw [Real.posLog_eq_log_max_one (x := max x 1) (le_trans hx (le_max_left _ _)),
    Real.posLog_eq_log_max_one hx]
  congr 1
  simp [max_comm]

/-- At a finite place `v` of a number field, the nonarchimedean inequality
`v (a - 1) ≤ max (v a) 1` holds; consequently the positive part of the logarithm of
`v (a - 1)` is bounded by that of `v a`, since `log⁺` is monotone and `log⁺ 1 = 0`. -/
theorem posLog_sub_one_finite {K : Type*} [Field K] [NumberField K]
    (v : NumberField.FinitePlace K) (a : K) :
    Real.posLog (v (a - 1)) ≤ Real.posLog (v a) := by
  have hnonneg : 0 ≤ v a := apply_nonneg v a
  -- `v` is nonarchimedean, so `v (a - 1) = v (a + (-1)) ≤ max (v a) (v (-1)) = max (v a) 1`.
  have hle : v (a - 1) ≤ max (v a) 1 := by
    have h : a - 1 = a + (-1 : K) := by ring
    rw [h]
    refine (NumberField.FinitePlace.add_le v a (-1)).trans ?_
    simp
  calc Real.posLog (v (a - 1))
      ≤ Real.posLog (max (v a) 1) :=
        Real.posLog_le_posLog (by have := apply_nonneg v (a - 1); linarith) hle
    _ = Real.posLog (v a) := posLog_max_one_eq hnonneg

end Work.BW.LiouvilleAux
