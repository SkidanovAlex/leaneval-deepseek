import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseKinLoc.Momentum

/-- If `‖q‖ > L` then some coordinate of `q` exceeds `L/√3` in absolute value:
otherwise all `|q i| ≤ L/√3` and the sum-of-squares identity
`‖q‖² = ∑ i, |q i|²` would give `‖q‖² ≤ 3·(L/√3)² = L²`. -/
theorem exterior_coord_gt (L : ℝ) (hL : 0 < L) (q : EuclideanSpace ℝ (Fin 3)) (hq : L < ‖q‖) :
    ∃ i : Fin 3, L / Real.sqrt 3 < |q i| := by
  by_contra h
  push_neg at h
  have hsq := EuclideanSpace.norm_sq_eq q
  have hsum : (∑ i : Fin 3, ‖q i‖ ^ 2) ≤ ∑ _i : Fin 3, (L / Real.sqrt 3) ^ 2 := by
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2
  have h3 : (∑ _i : Fin 3, (L / Real.sqrt 3) ^ 2) = L ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
    ring
  have hlt : L ^ 2 < ‖q‖ ^ 2 := by nlinarith [hq, norm_nonneg q, hL]
  rw [hsq] at hlt
  linarith

end Work.BoseKinLoc.Momentum
