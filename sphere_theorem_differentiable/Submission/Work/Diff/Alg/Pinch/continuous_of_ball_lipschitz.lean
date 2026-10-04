import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Local Lipschitz bounds on balls imply continuity

If a self-map `Q` of a real normed space satisfies, on every ball of radius `M` about the origin,
a Lipschitz bound `‖Q R - Q S‖ ≤ C * ‖R - S‖` (with `C` allowed to depend on `M`), then `Q` is
continuous. This is used to obtain continuity of Hamilton's reaction term `Q` on curvature
operators from the local Lipschitz estimate `Q_lipschitz_local`.

The constant `C` is not assumed nonnegative, so we replace it by `K = max C 0`; the estimate is
then a genuine Lipschitz bound on the ball and gives an explicit `ε`-`δ` modulus of continuity.
-/

namespace Work.Diff.Alg.Pinch

theorem continuous_of_ball_lipschitz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Q : E → E}
    (hLip : ∀ M : ℝ, ∃ C : ℝ, ∀ R S : E, ‖R‖ ≤ M → ‖S‖ ≤ M → ‖Q R - Q S‖ ≤ C * ‖R - S‖) :
    Continuous Q := by
  rw [continuous_iff_continuousAt]
  intro x
  -- a Lipschitz constant valid on the ball of radius `‖x‖ + 1` around the origin
  obtain ⟨C, hC⟩ := hLip (‖x‖ + 1)
  set K : ℝ := max C 0 with hKD
  have hK0 : 0 ≤ K := le_max_right C 0
  have hKle : C ≤ K := le_max_left C 0
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hden : (0 : ℝ) < K + 1 := by linarith
  -- `δ = min 1/2 (ε/(K+1))`: small enough that `y` stays in the ball, and `K·δ < ε`.
  refine ⟨min (1 / 2) (ε / (K + 1)), lt_min (by norm_num) (div_pos hε hden), ?_⟩
  intro y hyx
  have hynorm : ‖y‖ ≤ ‖x‖ + 1 := by
    have h1 : ‖y‖ ≤ ‖x‖ + ‖y - x‖ := by
      have h := norm_add_le x (y - x)
      rwa [add_sub_cancel] at h
    have h2 : ‖y - x‖ < 1 / 2 := by
      rw [← dist_eq_norm]
      exact lt_of_lt_of_le hyx (min_le_left _ _)
    linarith
  have hxnorm : ‖x‖ ≤ ‖x‖ + 1 := by linarith
  have hmain : ‖Q y - Q x‖ ≤ C * ‖y - x‖ := hC y x hynorm hxnorm
  have hstep1 : C * ‖y - x‖ ≤ K * ‖y - x‖ :=
    mul_le_mul_of_nonneg_right hKle (norm_nonneg _)
  have hdn : ‖y - x‖ ≤ ε / (K + 1) := by
    rw [← dist_eq_norm]
    exact le_trans (le_of_lt hyx) (min_le_right _ _)
  have hstep2 : K * ‖y - x‖ ≤ K * (ε / (K + 1)) :=
    mul_le_mul_of_nonneg_left hdn hK0
  have hlt : K * (ε / (K + 1)) < ε := by
    have hq : K / (K + 1) < 1 := (div_lt_one hden).mpr (by linarith)
    have h2 : ε * (K / (K + 1)) < ε * 1 := mul_lt_mul_of_pos_left hq hε
    have h3 : K * (ε / (K + 1)) = ε * (K / (K + 1)) := by ring
    linarith [h2]
  have hfin : dist (Q y) (Q x) ≤ K * (ε / (K + 1)) := by
    rw [dist_eq_norm]
    exact le_trans hmain (le_trans hstep1 hstep2)
  linarith [hfin, hlt]

end Work.Diff.Alg.Pinch
