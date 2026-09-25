import Mathlib

set_option linter.style.haveILetI false

open scoped NNReal

namespace Work.NN.Newton

/-- Banach fixed point theorem on a closed ball: a self-map of the closed ball of radius
`ρ ≥ 0` that is `1/2`-Lipschitz has a fixed point in the ball. -/
theorem closedBallContraction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {ρ : ℝ} (hρ : 0 ≤ ρ) {T : E → E}
    (hmaps : ∀ x ∈ Metric.closedBall (0 : E) ρ, T x ∈ Metric.closedBall (0 : E) ρ)
    (hcontr : ∀ x ∈ Metric.closedBall (0 : E) ρ, ∀ y ∈ Metric.closedBall (0 : E) ρ,
      ‖T x - T y‖ ≤ (1 / 2) * ‖x - y‖) :
    ∃ z ∈ Metric.closedBall (0 : E) ρ, T z = z := by
  -- the closed ball is nonempty and complete
  have hmem0 : (0 : E) ∈ Metric.closedBall (0 : E) ρ := by
    rw [Metric.mem_closedBall, dist_self]; exact hρ
  haveI : Nonempty (Metric.closedBall (0 : E) ρ) := ⟨⟨0, hmem0⟩⟩
  haveI : CompleteSpace (Metric.closedBall (0 : E) ρ) :=
    completeSpace_coe_iff_isComplete.2 (Metric.isClosed_closedBall.isComplete)
  -- restrict the map to the ball
  let f : Metric.closedBall (0 : E) ρ → Metric.closedBall (0 : E) ρ :=
    fun x => ⟨T x.1, hmaps x.1 x.2⟩
  have hf : ContractingWith (1/2 : ℝ≥0) f := by
    refine ⟨by norm_num, ?_⟩
    refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    have h := hcontr x.1 x.2 y.1 y.2
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    have h1 : ((1/2 : ℝ≥0) : ℝ) = 1/2 := by norm_num
    rw [h1]
    exact h
  -- extract the fixed point of the restriction
  let z : Metric.closedBall (0 : E) ρ := ContractingWith.fixedPoint f hf
  have hzf : f z = z := ContractingWith.fixedPoint_isFixedPt (f := f) hf
  refine ⟨(z : E), z.2, ?_⟩
  have h2 := congrArg Subtype.val hzf
  simpa [f] using h2

end Work.NN.Newton
