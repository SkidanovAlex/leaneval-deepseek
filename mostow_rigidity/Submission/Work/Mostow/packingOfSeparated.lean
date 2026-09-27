import Mathlib
import Submission.Work.Mostow.pigeonhole_totBounded

namespace Work.Mostow

/-- **Packing bound.** In a finite-dimensional real normed space, a `θ`-separated subset of the
closed unit ball has uniformly bounded cardinality: there is a single `N` (depending only on the
space and on `θ > 0`) bounding `S.ncard` for every such `S`.

This is the metric packing/covering statement used to recognise finite orbit sets: transport the
compactness of the closed unit ball into a finite `θ/2`-cover and count cells. -/
theorem packingOfSeparated {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] {θ : ℝ} (hθ : 0 < θ) :
    ∃ N : ℕ, ∀ S : Set X, (∀ x ∈ S, ‖x‖ ≤ 1) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → θ ≤ ‖x - y‖) → S.ncard ≤ N := by
  classical
  -- The closed unit ball is compact, hence totally bounded.
  have hK : TotallyBounded (Metric.closedBall (0 : X) (1 : ℝ)) :=
    (isCompact_closedBall (0 : X) (1 : ℝ)).totallyBounded
  -- Pigeonhole at scale `θ/2`: strictly fewer than `N` cells means two points closer than `θ`.
  obtain ⟨N, hN⟩ := pigeonhole_totBounded hK (show (0 : ℝ) < θ / 2 by linarith)
  refine ⟨N, fun S hSnorm hSsep => ?_⟩
  by_cases hfin : S.Finite
  · -- If `S` had more than `N` points, two of them would be closer than `θ`.
    by_contra hcon
    rw [not_le] at hcon
    have hSsub : S ⊆ Metric.closedBall (0 : X) (1 : ℝ) := by
      intro x hx
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hSnorm x hx
    obtain ⟨x, hx, y, hy, hxy, hd⟩ := hN S hfin hSsub hcon
    have hsep := hSsep x hx y hy hxy
    rw [dist_eq_norm] at hd
    linarith
  · -- An infinite `S` has `ncard = 0`.
    rw [Set.Infinite.ncard hfin]
    exact Nat.zero_le N

end Work.Mostow
