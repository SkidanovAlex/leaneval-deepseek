import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5G

lemma continuousOn_of_pointwise_of_equiholder {f : ℕ → ℝ × ℝ → ℝ} {Φ : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hpt : ∀ q ∈ U, Filter.Tendsto (fun n => f n q) Filter.atTop (nhds (Φ q))) (hequi : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ U → ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ p ∈ K, ∀ q ∈ K, dist (f n p) (f n q) ≤ C * dist p q ^ (1 / 2 : ℝ)) : ContinuousOn Φ U := by
  -- It suffices to prove that `Φ` is continuous at every point of `U`; for such a point we
  -- apply the equi-Hölder bound on a closed ball around it, which is compact and contained in `U`.
  have hcont : ∀ x ∈ U, ContinuousAt Φ x := by
    intro x hx
    obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
    have hKU : Metric.closedBall x (r/2) ⊆ U :=
      fun y hy => hrU (Metric.closedBall_subset_ball (by linarith) hy)
    obtain ⟨C, hC0, hC⟩ := hequi _ (isCompact_closedBall x (r/2)) hKU
    have hxK : x ∈ Metric.closedBall x (r/2) := by
      rw [Metric.mem_closedBall, dist_self]; linarith
    -- the Hölder bound passes to the limit `n → ∞` on the compact ball
    have hbound : ∀ y ∈ Metric.closedBall x (r/2),
        dist (Φ y) (Φ x) ≤ C * dist y x ^ (1/2 : ℝ) := by
      intro y hy
      exact le_of_tendsto ((hpt y (hKU hy)).dist (hpt x hx))
        (Filter.Eventually.of_forall (fun n => hC n y hy x hxK))
    rw [Metric.continuousAt_iff]
    intro ε hε
    -- a `≤ η` version of continuity, upgraded to `< ε` by taking `η = ε/2`
    have key : ∀ η > 0, ∃ δ > 0, ∀ y, dist y x < δ → dist (Φ y) (Φ x) ≤ η := by
      intro η hη
      have hC1 : (0:ℝ) < C + 1 := by linarith
      have hpos : 0 < η / (C + 1) := div_pos hη hC1
      refine ⟨min (r/2) ((η/(C+1))^2), lt_min (by linarith) (pow_pos hpos 2), ?_⟩
      intro y hy
      have hyK : y ∈ Metric.closedBall x (r/2) := by
        rw [Metric.mem_closedBall]
        exact le_of_lt (lt_of_lt_of_le hy (min_le_left _ _))
      have h1 := hbound y hyK
      have ht : dist y x < (η/(C+1))^2 := lt_of_lt_of_le hy (min_le_right _ _)
      have hs : Real.sqrt (dist y x) < η/(C+1) := (Real.sqrt_lt' hpos).mpr ht
      rw [show dist y x ^ (1/2:ℝ) = Real.sqrt (dist y x) from (Real.sqrt_eq_rpow _).symm] at h1
      calc dist (Φ y) (Φ x) ≤ C * Real.sqrt (dist y x) := h1
        _ ≤ C * (η/(C+1)) := mul_le_mul_of_nonneg_left hs.le hC0
        _ ≤ η := by
            rw [mul_div_assoc', div_le_iff₀ hC1]
            nlinarith [hη.le, hC0]
    obtain ⟨δ, hδ, hδb⟩ := key (ε/2) (by linarith)
    exact ⟨δ, hδ, fun y hy => lt_of_le_of_lt (hδb y hy) (by linarith)⟩
  exact fun x hx => (hcont x hx).continuousWithinAt

end Work.FTS.StrongEps.E5G
