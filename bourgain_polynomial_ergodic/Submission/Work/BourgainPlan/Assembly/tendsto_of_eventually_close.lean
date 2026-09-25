import Mathlib

namespace Work.BourgainPlan.Assembly

/-- A real sequence whose tails have arbitrarily small diameter (diameter `≤ 1/(m+1)` for
every `m`) converges to a real limit. -/
theorem tendsto_of_eventually_close (a : ℕ → ℝ)
    (h : ∀ m : ℕ, ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j → |a i - a j| ≤ 1 / ((m : ℝ) + 1)) :
    ∃ L : ℝ, Filter.Tendsto a Filter.atTop (nhds L) := by
  apply cauchySeq_tendsto_of_complete
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN⟩ := h m
  exact ⟨N, fun i hi j hj => by
    rw [Real.dist_eq]
    exact lt_of_le_of_lt (hN i j hi hj) hm⟩

end Work.BourgainPlan.Assembly
