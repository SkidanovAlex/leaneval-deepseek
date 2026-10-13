import Mathlib

namespace Work.WilE4.CAD

/-- If a predicate fails frequently near a point of a pseudo-metric space, there is a sequence
converging to that point along which it fails. -/
theorem seq_extract {α : Type*} [PseudoMetricSpace α] {x₀ : α} {P : α → Prop}
    (h : ¬ ∀ᶠ x in nhds x₀, P x) :
    ∃ u : ℕ → α, Filter.Tendsto u Filter.atTop (nhds x₀) ∧ ∀ n, ¬ P (u n) := by
  -- For every `n` there is a witness inside the ball of radius `1/(n+1)` on which `P` fails;
  -- otherwise `P` would hold on such a ball, hence eventually near `x₀`.
  have key : ∀ n : ℕ, ∃ y : α, dist y x₀ < (1 : ℝ) / (n + 1) ∧ ¬ P y := by
    intro n
    by_contra hc
    push Not at hc
    exact h (by
      filter_upwards [Metric.ball_mem_nhds x₀ (by positivity : (0 : ℝ) < 1 / (n + 1))]
        with y hy
      exact hc y hy)
  choose u hu using key
  refine ⟨u, ?_, fun n => (hu n).2⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  refine ⟨N, fun n hn => ?_⟩
  have hle : (1 : ℝ) / (n + 1) ≤ (1 : ℝ) / (N + 1) := by
    apply one_div_le_one_div_of_le
    · positivity
    · have : (N : ℝ) ≤ n := Nat.cast_le.mpr hn
      linarith
  calc dist (u n) x₀ < (1 : ℝ) / (n + 1) := (hu n).1
    _ ≤ (1 : ℝ) / (N + 1) := hle
    _ < ε := hN

end Work.WilE4.CAD
