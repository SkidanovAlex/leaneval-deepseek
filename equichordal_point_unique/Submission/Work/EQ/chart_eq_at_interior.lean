import Mathlib
import Submission.Work.EQ.EquiLocalDefs

namespace Work.EQ

open Filter _root_.Topology

/-- **The chart formula and continuity at an interior point of the punctured disc.**  For chart
data `E` with centre `w`, coefficient `κ` and exponent `k` (`IsChartData`), and any `z ≠ 0` with
`‖z‖ < 1`: the `ψ₁`-value of `E z` is `w + κ z ^ k` and `E` is continuous at `z` (its domain
`ball 0 1 \ {0}` is open). -/
theorem chart_eq_at_interior {a : ℝ} {h : ℂ → ℂ} {E : ℂ → ChainData} {w κ : ℂ} {k : ℕ}
    (hE : IsChartData a h E w κ k) {z : ℂ} (hz : z ≠ 0) (hz1 : ‖z‖ < 1) :
    (E z).2.1 = w + κ * z ^ k ∧ ContinuousAt E z := by
  obtain ⟨-, -, hval, -, hcont⟩ := hE
  have hzball : z ∈ Metric.ball (0 : ℂ) 1 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hz1
  have hzmem : z ∈ Metric.ball (0 : ℂ) 1 \ {0} := by
    refine ⟨hzball, ?_⟩
    simpa using hz
  refine ⟨(hval z hzmem).2, ?_⟩
  have hnhds : Metric.ball (0 : ℂ) 1 \ {0} ∈ 𝓝 z := by
    have h1 : Metric.ball (0 : ℂ) 1 ∈ 𝓝 z := Metric.isOpen_ball.mem_nhds hzball
    have h2 : ({0}ᶜ : Set ℂ) ∈ 𝓝 z :=
      isOpen_compl_singleton.mem_nhds (by simpa using hz)
    have hset : Metric.ball (0 : ℂ) 1 \ {0} = Metric.ball (0 : ℂ) 1 ∩ {0}ᶜ := by
      ext x; simp
    rw [hset]
    exact Filter.inter_mem h1 h2
  exact hcont.continuousAt hnhds

end Work.EQ
