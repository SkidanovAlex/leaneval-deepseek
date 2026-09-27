import Mathlib

namespace Work.EQ

open Filter Metric Set
open scoped Topology

/-- A function which is analytic on a punctured disc around `0` and bounded there is meromorphic
at `0` (Riemann's removable singularity theorem, in the `MeromorphicAt` formulation of Mathlib).

Proof: `Complex.differentiableOn_update_limUnder_of_bddAbove` applied to the ball
`Metric.ball 0 r` (a neighbourhood of `0`) shows that `Function.update f 0 L`, where
`L = limUnder (𝓝[≠] 0) f`, is complex differentiable on the whole ball; hence it is analytic at
`0` (`DifferentiableOn.analyticAt`), therefore meromorphic at `0`
(`AnalyticAt.meromorphicAt`).  Finally `Function.update f 0 L` agrees with `f` on the punctured
ball, which is a punctured neighbourhood of `0`, so `MeromorphicAt.congr` gives
`MeromorphicAt f 0`. -/
theorem meromorphicAt_punctured_bounded {f : ℂ → ℂ} {r C : ℝ} (hr : 0 < r)
    (han : AnalyticOnNhd ℂ f (Metric.ball (0 : ℂ) r \ {0}))
    (hb : ∀ z ∈ Metric.ball (0 : ℂ) r \ {0}, ‖f z‖ ≤ C) :
    MeromorphicAt f 0 := by
  -- the punctured ball is a punctured neighbourhood of `0`
  have hmem : Metric.ball (0 : ℂ) r \ {0} ∈ 𝓝[≠] (0 : ℂ) := by
    have h1 : Metric.ball (0 : ℂ) r ∈ 𝓝[≠] (0 : ℂ) :=
      nhdsWithin_le_nhds (Metric.ball_mem_nhds 0 hr)
    have h2 : ({0} : Set ℂ)ᶜ ∈ 𝓝[≠] (0 : ℂ) := self_mem_nhdsWithin
    exact Filter.mem_of_superset (Filter.inter_mem h1 h2) (fun z hz => hz)
  -- `f` is bounded on the punctured ball
  have hbdd : BddAbove (norm ∘ f '' (Metric.ball (0 : ℂ) r \ {0})) :=
    ⟨C, fun y hy => by
      rcases hy with ⟨z, hz, rfl⟩
      exact hb z hz⟩
  -- Riemann's removable singularity theorem: the updated function is differentiable on the ball
  have hdo := Complex.differentiableOn_update_limUnder_of_bddAbove
    (Metric.ball_mem_nhds (0 : ℂ) hr) han.differentiableOn hbdd
  have hanal : AnalyticAt ℂ (Function.update f 0 ((𝓝[≠] (0 : ℂ)).limUnder f)) 0 :=
    hdo.analyticAt (Metric.ball_mem_nhds (0 : ℂ) hr)
  refine MeromorphicAt.congr (AnalyticAt.meromorphicAt hanal) ?_
  filter_upwards [hmem] with z hz
  exact Function.update_of_ne hz.2 _ _

end Work.EQ
