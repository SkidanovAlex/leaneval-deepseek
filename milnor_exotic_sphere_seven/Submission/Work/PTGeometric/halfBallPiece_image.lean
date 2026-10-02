import Mathlib
import Submission.Work.Orient.Boundary

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.PTGeometric

theorem halfBallPiece_image (n : ℕ) (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W] (z : W) (r : ℝ) (hr : 0 < r)
    (hgood : Work.Orient.halfBallGood (n + 1) W z r) :
    ((extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) z) ''
        (Work.Orient.halfBallPiece (n + 1) W z r)
      ⊆ Metric.closedBall ((extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) z) z) (r / 2)
        ∩ Set.range (modelWithCornersEuclideanHalfSpace (n + 1))) ∧
    (Metric.closedBall ((extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) z) z) (r / 2)
        ∩ Set.range (modelWithCornersEuclideanHalfSpace (n + 1)))
      ⊆ (extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) z).target ∧
    IsCompact (Metric.closedBall ((extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) z) z)
        (r / 2) ∩ Set.range (modelWithCornersEuclideanHalfSpace (n + 1))) := by
  -- Write `H := EuclideanHalfSpace (n+1)`, `I := 𝓡∂ (n+1)` and `ch := chartAt H z`.
  -- The extended chart is `e = ch.extend I`, i.e. `e w = I (ch w)`.
  let I := modelWithCornersEuclideanHalfSpace (n + 1)
  let ch := chartAt (EuclideanHalfSpace (n + 1)) z
  let e := extChartAt I z
  have hmem : ∀ w : W, e w = I (ch w) := fun w => rfl
  -- `halfBallGood` says exactly that the open `I`-ball of radius `r` around `I (ch z)` sits
  -- inside the chart target.
  have hgood' : I ⁻¹' Metric.ball (I (ch z)) r ⊆ ch.target := hgood
  refine ⟨?_, ?_, ?_⟩
  · -- An element of the image is `e w` with `w` in the piece; by definition
    -- `I (ch w) ∈ closedBall (I (ch z)) (r/2)`, and every `e w` lies in the range of `I`.
    rintro y ⟨w, hw, rfl⟩
    obtain ⟨hw1, hw2⟩ := hw
    refine ⟨?_, ?_⟩
    · show dist (e w) (e z) ≤ r / 2
      rw [hmem w, hmem z]
      exact Metric.mem_closedBall.mp hw1
    · exact ⟨ch w, (hmem w).symm⟩
  · -- The closed `I`-ball of radius `r/2` lies in the open `I`-ball of radius `r`, hence its
    -- `I`-preimage lies in the chart target; and `e.target = I '' ch.target`.
    intro y hy
    obtain ⟨hy1, hy2⟩ := hy
    obtain ⟨x, hx⟩ := hy2
    have hxb : I x ∈ Metric.ball (I (ch z)) r := by
      rw [Metric.mem_ball]
      rw [hx, ← hmem z]
      have := Metric.mem_closedBall.mp hy1
      linarith
    have hxt : x ∈ ch.target := hgood' hxb
    have htarget : e.target = I '' ch.target := OpenPartialHomeomorph.extend_target' ch
    rw [htarget]
    exact ⟨x, hxt, hx⟩
  · -- A closed ball in a proper space is compact and `range I` is closed.
    exact (isCompact_closedBall (e z) (r / 2)).inter_right I.isClosedEmbedding.isClosed_range

end Work.PTGeometric
