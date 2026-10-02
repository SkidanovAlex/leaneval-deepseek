import Mathlib
import Submission.Work.Orient.Boundary

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# ORIENT: every point lies in a coordinate half-ball piece cut down to an open neighbourhood

The target

```
Work.Orient.exists_halfBallGood_piece n W z :
  ∃ r > 0, halfBallGood n W z r ∧ ∃ U open, z ∈ U ∧ U ⊆ halfBallPiece n W z r
```

is the "one point, open piece" form of the cover statement
`Work.Orient.Boundary.exists_halfBall_subset` of `Boundary/HalfCover.lean`: around every point `z` of
a space charted in the half-space model there is a coordinate half-ball `K = halfBallPiece n W z r`
with the side condition `halfBallGood n W z r`, and — this is the extra content here — an *open*
neighbourhood `U` of `z` contained in `K`.

The proof is the one used inside `HalfCover`: the open ball of radius `r/2` around the image of `z`
in the *ambient* Euclidean space is cut back to the half-space, and `z` lies in it; the chart
preimage of that (open) piece is the required open `U`, and it is contained in `K` because the open
ball is contained in the closed ball.

The only difference from `Boundary/HalfCover.lean` is the dimension index: that file states
everything for the model `𝓡∂ (n+1)` (the shape needed by `IsHalfOrientationFamily`), while the
present statement is about the model `𝓡∂ n` with `[NeZero n]`.  Rather than transporting along the
definitional (but not syntactically free) identification `(n - 1) + 1 = n`, the two tiny lemmas are
reproved here for the model `𝓡∂ n`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold

namespace Work.Orient

noncomputable section

/-- **Shrinking a neighbourhood of a point of the half-space to a ball.**  `EuclideanHalfSpace n`
carries no metric of its own; the ball is taken in the ambient space through
`Work.Orient.halfIncl n` (the closed embedding `𝓡∂ n`).  (The general-dimension form of
`Work.Orient.Boundary.exists_ball_subset_of_mem`, whose statement is specialised to `𝓡∂ (n+1)`.) -/
theorem exists_ball_subset_of_mem_halfIncl {n : ℕ} [NeZero n] {V : Set (EuclideanHalfSpace n)}
    (hV : IsOpen V) {c : EuclideanHalfSpace n} (hc : c ∈ V) :
    ∃ ρ : ℝ, 0 < ρ ∧ halfIncl n ⁻¹' Metric.ball (halfIncl n c) ρ ⊆ V := by
  obtain ⟨V', hV'open, hV'eq⟩ := isOpen_induced_iff.mp hV
  have hc' : (Subtype.val c : EuclideanSpace ℝ (Fin n)) ∈ V' := by
    have h := hc
    rw [← hV'eq] at h
    exact h
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp hV'open _ hc'
  exact ⟨ρ, hρ, fun y hy => by rw [← hV'eq]; exact hρsub hy⟩

/-- **A point lies in a coordinate half-ball piece with an open neighbourhood inside it.**  This is
the one-point form of `Work.Orient.Boundary.exists_halfBall_subset` (which is stated for the model
`𝓡∂ (n+1)`), *with* the additional content that the point has an open neighbourhood contained in the
piece: the chart preimage of the open half-ball of radius `r/2`, which is open because the chart is
an open partial homeomorphism. -/
theorem exists_halfBallGood_piece (n : ℕ) [NeZero n] (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace n) W] (z : W) :
    ∃ r : ℝ, 0 < r ∧ Work.Orient.halfBallGood n W z r ∧
      ∃ U : Set W, IsOpen U ∧ z ∈ U ∧ U ⊆ Work.Orient.halfBallPiece n W z r := by
  obtain ⟨ρ, hρ, hρsub⟩ :=
    exists_ball_subset_of_mem_halfIncl (n := n)
      (chartAt (EuclideanHalfSpace n) z).open_target
      ((chartAt (EuclideanHalfSpace n) z).map_source (mem_chart_source _ z))
  refine ⟨ρ, hρ, hρsub, ?_⟩
  refine ⟨(chartAt (EuclideanHalfSpace n) z).source ∩
      (chartAt (EuclideanHalfSpace n) z) ⁻¹'
        (halfIncl n ⁻¹'
          Metric.ball (halfIncl n ((chartAt (EuclideanHalfSpace n) z) z)) (ρ / 2)),
    ?_, ?_, ?_⟩
  · have hS : IsOpen (halfIncl n ⁻¹'
        Metric.ball (halfIncl n ((chartAt (EuclideanHalfSpace n) z) z)) (ρ / 2)) :=
      Metric.isOpen_ball.preimage continuous_subtype_val
    exact (chartAt (EuclideanHalfSpace n) z).isOpen_inter_preimage hS
  · exact ⟨mem_chart_source _ z, Metric.mem_ball_self (by linarith)⟩
  · intro y hy
    exact ⟨Metric.ball_subset_closedBall hy.2, hy.1⟩

end

end Work.Orient
