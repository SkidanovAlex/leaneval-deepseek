import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.MetricSpace.Infsep

namespace Commons.Topology.Metric

/-- In a metric space, a finite set of points is uniformly discrete: there is a positive `δ` such
that any two distinct points of the set are at distance at least `δ`.

(For a set with at most one point the condition is vacuous and any positive `δ` works; the interesting
case uses the infimum separation `Set.infsep`.) -/
theorem exists_pos_le_dist_of_finite {X : Type*} [MetricSpace X] {s : Set X} (hs : s.Finite) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ dist x y := by
  classical
  by_cases h : s.Subsingleton
  · exact ⟨1, one_pos, fun x hx y hy hxy => absurd (h hx hy) hxy⟩
  · have hnt : s.Nontrivial := Set.not_subsingleton_iff.mp h
    refine ⟨s.infsep, ?_, fun x hx y hy hxy => Set.infsep_le_dist_of_mem hx hy hxy⟩
    rw [Set.infsep_pos]
    exact ⟨hs.einfsep_pos, hnt.einfsep_ne_top.lt_top⟩

/-- Given a finite set `s` in a metric space and, for each `z ∈ s`, an open neighbourhood `O z` of
`z`, one can choose positive radii `r z` so that the balls `ball z (r z)` are contained in `O z` and
are pairwise disjoint for distinct points of `s`. -/
theorem exists_pairwiseDisjoint_ball_subset {X : Type*} [MetricSpace X]
    {s : Set X} (hs : s.Finite) (O : s → Set X) (hO : ∀ z : s, IsOpen (O z))
    (hz : ∀ z : s, (z : X) ∈ O z) :
    ∃ r : s → ℝ, (∀ z : s, 0 < r z) ∧ (∀ z : s, Metric.ball (z : X) (r z) ⊆ O z) ∧
      (∀ z z' : s, z ≠ z' → Disjoint (Metric.ball (z : X) (r z)) (Metric.ball (z' : X) (r z'))) := by
  classical
  -- a positive uniform separation of the points of `s`
  obtain ⟨δ, hδpos, hδ⟩ := exists_pos_le_dist_of_finite hs
  -- each point of `s` has a ball around it contained in its open neighbourhood
  have hε : ∀ z : s, ∃ ε : ℝ, 0 < ε ∧ Metric.ball (z : X) ε ⊆ O z :=
    fun z => (Metric.isOpen_iff.mp (hO z)) (z : X) (hz z)
  choose ε hεpos hεsub using hε
  -- shrink every radius to `min ε (δ/2)`
  refine ⟨fun z => min (ε z) (δ / 2), fun z => lt_min (hεpos z) (half_pos hδpos), ?_, ?_⟩
  · intro z
    exact subset_trans (Metric.ball_subset_ball (min_le_left _ _)) (hεsub z)
  · intro z z' hne
    rw [Set.disjoint_left]
    intro x hx hx'
    have hxz : dist x (z : X) < δ / 2 :=
      lt_of_lt_of_le (Metric.mem_ball.mp hx) (min_le_right _ _)
    have hxz' : dist x (z' : X) < δ / 2 :=
      lt_of_lt_of_le (Metric.mem_ball.mp hx') (min_le_right _ _)
    have hle : δ ≤ dist (z : X) (z' : X) :=
      hδ (z : X) z.2 (z' : X) z'.2 (fun h => hne (Subtype.ext h))
    have htri : dist (z : X) (z' : X) ≤ dist (z : X) x + dist x (z' : X) := dist_triangle _ _ _
    have hcomm : dist (z : X) x = dist x (z : X) := dist_comm _ _
    linarith

end Commons.Topology.Metric