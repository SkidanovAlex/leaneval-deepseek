import Mathlib
import Submission.Work.Smooth.JordanSeparation.isPreconnected_frontier_connectedComponentIn

/-!
# The frontier of a complementary domain of a compact connected set

For a closed set `K ⊆ ℂ` the frontier of a connected component `C` of `Kᶜ` is `closure C ∩ K`; if
in addition `K` is compact, connected and non-empty then that frontier is a non-empty continuum
(Wilder's "Brouwer property"; the connectedness half is
`Work.Smooth.JordanSeparation.isPreconnected_frontier_connectedComponentIn`).

* `frontier_connectedComponentIn_eq`;
* `frontier_component_continuum`.
-/

open Set Metric

namespace Work.Smooth.JordanSeparation

noncomputable section

/-- **The frontier of a complementary domain lies on the curve.**  For a closed set `K` the
frontier of a connected component of `Kᶜ` is the intersection of its closure with `K`. -/
theorem frontier_connectedComponentIn_eq {K : Set ℂ} (hK : IsClosed K) {x : ℂ} :
    frontier (connectedComponentIn Kᶜ x) = closure (connectedComponentIn Kᶜ x) ∩ K := by
  rcases em (x ∈ Kᶜ) with hxU | hxU
  · set C : Set ℂ := connectedComponentIn Kᶜ x with hC
    have hCopen : IsOpen C := hK.isOpen_compl.connectedComponentIn
    have hfront : frontier C = closure C \ C := hCopen.frontier_eq
    refine Set.Subset.antisymm ?_ ?_
    · intro z hz
      rw [hfront] at hz
      refine ⟨hz.1, ?_⟩
      by_contra hzK
      have hzU : z ∈ Kᶜ := hzK
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hK.isOpen_compl z hzU
      have hzball : z ∈ Metric.ball z r := by rw [Metric.mem_ball]; simpa using hr
      obtain ⟨y, hyB, hyC⟩ :=
        mem_closure_iff.mp hz.1 (Metric.ball z r) isOpen_ball hzball
      have hpre : IsPreconnected (C ∪ Metric.ball z r) :=
        IsPreconnected.union' ⟨y, hyC, hyB⟩ isPreconnected_connectedComponentIn
          (convex_ball z r).isPreconnected
      have hsub : C ∪ Metric.ball z r ⊆ Kᶜ :=
        Set.union_subset (connectedComponentIn_subset Kᶜ x) (fun w hw => hball hw)
      have hxC : x ∈ C ∪ Metric.ball z r := Or.inl (mem_connectedComponentIn hxU)
      have : z ∈ C := hpre.subset_connectedComponentIn hxC hsub (Or.inr hzball)
      exact hz.2 this
    · rintro z ⟨hzcl, hzK⟩
      rw [hfront]
      refine ⟨hzcl, ?_⟩
      intro hzC
      exact (connectedComponentIn_subset Kᶜ x hzC) hzK
  · rw [connectedComponentIn_eq_empty hxU]
    simp

/-- **The frontier of a complementary domain of a compact connected set is a continuum.**  For
compact connected non-empty `K` and `x ∉ K`, the frontier of the component of `x` in `Kᶜ` is
non-empty and preconnected. -/
theorem frontier_component_continuum {K : Set ℂ} (hK : IsCompact K) (hKp : IsPreconnected K)
    (hKne : K.Nonempty) {x : ℂ} (hx : x ∉ K) :
    (frontier (connectedComponentIn Kᶜ x)).Nonempty ∧
      IsPreconnected (frontier (connectedComponentIn Kᶜ x)) := by
  refine ⟨?_, ?_⟩
  · rw [frontier_connectedComponentIn_eq hK.isClosed]
    have h := nonempty_closure_connectedComponentIn_inter_compl (X := ℂ) hK.isClosed.isOpen_compl
      (x := x) hx (by
        intro h
        obtain ⟨y, hy⟩ := hKne
        have hy' : y ∈ Kᶜ := by rw [h]; exact Set.mem_univ y
        exact hy' hy)
    simpa using h
  · exact isPreconnected_frontier_connectedComponentIn hK hKp x

end

end Work.Smooth.JordanSeparation
