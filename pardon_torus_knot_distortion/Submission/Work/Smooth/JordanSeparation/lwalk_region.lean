import Mathlib
import Submission.Work.Smooth.JordanSeparation.lwalk_range
import Submission.Work.Smooth.SphereJordan.thetaPlaneTwoComponents
import Submission.Work.Topology.PlaneCurve.frontier_component_eq_range
import Submission.Work.Smooth.JordanSeparation.boundedSide_subset_of_compl_preconnected

/-!
# The two sides of a simple closed lattice walk

For a simple closed lattice walk `W` with at least four edges, the trace of `W.curve` is the trace
of the walk (`LWalk.range_curve_eq_range_path`), so

* `LWalk.curve` is a simple closed plane curve and admits a plane separation
  (`Work.Smooth.SphereJordan.nonempty_planeSeparation_of_continuous`);
* the frontier of each side is the trace, and the closure of the bounded side is the bounded side
  together with the trace;
* if `U` is open, contains the walk, and `Uᶜ ∪ {∞}` is preconnected in the sphere (`hpre`), then the
  bounded side and its closure are contained in `U`
  (`Work.Smooth.JordanSeparation.boundedSide_subset_of_compl_preconnected`).

This is step 2 of `_LWALK_PEEL_NOTES.md`.
-/

namespace Work.Smooth.JordanSeparation

open Set

noncomputable section

namespace LWalk

variable (W : LWalk)

/-- The `PlaneCurve` attached to a lattice walk. -/
abbrev toPlaneCurve : Work.Smooth.Jordan.PlaneCurve :=
  ⟨W.curve, W.continuous_curve, W.periodic_curve⟩

/-- **A simple closed lattice walk with at least four edges is a simple closed plane curve.** -/
theorem exists_planeSeparation (hW : W.IsSimple) (hn : 4 ≤ W.n) :
    Nonempty (Work.Smooth.Jordan.PlaneSeparation W.toPlaneCurve) :=
  Work.Smooth.SphereJordan.nonempty_planeSeparation_of_continuous W.continuous_curve
    W.periodic_curve (W.curve_injOn hW hn)

variable {W}

/-- The complement of the trace is not preconnected: it is the disjoint union of the two non-empty
sides. -/
theorem not_isPreconnected_compl (S : Work.Smooth.Jordan.PlaneSeparation W.toPlaneCurve) :
    ¬ IsPreconnected (Set.range W.curve)ᶜ := by
  intro hcon
  obtain ⟨u, hu⟩ := S.nonempty_U
  obtain ⟨v, hv⟩ := S.nonempty_V
  have hsub : (Set.range W.curve)ᶜ ⊆ S.U ∪ S.V := by
    intro z hz
    have : z ∈ (W.toPlaneCurve.trace)ᶜ := hz
    rw [← S.union_eq] at this
    exact this
  have hv' : v ∈ (Set.range W.curve)ᶜ := by
    have : v ∈ (W.toPlaneCurve.trace)ᶜ := by rw [← S.union_eq]; exact Or.inr hv
    exact this
  rcases hcon.subset_or_subset S.isOpen_U S.isOpen_V S.disjoint_UV hsub with h | h
  · exact Set.disjoint_left.mp S.disjoint_UV (h hv') hv
  · exact Set.disjoint_left.mp S.disjoint_UV hu (h (by
      have : u ∈ (W.toPlaneCurve.trace)ᶜ := by rw [← S.union_eq]; exact Or.inl hu
      exact this))

/-- The bounded side is the connected component of any of its points in the complement. -/
theorem connectedComponentIn_eq_V (S : Work.Smooth.Jordan.PlaneSeparation W.toPlaneCurve)
    {v : ℂ} (hv : v ∈ S.V) :
    connectedComponentIn (Set.range W.curve)ᶜ v = S.V := by
  have hvc : v ∈ (Set.range W.curve)ᶜ := by
    have : v ∈ (W.toPlaneCurve.trace)ᶜ := by rw [← S.union_eq]; exact Or.inr hv
    exact this
  refine Set.Subset.antisymm ?_ (S.preconn_V.subset_connectedComponentIn hv ?_)
  · intro z hz
    have hzsub : z ∈ (Set.range W.curve)ᶜ := connectedComponentIn_subset _ _ hz
    have hzsub' : z ∈ (W.toPlaneCurve.trace)ᶜ := hzsub
    rw [← S.union_eq] at hzsub'
    rcases hzsub' with h | h
    · exfalso
      have hcov : connectedComponentIn (Set.range W.curve)ᶜ v ⊆ S.U ∪ S.V := fun w hw => by
        rw [S.union_eq]; exact connectedComponentIn_subset _ _ hw
      rcases (isPreconnected_connectedComponentIn (F := (Set.range W.curve)ᶜ) (x := v)).subset_or_subset
        S.isOpen_U S.isOpen_V S.disjoint_UV hcov with h' | h'
      · exact Set.disjoint_left.mp S.disjoint_UV (h' (mem_connectedComponentIn hvc)) hv
      · exact Set.disjoint_left.mp S.disjoint_UV h (h' hz)
    · exact h
  · intro w hw
    have : w ∈ (W.toPlaneCurve.trace)ᶜ := by rw [← S.union_eq]; exact Or.inr hw
    exact this

/-- **The frontier of the bounded side is the trace of the walk.** -/
theorem frontier_V_eq_range (hW : W.IsSimple) (hn : 4 ≤ W.n)
    (S : Work.Smooth.Jordan.PlaneSeparation W.toPlaneCurve) :
    frontier S.V = Set.range W.curve := by
  obtain ⟨v, hv⟩ := S.nonempty_V
  have hvc : v ∈ (Set.range W.curve)ᶜ := by
    have : v ∈ (W.toPlaneCurve.trace)ᶜ := by rw [← S.union_eq]; exact Or.inr hv
    exact this
  rw [← connectedComponentIn_eq_V S hv]
  exact Work.Topology.PlaneCurve.frontier_component_eq_range W.continuous_curve W.periodic_curve
    (W.curve_injOn hW hn) (not_isPreconnected_compl S) v hvc

/-- **The closure of the bounded side is the bounded side together with the trace.** -/
theorem closure_V_eq (hW : W.IsSimple) (hn : 4 ≤ W.n)
    (S : Work.Smooth.Jordan.PlaneSeparation W.toPlaneCurve) :
    closure S.V = S.V ∪ Set.range W.curve := by
  rw [closure_eq_self_union_frontier, frontier_V_eq_range hW hn S]

/-- **The bounded side of a simple closed lattice walk lies in `U`.**  This is the only place the
preconnectedness hypothesis `hpre` is used. -/
theorem boundedSide_subset {U : Set ℂ} (hUo : IsOpen U)
    (hpre : IsPreconnected (((↑) : ℂ → OnePoint ℂ) '' Uᶜ ∪ {OnePoint.infty}))
    (hW : W.IsSimple) (hn : 4 ≤ W.n) (hval : ∀ t, W.path t ∈ U)
    (S : Work.Smooth.Jordan.PlaneSeparation W.toPlaneCurve) :
    S.V ⊆ U :=
  Work.Smooth.JordanSeparation.boundedSide_subset_of_compl_preconnected W.continuous_curve
    W.periodic_curve (W.curve_injOn hW hn) S hUo (W.range_curve_subset_of_path hval) hpre

/-- **The closure of the bounded side of a simple closed lattice walk lies in `U`.** -/
theorem closure_boundedSide_subset {U : Set ℂ} (hUo : IsOpen U)
    (hpre : IsPreconnected (((↑) : ℂ → OnePoint ℂ) '' Uᶜ ∪ {OnePoint.infty}))
    (hW : W.IsSimple) (hn : 4 ≤ W.n) (hval : ∀ t, W.path t ∈ U)
    (S : Work.Smooth.Jordan.PlaneSeparation W.toPlaneCurve) :
    closure S.V ⊆ U := by
  rw [closure_V_eq hW hn S]
  exact Set.union_subset (boundedSide_subset hUo hpre hW hn hval S) (W.range_curve_subset_of_path hval)

/-- **A preconnected set disjoint from the trace lies entirely on one side.** -/
theorem subset_U_or_subset_V (S : Work.Smooth.Jordan.PlaneSeparation W.toPlaneCurve)
    {A : Set ℂ} (hAc : IsPreconnected A) (hA : A ⊆ (Set.range W.curve)ᶜ) :
    A ⊆ S.U ∨ A ⊆ S.V := by
  have hsub : A ⊆ S.U ∪ S.V := by
    intro z hz
    have h : z ∈ (W.toPlaneCurve.trace)ᶜ := hA hz
    rw [← S.union_eq] at h
    exact h
  exact hAc.subset_or_subset S.isOpen_U S.isOpen_V S.disjoint_UV hsub


end LWalk

end

end Work.Smooth.JordanSeparation
