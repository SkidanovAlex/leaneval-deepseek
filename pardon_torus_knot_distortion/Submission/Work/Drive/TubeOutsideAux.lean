import Mathlib
import Submission.Work.Smooth.Jordan.All
import Submission.Work.Smooth.SphereJordan.annulusPreconnected
import Submission.Work.Smooth.SphereJordan.interior_closure_V_eq

/-!
# Elementary facts about the outward tube of a plane Jordan curve

For a simple closed plane curve `c` with a Jordan–Schoenflies datum `S` (`S.U` the unbounded side,
`S.V` the bounded side, `closure S.V` the closed disc bounded by the curve) and `r : ℝ`, the
*outward tube* is

`tubeOutside c S r = {z : ℂ | Metric.infDist z (Set.range c.γ) < r ∧ z ∉ closure S.V}`,

the points outside the closed disc at distance `< r` from the trace.

This file collects the small structural lemmas used in
`Work.Drive.TubeOutsidePreconnectedSmall`:

* `trace_subset_closure_V`, `frontier_subset_trace` — the trace is the frontier of the bounded side;
* `nonempty_inter_frontier_of_preconnected` — a preconnected set joining `V` to `Vᶜ` crosses the
  frontier;
* `connectedComponentIn_eq_of_mem` — components containing a common point coincide;
* `exists_nearest_of_compact` — every point has a nearest point of the compact trace;
* `isPreconnected_range_of_curve` — the trace is preconnected.
-/

namespace Work.Drive

open Set Metric

noncomputable section

variable {c : Work.Smooth.Jordan.PlaneCurve}

/-- The **outward tube** of radius `r`: the points at distance `< r` from the trace and outside the
closed disc bounded by the curve. -/
def tubeOutside (c : Work.Smooth.Jordan.PlaneCurve) (S : Work.Smooth.Jordan.PlaneSchoenflies c)
    (r : ℝ) : Set ℂ :=
  {z : ℂ | Metric.infDist z (Set.range c.γ) < r ∧ z ∉ closure S.V}

theorem mem_tubeOutside (S : Work.Smooth.Jordan.PlaneSchoenflies c) (r : ℝ) (z : ℂ) :
    z ∈ tubeOutside c S r ↔ Metric.infDist z (Set.range c.γ) < r ∧ z ∉ closure S.V := Iff.rfl

/-- The unbounded side is the complement of the closed Schoenflies disc. -/
theorem unboundedSide_eq_compl (S : Work.Smooth.Jordan.PlaneSchoenflies c) :
    S.U = (closure S.V)ᶜ :=
  Work.Smooth.SphereJordan.compl_closure_V_eq_unboundedSide S

/-- The trace is contained in the closure of the bounded side. -/
theorem trace_subset_closure_V (S : Work.Smooth.Jordan.PlaneSchoenflies c) :
    Set.range c.γ ⊆ closure S.V := by
  rw [Work.Smooth.SphereJordan.closure_V_eq S]
  exact Set.subset_union_right

/-- The trace is the frontier of the bounded side. -/
theorem frontier_subset_trace (S : Work.Smooth.Jordan.PlaneSchoenflies c) :
    frontier S.V ⊆ Set.range c.γ := by
  intro p hp
  rw [frontier_eq_closure_inter_closure] at hp
  have hp2 : p ∉ S.V := by
    rw [S.toPlaneSeparation.isOpen_V.isClosed_compl.closure_eq] at hp
    exact hp.2
  rw [Work.Smooth.SphereJordan.closure_V_eq S] at hp
  rcases hp.1 with h | h
  · exact absurd h hp2
  · exact h

/-- A preconnected set that meets `V` and the complement of `V` meets the frontier of `V`. -/
theorem nonempty_inter_frontier_of_preconnected {V s : Set ℂ} (hs : IsPreconnected s)
    (h1 : (s ∩ V).Nonempty) (h2 : (s ∩ Vᶜ).Nonempty) : (s ∩ frontier V).Nonempty := by
  by_contra hcon
  rw [Set.not_nonempty_iff_eq_empty] at hcon
  have hcover : s ⊆ closure (s ∩ V) ∪ closure (s ∩ Vᶜ) := by
    intro x hx
    by_cases hxV : x ∈ V
    · exact Or.inl (subset_closure ⟨hx, hxV⟩)
    · exact Or.inr (subset_closure ⟨hx, hxV⟩)
  have hdisj : s ∩ (closure (s ∩ V) ∩ closure (s ∩ Vᶜ)) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hxs, hx1, hx2⟩
    refine Set.eq_empty_iff_forall_notMem.mp hcon x ⟨hxs, ?_⟩
    rw [frontier_eq_closure_inter_closure]
    exact ⟨closure_mono Set.inter_subset_right hx1, closure_mono Set.inter_subset_right hx2⟩
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hs) (closure (s ∩ V))
      (closure (s ∩ Vᶜ)) isClosed_closure isClosed_closure hcover hdisj with h | h
  · obtain ⟨y, hys, hyVc⟩ := h2
    refine Set.eq_empty_iff_forall_notMem.mp hcon y ⟨hys, ?_⟩
    rw [frontier_eq_closure_inter_closure]
    exact ⟨closure_mono Set.inter_subset_right (h hys), subset_closure hyVc⟩
  · obtain ⟨y, hys, hyV⟩ := h1
    refine Set.eq_empty_iff_forall_notMem.mp hcon y ⟨hys, ?_⟩
    rw [frontier_eq_closure_inter_closure]
    exact ⟨subset_closure hyV, closure_mono Set.inter_subset_right (h hys)⟩

/-- Components of a set containing a common point coincide. -/
theorem connectedComponentIn_eq_of_mem {F : Set ℂ} {x y : ℂ} (hx : x ∈ F)
    (h : y ∈ connectedComponentIn F x) :
    connectedComponentIn F y = connectedComponentIn F x := by
  have h1 : connectedComponentIn F x ⊆ connectedComponentIn F y :=
    IsPreconnected.subset_connectedComponentIn isPreconnected_connectedComponentIn h
      (connectedComponentIn_subset F x)
  have h2 : connectedComponentIn F y ⊆ connectedComponentIn F x :=
    IsPreconnected.subset_connectedComponentIn isPreconnected_connectedComponentIn
      (h1 (mem_connectedComponentIn hx)) (connectedComponentIn_subset F y)
  exact Set.Subset.antisymm h2 h1

/-- Every point has a nearest point of the compact trace. -/
theorem exists_nearest_of_compact (c : Work.Smooth.Jordan.PlaneCurve) (z : ℂ) :
    ∃ q ∈ Set.range c.γ, Metric.infDist z (Set.range c.γ) = dist z q := by
  have hne : (Set.range c.γ).Nonempty := ⟨c.γ 0, ⟨0, rfl⟩⟩
  have hc : IsCompact (Set.range c.γ) := c.isCompact_trace
  obtain ⟨q, hqP, hmin⟩ := hc.exists_isMinOn hne
    (f := fun y : ℂ => dist z y) (continuous_const.dist continuous_id).continuousOn
  refine ⟨q, hqP, le_antisymm (Metric.infDist_le_dist_of_mem hqP) ?_⟩
  exact (Metric.le_infDist hne).mpr (fun y hy => hmin hy)

/-- The trace of a (not necessarily simple) closed curve is preconnected. -/
theorem isPreconnected_range_of_curve (c : Work.Smooth.Jordan.PlaneCurve) :
    IsPreconnected (Set.range c.γ) := by
  have h1 : Set.range c.γ = c.γ '' Set.Icc (0 : ℝ) (2 * Real.pi) := c.trace_eq_image_Icc
  rw [h1]
  exact isPreconnected_Icc.image c.γ c.cont.continuousOn

end

end Work.Drive
