import Submission.Work.Smooth.SphereJordan.jsepExists
import Submission.Work.Smooth.Jordan.trace_sdiff_arc_preconnected

/-!
# The two sides of a simple closed curve: elementary API

The facts about a `JSep` datum (`Work.Smooth.SphereJordan.JSep`) that the boundary-correspondence
argument of `Work.Smooth.Schoenflies.Injectivity` consumes:

* `not_bounded_U` — the `U` side of a `JSep` is unbounded (the `V` side is the bounded one);
* `eq_boundedSide_of_frontier` — an open, preconnected, bounded set whose frontier is the trace is
  *the* bounded side;
* `isPreconnected_trace_diff` — the trace with one point removed is preconnected (a circle minus a
  point is an arc);
* `subset_U_of_preconnected_unbounded` — a preconnected unbounded set avoiding the trace lies in the
  unbounded side.
-/

open Set Metric
open scoped Topology

namespace Work.Smooth.Schoenflies

noncomputable section

/-- **The `U` side of a `JSep` is unbounded.**  (`JSep` records that `V` is bounded; `U` must then
be unbounded, since otherwise `ℂ = trace ∪ U ∪ V` would be bounded.) -/
theorem not_bounded_U {γ : Work.Smooth.Jordan.PlaneCurve} (S : Work.Smooth.SphereJordan.JSep γ) :
    ¬ Bornology.IsBounded S.U := by
  intro hU
  have hUV : Bornology.IsBounded (S.U ∪ S.V) := hU.union S.bounded_V
  rw [S.union_eq] at hUV
  have ht : Bornology.IsBounded γ.trace := γ.isCompact_trace.isBounded
  have hall : Bornology.IsBounded (Set.univ : Set ℂ) := by
    have h1 : (γ.trace ∪ γ.traceᶜ : Set ℂ) = Set.univ := union_compl_self γ.trace
    rw [← h1]
    exact ht.union hUV
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp hall
  have h := hC (x := (0 : ℂ)) (by trivial) (y := (((max C 0 + 1 : ℝ)) : ℂ)) (by trivial)
  rw [dist_eq_norm, zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ max C 0 + 1)] at h
  linarith [le_max_left C 0, le_max_right C 0]

/-- **An open, preconnected, bounded set whose frontier is the trace is the bounded side of the
curve.** -/
theorem eq_boundedSide_of_frontier {γ : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.SphereJordan.JSep γ) {Ω : Set ℂ} (hΩo : IsOpen Ω)
    (hΩpre : IsPreconnected Ω) (hΩne : Ω.Nonempty) (hΩb : Bornology.IsBounded Ω)
    (hfr : frontier Ω = γ.trace) : Ω = S.V := by
  have hdisj : Disjoint (frontier Ω) Ω := disjoint_frontier_iff_isOpen.mpr hΩo
  have hUtrace : S.U ⊆ γ.traceᶜ := by
    rw [← S.union_eq]; exact subset_union_left
  have hVtrace : S.V ⊆ γ.traceᶜ := by
    rw [← S.union_eq]; exact subset_union_right
  have hsub : Ω ⊆ S.U ∪ S.V := by
    intro z hz
    have hzt : z ∉ γ.trace := by
      intro hzt
      exact Set.disjoint_left.mp hdisj (by rw [hfr]; exact hzt) hz
    rw [S.union_eq]
    exact hzt
  have hcl : closure Ω = Ω ∪ γ.trace := by rw [closure_eq_self_union_frontier, hfr]
  have hdisj2 : Disjoint Ω (closure Ω)ᶜ := by
    rw [Set.disjoint_left]
    intro z hz hz'
    exact hz' (subset_closure hz)
  rcases IsPreconnected.subset_or_subset S.isOpen_U S.isOpen_V S.disjoint_UV hsub hΩpre with
    hU | hV
  · -- `Ω ⊆ S.U` forces `Ω = S.U`, contradicting the boundedness of `Ω`
    exfalso
    have hsub2 : S.U ⊆ Ω ∪ (closure Ω)ᶜ := by
      intro z hz
      by_cases hzΩ : z ∈ Ω
      · exact Or.inl hzΩ
      · refine Or.inr ?_
        rintro hzcl
        rw [hcl] at hzcl
        rcases hzcl with h | h
        · exact hzΩ h
        · exact absurd h (hUtrace hz)
    have hSU : S.U ⊆ Ω := by
      rcases IsPreconnected.subset_or_subset hΩo isClosed_closure.isOpen_compl hdisj2 hsub2 S.preconn_U
        with h2 | h2
      · exact h2
      · exfalso
        obtain ⟨a, ha⟩ := hΩne
        exact (h2 (hU ha)) (subset_closure ha)
    have : S.U = Ω := subset_antisymm hSU hU
    rw [← this] at hΩb
    exact not_bounded_U S hΩb
  · -- `Ω ⊆ S.V` and `S.V ⊆ Ω`
    refine subset_antisymm hV ?_
    have hsub2 : S.V ⊆ Ω ∪ (closure Ω)ᶜ := by
      intro z hz
      by_cases hzΩ : z ∈ Ω
      · exact Or.inl hzΩ
      · refine Or.inr ?_
        rintro hzcl
        rw [hcl] at hzcl
        rcases hzcl with h | h
        · exact hzΩ h
        · exact absurd h (hVtrace hz)
    have hSV : S.V ⊆ Ω := by
      rcases IsPreconnected.subset_or_subset hΩo isClosed_closure.isOpen_compl hdisj2 hsub2 S.preconn_V
        with h2 | h2
      · exact h2
      · exfalso
        obtain ⟨a, ha⟩ := hΩne
        have haV : a ∈ S.V := hV ha
        exact (h2 haV) (subset_closure ha)
    exact hSV

/-- **The trace of a simple closed curve with one point removed is preconnected** (a circle minus a
point is an arc). -/
theorem isPreconnected_trace_diff {γ : Work.Smooth.Jordan.PlaneCurve} (hγ : γ.IsSimple) {w : ℂ}
    (hw : w ∈ γ.trace) : IsPreconnected (γ.trace \ {w}) := by
  obtain ⟨t₀, ht₀⟩ := hw
  have h := Work.Smooth.Jordan.trace_sdiff_arc_preconnected (c := γ) hγ (le_refl t₀)
    (by rw [sub_self]; positivity)
  rw [Set.Icc_self, Set.image_singleton, ht₀] at h
  exact h

/-- **A preconnected unbounded set avoiding the trace lies in the unbounded side**: the bounded side
is bounded, so it cannot contain an unbounded connected set, and the complement of the trace splits
into the two sides. -/
theorem subset_U_of_preconnected_unbounded {L : Work.Smooth.Jordan.PlaneCurve}
    (T : Work.Smooth.SphereJordan.JSep L) {A : Set ℂ} (hA : IsPreconnected A)
    (hu : ¬ Bornology.IsBounded A) (hdisj : Disjoint A L.trace) : A ⊆ T.U := by
  have hsub : A ⊆ T.U ∪ T.V := by
    intro z hz
    have h1 : z ∈ L.traceᶜ := by
      rintro h2
      exact (Set.disjoint_left.mp hdisj) hz h2
    rw [T.union_eq]
    exact h1
  rcases IsPreconnected.subset_or_subset T.isOpen_U T.isOpen_V T.disjoint_UV hsub hA with h | h
  · exact h
  · exact absurd (T.bounded_V.subset h) hu

end

end Work.Smooth.Schoenflies
