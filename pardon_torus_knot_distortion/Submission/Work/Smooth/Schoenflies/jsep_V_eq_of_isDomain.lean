import Mathlib
import Submission.Work.Smooth.SphereJordan.jsepDefs
import Submission.Work.Smooth.Jordan.Defs

/-!
# Uniqueness of the bounded side of a simple closed plane curve

`Work.Smooth.SphereJordan.JSep γ` is a separation datum for a simple closed plane curve `γ`: the
complement of the trace is the disjoint union of two non-empty preconnected open sets, the unbounded
side `U` and the bounded side `V`, both with frontier the trace.

This file records the *uniqueness* of the bounded side in the following form: an open, non-empty,
bounded, preconnected set `Ω` whose frontier is the trace is exactly `S.V`.

The proof is elementary and uses only the structure fields of `JSep`:

* since `Ω` is open it is disjoint from its own frontier `γ.trace`, so `Ω ⊆ U ∪ V`; as `Ω` is
  preconnected and `U`, `V` are disjoint open sets, `Ω` lies in one of the two sides;
* if a preconnected open set `T` contains a non-empty open set `A` and is disjoint from the frontier
  of `A`, then `T = A`: indeed `T ⊆ A ∪ (closure A)ᶜ` and `A`, `(closure A)ᶜ` are disjoint open
  sets, so the preconnected `T` lies in one of them — and it does meet `A`;
* applied with `T = S.U` this forces `S.U = Ω`, hence `S.U` bounded, contradicting the unboundedness
  of `U` (which follows from `U ∪ V = traceᶜ` with `V` and `trace` bounded);
* applied with `T = S.V` it gives `S.V = Ω`.

## Main results

* `not_isBounded_U` — the unbounded side of a `JSep` is unbounded;
* `eq_of_ssubset_of_disjoint_frontier` — the abstract "same frontier" step;
* `jsep_V_eq_of_isDomain` — the requested lemma.
-/

open Set Metric
open scoped Topology

namespace Work.Smooth.Schoenflies

noncomputable section

/-- **The unbounded side of a `JSep` is unbounded.**  `JSep` records that `V` is bounded and
`U ∪ V = γ.traceᶜ` with `γ.trace` compact; if `U` were bounded then all of `ℂ` would be bounded. -/
theorem not_isBounded_U {γ : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.SphereJordan.JSep γ) : ¬ Bornology.IsBounded S.U := by
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

/-- **A preconnected open set `T` containing a non-empty open set `A` and disjoint from the frontier
of `A` equals `A`.**

Because `closure A = A ∪ frontier A`, the hypothesis `Disjoint T (frontier A)` gives
`T ⊆ A ∪ (closure A)ᶜ`; the two sets on the right are disjoint open sets and `T` is preconnected,
so `T` lies in one of them, and it contains the non-empty `A`. -/
theorem eq_of_subset_of_disjoint_frontier {A T : Set ℂ} (hA : IsOpen A)
    (hAT : A ⊆ T) (hne : A.Nonempty) (hTpre : IsPreconnected T)
    (hdisj : Disjoint T (frontier A)) : T = A := by
  have hcl : closure A = A ∪ frontier A := closure_eq_self_union_frontier A
  have hsub : T ⊆ A ∪ (closure A)ᶜ := by
    intro z hz
    by_cases hzA : z ∈ A
    · exact Or.inl hzA
    · refine Or.inr ?_
      rintro hzcl
      rw [hcl] at hzcl
      rcases hzcl with h | h
      · exact hzA h
      · exact absurd h (Set.disjoint_left.mp hdisj hz)
  have hdisj2 : Disjoint A (closure A)ᶜ := by
    rw [Set.disjoint_left]
    intro z hz hz'
    exact hz' (subset_closure hz)
  rcases IsPreconnected.subset_or_subset hA isClosed_closure.isOpen_compl hdisj2 hsub hTpre with
    h | h
  · exact subset_antisymm h hAT
  · exact absurd (subset_closure (hne.choose_spec)) (h (hAT hne.choose_spec))

/-- **An open, non-empty, bounded, preconnected set whose frontier is the trace of `γ` is the
bounded side `S.V` of any Jordan separation datum `S` for `γ`.**

This is the "uniqueness of the bounded side": `Ω` is open, hence disjoint from its own frontier
`γ.trace`, so `Ω ⊆ U ∪ V`; preconnectedness puts `Ω` inside one of the two sides, and the abstract
step `eq_of_subset_of_disjoint_frontier` upgrades containment into equality.  The alternative
`Ω ⊆ U` is impossible because `U` is unbounded (`not_isBounded_U`) while `Ω` is bounded. -/
theorem jsep_V_eq_of_isDomain {γ : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.SphereJordan.JSep γ) {Ω : Set ℂ}
    (hΩo : IsOpen Ω) (hΩne : Ω.Nonempty) (hΩb : Bornology.IsBounded Ω)
    (hΩpre : IsPreconnected Ω) (hfr : frontier Ω = γ.trace) :
    S.V = Ω := by
  have hUtrace : S.U ⊆ γ.traceᶜ := subset_union_left.trans (le_of_eq S.union_eq)
  have hVtrace : S.V ⊆ γ.traceᶜ := subset_union_right.trans (le_of_eq S.union_eq)
  have hsub : Ω ⊆ S.U ∪ S.V := by
    intro z hz
    have hzt : z ∉ γ.trace := by
      intro hzt
      have hzfr : z ∈ frontier Ω := by rw [hfr]; exact hzt
      exact (Set.disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr hΩo).symm hz) hzfr
    rw [S.union_eq]
    exact hzt
  rcases IsPreconnected.subset_or_subset S.isOpen_U S.isOpen_V S.disjoint_UV hsub hΩpre with
    hU | hV
  · -- `Ω ⊆ S.U` forces `S.U = Ω`, contradicting the boundedness of `Ω`
    exfalso
    have hdisj : Disjoint S.U (frontier Ω) := by
      rw [hfr]
      exact disjoint_left.mpr fun z hz hzt => hUtrace hz hzt
    have hUeq : S.U = Ω := eq_of_subset_of_disjoint_frontier hΩo hU hΩne S.preconn_U hdisj
    exact not_isBounded_U S (hUeq ▸ hΩb)
  · -- `Ω ⊆ S.V`, and `S.V` has the same frontier, so `S.V = Ω`
    have hdisj : Disjoint S.V (frontier Ω) := by
      rw [hfr]
      exact disjoint_left.mpr fun z hz hzt => hVtrace hz hzt
    exact eq_of_subset_of_disjoint_frontier hΩo hV hΩne S.preconn_V hdisj

end

end Work.Smooth.Schoenflies
