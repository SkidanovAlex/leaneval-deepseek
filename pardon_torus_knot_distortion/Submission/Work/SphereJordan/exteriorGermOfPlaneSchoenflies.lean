import Mathlib
import Submission.Work.Smooth.Jordan.Separation
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.SphereJordan.exteriorGermSetup
import Submission.Work.SphereJordan.sideOfTraceComponentPreconnected

/-!
# The exterior germ of a plane Jordan–Schoenflies datum

For a simple closed plane curve `γ` with a Jordan–Schoenflies datum `S` (`S.U` the unbounded
side, `S.V` the bounded side), a point `γ θ₀` of the curve and any `ε > 0`, there is `ρ ∈ (0, ε)`
such that the part of the unbounded side inside `Metric.ball (γ θ₀) ρ` lies in a *single* connected
component of the part of the unbounded side inside `Metric.ball (γ θ₀) ε`.

## Route

By continuity of `γ` at `θ₀` there are `δ ∈ (0, π)` and a *window* parameter interval such that the
arc `A = γ '' Set.Icc (θ₀ - δ) (θ₀ + δ)` lies in the inner ball `Metric.ball (γ θ₀) (ε / 2)`
(`exists_localArc_scale'`), and by compactness of the trace outside a parameter window
(`exists_window`, `Work.SphereJordan.exteriorGermSetup`) — the trace only returns to a
neighbourhood of `γ θ₀` with parameters inside the window — the trace inside some smaller ball is
contained in `A`.

The remaining content is the local structure of the *chamber* of the trace component of `γ θ₀`: the
part of the unbounded side in the chamber is preconnected
(`Work.SphereJordan.sideOfTraceComponentPreconnected`, proved in the sibling module
`Submission/Work/SphereJordan/sideOfTraceComponentPreconnected.lean`), and the small ball minus the
trace lies in that chamber.  This is the reduction carried out below (`ballJoinGerm'`).
-/

/-!
## State of this file

Everything in this file is fully proved.  The imported ingredients of
`Work.SphereJordan.exteriorGermOfPlaneSchoenflies` are the two elementary reductions
`Work.SphereJordan.exists_localArc_scale'` and `Work.SphereJordan.exists_window` (the latter from
`Submission/Work/SphereJordan/exteriorGermSetup.lean`) together with the local chamber lemma
`Work.SphereJordan.sideOfTraceComponentPreconnected`
(`Submission/Work/SphereJordan/sideOfTraceComponentPreconnected.lean`), applied inside
`ballJoinGerm'` below.  That chamber lemma is in turn assembled from the one-sided collar
`Work.SphereJordan.chamberCollar` (`Submission/Work/SphereJordan/chamberCollar.lean`) — a single
germ of `S.U` along the trace component is contained in every `S.U`-cell of the punctured ball whose
closure meets that component — which is itself axiom-clean.  Hence
`#print axioms Work.SphereJordan.exteriorGermOfPlaneSchoenflies` is exactly
`propext`/`Classical.choice`/`Quot.sound`.

Recorded for the record: the *stronger* statement that `Metric.ball (γ.γ θ₀) ρ ∩ S.U` is
*preconnected* (for some ρ) is **false** in general — a trace that oscillates near the point gives
alternating exterior pieces at every scale (the "wiggly boundary" configuration).  The statement
proved here is the weaker, true form: the small ball's part of the unbounded side is contained in a
**single component** of the prescribed ball's part of the unbounded side, which is what is needed.
-/

namespace Work.SphereJordan

open Set Metric

noncomputable section

variable {γ : Work.Smooth.Jordan.PlaneCurve}

/-! ## Two elementary reductions -/

/-- **A local arc of the trace inside a prescribed ball.**  Near any point of the curve the trace
is contained in the image of a short parameter window lying inside a prescribed ball. -/
theorem exists_localArc_scale' {θ₀ : ℝ} {r : ℝ} (hr : 0 < r) :
    ∃ δ : ℝ, 0 < δ ∧ δ < Real.pi ∧
      γ.γ '' Set.Icc (θ₀ - δ) (θ₀ + δ) ⊆ Metric.ball (γ.γ θ₀) r := by
  have hcont : ContinuousAt γ.γ θ₀ := γ.cont.continuousAt
  obtain ⟨δ', hδ'pos, hδ'⟩ := Metric.continuousAt_iff.mp hcont r hr
  refine ⟨min (δ' / 2) (Real.pi / 2), lt_min (by linarith) (by linarith [Real.pi_pos]),
    lt_of_le_of_lt (min_le_right _ _) (by linarith [Real.pi_pos]), ?_⟩
  rintro z ⟨t, ht, rfl⟩
  have h1 : |t - θ₀| ≤ min (δ' / 2) (Real.pi / 2) := by
    rw [abs_le]; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h2 : dist t θ₀ < δ' := by
    rw [Real.dist_eq]
    exact lt_of_le_of_lt (le_trans h1 (min_le_left _ _)) (by linarith)
  have h3 := hδ' h2
  simpa [Metric.mem_ball, dist_eq_norm] using h3

/-- **The window property in closed-ball form.**  If every trace point within `ρ₀` of `p` lies on
the arc `A`, then every trace point in the *closed* ball of any smaller radius lies on `A`. -/
theorem trace_inter_closedBall_subset' {p : ℂ} {A : Set ℂ} {ρ₀ ρ : ℝ} (hlt : ρ < ρ₀)
    (hwin : γ.trace ∩ Metric.ball p ρ₀ ⊆ A) :
    γ.trace ∩ Metric.closedBall p ρ ⊆ A := by
  rintro z ⟨hzt, hzb⟩
  have hle : dist z p ≤ ρ := by rwa [Metric.mem_closedBall] at hzb
  exact hwin ⟨hzt, lt_of_le_of_lt hle hlt⟩

/-! ## The small-ball germ via the chamber -/

/-- The ball with all trace-components *other* than the one through `a` removed. -/
def otherTracePiece' (γ : Work.Smooth.Jordan.PlaneCurve) (p : ℂ) (ε : ℝ) (a : ℂ) : Set ℂ :=
  Metric.ball p ε \ ((γ.trace ∩ Metric.ball p ε) \ connectedComponentIn (γ.trace ∩ Metric.ball p ε) a)

/-- **The components of `ball p ρ ∩ S.U` are joined inside `ball p ε ∩ S.U`.**  Here `A` is a
preconnected piece of the trace containing the trace inside the closed ball of radius `ρ`, and `A`
lies in the inner ball `Metric.ball p (ε / 2)`; then the whole of `Metric.ball p ρ ∩ S.U` lies in a
single component of `Metric.ball p ε ∩ S.U`. -/
theorem ballJoinGerm' {γ : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSeparation γ) {A : Set ℂ} (hAtrace : A ⊆ γ.trace)
    (hAp : IsPreconnected A) {p : ℂ} {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) (hρlt : ρ < ε)
    (hAbound : A ⊆ Metric.ball p (ε / 2))
    (hwin : γ.trace ∩ Metric.closedBall p ρ ⊆ A) :
    ∀ x : ℂ, x ∈ Metric.ball p ρ ∩ S.U →
      Metric.ball p ρ ∩ S.U ⊆ connectedComponentIn (Metric.ball p ε ∩ S.U) x := by
  intro x hx
  by_cases hempty : (γ.trace ∩ Metric.ball p ρ : Set ℂ) = ∅
  · have hsub : Metric.ball p ρ ⊆ (γ.trace)ᶜ := by
      intro z hz hzt
      exact (Set.eq_empty_iff_forall_notMem.mp hempty) z ⟨hzt, hz⟩
    have hpre : IsPreconnected (Metric.ball p ρ) := (convex_ball p ρ).isPreconnected
    rcases hpre.subset_or_subset S.isOpen_U S.isOpen_V S.disjoint_UV
        (fun z hz => by rw [S.union_eq]; exact hsub hz) with hU | hV
    · intro y hy
      refine hpre.subset_connectedComponentIn hx.1 ?_ hy.1
      intro z hz
      exact ⟨Metric.ball_subset_ball hρlt.le hz, hU hz⟩
    · intro y hy
      exact (Set.disjoint_left.mp S.disjoint_UV hy.2 (hV hy.1)).elim
  · have hne : (γ.trace ∩ Metric.ball p ρ : Set ℂ).Nonempty := by
      rwa [Set.nonempty_iff_ne_empty]
    obtain ⟨a, ha⟩ := hne
    have haA : a ∈ A := hwin ⟨ha.1, Metric.ball_subset_closedBall ha.2⟩
    have haε : a ∈ Metric.ball p ε := Metric.ball_subset_ball hρlt.le ha.2
    have ha' : a ∈ γ.trace ∩ Metric.ball p ε := ⟨ha.1, haε⟩
    have hAin : A ⊆ γ.trace ∩ Metric.ball p ε :=
      fun z hz => ⟨hAtrace hz, Metric.ball_subset_ball (by linarith) (hAbound hz)⟩
    have hAT : A ⊆ connectedComponentIn (γ.trace ∩ Metric.ball p ε) a :=
      hAp.subset_connectedComponentIn haA hAin
    have hconf : γ.trace ∩ Metric.closedBall p ρ ⊆
        connectedComponentIn (γ.trace ∩ Metric.ball p ε) a :=
      fun z hz => hAT (hwin hz)
    have hT₀ρ : γ.trace ∩ Metric.ball p ρ ⊆
        connectedComponentIn (γ.trace ∩ Metric.ball p ε) a :=
      fun z hz => hconf ⟨hz.1, Metric.ball_subset_closedBall hz.2⟩
    have haT : a ∈ connectedComponentIn (γ.trace ∩ Metric.ball p ε) a :=
      mem_connectedComponentIn ha'
    -- the local structure of the chamber: its `U`-part is preconnected
    have hCpre : IsPreconnected (connectedComponentIn (otherTracePiece' γ p ε a) a ∩ S.U) := by
      simpa only [otherTracePiece'] using
        Work.SphereJordan.sideOfTraceComponentPreconnected (γ := γ) S.simple S hε hρ hρlt ha' hconf
    -- `T₀ ⊆ Ξ`
    have hT₀Ξ : connectedComponentIn (γ.trace ∩ Metric.ball p ε) a ⊆
        connectedComponentIn (otherTracePiece' γ p ε a) a := by
      refine isPreconnected_connectedComponentIn.subset_connectedComponentIn haT ?_
      intro w hw
      refine ⟨?_, ?_⟩
      · exact (connectedComponentIn_subset _ _ hw).2
      · intro hwd
        exact hwd.2 hw
    -- `ball p ρ ⊆ Ξ`
    have hbX : Metric.ball p ρ ⊆ otherTracePiece' γ p ε a := by
      intro w hw
      refine ⟨Metric.ball_subset_ball hρlt.le hw, ?_⟩
      intro hwd
      exact hwd.2 (hT₀ρ ⟨hwd.1.1, hw⟩)
    have hT₀X : connectedComponentIn (γ.trace ∩ Metric.ball p ε) a ⊆
        otherTracePiece' γ p ε a := by
      intro w hw
      refine ⟨(connectedComponentIn_subset _ _ hw).2, ?_⟩
      intro hwd
      exact hwd.2 hw
    have hbΞ : Metric.ball p ρ ⊆ connectedComponentIn (otherTracePiece' γ p ε a) a := by
      have hunion : IsPreconnected (Metric.ball p ρ ∪
          connectedComponentIn (γ.trace ∩ Metric.ball p ε) a) :=
        IsPreconnected.union a ha.2 (hT₀ρ ⟨ha.1, ha.2⟩)
          (convex_ball p ρ).isPreconnected isPreconnected_connectedComponentIn
      have hsub : Metric.ball p ρ ∪
          connectedComponentIn (γ.trace ∩ Metric.ball p ε) a ⊆ otherTracePiece' γ p ε a := by
        rintro w (hw | hw)
        · exact hbX hw
        · exact hT₀X hw
      have hall := hunion.subset_connectedComponentIn (Or.inr haT) hsub
      exact fun w hw => hall (Or.inl hw)
    intro y hy
    have hyC : y ∈ connectedComponentIn (otherTracePiece' γ p ε a) a ∩ S.U :=
      ⟨hbΞ hy.1, hy.2⟩
    have hxC : x ∈ connectedComponentIn (otherTracePiece' γ p ε a) a ∩ S.U :=
      ⟨hbΞ hx.1, hx.2⟩
    refine hCpre.subset_connectedComponentIn hxC ?_ hyC
    intro w hw
    have hwX : w ∈ otherTracePiece' γ p ε a := connectedComponentIn_subset _ _ hw.1
    exact ⟨hwX.1, hw.2⟩

/-! ## The target -/

theorem exteriorGermOfPlaneSchoenflies {γ : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {θ₀ : ℝ} {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < ε ∧
      ∀ x : ℂ, x ∈ Metric.ball (γ.γ θ₀) ρ ∩ S.U →
        Metric.ball (γ.γ θ₀) ρ ∩ S.U ⊆
          connectedComponentIn (Metric.ball (γ.γ θ₀) ε ∩ S.U) x := by
  -- a parameter window whose image lies in the inner ball
  obtain ⟨δ, hδ, hδπ, hAsub⟩ :=
    exists_localArc_scale' (γ := γ) (θ₀ := θ₀) (r := ε / 2) (by linarith)
  -- the trace inside a small ball is covered by the window
  obtain ⟨ρ₀, hρ₀, hwin₀⟩ := exists_window (γ := γ) S.simple hδ hδπ
  have hwin : γ.trace ∩ Metric.ball (γ.γ θ₀) ρ₀ ⊆ γ.γ '' Set.Icc (θ₀ - δ) (θ₀ + δ) := by
    rintro z ⟨⟨t, rfl⟩, hz⟩
    rw [Metric.mem_ball, dist_eq_norm] at hz
    obtain ⟨s, hs, hse⟩ := hwin₀ t hz
    exact ⟨s, hs, hse⟩
  refine ⟨min (ρ₀ / 2) (ε / 2), lt_min (by linarith) (by linarith),
    lt_of_le_of_lt (min_le_right _ _) (by linarith), ?_⟩
  intro x hx
  refine ballJoinGerm' (γ := γ) S.toPlaneSeparation
    (A := γ.γ '' Set.Icc (θ₀ - δ) (θ₀ + δ))
    (by rintro z ⟨t, -, rfl⟩; exact γ.mem_trace t)
    ((isPreconnected_Icc).image γ.γ γ.cont.continuousOn) hε
    (lt_min (by linarith) (by linarith))
    (lt_of_le_of_lt (min_le_right _ _) (by linarith)) hAsub ?_ x hx
  exact trace_inter_closedBall_subset' (γ := γ) (p := γ.γ θ₀)
    (A := γ.γ '' Set.Icc (θ₀ - δ) (θ₀ + δ))
    (lt_of_le_of_lt (min_le_left _ _) (by linarith)) hwin

end

end Work.SphereJordan
