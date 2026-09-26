import Mathlib
import Submission.Work.SphereJordan.chamberDefs
import Submission.Work.SphereJordan.exteriorGermSetup
import Submission.Work.SphereJordan.chamberLocalWindow
import Submission.Work.SphereJordan.chamberCollar

/-!
# The unbounded component of the chamber of a trace component

Let `γ` be a simple closed plane curve with a Jordan separation `S` (`S.U` the unbounded side),
`B = Metric.ball p ε` a ball, `a ∈ γ.trace ∩ B` and

`Ξ := connectedComponentIn (sideChamber γ p ε a) a`

the component of `a` in the *chamber* — the ball with all trace components other than
`A := traceComponent γ p ε a` deleted.  The target is

`∃ w, w ∈ Ξ ∩ S.U ∧ Ξ ∩ S.U = connectedComponentIn (Metric.ball p ε \ γ.trace) w`:

the part of the unbounded side in the chamber is exactly a single cell of the punctured ball
`Metric.ball p ε \ γ.trace`.

## Proof

By the crosscut theorem for the (open, preconnected) chamber minus the trace component
(`Work.SphereJordan.chamberCrosscut`, an instance of the crosscut theorem for a plane domain) the set
`Ξ \ A` has at most two components; since `Ξ ∩ S.U` and `Ξ ∩ S.V` are non-empty open and disjoint and
cover `Ξ \ A`, this makes `Ξ ∩ S.U` preconnected (`Work.SphereJordan.chamberU_preconnected_of_le_two`).
It is then clopen in `Metric.ball p ε \ γ.trace`, which forces it to be the full connected component
of a point of itself.

The elementary pieces (the chamber is open, `Ξ ∩ S.U` is closed in `Metric.ball p ε \ γ.trace`) are
proved below; `Work.SphereJordan.chamberLocalWindow` supplies the local window used for openness.
-/

namespace Work.SphereJordan

open Set Metric

noncomputable section

variable {γ : Work.Smooth.Jordan.PlaneCurve}

/-- The chamber is open: the components of `γ.trace ∩ Metric.ball p ε` are open in the trace, so
`Metric.ball p ε \ ((γ.trace ∩ Metric.ball p ε) \ traceComponent γ p ε a)` is a union of two open
sets. -/
theorem sideChamber_isOpen (hs : γ.IsSimple) {p : ℂ} {ε : ℝ} (hε : 0 < ε) {a : ℂ}
    (ha : a ∈ γ.trace ∩ Metric.ball p ε) :
    IsOpen (sideChamber γ p ε a) := by
  rw [Metric.isOpen_iff]
  intro z hz
  obtain ⟨hzB, hznot⟩ := hz
  have hzp : dist z p < ε := Metric.mem_ball.mp hzB
  by_cases hztr : z ∈ γ.trace
  · have hzC : z ∈ traceComponent γ p ε a := by
      by_contra hcon
      exact hznot ⟨⟨hztr, hzB⟩, hcon⟩
    obtain ⟨r, hr, hrsub⟩ := mem_traceComponent_open (γ := γ) hs hε ha hzC
    set r' : ℝ := min r (ε - dist z p) / 2 with hr'def
    have hr'pos : 0 < r' := by
      rw [hr'def]; exact div_pos (lt_min hr (by linarith)) two_pos
    have hr'le : r' ≤ r := by rw [hr'def]; linarith [min_le_left r (ε - dist z p)]
    have hr'p : r' ≤ ε - dist z p := by rw [hr'def]; linarith [min_le_right r (ε - dist z p)]
    refine ⟨r', hr'pos, ?_⟩
    intro w hw
    have hwz : dist w z < r' := Metric.mem_ball.mp hw
    have hwB : w ∈ Metric.ball p ε := by
      rw [Metric.mem_ball]
      calc dist w p ≤ dist w z + dist z p := dist_triangle _ _ _
        _ < r' + dist z p := by linarith
        _ ≤ (ε - dist z p) + dist z p := by linarith
        _ = ε := by ring
    rw [sideChamber_eq]
    by_cases hwtr : w ∈ γ.trace
    · refine Or.inr ?_
      have hmem : w ∈ γ.trace ∩ Metric.ball z r :=
        ⟨hwtr, Metric.mem_ball.mpr (lt_of_lt_of_le hwz hr'le)⟩
      exact hrsub hmem
    · refine Or.inl ?_; exact ⟨hwB, hwtr⟩
  · obtain ⟨δ₁, hδ₁, hδ₁sub⟩ :=
      Metric.mem_nhds_iff.mp (γ.isClosed_trace.isOpen_compl.mem_nhds hztr)
    have hδ₂ : 0 < ε - dist z p := by rw [sub_pos]; exact hzp
    refine ⟨min δ₁ (ε - dist z p), lt_min hδ₁ hδ₂, ?_⟩
    intro w hw
    have hw1 : dist w z < δ₁ := lt_of_lt_of_le (Metric.mem_ball.mp hw) (min_le_left _ _)
    have hw2 : dist w z < ε - dist z p := lt_of_lt_of_le (Metric.mem_ball.mp hw) (min_le_right _ _)
    have hwB : w ∈ Metric.ball p ε := by
      rw [Metric.mem_ball]
      calc dist w p ≤ dist w z + dist z p := dist_triangle _ _ _
        _ < (ε - dist z p) + dist z p := by linarith
        _ = ε := by ring
    have hwnt : w ∉ γ.trace := by
      have := hδ₁sub (Metric.mem_ball.mpr hw1); simpa using this
    rw [sideChamber_eq]
    refine Or.inl ?_; exact ⟨hwB, hwnt⟩

/-- **The requested lemma.**  The part of the unbounded side in the chamber component of `a` is a
single cell of the punctured ball. -/
theorem sideChamberUComponent {γ : Work.Smooth.Jordan.PlaneCurve}
    (hs : γ.IsSimple) (S : Work.Smooth.Jordan.PlaneSeparation γ)
    {p : ℂ} {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) (hρlt : ρ < ε) {a : ℂ}
    (ha : a ∈ γ.trace ∩ Metric.ball p ε)
    (hconf : γ.trace ∩ Metric.closedBall p ρ ⊆ Work.SphereJordan.traceComponent γ p ε a) :
    ∃ w : ℂ, w ∈ connectedComponentIn (Work.SphereJordan.sideChamber γ p ε a) a ∩ S.U ∧
      connectedComponentIn (Work.SphereJordan.sideChamber γ p ε a) a ∩ S.U =
        connectedComponentIn (Metric.ball p ε \ γ.trace) w := by
  have hpre : IsPreconnected (connectedComponentIn (sideChamber γ p ε a) a ∩ S.U) :=
    chamberU_preconnected_of_le_two (γ := γ) hs S ha (chamberCrosscut (γ := γ) hs S ha)
  have hUsub : S.U ⊆ γ.traceᶜ := by
    intro z hz; have : z ∈ S.U ∪ S.V := Or.inl hz; rw [S.union_eq] at this; exact this
  have hXiOpen : IsOpen (connectedComponentIn (sideChamber γ p ε a) a) :=
    (sideChamber_isOpen hs hε ha).connectedComponentIn
  have haSide : a ∈ sideChamber γ p ε a := by
    rw [sideChamber_eq]; exact Or.inr (mem_traceComponent ha)
  have haXi : a ∈ connectedComponentIn (sideChamber γ p ε a) a := mem_connectedComponentIn haSide
  have hacl : a ∈ closure S.U := by
    apply frontier_subset_closure; rw [frontier_U_eq_trace S]; exact ha.1
  obtain ⟨w, hw⟩ := mem_closure_iff_nhds.mp hacl _ (hXiOpen.mem_nhds haXi)
  refine ⟨w, hw, ?_⟩
  have hDsub : Metric.ball p ε \ γ.trace ⊆ sideChamber γ p ε a := by
    rw [sideChamber_eq]; exact Set.subset_union_left
  have hXi_sub : connectedComponentIn (sideChamber γ p ε a) a ∩ S.U ⊆
      Metric.ball p ε \ γ.trace := by
    intro z hz
    exact ⟨sideChamber_subset_ball γ p ε a (connectedComponentIn_subset _ _ hz.1), hUsub hz.2⟩
  apply Set.Subset.antisymm
  · exact hpre.subset_connectedComponentIn hw hXi_sub
  · intro y hy
    have hwD : w ∈ Metric.ball p ε \ γ.trace := hXi_sub hw
    have hpreD : IsPreconnected (connectedComponentIn (Metric.ball p ε \ γ.trace) w) :=
      isPreconnected_connectedComponentIn
    have hsubSide : connectedComponentIn (Metric.ball p ε \ γ.trace) w ⊆
        connectedComponentIn (sideChamber γ p ε a) w :=
      hpreD.subset_connectedComponentIn (mem_connectedComponentIn hwD)
        ((connectedComponentIn_subset _ _).trans hDsub)
    have hwXi : w ∈ connectedComponentIn (sideChamber γ p ε a) a := hw.1
    have heq : connectedComponentIn (sideChamber γ p ε a) a =
        connectedComponentIn (sideChamber γ p ε a) w := connectedComponentIn_eq hwXi
    have hyXi : y ∈ connectedComponentIn (sideChamber γ p ε a) a := by
      rw [heq]; exact hsubSide hy
    have hyU : y ∈ S.U := by
      have hsubU : connectedComponentIn (Metric.ball p ε \ γ.trace) w ⊆ S.U :=
        (hpreD.subset_or_subset S.isOpen_U S.isOpen_V S.disjoint_UV
          (fun z hz => by
            have hz1 : z ∉ γ.trace := (connectedComponentIn_subset _ _ hz).2
            have : z ∈ S.U ∪ S.V := by rw [S.union_eq]; exact hz1
            exact this)).resolve_right (fun hV =>
              Set.disjoint_left.mp S.disjoint_UV hw.2 (hV (mem_connectedComponentIn hwD)))
      exact hsubU hy
    exact ⟨hyXi, hyU⟩

end

end Work.SphereJordan
