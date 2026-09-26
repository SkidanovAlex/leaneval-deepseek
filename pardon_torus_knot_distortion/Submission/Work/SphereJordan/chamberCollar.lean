import Mathlib
import Submission.Work.SphereJordan.chamberDefs
import Submission.Work.SphereJordan.chamberLocalWindow
import Submission.Work.SphereJordan.exteriorGermSetup
import Submission.Work.SphereJordan.chamberCrosscutClean

/-!
# The one-sided collar of a trace component

For a simple closed plane curve `γ`, a Jordan separation `S` (`S.U` the unbounded side), a ball
`Metric.ball p ε` and `a ∈ γ.trace ∩ Metric.ball p ε`, we build a non-empty preconnected set
`G ⊆ S.U` contained in every cell `Ω` of the punctured ball `Metric.ball p ε \ γ.trace` which lies
in `S.U` and whose closure meets the trace component `A = traceComponent γ p ε a`.

The proof takes `G := Ξ ∩ S.U` where `Ξ = connectedComponentIn (sideChamber γ p ε a) a` is the
chamber of `a`.  Since `A` is a crosscut of the chamber, `Ξ \ A` has at most two components
(`Work.SphereJordan.chamberCrosscut`), and it is the disjoint union of the two open subsets
`Ξ ∩ S.U` and `Ξ ∩ S.V` (`chamber_sdiff_eq_local`); the pigeonhole form of the crosscut theorem
therefore forces `Ξ ∩ S.U` to be preconnected (`chamberU_preconnected_of_le_two`).  Any cell `Ω`
of the punctured ball with `Ω ⊆ S.U` and `closure Ω ∩ A ≠ ∅` is contained in `Ξ`
(`component_subset_chamber_of_closure_meets_local`), so `G ⊆ Ω`.
-/

namespace Work.SphereJordan

open Set

noncomputable section

set_option maxHeartbeats 2000000

/-! ## Local copies of the chamber bookkeeping lemmas (the originals live in
`chamberUPreconnected`, whose import closure clashes with the crosscut theorem's). -/

/-- The trace component of `a` lies in the chamber component of `a`. -/
theorem traceComponent_subset_chamberComponent_local {γ : Work.Smooth.Jordan.PlaneCurve}
    {p : ℂ} {ε : ℝ} {a : ℂ} (ha : a ∈ γ.trace ∩ Metric.ball p ε) :
    traceComponent γ p ε a ⊆ connectedComponentIn (sideChamber γ p ε a) a :=
  isPreconnected_connectedComponentIn.subset_connectedComponentIn (mem_traceComponent ha)
    (by intro y hy; rw [sideChamber_eq]; exact Or.inr hy)

/-- The unbounded side of a separation avoids the trace. -/
theorem unboundedSide_subset_compl_trace_local {γ : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSeparation γ) : S.U ⊆ γ.traceᶜ := by
  intro y hy
  have h : y ∈ S.U ∪ S.V := Or.inl hy
  rw [S.union_eq] at h
  exact h

/-- A cell of the punctured ball which accumulates at the trace component `A` lies in the chamber
component of `a`. -/
theorem component_subset_chamber_of_closure_meets_local {γ : Work.Smooth.Jordan.PlaneCurve}
    {p : ℂ} {ε : ℝ} {a : ℂ} (ha : a ∈ γ.trace ∩ Metric.ball p ε) {w : ℂ}
    (hw : w ∈ Metric.ball p ε \ γ.trace)
    (hacc : (closure (connectedComponentIn (Metric.ball p ε \ γ.trace) w) ∩
      traceComponent γ p ε a).Nonempty) :
    connectedComponentIn (Metric.ball p ε \ γ.trace) w ⊆
      connectedComponentIn (sideChamber γ p ε a) a := by
  obtain ⟨z, hzcl, hzA⟩ := hacc
  have hpre : IsPreconnected (connectedComponentIn (Metric.ball p ε \ γ.trace) w ∪ {z}) :=
    IsPreconnected.subset_closure isPreconnected_connectedComponentIn
      (fun y hy => Or.inl hy)
      (by intro y hy
          rcases hy with h | h
          · exact subset_closure h
          · rw [h]; exact hzcl)
  have hzside : z ∈ sideChamber γ p ε a := by
    rw [sideChamber_eq]; exact Or.inr hzA
  have hsub : connectedComponentIn (Metric.ball p ε \ γ.trace) w ∪ {z} ⊆
      sideChamber γ p ε a := by
    intro y hy
    rcases hy with h | h
    · rw [sideChamber_eq]; exact Or.inl (connectedComponentIn_subset _ _ h)
    · rw [Set.mem_singleton_iff] at h; rw [h]; exact hzside
  have hsub' : connectedComponentIn (Metric.ball p ε \ γ.trace) w ∪ {z} ⊆
      connectedComponentIn (sideChamber γ p ε a) z :=
    hpre.subset_connectedComponentIn
      (show z ∈ connectedComponentIn (Metric.ball p ε \ γ.trace) w ∪ {z} from
        Or.inr (Set.mem_singleton z)) hsub
  rw [← connectedComponentIn_eq (F := sideChamber γ p ε a)
    (x := a) (y := z) (traceComponent_subset_chamberComponent_local ha hzA)] at hsub'
  exact fun y hy => hsub' (Or.inl hy)

theorem isOpen_sideChamber_local {γ : Work.Smooth.Jordan.PlaneCurve} (hs : γ.IsSimple)
    {p : ℂ} {ε : ℝ} (hε : 0 < ε) {a : ℂ} (ha : a ∈ γ.trace ∩ Metric.ball p ε) :
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
      exact hrsub ⟨hwtr, Metric.mem_ball.mpr (lt_of_lt_of_le hwz hr'le)⟩
    · exact Or.inl ⟨hwB, hwtr⟩
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
    exact Or.inl ⟨hwB, hwnt⟩

/-- Ξ ∩ trace = A -/
theorem chamber_inter_trace_local {γ : Work.Smooth.Jordan.PlaneCurve}
    {p : ℂ} {ε : ℝ} {a : ℂ} (ha : a ∈ γ.trace ∩ Metric.ball p ε) :
    connectedComponentIn (sideChamber γ p ε a) a ∩ γ.trace = traceComponent γ p ε a := by
  apply Set.Subset.antisymm
  · intro y hy
    have h2 : y ∈ sideChamber γ p ε a := connectedComponentIn_subset _ _ hy.1
    rw [sideChamber_eq] at h2
    rcases h2 with h | h
    · exact absurd hy.2 h.2
    · exact h
  · intro y hy
    exact ⟨traceComponent_subset_chamberComponent_local ha hy, traceComponent_subset_trace γ p ε a hy⟩

/-- Ξ \ A = (Ξ ∩ U) ∪ (Ξ ∩ V) -/
theorem chamber_sdiff_eq_local {γ : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSeparation γ) {p : ℂ} {ε : ℝ} {a : ℂ}
    (ha : a ∈ γ.trace ∩ Metric.ball p ε) :
    connectedComponentIn (sideChamber γ p ε a) a \ traceComponent γ p ε a =
      (connectedComponentIn (sideChamber γ p ε a) a ∩ S.U) ∪
      (connectedComponentIn (sideChamber γ p ε a) a ∩ S.V) := by
  have htr := chamber_inter_trace_local (γ := γ) ha
  apply Set.Subset.antisymm
  · rintro y ⟨hyΞ, hyA⟩
    have hyt : y ∉ γ.trace := fun h => hyA (by rw [← htr]; exact ⟨hyΞ, h⟩)
    have hyU : y ∈ S.U ∪ S.V := by rw [S.union_eq]; exact hyt
    rcases hyU with h | h
    · exact Or.inl ⟨hyΞ, h⟩
    · exact Or.inr ⟨hyΞ, h⟩
  · rintro y (⟨hyΞ, hyU⟩ | ⟨hyΞ, hyV⟩)
    · refine ⟨hyΞ, fun hyA => ?_⟩
      have hyt : y ∈ γ.trace := traceComponent_subset_trace γ p ε a hyA
      have h2 : y ∈ S.U ∪ S.V := Or.inl hyU
      rw [S.union_eq] at h2
      exact h2 hyt
    · refine ⟨hyΞ, fun hyA => ?_⟩
      have hyt : y ∈ γ.trace := traceComponent_subset_trace γ p ε a hyA
      have h2 : y ∈ S.U ∪ S.V := Or.inr hyV
      rw [S.union_eq] at h2
      exact h2 hyt

/-- A meets the closure of both one-sided parts -/
theorem traceComponent_subset_closure_sides_local {γ : Work.Smooth.Jordan.PlaneCurve}
    (hs : γ.IsSimple) (S : Work.Smooth.Jordan.PlaneSeparation γ)
    {p : ℂ} {ε : ℝ} {a : ℂ} (ha : a ∈ γ.trace ∩ Metric.ball p ε) :
    traceComponent γ p ε a ⊆
      closure (connectedComponentIn (sideChamber γ p ε a) a ∩ S.U) ∧
    traceComponent γ p ε a ⊆
      closure (connectedComponentIn (sideChamber γ p ε a) a ∩ S.V) := by
  have hε : 0 < ε := lt_of_le_of_lt dist_nonneg (Metric.mem_ball.mp ha.2)
  have hOpenΞ : IsOpen (connectedComponentIn (sideChamber γ p ε a) a) :=
    (isOpen_sideChamber_local (γ := γ) hs hε ha).connectedComponentIn
  have key : ∀ z ∈ traceComponent γ p ε a, ∀ C : Set ℂ, z ∈ closure C →
      z ∈ closure (connectedComponentIn (sideChamber γ p ε a) a ∩ C) := by
    intro z hz C hzC
    have hzΞ : z ∈ connectedComponentIn (sideChamber γ p ε a) a :=
      traceComponent_subset_chamberComponent_local ha hz
    obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp hOpenΞ z hzΞ
    rw [Metric.mem_closure_iff]
    intro r hr
    obtain ⟨w, hwC, hwd⟩ := Metric.mem_closure_iff.mp hzC (min r ρ) (lt_min hr hρ)
    have hwz : w ∈ Metric.ball z ρ := by
      rw [Metric.mem_ball, dist_comm]
      exact lt_of_lt_of_le hwd (min_le_right r ρ)
    exact ⟨w, ⟨hρsub hwz, hwC⟩, lt_of_lt_of_le hwd (min_le_left r ρ)⟩
  constructor
  · intro z hz
    exact key z hz S.U
      (Work.SphereJordan.trace_subset_closure_U S (traceComponent_subset_trace γ p ε a hz))
  · intro z hz
    exact key z hz S.V
      (Work.SphereJordan.trace_subset_closure_V S (traceComponent_subset_trace γ p ε a hz))

theorem chamberU_preconnected_of_le_two {γ : Work.Smooth.Jordan.PlaneCurve} (hs : γ.IsSimple)
    (S : Work.Smooth.Jordan.PlaneSeparation γ) {p : ℂ} {ε : ℝ} {a : ℂ}
    (ha : a ∈ γ.trace ∩ Metric.ball p ε)
    (hcc : ∀ x y z : ℂ,
      x ∈ connectedComponentIn (sideChamber γ p ε a) a \ traceComponent γ p ε a →
      y ∈ connectedComponentIn (sideChamber γ p ε a) a \ traceComponent γ p ε a →
      z ∈ connectedComponentIn (sideChamber γ p ε a) a \ traceComponent γ p ε a →
      connectedComponentIn (connectedComponentIn (sideChamber γ p ε a) a \ traceComponent γ p ε a) x =
        connectedComponentIn (connectedComponentIn (sideChamber γ p ε a) a \ traceComponent γ p ε a) y ∨
      connectedComponentIn (connectedComponentIn (sideChamber γ p ε a) a \ traceComponent γ p ε a) x =
        connectedComponentIn (connectedComponentIn (sideChamber γ p ε a) a \ traceComponent γ p ε a) z ∨
      connectedComponentIn (connectedComponentIn (sideChamber γ p ε a) a \ traceComponent γ p ε a) y =
        connectedComponentIn (connectedComponentIn (sideChamber γ p ε a) a \ traceComponent γ p ε a) z) :
    IsPreconnected (connectedComponentIn (sideChamber γ p ε a) a ∩ S.U) := by
  have hε : 0 < ε := lt_of_le_of_lt dist_nonneg (Metric.mem_ball.mp ha.2)
  have hΞopen : IsOpen (connectedComponentIn (sideChamber γ p ε a) a) :=
    (isOpen_sideChamber_local (γ := γ) hs hε ha).connectedComponentIn
  have hsd := chamber_sdiff_eq_local (γ := γ) S ha
  have hUopen : IsOpen (connectedComponentIn (sideChamber γ p ε a) a ∩ S.U) := hΞopen.inter S.isOpen_U
  have hVopen : IsOpen (connectedComponentIn (sideChamber γ p ε a) a ∩ S.V) := hΞopen.inter S.isOpen_V
  have hdisj : Disjoint (connectedComponentIn (sideChamber γ p ε a) a ∩ S.U)
      (connectedComponentIn (sideChamber γ p ε a) a ∩ S.V) :=
    S.disjoint_UV.mono Set.inter_subset_right Set.inter_subset_right
  have hsides := traceComponent_subset_closure_sides_local (γ := γ) hs S ha
  have hUne : (connectedComponentIn (sideChamber γ p ε a) a ∩ S.U).Nonempty := by
    rcases Metric.mem_closure_iff.mp (hsides.1 (mem_traceComponent ha)) 1 (by norm_num) with ⟨y, hy, -⟩
    exact ⟨y, hy⟩
  have hVne : (connectedComponentIn (sideChamber γ p ε a) a ∩ S.V).Nonempty := by
    rcases Metric.mem_closure_iff.mp (hsides.2 (mem_traceComponent ha)) 1 (by norm_num) with ⟨y, hy, -⟩
    exact ⟨y, hy⟩
  obtain ⟨x₀, hx₀U⟩ := hUne
  obtain ⟨x₃, hx₃V⟩ := hVne
  have memC : ∀ y : ℂ, y ∈ connectedComponentIn (sideChamber γ p ε a) a ∩ S.U ∨
      y ∈ connectedComponentIn (sideChamber γ p ε a) a ∩ S.V →
      y ∈ connectedComponentIn (sideChamber γ p ε a) a \ traceComponent γ p ε a := by
    intro y hy
    rw [hsd]
    exact hy
  have hx₀C := memC x₀ (Or.inl hx₀U)
  have hx₃C := memC x₃ (Or.inr hx₃V)
  have hcompU : ∀ y : ℂ, y ∈ connectedComponentIn (sideChamber γ p ε a) a ∩ S.U →
      connectedComponentIn (connectedComponentIn (sideChamber γ p ε a) a \ traceComponent γ p ε a) y ⊆
        connectedComponentIn (sideChamber γ p ε a) a ∩ S.U := by
    intro y hy
    have hyC : y ∈ connectedComponentIn (sideChamber γ p ε a) a \ traceComponent γ p ε a := memC y (Or.inl hy)
    have hsub : connectedComponentIn
        (connectedComponentIn (sideChamber γ p ε a) a \ traceComponent γ p ε a) y ⊆
        (connectedComponentIn (sideChamber γ p ε a) a ∩ S.U) ∪
          (connectedComponentIn (sideChamber γ p ε a) a ∩ S.V) := by
      intro u hu
      rw [← hsd]
      exact connectedComponentIn_subset _ _ hu
    rcases isPreconnected_connectedComponentIn.subset_or_subset hUopen hVopen hdisj hsub with h | h
    · exact h
    · exfalso
      exact hdisj.le_bot ⟨hy, h (mem_connectedComponentIn hyC)⟩
  have hDsub : connectedComponentIn
      (connectedComponentIn (sideChamber γ p ε a) a \ traceComponent γ p ε a) x₀ ⊆
      connectedComponentIn (sideChamber γ p ε a) a ∩ S.U := hcompU x₀ hx₀U
  have hUsub : connectedComponentIn (sideChamber γ p ε a) a ∩ S.U ⊆
      connectedComponentIn
        (connectedComponentIn (sideChamber γ p ε a) a \ traceComponent γ p ε a) x₀ := by
    intro y hy
    by_contra hyD
    have hyC : y ∈ connectedComponentIn (sideChamber γ p ε a) a \ traceComponent γ p ε a :=
      memC y (Or.inl hy)
    have hcyU : connectedComponentIn
        (connectedComponentIn (sideChamber γ p ε a) a \ traceComponent γ p ε a) y ⊆
        connectedComponentIn (sideChamber γ p ε a) a ∩ S.U := hcompU y hy
    have hneq1 : connectedComponentIn
        (connectedComponentIn (sideChamber γ p ε a) a \ traceComponent γ p ε a) x₀ ≠
        connectedComponentIn (connectedComponentIn (sideChamber γ p ε a) a \ traceComponent γ p ε a) y := by
      intro h
      have : y ∈ connectedComponentIn
          (connectedComponentIn (sideChamber γ p ε a) a \ traceComponent γ p ε a) x₀ := by
        rw [h]; exact mem_connectedComponentIn hyC
      exact hyD this
    have hneq2 : connectedComponentIn
        (connectedComponentIn (sideChamber γ p ε a) a \ traceComponent γ p ε a) x₀ ≠
        connectedComponentIn (connectedComponentIn (sideChamber γ p ε a) a \ traceComponent γ p ε a) x₃ := by
      intro h
      have : x₃ ∈ connectedComponentIn
          (connectedComponentIn (sideChamber γ p ε a) a \ traceComponent γ p ε a) x₀ := by
        rw [h]; exact mem_connectedComponentIn hx₃C
      exact (Set.disjoint_left.mp S.disjoint_UV (hDsub this).2) hx₃V.2
    have hneq3 : connectedComponentIn
        (connectedComponentIn (sideChamber γ p ε a) a \ traceComponent γ p ε a) y ≠
        connectedComponentIn (connectedComponentIn (sideChamber γ p ε a) a \ traceComponent γ p ε a) x₃ := by
      intro h
      have : x₃ ∈ connectedComponentIn
          (connectedComponentIn (sideChamber γ p ε a) a \ traceComponent γ p ε a) y := by
        rw [h]; exact mem_connectedComponentIn hx₃C
      exact (Set.disjoint_left.mp S.disjoint_UV (hcyU this).2) hx₃V.2
    rcases hcc x₀ y x₃ hx₀C hyC hx₃C with h | h | h
    · exact hneq1 h
    · exact hneq2 h
    · exact hneq3 h
  rw [← Set.Subset.antisymm hDsub hUsub]
  exact isPreconnected_connectedComponentIn



/-- **The chamber collar**: a single `S.U`-germ of the trace component `A` is contained in every
`S.U`-cell of the punctured ball whose closure meets `A`. -/
theorem chamberCollar {γ : Work.Smooth.Jordan.PlaneCurve}
    (hs : γ.IsSimple) (S : Work.Smooth.Jordan.PlaneSeparation γ)
    {p : ℂ} {ε : ℝ} {a : ℂ} (ha : a ∈ γ.trace ∩ Metric.ball p ε) :
    ∃ G : Set ℂ, G.Nonempty ∧ IsPreconnected G ∧ G ⊆ S.U ∧
      ∀ Ω : Set ℂ, (∃ w ∈ Metric.ball p ε \ γ.trace,
          Ω = connectedComponentIn (Metric.ball p ε \ γ.trace) w) →
        Ω ⊆ S.U → (closure Ω ∩ Work.SphereJordan.traceComponent γ p ε a).Nonempty → G ⊆ Ω := by
  have hpre : IsPreconnected (connectedComponentIn (sideChamber γ p ε a) a ∩ S.U) :=
    chamberU_preconnected_of_le_two (γ := γ) hs S ha (chamberCrosscut (γ := γ) hs S ha)
  refine ⟨connectedComponentIn (sideChamber γ p ε a) a ∩ S.U, ?_, hpre,
    Set.inter_subset_right, ?_⟩
  · -- nonempty: `A` meets the closure of `Ξ ∩ S.U`
    have hcl := (traceComponent_subset_closure_sides_local (γ := γ) hs S ha).1
      (mem_traceComponent ha)
    rcases Metric.mem_closure_iff.mp hcl 1 (by norm_num) with ⟨y, hy, -⟩
    exact ⟨y, hy⟩
  · intro Ω hΩ hU hacc
    obtain ⟨w, hw, rfl⟩ := hΩ
    have hΞ : connectedComponentIn (Metric.ball p ε \ γ.trace) w ⊆
        connectedComponentIn (sideChamber γ p ε a) a :=
      component_subset_chamber_of_closure_meets_local (γ := γ) ha hw hacc
    have hxΩ : w ∈ connectedComponentIn (Metric.ball p ε \ γ.trace) w :=
      mem_connectedComponentIn hw
    have hxU : w ∈ connectedComponentIn (sideChamber γ p ε a) a ∩ S.U :=
      ⟨hΞ hxΩ, hU hxΩ⟩
    have hsub : connectedComponentIn (sideChamber γ p ε a) a ∩ S.U ⊆
        Metric.ball p ε \ γ.trace := by
      rintro y ⟨hyΞ, hyU⟩
      exact ⟨sideChamber_subset_ball γ p ε a (connectedComponentIn_subset _ _ hyΞ),
        fun hyt => (unboundedSide_subset_compl_trace_local S hyU) hyt⟩
    exact hpre.subset_connectedComponentIn hxU hsub

end

end Work.SphereJordan
