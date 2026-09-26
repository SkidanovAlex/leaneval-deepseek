import Mathlib
import Submission.OChartExhaustion
import Submission.ChartTracePath
import Submission.ConnectedWalk

open LeanEval.KnotTheory.Quadrisecant
open LeanEval.KnotTheory.Quadrisecant.ConnectedWalk
open Set
open scoped Real Topology unitInterval

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

/-!
# The component chart-trace walk: instantiation of the ConnectedWalk
machinery over the chart-trace cover of a component (S115)

`OChartComponent.lean` (S107) proved that every connected component
`C = connectedComponent c₀` of the trisecant set is covered by the chart
traces of countably many classes of `C` itself (`component_countable_chart_cover`,
the family `cl : ℕ → OSub r`); `ChartTracePath.lean` (S114) proved that
each chart trace is open and path-connected (it is homeomorphic to an
open real interval, `chartInterval_pathConnected` + the chart homeo).
This module INSTANTIATES the generic overlap-walk / path-connected
exhaustion machinery of `ConnectedWalk.lean` (S113) at the component:

1. `isOpen_OChartTraceSet` and `OChartTrace_subset_component` (the trace
   of a chart of the S107 family lies inside the component, since it is
   path-connected — hence connected — and contains its centre class);
2. **`component_trace_walk`**: over the component (realised as the
   preconnected subspace `ComponentSub c₀ := {y : OSub r // y ∈
   connectedComponent c₀}`), there is an enumeration `cl` (the S107
   cover) and an overlap walk `e` of its trace indices with `e 0 = 0`,
   surjective, consecutive traces overlapping, and the partial unions
   `⋃_{m < n+1} OChartTraceSet (cl (e m))` are path-connected open sets,
   increasing, contained in the component, and exhausting it — the
   topological skeleton of the interval-chain-ordering construction of
   the component classification (brick (b) remainder).

The transfer from the abstract subspace to the ambient trace sets uses
the embedding `ComponentSub c₀ → OSub r` together with
`IsInducing.isPathConnected_iff` and `Subtype.image_preimage_val` (the
trace lies inside the component, so the projection recovers it exactly).

Everything here is elementary and verified (no axioms, no `sorry`).
-/

/-- A connected component of the trisecant set, as a topological subspace
of `OSub r`. -/
abbrev ComponentSub {r : ℝ → Space} (c₀ : OSub r) : Type :=
  {y : OSub r // y ∈ connectedComponent c₀}

/-- A connected component is a preconnected space. -/
instance preconnectedSpace_componentSub {r : ℝ → Space} (c₀ : OSub r) :
    PreconnectedSpace (ComponentSub c₀) :=
  Subtype.preconnectedSpace (s := connectedComponent c₀) isPreconnected_connectedComponent

/-- The trace of the chart at `x` (an `OChartTraceSet`) is open in
`OSub r`. -/
lemma isOpen_OChartTraceSet {r : ℝ → Space} {h : IsSmoothKnot r}
    {hqf : QuadrisecantFree r} {hgp : TorusGeneralPositionTransverse r} (x : OSub r) :
    IsOpen (OChartTraceSet h hqf hgp x) := by
  dsimp [OChartTraceSet]
  exact ((oChartAtClass h hqf hgp x).W_open).preimage continuous_subtype_val

/-- The chart trace at `x` lies in the connected component of `x` (it is
path-connected, hence connected, and contains its centre class). -/
lemma OChartTrace_subset_component {r : ℝ → Space} {h : IsSmoothKnot r}
    {hqf : QuadrisecantFree r} {hgp : TorusGeneralPositionTransverse r}
    (c₀ x : OSub r) (hx : x ∈ connectedComponent c₀) :
    OChartTraceSet h hqf hgp x ⊆ connectedComponent c₀ := by
  have hsub := chartTrace_subset_connectedComponent (oChartAtClass h hqf hgp x)
  have htr : OChartTraceSet h hqf hgp x = chartTrace (oChartAtClass h hqf hgp x) := by
    rfl
  rw [htr]
  rw [← (connectedComponent_eq hx)] at hsub
  exact hsub

/-- Membership in an `Iio`-indexed union of sets. -/
private lemma mem_iUnion_Iio {X : Type*} (U : ℕ → Set X) (n : ℕ) (x : X) :
    (x ∈ ⋃ m ∈ Set.Iio n, U m) ↔ ∃ m : ℕ, m < n ∧ x ∈ U m := by
  simp

/-- **Component chart-trace walk and exhaustion.**  A connected component
of the trisecant set carries an overlap walk over its S107 chart-trace
cover whose partial unions are path-connected open sets exhausting the
component: the enumeration input of the interval-chain-ordering
construction (S113 machinery instantiated with the S114 trace facts). -/
theorem component_trace_walk {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r) (c₀ : OSub r) :
    ∃ (cl : ℕ → OSub r) (e : ℕ → ℕ),
      (∀ n : ℕ, cl n ∈ connectedComponent c₀) ∧ e 0 = 0 ∧ Function.Surjective e ∧
      (∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
          OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty) ∧
      (∀ n : ℕ, IsPathConnected
        (⋃ m ∈ Set.Iio (n + 1), OChartTraceSet h hqf hgp (cl (e m)))) ∧
      (∀ n : ℕ, (⋃ m ∈ Set.Iio (n + 1), OChartTraceSet h hqf hgp (cl (e m))) ⊆
        connectedComponent c₀) ∧
      (∀ n : ℕ, (⋃ m ∈ Set.Iio (n + 1), OChartTraceSet h hqf hgp (cl (e m))) ⊆
        ⋃ m ∈ Set.Iio (n + 2), OChartTraceSet h hqf hgp (cl (e m))) ∧
      (connectedComponent c₀ ⊆
        ⋃ n : ℕ, ⋃ m ∈ Set.Iio (n + 1), OChartTraceSet h hqf hgp (cl (e m))) := by
  classical
  rcases component_countable_chart_cover h hqf hgp c₀ with ⟨cl, hclmem, hcover⟩
  -- the chart-trace cover on the component subspace ComponentSub c₀
  let U : ℕ → Set (ComponentSub c₀) :=
    fun n => {p : ComponentSub c₀ | (p : OSub r) ∈ OChartTraceSet h hqf hgp (cl n)}
  have hUo : ∀ n, IsOpen (U n) := by
    intro n
    dsimp [U]
    exact (isOpen_OChartTraceSet (x := cl n)).preimage continuous_subtype_val
  have hUn : ∀ n, (U n).Nonempty := by
    intro n
    refine ⟨⟨cl n, hclmem n⟩, ?_⟩
    dsimp [U]
    exact (oChartAtClass h hqf hgp (cl n)).c₀_mem
  have hUcov : ∀ p : ComponentSub c₀, ∃ n, p ∈ U n := by
    intro p
    rcases hcover p.1 p.2 with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    dsimp [U]
    exact hn
  have hUpc : ∀ n, IsPathConnected (U n) := by
    intro n
    let T : Set (OSub r) := OChartTraceSet h hqf hgp (cl n)
    have hTpc : IsPathConnected T := oChartTrace_pathConnected (x := cl n)
    have hTsub : T ⊆ connectedComponent c₀ :=
      OChartTrace_subset_component c₀ (cl n) (hclmem n)
    have hUn_eq : U n = (fun p : ComponentSub c₀ => (p : OSub r)) ⁻¹' T := by
      ext p
      rfl
    rw [hUn_eq]
    rw [(Topology.IsInducing.isPathConnected_iff
        (X := ComponentSub c₀) (Y := OSub r)
        (f := fun p : ComponentSub c₀ => (p : OSub r))
        (F := (fun p : ComponentSub c₀ => (p : OSub r)) ⁻¹' T)
        (Topology.IsInducing.subtypeVal (Y := OSub r) (t := connectedComponent c₀)))]
    rw [Subtype.image_preimage_val (connectedComponent c₀) T]
    rw [Set.inter_comm]
    rw [Set.inter_eq_left.mpr hTsub]
    exact hTpc
  rcases exists_pathConnected_open_exhaustion
    (X := ComponentSub c₀) U hUo hUn hUcov hUpc with
    ⟨e, V, e0, esurj, hadj, hVopen, hVpc, hVinc, hVcov, hVeq⟩
  refine ⟨cl, e, hclmem, e0, esurj, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    rcases hadj n with ⟨p, hpU1, hpU2⟩
    refine ⟨(p : OSub r), hpU1, hpU2⟩
  · intro n
    have hcont : Continuous (fun p : ComponentSub c₀ => (p : OSub r)) := continuous_subtype_val
    have himg : IsPathConnected ((fun p : ComponentSub c₀ => (p : OSub r)) '' V n) :=
      (hVpc n).image hcont
    have htraces : (fun p : ComponentSub c₀ => (p : OSub r)) '' V n =
        (⋃ m ∈ Set.Iio (n + 1), OChartTraceSet h hqf hgp (cl (e m))) := by
      ext y
      rw [mem_iUnion_Iio]
      constructor
      · rintro ⟨p, hpV, rfl⟩
        rw [hVeq n] at hpV
        rw [mem_iUnion_Iio] at hpV
        rcases hpV with ⟨m, hm, hpm⟩
        refine ⟨m, hm, ?_⟩
        simpa [U] using hpm
      · rintro ⟨m, hm, hym⟩
        refine ⟨⟨y, OChartTrace_subset_component c₀ (cl (e m)) (hclmem (e m)) hym⟩, ?_, rfl⟩
        rw [hVeq n]
        rw [mem_iUnion_Iio]
        refine ⟨m, hm, ?_⟩
        simpa [U] using hym
    rwa [← htraces]
  · intro n y hy
    rw [mem_iUnion_Iio] at hy
    rcases hy with ⟨m, hm, hym⟩
    exact OChartTrace_subset_component c₀ (cl (e m)) (hclmem (e m)) hym
  · intro n y hy
    rw [mem_iUnion_Iio] at hy
    rcases hy with ⟨m, hm, hym⟩
    have hyVn : (⟨y, OChartTrace_subset_component c₀ (cl (e m)) (hclmem (e m)) hym⟩ :
        ComponentSub c₀) ∈ V n := by
      rw [hVeq n]
      rw [mem_iUnion_Iio]
      refine ⟨m, hm, ?_⟩
      simpa [U] using hym
    have hyVn1 : (⟨y, OChartTrace_subset_component c₀ (cl (e m)) (hclmem (e m)) hym⟩ :
        ComponentSub c₀) ∈ V (n + 1) :=
      hVinc n hyVn
    rw [hVeq (n + 1)] at hyVn1
    rw [mem_iUnion_Iio] at hyVn1
    rcases hyVn1 with ⟨m', hm', hpm'⟩
    have hym' : y ∈ OChartTraceSet h hqf hgp (cl (e m')) := by
      simpa [U] using hpm'
    exact Set.mem_iUnion₂.mpr ⟨m', Set.mem_Iio.mpr hm', hym'⟩
  · intro y hy
    let p : ComponentSub c₀ := ⟨y, hy⟩
    rcases hVcov p with ⟨n, hpn⟩
    rw [hVeq n] at hpn
    rw [mem_iUnion_Iio] at hpn
    rcases hpn with ⟨m, hm, hpm⟩
    have hym : y ∈ OChartTraceSet h hqf hgp (cl (e m)) := by
      simpa [U, p] using hpm
    exact Set.mem_iUnion.mpr ⟨n,
      (Set.mem_iUnion₂.mpr ⟨m, Set.mem_Iio.mpr hm, hym⟩)⟩

end LeanEval.KnotTheory.Quadrisecant
