import Mathlib
import Submission.NestedFamily
import Submission.JunctionOrder
import Submission.OverlapConn

open LeanEval.KnotTheory.Quadrisecant
open Set
open scoped Real Topology

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false

noncomputable section
namespace LeanEval.KnotTheory.Quadrisecant

/-!
# S201 — the overlap-connectivity reduction to the local interfaces (the
first ordering-content lemmas of the O-side; module
Submission/OverlapHconn.lean)

The S200 certificate (`prefixOverlap_connected_of_terminal`) turns the
facing-terminal data of the chain step into the S183 `hconn` at a level.
The remaining O-side ordering content is the supply of that facing-
terminal/overlap structure from the walk geometry.  This module proves
the FIRST reduction of that supply chain — from the global prefix-overlap
`hconn` to two LOCAL interface conditions:

1. **`chartOverlap_connected_of_transitionDomain`** — the trace-overlap
   connectedness transfer: the overlap `chartTrace ch₁ ∩ chartTrace ch₂`
   of two chart traces is connected exactly when the transition domain
   `transitionDomain ch₁ ch₂` (the `ch₁`-coordinates whose classes lie
   in `ch₂`'s trace — the coordinate set of the overlap) is connected.
   Proof: the overlap is the range of the continuous map
   `x ↦ oChartLift ch₁ x` on the transition-domain subtype
   (`isConnected_range`), and every overlap class is the lift of its own
   `ch₁`-coordinate (`chParam` + `chParam_lift`), so the range is the
   whole overlap.  This is where the S199/WI machinery attaches: it
   certifies connectedness on the junction component of the transition
   domain component-wise;
2. **`walk_prefixOverlap_connected_of_nonWrapping`** — the S183 `hconn k`
   of the walk prefix from the NON-WRAPPING interface: if the next trace
   meets the `k`-prefix only inside the last trace `T k`
   (`hNW : P'_k ∩ T (k+1) ⊆ T k` — the new trace attaches only at the
   terminal end, never wrapping back to earlier traces) and the
   successive transition domain `D_k` is connected (`hD`, the local
   interface), then the prefix-overlap subtype is `ConnectedSpace` —
   the `hconn k` of the S183 engine at level `k`.  Proof: `hNW` gives
   the set equality `P'_k ∩ T (k+1) = T k ∩ T (k+1)` (the reverse
   inclusion is `T k ⊆ P'_k`), and (1) transfers the transition-domain
   connectedness to the successive overlap.

These two lemmas are the first verified pieces of the O-side ordering
content: they reduce the global overlap-connectivity obligation of the
chaining to (a) the non-wrapping interface hypothesis (the dichotomy
content, to be supplied by the walk/component geometry) and (b) the
connectedness of each successive transition domain (the local fact the
S199 class-order/WI machinery certifies on the junction component, and
which the per-length cells (S195–S198) refine near the orbit class).

Everything here is verified (no axioms, no `sorry`).
-/

/-- **S201(i) — the trace-overlap connectedness transfer.**  The overlap
of two chart traces is connected iff the transition domain of `ch₁`
towards `ch₂` (the `ch₁`-coordinates whose classes lie in the `ch₂`
trace — the coordinate set of the overlap) is connected: the overlap is
the continuous image `x ↦ oChartLift ch₁ x` of the transition-domain
subtype, and every overlap class is the lift of its own `ch₁`-coordinate.
This reduces the S183 `hconn` of a successive overlap to a statement
about the transition domain in ONE chart's coordinates — the local
certificate the S199/WI machinery supplies component-wise. -/
lemma chartOverlap_connected_of_transitionDomain {r : ℝ → Space} {c₁₀ c₂₀ : OSub r}
    (ch₁ : OSub1Chart r c₁₀) (ch₂ : OSub1Chart r c₂₀)
    (hD : IsConnected (transitionDomain ch₁ ch₂)) :
    IsConnected (chartTrace ch₁ ∩ chartTrace ch₂ : Set (OSub r)) := by
  let D : Set (ChartInterval ch₁.lo ch₁.hi) := transitionDomain ch₁ ch₂
  let B := {x : ChartInterval ch₁.lo ch₁.hi // x ∈ D}
  haveI : ConnectedSpace B := Subtype.connectedSpace (s := D) hD
  let f : B → OSub r := fun x => oChartLift ch₁ x.1
  have hf : Continuous f := by
    dsimp [f]
    exact (continuous_oChartLift ch₁).comp continuous_subtype_val
  have hconnRange : IsConnected (Set.range f) := isConnected_range hf
  have hrange : Set.range f = chartTrace ch₁ ∩ chartTrace ch₂ := by
    ext c
    constructor
    · rintro ⟨x, rfl⟩
      constructor
      · exact (mem_chartTrace ch₁ (oChartLift ch₁ x.1)).mpr (oChartLift_mem_W ch₁ x.1)
      · exact x.2
    · intro hc
      rcases hc with ⟨hc1, hc2⟩
      let x₀ : ChartInterval ch₁.lo ch₁.hi := chParam ch₁ c ((mem_chartTrace ch₁ c).mp hc1)
      have hx₀D : x₀ ∈ D := by
        dsimp [x₀, D, transitionDomain]
        have hl : oChartLift ch₁ (chParam ch₁ c ((mem_chartTrace ch₁ c).mp hc1)) = c :=
          chParam_lift ch₁ ((mem_chartTrace ch₁ c).mp hc1)
        rw [hl]
        exact (mem_chartTrace ch₂ c).mp hc2
      refine ⟨⟨x₀, hx₀D⟩, ?_⟩
      dsimp [f]
      change oChartLift ch₁ (chParam ch₁ c ((mem_chartTrace ch₁ c).mp hc1)) = c
      exact chParam_lift ch₁ ((mem_chartTrace ch₁ c).mp hc1)
  rw [← hrange]
  exact hconnRange

/-- **S201(ii) — the walk prefix-overlap connectedness from the
non-wrapping + transition-domain-connectivity interface.**  With the
non-wrapping hypothesis (`hNW`: the next trace meets the prefix only
inside the last trace `T k`) and connectedness of the successive
transition domain `D_k` (the interface the S199/WI machinery certifies
on the junction component), the prefix-overlap of the S183 engine is
connected (`hconn k`). -/
theorem walk_prefixOverlap_connected_of_nonWrapping {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (k : ℕ)
    (hNW : ∀ c : OSub r,
        c ∈ (⋃ j ∈ Finset.range (k + 1), chartTrace (walkChart h hqf hgp cl e j)) ∩
            chartTrace (walkChart h hqf hgp cl e (k + 1)) →
        c ∈ chartTrace (walkChart h hqf hgp cl e k))
    (hD : IsConnected (transitionDomain (walkChart h hqf hgp cl e k)
      (walkChart h hqf hgp cl e (k + 1)))) :
    ConnectedSpace {c : OSub r // c ∈ (⋃ j ∈ Finset.range (k + 1),
        chartTrace (walkChart h hqf hgp cl e j)) ∩
          chartTrace (walkChart h hqf hgp cl e (k + 1))} := by
  have hk : k ∈ Finset.range (k + 1) := by
    exact (Finset.mem_range).mpr (by omega)
  have hset : (⋃ j ∈ Finset.range (k + 1), chartTrace (walkChart h hqf hgp cl e j)) ∩
        chartTrace (walkChart h hqf hgp cl e (k + 1)) =
      chartTrace (walkChart h hqf hgp cl e k) ∩
        chartTrace (walkChart h hqf hgp cl e (k + 1)) := by
    ext c
    constructor
    · intro hc
      rcases hc with ⟨hcP, hcN⟩
      constructor
      · exact hNW c ⟨hcP, hcN⟩
      · exact hcN
    · intro hc
      rcases hc with ⟨hck, hcN⟩
      constructor
      · exact Set.mem_iUnion₂.mpr ⟨k, hk, hck⟩
      · exact hcN
  have hconnA : IsConnected ((⋃ j ∈ Finset.range (k + 1),
        chartTrace (walkChart h hqf hgp cl e j)) ∩
          chartTrace (walkChart h hqf hgp cl e (k + 1)) : Set (OSub r)) := by
    rw [hset]
    exact chartOverlap_connected_of_transitionDomain
      (walkChart h hqf hgp cl e k) (walkChart h hqf hgp cl e (k + 1)) hD
  exact Subtype.connectedSpace (s := (⋃ j ∈ Finset.range (k + 1),
        chartTrace (walkChart h hqf hgp cl e j)) ∩
          chartTrace (walkChart h hqf hgp cl e (k + 1))) hconnA

end LeanEval.KnotTheory.Quadrisecant
