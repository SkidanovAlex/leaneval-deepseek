import Mathlib
import Submission.OverlapHconn

open LeanEval.KnotTheory.Quadrisecant
open Set
open scoped Real Topology

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false

noncomputable section
namespace LeanEval.KnotTheory.Quadrisecant

/-!
# S202 — the first-level `hD` interface: exposing what the junction
geometry must deliver (module Submission/LevelZeroHconn.lean)

Per the S201 STATUS, the remaining supply chain is two links: `hD`
(transition-domain connectedness at each junction) and `hNW`
(non-wrapping).  This module takes the FIRST of them at the FIRST
nontrivial level (k = 0) and exposes precisely what it needs:

1. **`walk_prefixOverlap_connected_zero`** — the S183 `hconn 0`
   instance: at the first junction the non-wrapping hypothesis is
   VACUOUS (the prefix `P'_1` is the single trace `T 0` — there are no
   earlier traces to wrap back to), so `hconn 0` reduces to the single
   atomic interface `hD₀ := IsConnected (transitionDomain (walkChart
   h hqf hgp cl e 0) (walkChart h hqf hgp cl e 1))` — connectedness of
   the coordinate set of the overlap `T 0 ∩ T 1`.  Proof: the prefix
   set-equality `P'_1 = T 0` (`Finset.range_one`), then the S201(i)
   transfer + `Subtype.connectedSpace`;
2. **`walk_transitionDomain_nonempty`** — the `Nonempty` HALF of the
   `hD` interface at every junction `k`: the walk-overlap class
   `z_k ∈ T k ∩ T (k+1)` has a `ch k`-coordinate, which lies in the
   transition domain (this is provable outright — the overlap data
   `hoverlap` supplies `z_k`).

**Honest analysis of what `hD` needs (recorded here per the S106
policy).**  `IsConnected (transitionDomain …)` splits as
`Nonempty ∧ IsPreconnected`.  The Nonempty half is now PROVED
(`walk_transitionDomain_nonempty` — the WI/S150 machinery certifies the
component `C_k` of the overlap-class coordinate, open and preconnected
by S150 CO, and `C_k` is nonempty exactly by the overlap class).  The
Preconnected half — that `D_k` has no SECOND component (no "wrap"
component far from `z_k`) — is NOT derivable from the junction-component
geometry alone: two open arcs of a circle component can intersect in two
components (an arc longer than a semicircle wraps and meets its
successor twice), so `D_k` (the coordinate set of the successive
overlap) can be two intervals even though the WI component around `z_k`
is a single interval; ruling out the second component is exactly the
non-wrapping/dichotomy content.  Hence `hD` is an ATOMIC interface: the
first chaining step needs `hD₀`, and the dichotomy's interval side (or
an equivalent no-wrap ordering lemma) is what supplies `hD_k` at each
level.  The delegation target, once that side exists: the per-level
`IsConnected (transitionDomain (walkChart k) (walkChart (k+1)))`
instances feeding `walk_prefixOverlap_connected_zero` (k = 0) and
`walk_prefixOverlap_connected_of_nonWrapping` (k ≥ 1, with `hNW`).

Everything here is verified (no axioms, no `sorry`).
-/

/-- **S202 — the first-level `hconn` instance (k = 0).**  At the first
junction the non-wrapping hypothesis of
`walk_prefixOverlap_connected_of_nonWrapping` is VACUOUS (the prefix is
the single trace `T 0`), so the S183 `hconn 0` obligation reduces to the
single atomic interface `hD₀`: connectedness of the transition domain
`D₀` of chart 0 towards chart 1 (the coordinate set of the overlap
`T 0 ∩ T 1`). -/
theorem walk_prefixOverlap_connected_zero {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (hD : IsConnected (transitionDomain (walkChart h hqf hgp cl e 0)
      (walkChart h hqf hgp cl e 1))) :
    ConnectedSpace {c : OSub r // c ∈ (⋃ j ∈ Finset.range (1),
        chartTrace (walkChart h hqf hgp cl e j)) ∩
          chartTrace (walkChart h hqf hgp cl e 1)} := by
  have hconnA : IsConnected ((⋃ j ∈ Finset.range (1),
        chartTrace (walkChart h hqf hgp cl e j)) ∩
          chartTrace (walkChart h hqf hgp cl e 1) : Set (OSub r)) := by
    have hset : (⋃ j ∈ Finset.range (1), chartTrace (walkChart h hqf hgp cl e j)) =
        chartTrace (walkChart h hqf hgp cl e 0) := by
      ext c
      simp [Finset.range_one]
    rw [hset]
    exact chartOverlap_connected_of_transitionDomain
      (walkChart h hqf hgp cl e 0) (walkChart h hqf hgp cl e 1) hD
  exact Subtype.connectedSpace (s := (⋃ j ∈ Finset.range (1),
        chartTrace (walkChart h hqf hgp cl e j)) ∩
          chartTrace (walkChart h hqf hgp cl e 1)) hconnA

/-- **S202 — the transition domain is nonempty at every junction** (the
`Nonempty` half of the `hD` interface): the walk-overlap class
`z_k ∈ T k ∩ T (k+1)` has a `ch k`-coordinate, which lies in the
transition domain.  The remaining half of `hD = IsConnected
(transitionDomain …)` is `IsPreconnected` — the no-wrap content. -/
lemma walk_transitionDomain_nonempty {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (k : ℕ) :
    (transitionDomain (walkChart h hqf hgp cl e k) (walkChart h hqf hgp cl e (k + 1))).Nonempty := by
  let ch₁ := walkChart h hqf hgp cl e k
  let ch₂ := walkChart h hqf hgp cl e (k + 1)
  let t₀ : OChartTransitionDomain ch₁ ch₂ :=
    oChartTraceOverlapParam ch₁ ch₂ (walkOverlapClass h hqf hgp cl e hoverlap k)
      (walkOverlapClass_mem_left h hqf hgp cl e hoverlap k)
      (walkOverlapClass_mem_right h hqf hgp cl e hoverlap k)
  refine ⟨t₀.1, ?_⟩
  dsimp [transitionDomain, ch₁, ch₂]
  exact t₀.2

end LeanEval.KnotTheory.Quadrisecant
