import Mathlib
import Submission.LevelZeroHconn
import Submission.TwoArcUnion
import Submission.RealIntervalShape

open LeanEval.KnotTheory.Quadrisecant
open Set
open scoped Real Topology

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false

noncomputable section
namespace LeanEval.KnotTheory.Quadrisecant

/-!
# S203 — the `hNW` interface at the first non-vacuous level and the
first two-junction prefix chart (module Submission/FirstPrefixChart.lean)

Per the S202 STATUS, the supply chain is down to the two interfaces
`hD` and `hNW`.  This module stabilises `hNW` at its FIRST non-vacuous
level (k = 1: the third trace must meet the two-trace prefix only
inside the last trace) and — with the `hD` interfaces of S202 — proves
the FIRST GENUINE OUTPUT of the chaining: the interval chart of the
three-trace prefix `P'_3 = T 0 ∪ T 1 ∪ T 2` (two junctions).

1. **`walk_prefixOverlap_connected_one`** — the S183 `hconn 1`
   instance: `hNW₁` (the `k = 1` non-wrapping interface: `P'_2 ∩ T 2
   ⊆ T 1`) + `hD₁` (the `k = 1` transition-domain connectedness) ⇒
   the prefix-overlap at `k = 1` is connected (the S201(ii)
   `walk_prefixOverlap_connected_of_nonWrapping` instantiated at
   `k = 1` — the first level where `hNW` is genuinely needed);
2. **`walkChart_lt`** — the walk chart interval is nondegenerate (from
   the chart's `x₀_mem`), and **`walkTraceORI`** — the ORI-`(0,1)`
   chart of a walk trace: `chartTraceHomeo` composed with the affine
   interval normalisation (`homeo_Ioo_openUnit`, S162/commons L30);
3. **`walk_prefixThree_intervalChart`** — the landmark: from `hD₀`
   (S202) + `hNW₁` + `hD₁`, the S183 finite-chain engine charts the
   three-trace prefix: `Nonempty (ORI 0 1 ≃ₜ ↑P'_3)`.  Proof: the
   per-trace openness (`isOpen_chartTrace`), the per-trace ORI charts
   (`walkTraceORI`), and the two `hconn` instances (0 from S202, 1 from
   (1)) are exactly the hypotheses of
   `finite_chain_union_interval` (S183) at `n = 2`.

This is the first verified interval-chart of a MULTI-JUNCTION walk
prefix — the shape the S147-T chaining was aiming for — delivered from
the two atomic interfaces `hD` and `hNW`, each now with a stable
statement at the levels it is first needed.

Everything here is verified (no axioms, no `sorry`).
-/

/-- **S203(i) — the `hconn 1` instance from the interfaces** (`hNW 1`:
the third trace meets the two-trace prefix only inside the last trace
`T 1`; `hD₁`: connectedness of the transition domain of chart 1 towards
chart 2).  This is the S183 `hconn` at the first non-vacuous level —
the first level at which the non-wrapping hypothesis `hNW` is genuinely
needed. -/
theorem walk_prefixOverlap_connected_one {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (hNW1 : ∀ c : OSub r,
        c ∈ (⋃ j ∈ Finset.range 2, chartTrace (walkChart h hqf hgp cl e j)) ∩
            chartTrace (walkChart h hqf hgp cl e 2) →
        c ∈ chartTrace (walkChart h hqf hgp cl e 1))
    (hD1 : IsConnected (transitionDomain (walkChart h hqf hgp cl e 1)
      (walkChart h hqf hgp cl e 2))) :
    ConnectedSpace {c : OSub r // c ∈ (⋃ j ∈ Finset.range 2,
        chartTrace (walkChart h hqf hgp cl e j)) ∩
          chartTrace (walkChart h hqf hgp cl e 2)} := by
  exact walk_prefixOverlap_connected_of_nonWrapping h hqf hgp cl e hoverlap 1 hNW1 hD1

/-- The chart interval of a walk chart is nondegenerate. -/
lemma walkChart_lt {r : ℝ → Space} (h : IsSmoothKnot r) (hqf : QuadrisecantFree r)
    (hgp : TorusGeneralPositionTransverse r) (cl : ℕ → OSub r) (e : ℕ → ℕ) (k : ℕ) :
    (walkChart h hqf hgp cl e k).lo < (walkChart h hqf hgp cl e k).hi := by
  exact lt_trans (walkChart h hqf hgp cl e k).x₀_mem.1 (walkChart h hqf hgp cl e k).x₀_mem.2

/-- The ORI-`(0,1)` chart of a walk trace (from the chart homeo + the
affine interval normalisation of S162). -/
noncomputable def walkTraceORI {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ) (k : ℕ) :
    OpenRealInterval 0 1 ≃ₜ {c : OSub r // c ∈ chartTrace (walkChart h hqf hgp cl e k)} := by
  let e01 := Classical.choice (homeo_Ioo_openUnit (walkChart h hqf hgp cl e k).lo
    (walkChart h hqf hgp cl e k).hi (walkChart_lt h hqf hgp cl e k))
  exact e01.symm.trans (chartTraceHomeo (walkChart h hqf hgp cl e k))

/-- **S203(ii) — the first two-junction prefix interval chart.**  With
the two `hD` interfaces (`hD₀`, `hD₁`) and the first non-vacuous
non-wrapping interface (`hNW₁`), the three-trace prefix
`P'_3 = T 0 ∪ T 1 ∪ T 2` is interval-charted — the first genuine
output of the S183 finite-chain engine on the walk traces (the
`hconn` hypotheses 0 and 1 are exactly
`walk_prefixOverlap_connected_zero` and
`walk_prefixOverlap_connected_one`). -/
theorem walk_prefixThree_intervalChart {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (hD0 : IsConnected (transitionDomain (walkChart h hqf hgp cl e 0)
      (walkChart h hqf hgp cl e 1)))
    (hNW1 : ∀ c : OSub r,
        c ∈ (⋃ j ∈ Finset.range 2, chartTrace (walkChart h hqf hgp cl e j)) ∩
            chartTrace (walkChart h hqf hgp cl e 2) →
        c ∈ chartTrace (walkChart h hqf hgp cl e 1))
    (hD1 : IsConnected (transitionDomain (walkChart h hqf hgp cl e 1)
      (walkChart h hqf hgp cl e 2))) :
    Nonempty (OpenRealInterval 0 1 ≃ₜ {c : OSub r // c ∈ ⋃ j ∈ Finset.range 3,
        chartTrace (walkChart h hqf hgp cl e j)}) := by
  let T : ℕ → Set (OSub r) := fun j => chartTrace (walkChart h hqf hgp cl e j)
  have hopen : ∀ k : ℕ, k ≤ 2 → IsOpen (T k) := by
    intro k hk
    dsimp [T]
    exact isOpen_chartTrace (walkChart h hqf hgp cl e k)
  have hchart : ∀ k : ℕ, k ≤ 2 → Nonempty (OpenRealInterval 0 1 ≃ₜ {x : OSub r // x ∈ T k}) := by
    intro k hk
    dsimp [T]
    exact ⟨walkTraceORI h hqf hgp cl e k⟩
  have hconn : ∀ k : ℕ, k < 2 →
      ConnectedSpace {x : OSub r // x ∈ (⋃ j ∈ Finset.range (k + 1), T j) ∩ T (k + 1)} := by
    intro k hk
    have hk0 : k = 0 ∨ k = 1 := by omega
    rcases hk0 with hk0 | hk1
    · subst k
      dsimp [T]
      exact walk_prefixOverlap_connected_zero h hqf hgp cl e hoverlap hD0
    · subst k
      dsimp [T]
      exact walk_prefixOverlap_connected_one h hqf hgp cl e hoverlap hNW1 hD1
  rcases finite_chain_union_interval (X := OSub r) T 2 hopen hchart hconn with ⟨e⟩
  refine ⟨e.symm⟩

end LeanEval.KnotTheory.Quadrisecant
