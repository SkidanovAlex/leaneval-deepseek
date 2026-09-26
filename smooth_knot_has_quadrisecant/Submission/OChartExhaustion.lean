import Mathlib
import Submission.OChartComponent
import Submission.OChartChain

open LeanEval.KnotTheory.Quadrisecant
open Filter
open scoped Real Topology unitInterval

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

/-!
# Milestone-2 (iv) step 6, brick (b) — the exhaustion of a component by
chart traces (first exhaustion lemma)

`OChartComponent.lean` (S107) proved that every connected component
`C = connectedComponent c₀` of the trisecant set is covered by the traces
of the interval charts centred at countably many classes of `C`
(`component_countable_chart_cover`, via hereditarily Lindelöf).  This
module proves the first exhaustion lemma of the arc/circle classification
route: the **increasing exhaustion by chart traces**.

1. **generic exhaustion set arithmetic** (pure, over any family
   `tr : ℕ → Set α` and set `C`): `exhaustionStep C tr n` (the step
   `Eₙ = (⋃_{m<n} tr m) ∩ C`), `exhaustionStep_subset` (`Eₙ ⊆ C`),
   `exhaustionStep_mono` (`Eₙ ⊆ Eₙ₊₁`), and
   `subset_iUnion_exhaustionStep_of_cover` (if `tr` covers `C` then
   `C ⊆ ⋃ₙ Eₙ`, with `E_{m+1}` witnessing the point covered at index
   `m`);
2. **the chart-trace instance** — `OChartTraceSet h hqf hgp x` (the trace
   of the interval chart at `x` as a set of `OSub r`) and
   **`component_chart_exhaustion`**: from `component_countable_chart_cover`
   one obtains `cl : ℕ → OSub r` with all `cl n ∈ C` such that the steps
   `Eₙ = (⋃_{m<n} OChartTraceSet (cl m)) ∩ C` are increasing
   (`Eₙ ⊆ Eₙ₊₁`) and cover `C` (`C ⊆ ⋃ₙ Eₙ`).

This is the countable-exhaustion foundation on which the interval-chain
exhaustion (next slice: build from each `Eₙ` an interval-charted open set
`Uₙ`, gluing chart traces by the transition homeomorphisms with the
orientation data of the monotone machinery) and finally the dichotomy
"compact ⇒ circle / non-compact ⇒ open interval" are assembled.

Everything here is elementary and verified (no axioms, no `sorry`).
-/

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

/-- The `n`-th exhaustion step: the union of the first `n` trace sets of
the family `tr` intersected with the component `C` (`Eₙ = (⋃_{m<n} tr m)
∩ C`). -/
def exhaustionStep {α : Type*} (C : Set α) (tr : ℕ → Set α) (n : ℕ) : Set α :=
  (⋃ m ∈ Set.Iio n, tr m) ∩ C

/-- The exhaustion steps lie inside the component. -/
lemma exhaustionStep_subset {α : Type*} (C : Set α) (tr : ℕ → Set α) (n : ℕ) :
    exhaustionStep C tr n ⊆ C := by
  intro x hx
  exact hx.2

/-- The exhaustion is increasing: `Eₙ ⊆ Eₙ₊₁` (pure set arithmetic over
the initial segments `Iio n`). -/
lemma exhaustionStep_mono {α : Type*} (C : Set α) (tr : ℕ → Set α) (n : ℕ) :
    exhaustionStep C tr n ⊆ exhaustionStep C tr (n + 1) := by
  intro x hx
  constructor
  · rcases Set.mem_iUnion₂.mp hx.1 with ⟨m, hm, hxm⟩
    have hmn : m < n := Set.mem_Iio.mp hm
    exact Set.mem_iUnion₂.mpr ⟨m, Set.mem_Iio.mpr (by omega), hxm⟩
  · exact hx.2

/-- **The exhaustion covers the component.**  If the family `tr` covers
`C`, then every point of `C` lies in some exhaustion step (`E_{m+1}` for
the index `m` covering it): `C ⊆ ⋃ₙ Eₙ`. -/
lemma subset_iUnion_exhaustionStep_of_cover {α : Type*} (C : Set α) (tr : ℕ → Set α)
    (hcover : C ⊆ ⋃ n : ℕ, tr n) :
    C ⊆ ⋃ n : ℕ, exhaustionStep C tr n := by
  intro x hx
  rcases Set.mem_iUnion.mp (hcover hx) with ⟨m, hxm⟩
  exact Set.mem_iUnion.mpr ⟨m + 1, by
    constructor
    · exact Set.mem_iUnion₂.mpr ⟨m, Set.mem_Iio.mpr (by omega), hxm⟩
    · exact hx⟩




/-- The chart trace set of a class, as a set of `OSub r`: the classes
whose band value lies in the trace `W` of the interval chart at `x`. -/
def OChartTraceSet {r : ℝ → Space} (h : IsSmoothKnot r) (hqf : QuadrisecantFree r)
    (hgp : TorusGeneralPositionTransverse r) (x : OSub r) : Set (OSub r) :=
  {y : OSub r | (y : OpenMobius) ∈ (oChartAtClass h hqf hgp x).W}

/-- **The chart-trace exhaustion of a component.**  The countable cover of
`component_countable_chart_cover` gives an increasing exhaustion of the
component by the chart-trace steps
`Eₙ = (⋃_{m<n} trace(cl m)) ∩ connectedComponent c₀`:
`Eₙ ⊆ Eₙ₊₁` for all `n` and `C ⊆ ⋃ₙ Eₙ` — the first exhaustion lemma of
the arc/circle classification route (pure set arithmetic over the
countable cover). -/
theorem component_chart_exhaustion {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r) (c₀ : OSub r) :
    ∃ cl : ℕ → OSub r,
      (∀ n : ℕ, cl n ∈ connectedComponent c₀) ∧
      (∀ n : ℕ,
        exhaustionStep (connectedComponent c₀)
            ((OChartTraceSet h hqf hgp) ∘ cl) n ⊆
          exhaustionStep (connectedComponent c₀)
            ((OChartTraceSet h hqf hgp) ∘ cl) (n + 1)) ∧
      (connectedComponent c₀ ⊆
        ⋃ n : ℕ, exhaustionStep (connectedComponent c₀)
          ((OChartTraceSet h hqf hgp) ∘ cl) n) := by
  rcases component_countable_chart_cover h hqf hgp c₀ with ⟨cl, hclmem, hcover⟩
  refine ⟨cl, hclmem, ?_, ?_⟩
  · intro n
    exact exhaustionStep_mono (connectedComponent c₀) ((OChartTraceSet h hqf hgp) ∘ cl) n
  · have hcovset : (connectedComponent c₀ : Set (OSub r)) ⊆
        ⋃ n : ℕ, ((OChartTraceSet h hqf hgp) ∘ cl) n := by
      intro y hy
      rcases hcover y hy with ⟨n, hyn⟩
      exact Set.mem_iUnion.mpr ⟨n, by simpa [OChartTraceSet] using hyn⟩
    exact subset_iUnion_exhaustionStep_of_cover (connectedComponent c₀)
      ((OChartTraceSet h hqf hgp) ∘ cl) hcovset

end LeanEval.KnotTheory.Quadrisecant
