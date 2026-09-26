import Mathlib
import Submission.NestedDatum

open LeanEval.KnotTheory.Quadrisecant
open Set
open scoped Real Topology

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

noncomputable section
namespace LeanEval.KnotTheory.Quadrisecant

/-!
# S195 — the per-length cell interface of the nested datum family
(module Submission/PerLengthCell.lean)

The NestedDatum family (`perLength_nested_datum_family`, S193/S194)
provides per-length aligned datums `subfam n` with head intervals
containing the orbit parameter `x₀`, nested heads, and per-length
forward totality.  This module PACKAGES that datum family into its
geometric interface — the per-length CELLS of the orbit class in the
trisecant-set component:

- `perLengthCell … subfam n` — the level-`n` cell: the range of the
  level-`n` arc (`walkAlignedArcMap … (subfam n)`, the `ch 0`-lift of
  the aligned start interval);
- `perLengthCell_open` — each cell is open (the S139 range openness read
  off the datum);
- `perLengthCell_antitone` — the cells NEST (decreasing): level-`(n+1)`
  ⊆ level-`n` (the S140b range nesting from the head nesting `hI`);
- `perLengthOrbitClass` — the orbit class `c₀` (the `ch 0`-lift of the
  parameter `x₀`);
- `perLengthCell_package` — at every level: the cell lies in the
  component of `c₀` and in the walk partial union `P'_{n+2}`, and the
  orbit class lies in the cell (the S140d single-level package read off
  the datum via `alignedData_arc_openSet`);
- `perLengthCell_chart` — each cell is interval-charted
  (`ChartInterval (datumPiece (subfam n 0)) ≃ₜ ↑cell`, the S140a chart
  of the datum range);
- **`perLength_cell_family`** — the packaged family theorem: from the
  walk data + orbit (`hland`), a family `subfam` with the three datum
  conjuncts AND the per-level cell interface (open, antitone, in the
  component, in `P'_{n+2}`, containing the orbit class, interval-
  charted).  The coordinate-compatibility conjuncts (the real-identity
  reindexing between consecutive level charts) are
  `perLength_reindex_identity`/`perLength_reindex_monotone` (S194),
  which take `(subfam, hI)` and instantiate directly after the `rcases`.

Everything here is elementary and verified (no axioms, no `sorry`).

S197 (appended): **`perLength_cell_family_prefix`** — the combined
family theorem: from the walk data + component + orbit (`hland`) a
per-length datum family whose level-`n` cells are open interval-charted
arcs in `C ∩ P'_{n+2}` that contain the orbit class, nest antitone, AND
lie in every prefix trace `T_m` (`m ≤ n+1`) — the single-interface
statement the S147-T chaining consumes (cells as the common-class
coordinate refinements of each prefix union).

S196 (appended): the per-length cells sit inside EVERY prefix trace of
the walk — the S147 interlock content in cell form:

- **`perLengthCell_subset_trace`** — the level-`n` cell lies in
  `T_m := OChartTraceSet (cl (e m))` for every `m ≤ n + 1`: a cell
  class is the `ch 0`-lift of a head parameter, and its prefix
  transport through the level-`n` datum sub-piece chain (the level
  totality restricted to the prefix `m−1` by
  `transports_chainTail_prefix`) is the `ch m`-coordinate of the same
  class (the S119 class-coordinate identification at the prefix) —
  hence the class lies in the `m`-th chart's trace; `m = 0` is the
  start-chart trace by construction;
- **`perLengthOrbitClass_mem_all_traces`** — the orbit class (the
  `ch 0`-lift of `x₀`) lies in EVERY walk trace `T_m` (`m ∈ ℕ`): under
  `hland`, `walkOrbit_all_lengths` transports the orbit parameter
  through every prefix and `walkOrbitClass_mem_traces` places its class
  in the reached chart's trace at each prefix length — the S147
  "one class common to all the walk traces" special configuration.

Together: each level-`n` cell is an interval-charted open arc inside
`C ∩ ⋂_{m ≤ n+1} T_m` containing the orbit class — the coordinate
refinement of the prefix union `P'_{n+2}` around the common class that
the S147-T chaining (H1 interlock) composes.
-/

/-- The level-`n` cell: the range of the level-`n` arc of a per-length
datum family. -/
def perLengthCell {r : ℝ → Space} (h : IsSmoothKnot r) (hqf : QuadrisecantFree r)
    (hgp : TorusGeneralPositionTransverse r) (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (subfam : (n : ℕ) → (i : ℕ) → SubDatum (WP h hqf hgp cl e hoverlap i))
    (n : ℕ) : Set (OSub r) :=
  Set.range (walkAlignedArcMap h hqf hgp cl e hoverlap (subfam n))

/-- The level-`n` cell is open (the range is the chart-lift image of the
open parameter cell — S139 range openness read off the datum). -/
lemma perLengthCell_open {r : ℝ → Space} (h : IsSmoothKnot r) (hqf : QuadrisecantFree r)
    (hgp : TorusGeneralPositionTransverse r) (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (subfam : (n : ℕ) → (i : ℕ) → SubDatum (WP h hqf hgp cl e hoverlap i))
    (n : ℕ) : IsOpen (perLengthCell h hqf hgp cl e hoverlap subfam n) := by
  dsimp [perLengthCell]
  rw [walkAlignedArcMap_range_eq_liftCell h hqf hgp cl e hoverlap (subfam n)]
  exact isOpen_lift_cell (walkChart h hqf hgp cl e 0)

/-- Cells nest (decreasing): level-`(n+1)` ⊆ level-`n` from the head
nesting `hI` (the S140b range nesting). -/
lemma perLengthCell_antitone {r : ℝ → Space} (h : IsSmoothKnot r) (hqf : QuadrisecantFree r)
    (hgp : TorusGeneralPositionTransverse r) (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (subfam : (n : ℕ) → (i : ℕ) → SubDatum (WP h hqf hgp cl e hoverlap i))
    (hI : ∀ n : ℕ,
      Set.Ioo (datumPiece (subfam (n + 1) 0)).lo (datumPiece (subfam (n + 1) 0)).hi ⊆
        Set.Ioo (datumPiece (subfam n 0)).lo (datumPiece (subfam n 0)).hi)
    (n : ℕ) :
    perLengthCell h hqf hgp cl e hoverlap subfam (n + 1) ⊆
      perLengthCell h hqf hgp cl e hoverlap subfam n := by
  intro c hc
  dsimp [perLengthCell] at hc ⊢
  rcases hc with ⟨u, rfl⟩
  exact walkAlignedArcMap_nested_range_mem h hqf hgp cl e hoverlap
    (subfam n) (subfam (n + 1)) (hI n) u

/-- The orbit class `c₀`: the `ch 0`-lift of the orbit parameter `x₀`
(the class common to all the walk traces — the anchor of the per-length
cells). -/
abbrev perLengthOrbitClass {r : ℝ → Space} (h : IsSmoothKnot r) (hqf : QuadrisecantFree r)
    (hgp : TorusGeneralPositionTransverse r) (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (x₀ : ChartInterval (WP h hqf hgp cl e hoverlap 0).lo (WP h hqf hgp cl e hoverlap 0).hi) :
    OSub r :=
  oChartLift (walkChart h hqf hgp cl e 0)
    ⟨(x₀ : ℝ), walkJunction_subset h hqf hgp cl e hoverlap 0 x₀.2⟩

/-- Cell containment package at a level (S140d read off a datum): cell
⊆ component of `c₀`, cell ⊆ the `(n+2)`-prefix union of traces, and the
orbit class lies in the cell. -/
lemma perLengthCell_package {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (c₀ : OSub r) (hc0 : cl (e 0) ∈ connectedComponent c₀)
    (x₀ : ChartInterval (WP h hqf hgp cl e hoverlap 0).lo (WP h hqf hgp cl e hoverlap 0).hi)
    (subfam : (n : ℕ) → (i : ℕ) → SubDatum (WP h hqf hgp cl e hoverlap i))
    (hmem : ∀ n : ℕ, (x₀ : ℝ) ∈
      Set.Ioo (datumPiece (subfam n 0)).lo (datumPiece (subfam n 0)).hi)
    (htot : ∀ n : ℕ, ∀ y : ChartInterval (datumPiece (subfam n 0)).lo (datumPiece (subfam n 0)).hi,
      transports (datumPiece (subfam n 0)) (chainTail (fun i => datumPiece (subfam n i)) 0 n) y)
    (n : ℕ) :
    perLengthCell h hqf hgp cl e hoverlap subfam n ⊆ connectedComponent c₀ ∧
    perLengthCell h hqf hgp cl e hoverlap subfam n ⊆
      ⋃ m ∈ Set.Iio (n + 2), OChartTraceSet h hqf hgp (cl (e m)) ∧
    perLengthOrbitClass h hqf hgp cl e hoverlap x₀ ∈
      perLengthCell h hqf hgp cl e hoverlap subfam n := by
  rcases alignedData_arc_openSet h hqf hgp cl e hoverlap c₀ hc0 n x₀
      (subfam n 0) (subfam n) rfl (hmem n) (htot n) with
    ⟨hinj, hcont, hopen, hC, hP, hanchor⟩
  constructor
  · intro c hc
    rcases hc with ⟨u, rfl⟩
    exact hC u
  constructor
  · intro c hc
    rcases hc with ⟨u, rfl⟩
    exact hP u
  · dsimp [perLengthCell, perLengthOrbitClass]
    exact hanchor

/-- The level-`n` cell is interval-charted (S140a chart of the datum
range). -/
noncomputable def perLengthCell_chart {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (subfam : (n : ℕ) → (i : ℕ) → SubDatum (WP h hqf hgp cl e hoverlap i))
    (n : ℕ) :
    ChartInterval (datumPiece (subfam n 0)).lo (datumPiece (subfam n 0)).hi ≃ₜ
      {c : OSub r // c ∈ perLengthCell h hqf hgp cl e hoverlap subfam n} := by
  change ChartInterval (datumPiece (subfam n 0)).lo (datumPiece (subfam n 0)).hi ≃ₜ
    {c : OSub r // c ∈ Set.range (walkAlignedArcMap h hqf hgp cl e hoverlap (subfam n))}
  exact walkAlignedArcMap_homeo_range h hqf hgp cl e hoverlap (subfam n)

/-- **S195 — the packaged per-length cell family.**  From walk data, a
component (`c₀` with the first walk class in it) and an orbit parameter
`x₀` with the uniform-landing property `hland` (S136/S190), there is a
per-length datum family `subfam` whose level-`n` cell interface is: head
contains `x₀` (C1); heads nest (C2, the S189 `hI`); forward totality
(C3); the cell is OPEN (C4); the cells nest (C5); the cell lies in the
component of `c₀` (C6) and in the walk partial union `P'_{n+2}` (C7);
the orbit class lies in every cell (C8); and each cell is interval-
charted (C9).  The consecutive-level coordinate compatibility
(real-identity reindexing) is `perLength_reindex_identity` /
`perLength_reindex_monotone` (S194), instantiable from the returned
`subfam`/C2. -/
theorem perLength_cell_family {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (c₀ : OSub r) (hc0 : cl (e 0) ∈ connectedComponent c₀)
    (x₀ : ChartInterval (WP h hqf hgp cl e hoverlap 0).lo (WP h hqf hgp cl e hoverlap 0).hi)
    (hland : ∀ (n : ℕ)
        (htr : transports (WP h hqf hgp cl e hoverlap 0)
          (chainTail (WP h hqf hgp cl e hoverlap) 0 n) x₀),
      chainValue (WP h hqf hgp cl e hoverlap 0 ::
          chainTail (WP h hqf hgp cl e hoverlap) 0 n) ⟨x₀, htr⟩ ∈
        Set.Ioo (WP h hqf hgp cl e hoverlap (n + 1)).lo (WP h hqf hgp cl e hoverlap (n + 1)).hi) :
    ∃ subfam : (n : ℕ) → (i : ℕ) → SubDatum (WP h hqf hgp cl e hoverlap i),
      (∀ n : ℕ, (x₀ : ℝ) ∈
        Set.Ioo (datumPiece (subfam n 0)).lo (datumPiece (subfam n 0)).hi) ∧
      (∀ n : ℕ,
        Set.Ioo (datumPiece (subfam (n + 1) 0)).lo (datumPiece (subfam (n + 1) 0)).hi ⊆
          Set.Ioo (datumPiece (subfam n 0)).lo (datumPiece (subfam n 0)).hi) ∧
      (∀ n : ℕ, ∀ y : ChartInterval (datumPiece (subfam n 0)).lo (datumPiece (subfam n 0)).hi,
        transports (datumPiece (subfam n 0))
          (chainTail (fun i => datumPiece (subfam n i)) 0 n) y) ∧
      (∀ n : ℕ, IsOpen (perLengthCell h hqf hgp cl e hoverlap subfam n)) ∧
      (∀ n : ℕ,
        perLengthCell h hqf hgp cl e hoverlap subfam (n + 1) ⊆
          perLengthCell h hqf hgp cl e hoverlap subfam n) ∧
      (∀ n : ℕ, perLengthCell h hqf hgp cl e hoverlap subfam n ⊆ connectedComponent c₀) ∧
      (∀ n : ℕ, perLengthCell h hqf hgp cl e hoverlap subfam n ⊆
        ⋃ m ∈ Set.Iio (n + 2), OChartTraceSet h hqf hgp (cl (e m))) ∧
      (∀ n : ℕ, perLengthOrbitClass h hqf hgp cl e hoverlap x₀ ∈
        perLengthCell h hqf hgp cl e hoverlap subfam n) ∧
      (∀ n : ℕ, Nonempty (ChartInterval (datumPiece (subfam n 0)).lo (datumPiece (subfam n 0)).hi ≃ₜ
        {c : OSub r // c ∈ perLengthCell h hqf hgp cl e hoverlap subfam n})) := by
  rcases perLength_nested_datum_family h hqf hgp cl e hoverlap x₀ hland with
    ⟨subfam, hmem, hI, htot⟩
  refine ⟨subfam, hmem, hI, htot, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact perLengthCell_open h hqf hgp cl e hoverlap subfam n
  · intro n
    exact perLengthCell_antitone h hqf hgp cl e hoverlap subfam hI n
  · intro n
    exact (perLengthCell_package h hqf hgp cl e hoverlap c₀ hc0 x₀ subfam hmem htot n).1
  · intro n
    exact (perLengthCell_package h hqf hgp cl e hoverlap c₀ hc0 x₀ subfam hmem htot n).2.1
  · intro n
    exact (perLengthCell_package h hqf hgp cl e hoverlap c₀ hc0 x₀ subfam hmem htot n).2.2
  · intro n
    exact ⟨perLengthCell_chart h hqf hgp cl e hoverlap subfam n⟩

/-! ## S196 — the cells and the orbit class inside every prefix trace

The level-`n` cell is the `ch 0`-lift of the aligned head interval; the
level-`n` totality transports every head parameter through the `n`-tail
datum sub-piece chain.  Restricting the totality to the prefix `i ≤ n`
(`transports_chainTail_prefix`), the S119 class-coordinate
identification at the prefix places the class of every cell point in the
trace of the `(i+1)`-th walk chart — so the level-`n` cell lies in
`T_m` for every `m ≤ n + 1`.  The orbit class (the `ch 0`-lift of
`x₀`) lies in every `T_m` (`m ∈ ℕ`) by the all-lengths orbit
(`walkOrbit_all_lengths`) and the prefix-trace theorem
(`walkOrbitClass_mem_traces`).  Everything here is verified (no axioms,
no `sorry`). -/

/-- **The level-`n` cell lies in every prefix trace `T_m` (`m ≤ n+1`).**
A cell class is the `ch 0`-lift of a head parameter; the level-`n`
totality transports it through the level-`n` datum sub-piece chain, and
at the prefix of length `m−1` the S119 class-coordinate identification
places the class in the `m`-th chart's trace (`m = 0` is the start
chart). -/
lemma perLengthCell_subset_trace {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (subfam : (n : ℕ) → (i : ℕ) → SubDatum (WP h hqf hgp cl e hoverlap i))
    (htot : ∀ n : ℕ, ∀ y : ChartInterval (datumPiece (subfam n 0)).lo (datumPiece (subfam n 0)).hi,
      transports (datumPiece (subfam n 0)) (chainTail (fun i => datumPiece (subfam n i)) 0 n) y)
    (n : ℕ) : ∀ m : ℕ, m ≤ n + 1 →
    perLengthCell h hqf hgp cl e hoverlap subfam n ⊆
      OChartTraceSet h hqf hgp (cl (e m)) := by
  intro m hm
  rcases m with _ | m
  · intro c hc
    rcases hc with ⟨u, rfl⟩
    have hmem0 : oChartLift (walkChart h hqf hgp cl e 0)
        ⟨(u : ℝ), datumPiece_chartSubset h hqf hgp cl e hoverlap 0 (subfam n 0) u.2⟩ ∈
        chartTrace (walkChart h hqf hgp cl e 0) := by
      exact (mem_chartTrace (walkChart h hqf hgp cl e 0)
        (oChartLift (walkChart h hqf hgp cl e 0)
          ⟨(u : ℝ), datumPiece_chartSubset h hqf hgp cl e hoverlap 0 (subfam n 0) u.2⟩)).mpr
        (oChartLift_mem_W (walkChart h hqf hgp cl e 0)
          ⟨(u : ℝ), datumPiece_chartSubset h hqf hgp cl e hoverlap 0 (subfam n 0) u.2⟩)
    change oChartLift (walkChart h hqf hgp cl e 0)
        ⟨(u : ℝ), datumPiece_chartSubset h hqf hgp cl e hoverlap 0 (subfam n 0) u.2⟩ ∈
        OChartTraceSet h hqf hgp (cl (e 0))
    simpa [OChartTraceSet, chartTrace, walkChart] using hmem0
  · have hmle : m ≤ n := by omega
    intro c hc
    rcases hc with ⟨u, rfl⟩
    let p : ℕ → MonoPiece := fun i => datumPiece (subfam n i)
    have htrp : transports (p 0) (chainTail p 0 m) u := by
      have htrfull : transports (p 0) (chainTail p 0 n) u := by
        change transports (datumPiece (subfam n 0))
            (chainTail (fun i => datumPiece (subfam n i)) 0 n) u
        exact htot n u
      exact transports_chainTail_prefix (p := p) 0 n m hmle u htrfull
    rcases chain_transport_class_coordinate (ch := walkChart h hqf hgp cl e)
        (p := p)
        (hsub := fun i => datumPiece_chartSubset h hqf hgp cl e hoverlap i (subfam n i))
        (hsem := fun i v => datumPiece_semantics h hqf hgp cl e hoverlap i (subfam n i) v)
        0 m ⟨u, htrp⟩ with ⟨yfar, hyfar⟩
    have hmemy : oChartLift (walkChart h hqf hgp cl e (0 + m + 1)) yfar.1 ∈
        chartTrace (walkChart h hqf hgp cl e (0 + m + 1)) := by
      exact (mem_chartTrace (walkChart h hqf hgp cl e (0 + m + 1))
        (oChartLift (walkChart h hqf hgp cl e (0 + m + 1)) yfar.1)).mpr
        (oChartLift_mem_W (walkChart h hqf hgp cl e (0 + m + 1)) yfar.1)
    have hcy : oChartLift (walkChart h hqf hgp cl e 0)
        ⟨(u : ℝ), datumPiece_chartSubset h hqf hgp cl e hoverlap 0 (subfam n 0) u.2⟩ ∈
        chartTrace (walkChart h hqf hgp cl e (0 + m + 1)) := by
      rw [hyfar.1] at hmemy
      exact hmemy
    have hm' : (0 + m + 1 : ℕ) = m + 1 := by omega
    rw [hm'] at hcy
    change oChartLift (walkChart h hqf hgp cl e 0)
        ⟨(u : ℝ), datumPiece_chartSubset h hqf hgp cl e hoverlap 0 (subfam n 0) u.2⟩ ∈
        OChartTraceSet h hqf hgp (cl (e (m + 1)))
    simpa [OChartTraceSet, chartTrace, walkChart] using hcy

/-- **The orbit class lies in EVERY walk trace `T_m` (`m ∈ ℕ`).**  Under
the uniform landing hypothesis `hland`, the orbit parameter transports
through every prefix (`walkOrbit_all_lengths`), and
`walkOrbitClass_mem_traces` places its class in the reached chart's
trace at each prefix length — the orbit class is common to ALL the walk
traces (the S147 special configuration the winding arguments produce). -/
lemma perLengthOrbitClass_mem_all_traces {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (x₀ : ChartInterval (WP h hqf hgp cl e hoverlap 0).lo (WP h hqf hgp cl e hoverlap 0).hi)
    (hland : ∀ (n : ℕ)
        (htr : transports (WP h hqf hgp cl e hoverlap 0)
          (chainTail (WP h hqf hgp cl e hoverlap) 0 n) x₀),
      chainValue (WP h hqf hgp cl e hoverlap 0 ::
          chainTail (WP h hqf hgp cl e hoverlap) 0 n) ⟨x₀, htr⟩ ∈
        Set.Ioo (WP h hqf hgp cl e hoverlap (n + 1)).lo (WP h hqf hgp cl e hoverlap (n + 1)).hi) :
    ∀ m : ℕ, perLengthOrbitClass h hqf hgp cl e hoverlap x₀ ∈
      OChartTraceSet h hqf hgp (cl (e m)) := by
  intro m
  rcases m with _ | m
  · have hmem0 : oChartLift (walkChart h hqf hgp cl e 0)
        ⟨(x₀ : ℝ), walkJunction_subset h hqf hgp cl e hoverlap 0 x₀.2⟩ ∈
        chartTrace (walkChart h hqf hgp cl e 0) := by
      exact (mem_chartTrace (walkChart h hqf hgp cl e 0) _).mpr
        (oChartLift_mem_W (walkChart h hqf hgp cl e 0)
          ⟨(x₀ : ℝ), walkJunction_subset h hqf hgp cl e hoverlap 0 x₀.2⟩)
    simpa [perLengthOrbitClass, OChartTraceSet, chartTrace, walkChart] using hmem0
  · have htr : transports (WP h hqf hgp cl e hoverlap 0)
        (chainTail (WP h hqf hgp cl e hoverlap) 0 m) x₀ :=
      walkOrbit_all_lengths h hqf hgp cl e hoverlap x₀ hland m
    have hmem : perLengthOrbitClass h hqf hgp cl e hoverlap x₀ ∈
        chartTrace (walkChart h hqf hgp cl e (0 + m + 1)) := by
      have htrc := walkOrbitClass_mem_traces h hqf hgp cl e hoverlap m x₀ htr m (by omega)
      simpa [perLengthOrbitClass] using htrc
    have hm' : (0 + m + 1 : ℕ) = m + 1 := by omega
    rw [hm'] at hmem
    change perLengthOrbitClass h hqf hgp cl e hoverlap x₀ ∈
        OChartTraceSet h hqf hgp (cl (e (m + 1)))
    simpa [OChartTraceSet, chartTrace, walkChart] using hmem

/-! ## S197 — the combined prefix family theorem

`perLength_cell_family_prefix` gathers the S195 cell family (nine
conjuncts) and the S196 prefix-trace content into ONE statement: every
level-`n` cell is an open interval-charted arc in
`C ∩ ⋂_{m ≤ n+1} T_m` containing the orbit class, antitone in `n` —
the common-class coordinate refinement of the prefix union `P'_{n+2}`
that the S147-T chaining composes.  Everything here is verified (no
axioms, no `sorry`). -/

/-- **S197 — the per-length cell family with the prefix-trace
conjunct.**  From the walk data, a component (`c₀`, `hc0`) and an orbit
parameter (`x₀`, `hland`), a per-length datum family `subfam` whose
level-`n` cells: contain `x₀` in the head (C1); nest heads (C2); have
forward totality (C3); are open (C4); nest antitone (C5); lie in the
component of `c₀` (C6); lie in `P'_{n+2}` (C7); contain the orbit class
(C8); are interval-charted (C9); AND lie in every prefix trace `T_m`
for `m ≤ n+1` (C10, the S196 interlock). -/
theorem perLength_cell_family_prefix {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (c₀ : OSub r) (hc0 : cl (e 0) ∈ connectedComponent c₀)
    (x₀ : ChartInterval (WP h hqf hgp cl e hoverlap 0).lo (WP h hqf hgp cl e hoverlap 0).hi)
    (hland : ∀ (n : ℕ)
        (htr : transports (WP h hqf hgp cl e hoverlap 0)
          (chainTail (WP h hqf hgp cl e hoverlap) 0 n) x₀),
      chainValue (WP h hqf hgp cl e hoverlap 0 ::
          chainTail (WP h hqf hgp cl e hoverlap) 0 n) ⟨x₀, htr⟩ ∈
        Set.Ioo (WP h hqf hgp cl e hoverlap (n + 1)).lo (WP h hqf hgp cl e hoverlap (n + 1)).hi) :
    ∃ subfam : (n : ℕ) → (i : ℕ) → SubDatum (WP h hqf hgp cl e hoverlap i),
      (∀ n : ℕ, (x₀ : ℝ) ∈
        Set.Ioo (datumPiece (subfam n 0)).lo (datumPiece (subfam n 0)).hi) ∧
      (∀ n : ℕ,
        Set.Ioo (datumPiece (subfam (n + 1) 0)).lo (datumPiece (subfam (n + 1) 0)).hi ⊆
          Set.Ioo (datumPiece (subfam n 0)).lo (datumPiece (subfam n 0)).hi) ∧
      (∀ n : ℕ, ∀ y : ChartInterval (datumPiece (subfam n 0)).lo (datumPiece (subfam n 0)).hi,
        transports (datumPiece (subfam n 0))
          (chainTail (fun i => datumPiece (subfam n i)) 0 n) y) ∧
      (∀ n : ℕ, IsOpen (perLengthCell h hqf hgp cl e hoverlap subfam n)) ∧
      (∀ n : ℕ,
        perLengthCell h hqf hgp cl e hoverlap subfam (n + 1) ⊆
          perLengthCell h hqf hgp cl e hoverlap subfam n) ∧
      (∀ n : ℕ, perLengthCell h hqf hgp cl e hoverlap subfam n ⊆ connectedComponent c₀) ∧
      (∀ n : ℕ, perLengthCell h hqf hgp cl e hoverlap subfam n ⊆
        ⋃ m ∈ Set.Iio (n + 2), OChartTraceSet h hqf hgp (cl (e m))) ∧
      (∀ n : ℕ, perLengthOrbitClass h hqf hgp cl e hoverlap x₀ ∈
        perLengthCell h hqf hgp cl e hoverlap subfam n) ∧
      (∀ n : ℕ, Nonempty (ChartInterval (datumPiece (subfam n 0)).lo (datumPiece (subfam n 0)).hi ≃ₜ
        {c : OSub r // c ∈ perLengthCell h hqf hgp cl e hoverlap subfam n})) ∧
      (∀ n : ℕ, ∀ m : ℕ, m ≤ n + 1 →
        perLengthCell h hqf hgp cl e hoverlap subfam n ⊆
          OChartTraceSet h hqf hgp (cl (e m))) := by
  rcases perLength_cell_family h hqf hgp cl e hoverlap c₀ hc0 x₀ hland with
    ⟨subfam, hmem, hI, htot, hopen, hanti, hC, hP, horbit, hchart⟩
  refine ⟨subfam, hmem, hI, htot, hopen, hanti, hC, hP, horbit, hchart, ?_⟩
  intro n m hm
  exact perLengthCell_subset_trace h hqf hgp cl e hoverlap subfam htot n m hm

end LeanEval.KnotTheory.Quadrisecant
