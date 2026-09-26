import Mathlib
import Submission.TraceOverlap

open LeanEval.KnotTheory.Quadrisecant
open Set
open scoped Real Topology

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

noncomputable section
namespace LeanEval.KnotTheory.Quadrisecant

/-!
# S185 — the monotone cell transport (first lemma of the sweep's ordering
slice, module Submission/OverlapOrder.lean)

The ordering slice (ROADMAP S147-T / S184 NEXT) must produce connected
prefix-overlap sets from the walk's monotone junction cells; this module
is its first permanent lemma: the transport across an `OChartMonotoneNbhd`
cell (OChartGlue S98) is continuous and maps the cell onto a SINGLE
CONNECTED interval of the NEXT chart's coordinates, contained in the next
chart's interval — with the strict monotone direction recorded by the
neighbourhood itself.  Content (namespace
LeanEval.KnotTheory.Quadrisecant):

1. `cellTransport` — the real transport value at a cell parameter `u ∈
   (nb.lo, nb.hi)`: the `ch₁`-coordinate (in chart `ch₁`'s interval) of
   the trisecant class that `ch₀`'s parameter `⟨u, nb.subset hu⟩`
   describes (0 outside the cell; by `oChartNbhd_piece_coordinate` these
   are the ch₁-coordinates of the SAME classes as the cell parameters);
2. `continuousOn_cellTransport` — continuous on the open cell (the cell
   domRestrict equals the continuous `oChartTransitionOnInterval` read
   through the cell embedding);
3. **`oChartCellTransport_image_connected`** — the transported coordinate
   set `cellTransport '' (nb.lo, nb.hi)` is CONNECTED (continuous image of
   the connected open interval `isConnected_Ioo nb.lo_lt_hi`);
4. `oChartCellTransport_image_eq_range` — the image equals the range of
   the interval-parametrised transport `oChartTransitionOnInterval`;
5. **`oChartTransitionOnInterval_range_subset_chart`** — the range lies
   inside the next chart's interval `(ch₁.lo, ch₁.hi)` (transport values
   are coordinates of chart-ch₁ parameters).

Together with `nb.monotone` (the strict one-direction monotonicity on the
cell) these say: through each junction's monotone cell the walk's
transport reaches a single connected interval of the next chart's
coordinates, strictly ordered — the local "single interval" half of the
ordered-chain overlap content.  The full prefix-overlap connectivity
(`ConnectedSpace {x ∈ P'_k ∩ T (k+1)}`, the S183 hypothesis) still
requires the ordered-chain induction of S147-T (consecutive cells
interlocking with consistent directions — H1, and the no-wrap H2); this
module provides the per-cell transport facts that induction composes.
Everything here is verified (no axioms, no `sorry`).
-/
/-- The transport value at a real cell parameter `u ∈ (nb.lo, nb.hi)`: the
`ch₁`-coordinate (in `ch₂`'s chart interval) of the trisecant class that
`ch₀`'s parameter `⟨u, nb.subset hu⟩` describes (0 outside the cell). -/
noncomputable def cellTransport {r : ℝ → Space} {c₀ c₁ : OSub r}
    (ch₀ : OSub1Chart r c₀) (ch₁ : OSub1Chart r c₁)
    (x₀ : OChartTransitionDomain ch₀ ch₁) (nb : OChartMonotoneNbhd ch₀ ch₁ x₀)
    (u : ℝ) : ℝ :=
  if hu : u ∈ Set.Ioo nb.lo nb.hi then
    oChartTransitionReal ch₀ ch₁
      ⟨⟨u, nb.subset hu⟩, nb.dom ⟨u, nb.subset hu⟩ hu⟩
  else 0

/-- On the open cell, the transport is continuous (it is the continuous
transition relabelling read through the continuous cell embedding). -/
lemma continuousOn_cellTransport {r : ℝ → Space} {c₀ c₁ : OSub r}
    (ch₀ : OSub1Chart r c₀) (ch₁ : OSub1Chart r c₁)
    (x₀ : OChartTransitionDomain ch₀ ch₁) (nb : OChartMonotoneNbhd ch₀ ch₁ x₀) :
    ContinuousOn (cellTransport ch₀ ch₁ x₀ nb) (Set.Ioo nb.lo nb.hi) := by
  let S : Set ℝ := Set.Ioo nb.lo nb.hi
  rw [continuousOn_iff_continuous_domRestrict]
  have hgS : S.domRestrict (cellTransport ch₀ ch₁ x₀ nb) =
      fun u : {x : ℝ // x ∈ S} =>
        oChartTransitionOnInterval ch₀ ch₁ nb.subset nb.dom ⟨(u : ℝ), u.2⟩ := by
    funext u
    dsimp [cellTransport, S, Set.domRestrict]
    rw [dif_pos u.2]
    rfl
  rw [hgS]
  exact (continuous_oChartTransitionOnInterval ch₀ ch₁ nb.subset nb.dom).comp
    (Continuous.subtype_mk continuous_subtype_val (fun u => u.2))

/-- **S185 — the monotone cell transports onto a connected set of the next
chart's coordinates (the "single interval" half of the overlap-order
content)**: the `ch₁`-coordinates (in chart `ch₁`'s interval) reached from
the monotone transition cell around a transition parameter form a
connected set — by `oChartNbhd_piece_coordinate` these are the `ch₁`-
coordinates of the SAME trisecant classes as the cell parameters, and by
`nb.monotone` the relabelling is strictly monotone in one direction on the
cell.  The ordered chain (S147-T) transports through such cells; their
coordinate images being single connected intervals is the local content
that keeps successive overlaps single-interval in the next chart. -/
theorem oChartCellTransport_image_connected {r : ℝ → Space} {c₀ c₁ : OSub r}
    (ch₀ : OSub1Chart r c₀) (ch₁ : OSub1Chart r c₁)
    (x₀ : OChartTransitionDomain ch₀ ch₁) (nb : OChartMonotoneNbhd ch₀ ch₁ x₀) :
    IsConnected (cellTransport ch₀ ch₁ x₀ nb '' Set.Ioo nb.lo nb.hi) := by
  exact IsConnected.image (isConnected_Ioo nb.lo_lt_hi) (cellTransport ch₀ ch₁ x₀ nb)
    (continuousOn_cellTransport ch₀ ch₁ x₀ nb)

/-- The cell transport image equals the image of the interval-parametrised
transport over the whole `ChartInterval nb.lo nb.hi` (the range of
`oChartTransitionOnInterval`): the connected set above is exactly the
coordinate range of the interval piece. -/
lemma oChartCellTransport_image_eq_range {r : ℝ → Space} {c₀ c₁ : OSub r}
    (ch₀ : OSub1Chart r c₀) (ch₁ : OSub1Chart r c₁)
    (x₀ : OChartTransitionDomain ch₀ ch₁) (nb : OChartMonotoneNbhd ch₀ ch₁ x₀) :
    cellTransport ch₀ ch₁ x₀ nb '' Set.Ioo nb.lo nb.hi =
      Set.range (oChartTransitionOnInterval ch₀ ch₁ nb.subset nb.dom) := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨u, hu, hyu⟩
    refine ⟨⟨u, hu⟩, ?_⟩
    dsimp [cellTransport] at hyu
    rw [dif_pos hu] at hyu
    rw [← hyu]
    rfl
  · intro hy
    rcases hy with ⟨w, rfl⟩
    refine ⟨(w : ℝ), w.2, ?_⟩
    dsimp [cellTransport]
    rw [dif_pos w.2]
    rfl



/-- The transported coordinates stay inside the next chart's interval: the
range of the interval-piece transport lies in `(ch₁.lo, ch₁.hi)` (the
values are coordinates of chart `ch₁` parameters).  Together with
`oChartCellTransport_image_connected` this says the monotone cell reaches
a single CONNECTED interval of the next chart's coordinates. -/
theorem oChartTransitionOnInterval_range_subset_chart {r : ℝ → Space} {c₀ c₁ : OSub r}
    (ch₀ : OSub1Chart r c₀) (ch₁ : OSub1Chart r c₁)
    (x₀ : OChartTransitionDomain ch₀ ch₁) (nb : OChartMonotoneNbhd ch₀ ch₁ x₀) :
    Set.range (oChartTransitionOnInterval ch₀ ch₁ nb.subset nb.dom) ⊆
      Set.Ioo ch₁.lo ch₁.hi := by
  intro y hy
  rcases hy with ⟨w, rfl⟩
  change oChartTransitionReal ch₀ ch₁
      ⟨⟨(w : ℝ), nb.subset w.2⟩, nb.dom ⟨(w : ℝ), nb.subset w.2⟩ w.2⟩ ∈ Set.Ioo ch₁.lo ch₁.hi
  -- the value is the coordinate of a chart-ch₁ parameter:
  exact (((oChartTransitionTo ch₀ ch₁
      ⟨⟨(w : ℝ), nb.subset w.2⟩, nb.dom ⟨(w : ℝ), nb.subset w.2⟩ w.2⟩
        : OChartTransitionDomain ch₁ ch₀) : ChartInterval ch₁.lo ch₁.hi).2)


/-! ## S186 — the S147-T preamble: the ordered-cell-chain transport

The induction shape of the sweep's charting (ROADMAP S147-T): S185 gave
the per-junction cell transport (continuous, injective, connected image,
in-window).  This section proves the ordered-chain transport over an
INTERLOCKING chain of cells — the pure induction engine the S147-T
coordinate (`φ : ChartInterval lo hi ≃ₜ {c // c ∈ walkPartialUnion …}`)
is built from — and the O-side single-junction certificate that seeds it.

**Junction-level hypotheses (the precise H1/H2 at junction level).**  At
walk junction `m` the O-side data are: the charts
`ch m := walkChart … m`, the junction transition parameter
`x m := oChartTraceOverlapParam (ch m) (ch (m+1)) (walkOverlapClass m) …`,
and the monotone neighbourhood `nb m := walkJunctionNbhd … m`
(`OChartMonotoneNbhd`, OChartGlue S98 / IntervalCoverU) with the real
cell `C m := Ioo (nb m).lo (nb m).hi`.  The per-junction transport is
`trans m := cellTransport (ch m) (ch (m+1)) (x m) (nb m)`.  Then

- **H1 (ordered interlock)** — the precise junction-level formulation:
  `InterlockCells C trans`, i.e. for every `m`, the image of the cell
  `C m` under the transport `trans m` lies inside the NEXT cell `C (m+1)`
  (so the chain never leaves the cells and every next transport applies
  to the transported coordinates — the coordinates line up so that the
  junction parameter regions chain monotonically);
- **H2 (no wrapping)** — the chain does not wind: the composed transport
  over the whole prefix never returns into the starting cell/region in a
  way that identifies distinct parameters of `C 0` (the closed-walk /
  circular side of the dichotomy); H2 is needed only when matching the
  composed coordinate to the classes of a closed walk and is recorded
  here as the open geometric input together with H1 (both to be supplied
  by the walk/O-chart geometry when S147-T is instantiated; the pure
  engine below needs only H1).

  **CORRECTION (S187 — the raw cells do NOT interlock).**  The statement
  `trans m u ∈ C (m+1)` for all `u ∈ C m` — with the RAW S185 cells
  `C m` (the `OChartMonotoneNbhd` cells at the walk junctions) — is NOT a
  theorem.  Reason: `C m` sits around `x_m` (the `ch m`-coordinate of
  the junction class `z m ∈ T m ∩ T (m+1)`), and `trans m` maps `C m`
  onto an interval around the coordinate `y m` of `z m` in chart
  `(m+1)`, whereas `C (m+1)` sits around `x_{m+1}` — the coordinate of
  the NEXT junction class `z (m+1) ∈ T (m+1) ∩ T (m+2)`; `hoverlap`
  imposes no relation between `z m` and `z (m+1)`, so `y m` and
  `x_{m+1}` are independent and the image of `C m` need not lie in
  `C (m+1)`.  The genuine interlock of the sweep is the ALIGNED
  SUB-PIECE construction: `ChainAlignment.exists_aligned_subpieces`
  (S133) shrinks the junction pieces backwards around a forward-orbit
  start parameter so that EVERY parameter of the aligned sub-pieces
  transports forward (`AlignedTotality`) — and the sweep's transport
  representation is the MonoPiece/`ChartInterval` machinery
  (`ChainTransport`/`ChainDomain`, S111; `walkJunctionPiece`,
  `IntervalCoverU` S116), not the real-valued `iterTrans` of this
  section.  `orderedChain_transport` above remains valid as a standalone
  real-coordinate engine; its H1 (`InterlockCells`) is satisfied by
  ALIGNED sub-cells (the shrinking outcome), which the O-side/walk
  instantiation must supply in the ChainTransport representation — the
  S147-T assembly step records this as the next task.

**The induction engine (pure).**  `iterTrans trans m` composes the first
`m` transports; `InterlockCells` is H1.  `iterTrans_mapsTo` (interlock
keeps the iterate in cell `m`), `iterTrans_continuousOn` (composition of
continuous cell transports), `iterTrans_injOn` (composition of injective
cell transports), and **`orderedChain_transport`**: under `H1` with each
cell transport continuous and injective on its cell (the S185
certificates), the `m`-fold transport started at a `C 0`-parameter is
continuous, injective, and sweeps a CONNECTED interval of window `m` —
`IsConnected (iterTrans trans m '' C 0)`.  Base `m = 1` is the
single-junction certificate; the step composes the same certificate at
the next junction (H1 makes the composition defined).

**The O-side base certificate.**  `cellTransport_eq_transitionOnInterval`
(the pointwise identity of `cellTransport` with the interval-piece
transport on the cell), `injOn_cellTransport` (injectivity from the
strict monotone direction `nb.monotone` via
`injective_oChartTransitionOnInterval`), and
**`oChartCell_single_transport_cert`** — at one junction the cell
transport is injective, continuous, with connected image: the `m = 1`
instance of the induction hypotheses (S185 + injectivity).

Everything here is verified (no axioms, no `sorry`).
-/
/-- The `m`-fold transport over a chain of cells: `iterTrans trans (m+1) u
= trans m (iterTrans trans m u)` — the coordinate reached in window `m`
from the starting coordinate `u` by composing the consecutive cell
transports `trans 0, …, trans (m-1)`. -/
def iterTrans (trans : ℕ → ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0, u => u
  | m + 1, u => trans m (iterTrans trans m u)

/-- Interlocking (H1): each cell transport sends the cell into the NEXT
cell, so the composition never leaves the cells and the next transport
always applies. -/
def InterlockCells (cellLo cellHi : ℕ → ℝ) (trans : ℕ → ℝ → ℝ) : Prop :=
  ∀ m : ℕ, ∀ ⦃u : ℝ⦄, u ∈ Set.Ioo (cellLo m) (cellHi m) →
    trans m u ∈ Set.Ioo (cellLo (m + 1)) (cellHi (m + 1))

/-- Under interlocking, the iterated transport from a cell-0 parameter
lands in cell `m` at step `m` (induction over `m`, the interlock at each
junction). -/
lemma iterTrans_mapsTo {cellLo cellHi : ℕ → ℝ} {trans : ℕ → ℝ → ℝ}
    (hint : InterlockCells cellLo cellHi trans) (m : ℕ) :
    ∀ ⦃u : ℝ⦄, u ∈ Set.Ioo (cellLo 0) (cellHi 0) →
      iterTrans trans m u ∈ Set.Ioo (cellLo m) (cellHi m) := by
  induction m with
  | zero => intro u hu; simpa [iterTrans] using hu
  | succ m ih =>
      intro u hu
      have hprev : iterTrans trans m u ∈ Set.Ioo (cellLo m) (cellHi m) := ih hu
      have hnext := hint m hprev
      simpa [iterTrans] using hnext

/-- The iterated transport is continuous on the starting cell (each step
composes a continuous cell transport with the previous continuous iterate
through the interlock). -/
lemma iterTrans_continuousOn {cellLo cellHi : ℕ → ℝ} {trans : ℕ → ℝ → ℝ}
    (hcont : ∀ m : ℕ, ContinuousOn (trans m) (Set.Ioo (cellLo m) (cellHi m)))
    (hint : InterlockCells cellLo cellHi trans) :
    ∀ m : ℕ, ContinuousOn (iterTrans trans m) (Set.Ioo (cellLo 0) (cellHi 0)) := by
  intro m
  induction m with
  | zero =>
      change ContinuousOn (fun x : ℝ => x) (Set.Ioo (cellLo 0) (cellHi 0))
      exact continuousOn_id
  | succ m ih =>
      have hmaps : Set.MapsTo (iterTrans trans m) (Set.Ioo (cellLo 0) (cellHi 0))
          (Set.Ioo (cellLo m) (cellHi m)) := by
        intro u hu
        exact iterTrans_mapsTo (trans := trans) hint m hu
      have hgoal : ContinuousOn (fun u => trans m (iterTrans trans m u))
          (Set.Ioo (cellLo 0) (cellHi 0)) :=
        (hcont m).comp ih hmaps
      simpa [iterTrans] using hgoal

/-- The iterated transport is injective on the starting cell (composition
of per-junction injective cell transports through the interlock). -/
lemma iterTrans_injOn {cellLo cellHi : ℕ → ℝ} {trans : ℕ → ℝ → ℝ}
    (hinj : ∀ m : ℕ, Set.InjOn (trans m) (Set.Ioo (cellLo m) (cellHi m)))
    (hint : InterlockCells cellLo cellHi trans) :
    ∀ m : ℕ, Set.InjOn (iterTrans trans m) (Set.Ioo (cellLo 0) (cellHi 0)) := by
  intro m
  induction m with
  | zero =>
      intro u hu v hv h
      simpa [iterTrans] using h
  | succ m ih =>
      intro u hu v hv h
      have hf : iterTrans trans m u = iterTrans trans m v := by
        have hm1 := hinj m (iterTrans_mapsTo (trans := trans) hint m hu)
          (iterTrans_mapsTo (trans := trans) hint m hv)
        exact hm1 (by simpa [iterTrans] using h)
      exact ih hu hv hf

/-- **S147-T preamble — the ordered-chain transport (induction)**: given
interlocking cells (`H1`), each junction transport continuous (`hcont`,
from S185 `continuousOn_cellTransport` on the O-side) and injective on its
cell (`hinj`, from the strict monotone direction `nb.monotone`), the
`m`-fold transport started at a cell-0 parameter is continuous, injective,
and its image from the connected starting cell is CONNECTED: the
coordinate reached in window `m` sweeps a single connected interval as the
starting parameter ranges over the cell.  Base `m = 1` is exactly the
single-junction content of S185 (`oChartCellTransport_image_connected` +
continuity + injectivity); the step composes the same facts at the next
junction.  (No-wrapping H2 enters only when matching the composed
coordinate to the actual classes of a closed walk — recorded in the
module doc.) -/
theorem orderedChain_transport {cellLo cellHi : ℕ → ℝ} {trans : ℕ → ℝ → ℝ}
    (hcell0 : cellLo 0 < cellHi 0)
    (hcont : ∀ m : ℕ, ContinuousOn (trans m) (Set.Ioo (cellLo m) (cellHi m)))
    (hinj : ∀ m : ℕ, Set.InjOn (trans m) (Set.Ioo (cellLo m) (cellHi m)))
    (hint : InterlockCells cellLo cellHi trans) :
    ∀ m : ℕ,
      ContinuousOn (iterTrans trans m) (Set.Ioo (cellLo 0) (cellHi 0)) ∧
      Set.InjOn (iterTrans trans m) (Set.Ioo (cellLo 0) (cellHi 0)) ∧
      IsConnected (iterTrans trans m '' Set.Ioo (cellLo 0) (cellHi 0)) := by
  intro m
  constructor
  · exact iterTrans_continuousOn (trans := trans) hcont hint m
  · constructor
    · exact iterTrans_injOn (trans := trans) hinj hint m
    · exact IsConnected.image (isConnected_Ioo hcell0) (iterTrans trans m)
        (iterTrans_continuousOn (trans := trans) hcont hint m)



/-- On the cell, `cellTransport` agrees pointwise with the interval-piece
transport `oChartTransitionOnInterval` (the definitions coincide). -/
lemma cellTransport_eq_transitionOnInterval {r : ℝ → Space} {c₀ c₁ : OSub r}
    (ch₀ : OSub1Chart r c₀) (ch₁ : OSub1Chart r c₁)
    (x₀ : OChartTransitionDomain ch₀ ch₁) (nb : OChartMonotoneNbhd ch₀ ch₁ x₀)
    (u : ℝ) (hu : u ∈ Set.Ioo nb.lo nb.hi) :
    cellTransport ch₀ ch₁ x₀ nb u =
      oChartTransitionOnInterval ch₀ ch₁ nb.subset nb.dom ⟨u, hu⟩ := by
  dsimp [cellTransport]
  rw [dif_pos hu]
  rfl

/-- The O-side single-junction transport is injective on the cell (the
strict one-direction monotonicity `nb.monotone` of the interval-piece
transport + `injective_oChartTransitionOnInterval`). -/
lemma injOn_cellTransport {r : ℝ → Space} {c₀ c₁ : OSub r}
    (ch₀ : OSub1Chart r c₀) (ch₁ : OSub1Chart r c₁)
    (x₀ : OChartTransitionDomain ch₀ ch₁) (nb : OChartMonotoneNbhd ch₀ ch₁ x₀) :
    Set.InjOn (cellTransport ch₀ ch₁ x₀ nb) (Set.Ioo nb.lo nb.hi) := by
  intro u hu v hv huv
  have h1 := cellTransport_eq_transitionOnInterval ch₀ ch₁ x₀ nb u hu
  have h2 := cellTransport_eq_transitionOnInterval ch₀ ch₁ x₀ nb v hv
  have hiv : oChartTransitionOnInterval ch₀ ch₁ nb.subset nb.dom ⟨u, hu⟩ =
      oChartTransitionOnInterval ch₀ ch₁ nb.subset nb.dom ⟨v, hv⟩ := by
    rw [← h1, ← h2]
    exact huv
  have hpar := injective_oChartTransitionOnInterval ch₀ ch₁ nb.subset nb.dom hiv
  have hval : u = v := congrArg (fun z : ChartInterval nb.lo nb.hi => (z : ℝ)) hpar
  exact hval

/-- **O-side single-junction base certificate**: at one junction the cell
transport is injective, continuous and has connected image — exactly the
`m = 1` instance of the hypotheses of `orderedChain_transport` (the S185
connectedness/continuity + `injOn_cellTransport`).  The ordered chain
feeds these per-junction certificates through `orderedChain_transport`,
whose remaining geometric input is the H1 interlock (each cell's image
inside the next cell) supplied by the walk. -/
theorem oChartCell_single_transport_cert {r : ℝ → Space} {c₀ c₁ : OSub r}
    (ch₀ : OSub1Chart r c₀) (ch₁ : OSub1Chart r c₁)
    (x₀ : OChartTransitionDomain ch₀ ch₁) (nb : OChartMonotoneNbhd ch₀ ch₁ x₀) :
    Set.InjOn (cellTransport ch₀ ch₁ x₀ nb) (Set.Ioo nb.lo nb.hi) ∧
    ContinuousOn (cellTransport ch₀ ch₁ x₀ nb) (Set.Ioo nb.lo nb.hi) ∧
    IsConnected (cellTransport ch₀ ch₁ x₀ nb '' Set.Ioo nb.lo nb.hi) := by
  constructor
  · exact injOn_cellTransport ch₀ ch₁ x₀ nb
  · constructor
    · exact continuousOn_cellTransport ch₀ ch₁ x₀ nb
    · exact oChartCellTransport_image_connected ch₀ ch₁ x₀ nb
end LeanEval.KnotTheory.Quadrisecant
