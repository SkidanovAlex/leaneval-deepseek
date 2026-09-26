import Mathlib
import Submission.Commons.Topology.ConnectedReal.preconnected_inter_of_homeoUnit
import Submission.OneManifold
import Submission.IntervalSide

open LeanEval.KnotTheory.Quadrisecant
open Set
open scoped Real Topology

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false

noncomputable section
namespace LeanEval.KnotTheory.Quadrisecant

/-!
# S210 — route (α): the two-chart intersection mechanism and its walk
instance (module Submission/ChartRefine.lean)

Item (i) of the S206 interval side needs per-step OVERLAP-connectedness
of the next arc to the prefix in the generic (non-walk) setting.  Route
(α) supplies it by REFINEMENT: if any two intersecting cover arcs lie
inside ONE interval-charted open region, they meet connectedly — no
wrapping is possible inside a single ambient arc.  This module proves
that mechanism and its O-side walk instance:

1. **`inter_connected_of_common_intervalChart`** — the precise meaning
   of "intersecting arcs meet connectedly" in interval-chart
   coordinates: two open preconnected subsets `s`, `t` of `X` that both
   lie inside one interval-charted open region `W`
   (`ρ : ↑W ≃ₜ (0,1)`) meet CONNECTEDLY when nonempty (in the region's
   interval coordinates both are open intervals, whose intersection is
   an interval — the L34 commons fact, wrapped at the subtype level);
2. **`walkTrace_inter_connected_of_common_region`** — the O-side
   instance: two consecutive walk traces both contained in one
   interval-charted region meet connectedly (the traces are open by
   `isOpen_chartTrace` and preconnected by `chartTrace_preconnected`,
   S204) — the region-local form of the per-level `hD` supply (the
   region may be SMALLER than the whole component: exactly the
   refinement-style locality route (α) needs).

The remaining piece of route (α) — producing, from the countable
open-arc cover of the 1-manifold, a refinement whose intersecting
members admit a common interval-charted region (the "arcs shorter than
the wrap" content, requiring an arc-length/order development or the
compact-side exclusion) — is recorded in ROADMAP S210.

Everything here is verified (no axioms, no `sorry`).
-/

/-- **S210 — the two-chart intersection mechanism (route (α)).**  Two
open preconnected subsets (`s`, `t`) of an ambient `X` that both lie
inside ONE interval-charted open region `W` (`ρ : ↑W ≃ₜ (0,1)`) meet
CONNECTEDLY (whenever their intersection is nonempty): in the region's
interval coordinates both are open intervals, whose intersection is an
interval — the L34 commons fact, wrapped at the subtype level.  This is
the precise meaning of "intersecting arcs meet connectedly" in
interval-chart coordinates: no wrapping is possible inside a single
ambient arc. -/
theorem inter_connected_of_common_intervalChart {X : Type*} [TopologicalSpace X]
    {W : Set X} (ρ : {x : X // x ∈ W} ≃ₜ OpenRealInterval 0 1)
    {s t : Set X} (hs_open : IsOpen s) (ht_open : IsOpen t)
    (hssub : s ⊆ W) (htsub : t ⊆ W)
    (hs_pre : IsPreconnected s) (ht_pre : IsPreconnected t)
    (hne : (s ∩ t).Nonempty) :
    ConnectedSpace {x : X // x ∈ s ∩ t} := by
  have hpre : IsPreconnected (s ∩ t) :=
    Commons.Topology.ConnectedReal.preconnected_inter_of_homeoUnit
      (X := X) (Ω := W) ρ hs_open ht_open hssub htsub hs_pre ht_pre hne
  have hsetconn : IsConnected (s ∩ t : Set X) := ⟨hne, hpre⟩
  exact Subtype.connectedSpace (s := s ∩ t) hsetconn

/-- **S210 — the walk instance: consecutive traces in one
interval-charted region meet connectedly.**  If two consecutive walk
traces (`chartTrace (walkChart j)`, `chartTrace (walkChart (j+1))`) both
lie inside an interval-charted open region `W` and overlap, their
intersection is connected (the traces are open by `isOpen_chartTrace`
and preconnected by `chartTrace_preconnected`) — the region-local form
of the per-level overlap content (the region may be smaller than the
whole component: the refinement-style locality route (α) needs). -/
theorem walkTrace_inter_connected_of_common_region {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (j : ℕ) {W : Set (OSub r)}
    (ρ : {c : OSub r // c ∈ W} ≃ₜ OpenRealInterval 0 1)
    (hWj : chartTrace (walkChart h hqf hgp cl e j) ⊆ W)
    (hWj1 : chartTrace (walkChart h hqf hgp cl e (j + 1)) ⊆ W) :
    ConnectedSpace {c : OSub r // c ∈ chartTrace (walkChart h hqf hgp cl e j) ∩
        chartTrace (walkChart h hqf hgp cl e (j + 1))} := by
  have hne : (chartTrace (walkChart h hqf hgp cl e j) ∩
        chartTrace (walkChart h hqf hgp cl e (j + 1))).Nonempty := by
    have hov := hoverlap j
    rw [show OChartTraceSet h hqf hgp (cl (e j)) = chartTrace (walkChart h hqf hgp cl e j) by
        simp [OChartTraceSet, walkChart, chartTrace]] at hov
    rw [show OChartTraceSet h hqf hgp (cl (e (j + 1))) =
        chartTrace (walkChart h hqf hgp cl e (j + 1)) by
        simp [OChartTraceSet, walkChart, chartTrace]] at hov
    exact hov
  exact inter_connected_of_common_intervalChart (X := OSub r) (W := W) ρ
    (isOpen_chartTrace (walkChart h hqf hgp cl e j))
    (isOpen_chartTrace (walkChart h hqf hgp cl e (j + 1)))
    hWj hWj1
    (chartTrace_preconnected (walkChart h hqf hgp cl e j))
    (chartTrace_preconnected (walkChart h hqf hgp cl e (j + 1)))
    hne

/-! ## S211 — the local-refinement heart: cells of a chart

Route (α) needs: shrinking a chart trace to a sub-interval of its
coordinates is still an interval-charted open subregion, and any two
such subregions of one chart meet connectedly (in a cell).  This section
proves the heart inside ONE chart's `(lo,hi)`-coordinates:

1. **`chartCell` / `isOpen_chartCell`** — the subregion of a chart
   trace over the coordinate interval `(a,b)` (the lift of the open
   parameter cell), which is OPEN in `OSub r` (S139 `isOpen_lift_cell`);
2. **`chartCellHomeo`** — a sub-interval `(a,b) ⊆ (lo,hi)` is still a
   chart of the open subregion: `ChartInterval a b ≃ₜ {c // c ∈
   chartCell ch a b}` (the cell map `u ↦ oChartLift ch ⟨(u : ℝ),
   hsub u.2⟩` is continuous/injective/open with range the cell — the
   S140a pattern at raw chart level);
3. **`chartCell_inter`** — two cells of one chart meet in the cell of
   the overlap interval: `chartCell ch a b ∩ chartCell ch c d =
   chartCell ch (max a c) (min b d)` (the lift is injective, so the
   image of an intersection is the intersection of the images; the real
   interval identity `Ioo a b ∩ Ioo c d = Ioo (max a c) (min b d)` by
   `max_lt_iff`/`lt_min_iff`);
4. **`chartCell_inter_homeo`** — the pairwise content: the intersection
   of two cells of one chart is interval-charted (by the overlap
   interval), so any two sub-arcs of one chart meet connectedly (in an
   interval-charted arc).

This is the first sub-lemma of the local-refinement construction
recorded in ROADMAP S210: the neighbourhood basis at a point is the
family of cells over the coordinate intervals around the point's
parameter; the pairwise-connectedness is (4).  Everything here is
verified (no axioms, no `sorry`).
-/

/-- The subregion of a chart trace over the coordinate interval `(a,b)`:
the classes whose `ch`-coordinate lies in `(a,b)` (the lift of the open
parameter cell). -/
def chartCell {r : ℝ → Space} {c₀ : OSub r} (ch : OSub1Chart r c₀) (a b : ℝ) : Set (OSub r) :=
  (fun t : ChartInterval ch.lo ch.hi => oChartLift ch t) ''
    {t : ChartInterval ch.lo ch.hi | (t : ℝ) ∈ Set.Ioo a b}

/-- The chart cell is open (the lift of the open parameter cell — S139). -/
lemma isOpen_chartCell {r : ℝ → Space} {c₀ : OSub r} (ch : OSub1Chart r c₀) (a b : ℝ) :
    IsOpen (chartCell ch a b) := by
  dsimp [chartCell]
  exact isOpen_lift_cell ch

/-- **S211(i) — a sub-interval is still a chart of an open subregion.**
For a sub-interval `(a,b)` of the chart's coordinate interval, the cell
`chartCell ch a b` is interval-charted by `ChartInterval a b` — the
local-refinement heart: shrinking a chart trace to the coordinates
`(a,b)` gives an open subregion still homeomorphic to an open interval. -/
noncomputable def chartCellHomeo {r : ℝ → Space} {c₀ : OSub r} (ch : OSub1Chart r c₀)
    {a b : ℝ} (hsub : Set.Ioo a b ⊆ Set.Ioo ch.lo ch.hi) :
    ChartInterval a b ≃ₜ {c : OSub r // c ∈ chartCell ch a b} := by
  let emb : ChartInterval a b → ChartInterval ch.lo ch.hi := fun u =>
    ⟨(u : ℝ), hsub u.2⟩
  let f : ChartInterval a b → OSub r := fun u => oChartLift ch (emb u)
  have hcomp : f = (fun t : ChartInterval ch.lo ch.hi => oChartLift ch t) ∘ emb := by
    funext u
    rfl
  have hf_cont : Continuous f := by
    rw [hcomp]
    exact (continuous_oChartLift ch).comp
      (Continuous.subtype_mk continuous_subtype_val (fun u => hsub u.2))
  have hf_inj : Function.Injective f := by
    intro u v h
    dsimp [f] at h
    have hE : (⟨(u : ℝ), hsub u.2⟩ : ChartInterval ch.lo ch.hi) =
        ⟨(v : ℝ), hsub v.2⟩ := by
      apply oChartLift_injective ch
      exact h
    apply Subtype.ext
    exact congrArg (fun t : ChartInterval ch.lo ch.hi => (t : ℝ)) hE
  have hf_open : IsOpenMap f := by
    rw [hcomp]
    exact IsOpenMap.comp (isOpenMap_oChartLift ch)
      (isOpenMap_paramEmbedding (lo := ch.lo) (hi := ch.hi) (a := a) (b := b) hsub)
  have hrange : Set.range f = chartCell ch a b := by
    ext c
    constructor
    · rintro ⟨u, rfl⟩
      dsimp [chartCell, f, emb]
      refine ⟨⟨(u : ℝ), hsub u.2⟩, ?_, ?_⟩
      · change (u : ℝ) ∈ Set.Ioo a b
        exact u.2
      · rfl
    · intro hc
      rcases hc with ⟨t, ht, rfl⟩
      let u : ChartInterval a b := ⟨(t : ℝ), ht⟩
      refine ⟨u, ?_⟩
      dsimp [f, emb, u]
  let e := homeo_range_of_continuous_injective_isOpenMap f hf_cont hf_inj hf_open
  exact e.trans (setEqSubtypeHomeoX hrange)

/-- **S211(ii) — cells of one chart meet in the cell of the overlap
interval.**  The intersection of two cells of the same chart over
`(a,b)` and `(c,d)` is the cell over `(max a c, min b d)` — the
coordinate-interval identity (the lift is injective, so the image of an
intersection is the intersection of the images). -/
lemma chartCell_inter {r : ℝ → Space} {c₀ : OSub r} (ch : OSub1Chart r c₀) (a b c d : ℝ) :
    chartCell ch a b ∩ chartCell ch c d = chartCell ch (max a c) (min b d) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hx1, hx2⟩
    dsimp [chartCell] at hx1 hx2 ⊢
    rcases hx1 with ⟨t1, ht1, rfl⟩
    rcases hx2 with ⟨t2, ht2, hE⟩
    have htEq : t1 = t2 := oChartLift_injective ch hE.symm
    subst t2
    refine ⟨t1, ?_, rfl⟩
    change (t1 : ℝ) ∈ Set.Ioo (max a c) (min b d)
    rcases ht1 with ⟨ha, hb⟩
    rcases ht2 with ⟨hc, hd⟩
    constructor
    · exact max_lt_iff.mpr ⟨ha, hc⟩
    · exact lt_min_iff.mpr ⟨hb, hd⟩
  · intro hx
    rcases hx with ⟨t, ht, rfl⟩
    dsimp [chartCell]
    rcases ht with ⟨hm, hn⟩
    have hmem1 : (t : ℝ) ∈ Set.Ioo a b := by
      exact ⟨(max_lt_iff.mp hm).1, (lt_min_iff.mp hn).1⟩
    have hmem2 : (t : ℝ) ∈ Set.Ioo c d := by
      exact ⟨(max_lt_iff.mp hm).2, (lt_min_iff.mp hn).2⟩
    constructor
    · exact ⟨t, hmem1, rfl⟩
    · exact ⟨t, hmem2, rfl⟩

/-- **S211(iii) — the pairwise content: cells of one chart meet in an
interval-charted arc.**  The intersection of two cells of one chart over
sub-intervals of its coordinate interval is interval-charted (by the
overlap interval) — any two sub-arcs of one chart meet connectedly. -/
lemma chartCell_inter_homeo {r : ℝ → Space} {c₀ : OSub r} (ch : OSub1Chart r c₀)
    {a b c d : ℝ} (hsub1 : Set.Ioo a b ⊆ Set.Ioo ch.lo ch.hi)
    (hsub2 : Set.Ioo c d ⊆ Set.Ioo ch.lo ch.hi) :
    Nonempty (ChartInterval (max a c) (min b d) ≃ₜ
      {z : OSub r // z ∈ chartCell ch a b ∩ chartCell ch c d}) := by
  have hsub : Set.Ioo (max a c) (min b d) ⊆ Set.Ioo ch.lo ch.hi := by
    intro x hx
    rcases hx with ⟨hm, hn⟩
    have hxab : x ∈ Set.Ioo a b :=
      ⟨(max_lt_iff.mp hm).1, (lt_min_iff.mp hn).1⟩
    exact hsub1 hxab
  rw [chartCell_inter ch a b c d]
  exact ⟨chartCellHomeo ch hsub⟩

/-! ## S212 — the cell neighbourhood basis and the pairwise common cell

S211 verified that cells of one chart are interval-charted open
subregions meeting pairwise in interval-charted cells.  This section
adds the basis statement: the cells over coordinate intervals around a
parameter form a NEIGHBOURHOOD BASIS of its lift, and any two cells
containing the same lifted point meet in an interval-charted common
cell containing it:

1. **`chartCell_nhds_basis`** — for a chart `ch`, a parameter `t₀` and
   any open neighbourhood `U` of `oChartLift ch t₀`, there is a cell
   `chartCell ch a b` over a coordinate interval around `t₀` containing
   the point and lying inside `U` (real-interval basis in the chart's
   `(lo,hi)` coordinates via the metric: the open preimage `P` of `U`
   under the continuous lift gives an ε-ball, halved to a real interval
   `(max ch.lo (t₀−δ), min ch.hi (t₀+δ))`);
2. **`chartCell_pairwise_common_at_point`** — two cells of one chart
   both containing the lifted point `x = oChartLift ch t₀` meet in the
   interval-charted common cell `cell (max a c) (min b d)` containing
   `x` (the S211 inter-identity + inter-homeo + the membership of `x`).

The covering argument (S209/S210 route (α)) will pick, at each point, a
basis cell and use (2) for the pairwise-connectedness of its overlaps.

Everything here is verified (no axioms, no `sorry`).
-/

/-- **S212 — the cell neighbourhood basis at a parameter point.**  For a
chart `ch`, a parameter `t₀` and any open neighbourhood `U` of the lifted
point `oChartLift ch t₀`, there is a cell `chartCell ch a b` over a
coordinate interval around `t₀` that contains the point and lies inside
`U`: the cells over coordinate intervals form a neighbourhood basis of
the lift (real-interval basis in the chart's `(lo,hi)` coordinates +
chart continuity). -/
theorem chartCell_nhds_basis {r : ℝ → Space} {c₀ : OSub r} (ch : OSub1Chart r c₀)
    (t₀ : ChartInterval ch.lo ch.hi) :
    ∀ U : Set (OSub r), IsOpen U → oChartLift ch t₀ ∈ U →
      ∃ a b : ℝ, (t₀ : ℝ) ∈ Set.Ioo a b ∧
        oChartLift ch t₀ ∈ chartCell ch a b ∧ chartCell ch a b ⊆ U ∧
        Set.Ioo a b ⊆ Set.Ioo ch.lo ch.hi := by
  intro U hUopen hxU
  let P : Set (ChartInterval ch.lo ch.hi) :=
    {t | oChartLift ch t ∈ U}
  have hPopen : IsOpen P := by
    dsimp [P]
    exact hUopen.preimage (continuous_oChartLift ch)
  have ht₀P : t₀ ∈ P := by
    dsimp [P]
    exact hxU
  have hnhd : P ∈ 𝓝 t₀ := hPopen.mem_nhds ht₀P
  rcases Metric.mem_nhds_iff.mp hnhd with ⟨ε, hε, hball⟩
  let δ : ℝ := ε / 2
  let a : ℝ := max ch.lo (t₀.1 - δ)
  let b : ℝ := min ch.hi (t₀.1 + δ)
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith
  have hδle : δ ≤ ε := by
    dsimp [δ]
    linarith
  have hδlt : δ < ε := by
    dsimp [δ]
    linarith
  have ht₀ab : (t₀ : ℝ) ∈ Set.Ioo a b := by
    change max ch.lo (t₀.1 - δ) < t₀.1 ∧ t₀.1 < min ch.hi (t₀.1 + δ)
    constructor
    · rw [max_lt_iff]
      constructor
      · exact t₀.2.1
      · linarith [hδ]
    · rw [lt_min_iff]
      constructor
      · exact t₀.2.2
      · linarith [hδ]
  have hsub : Set.Ioo a b ⊆ Set.Ioo ch.lo ch.hi := by
    intro r hr
    rcases hr with ⟨hra, hrb⟩
    constructor
    · exact lt_of_le_of_lt (le_max_left ch.lo (t₀.1 - δ)) hra
    · exact lt_of_lt_of_le hrb (min_le_left ch.hi (t₀.1 + δ))
  refine ⟨a, b, ht₀ab, ?_, ?_, hsub⟩
  · dsimp [chartCell]
    refine ⟨t₀, ht₀ab, rfl⟩
  · intro c hc
    dsimp [chartCell] at hc
    rcases hc with ⟨t, ht, rfl⟩
    have hlo : t₀.1 - δ < t.1 :=
      lt_of_le_of_lt (le_max_right ch.lo (t₀.1 - δ)) ht.1
    have hhi : t.1 < t₀.1 + δ :=
      lt_of_lt_of_le ht.2 (min_le_right ch.hi (t₀.1 + δ))
    have hballt : t ∈ Metric.ball t₀ ε := by
      rw [Metric.mem_ball]
      change dist t.1 t₀.1 < ε
      rw [Real.dist_eq]
      apply abs_lt.mpr
      constructor <;> linarith [hlo, hhi, hδle, hδlt]
    exact hball hballt

/-- **S212 — two cells containing the same point meet in an
interval-charted common cell.**  If two cells of one chart over
`(a,b)`, `(c,d)` both contain the lifted point `x = oChartLift ch t₀`
(equivalently `(t₀ : ℝ)` lies in both coordinate intervals), then their
intersection is the interval-charted cell over the overlap interval and
contains `x`. -/
lemma chartCell_pairwise_common_at_point {r : ℝ → Space} {c₀ : OSub r}
    (ch : OSub1Chart r c₀) (t₀ : ChartInterval ch.lo ch.hi)
    {a b c d : ℝ} (hsub1 : Set.Ioo a b ⊆ Set.Ioo ch.lo ch.hi)
    (hsub2 : Set.Ioo c d ⊆ Set.Ioo ch.lo ch.hi)
    (ht1 : (t₀ : ℝ) ∈ Set.Ioo a b) (ht2 : (t₀ : ℝ) ∈ Set.Ioo c d) :
    oChartLift ch t₀ ∈ chartCell ch a b ∩ chartCell ch c d ∧
    Nonempty (ChartInterval (max a c) (min b d) ≃ₜ
      {z : OSub r // z ∈ chartCell ch a b ∩ chartCell ch c d}) := by
  constructor
  · dsimp [chartCell]
    constructor
    · refine ⟨t₀, ht1, rfl⟩
    · refine ⟨t₀, ht2, rfl⟩
  · exact chartCell_inter_homeo ch hsub1 hsub2

/-! ## S213 — the countable cover by chart cells

S212 gives a neighbourhood basis of interval-charted cells at every
parameter point.  This section assembles the COUNTABLE COVER by basis
cells: at each class `x` of the trisecant set take the canonical basis
cell of its own chart (the basis with the whole space as the
neighbourhood — `basisCellA`/`basisCellB`/`basisCell_spec`), giving an
open cover indexed by the classes; the Lindelöf property of the
second-countable trisecant set extracts a COUNTABLE subcover, each
member open and interval-charted:

- **`basisCellA` / `basisCellB` / `basisCell_spec`** — the canonical
  basis cell of a chart around a parameter (coordinate interval contains
  `t₀`; its lift lies in the cell; the interval embeds in the chart's
  coordinate interval — the latter via the S212 basis's containment
  conjunct, giving `chartCellHomeo`'s `hsub`);
- **`osub_countable_chartCell_cover`** — the COVER LEMMA: there is a
  COUNTABLE set `R` of centres such that the family of their basis
  cells (i) is open and interval-charted at every `y ∈ R` (S211
  `chartCellHomeo`) and (ii) covers the whole trisecant set.  This is
  the combinatorial core of route (α): a countable cover whose members
  are chart cells, each carrying its parent chart, so that
  S212-pairwise-connectedness applies within each parent chart.

The exhaustion/refinement ordering (S209/S210 route (α)) continues from
here: pick the cover (this lemma), order the cells along the walk of the
connected component, and use the S210-mechanism/S212 pairwise content to
certify the per-step overlaps.  Everything here is verified (no axioms,
no `sorry`).
-/

/-- The lower endpoint of the canonical basis cell around a parameter
(for the whole space as the neighbourhood). -/
noncomputable def basisCellA {r : ℝ → Space} {c₀ : OSub r} (ch : OSub1Chart r c₀)
    (t₀ : ChartInterval ch.lo ch.hi) : ℝ :=
  Classical.choose (chartCell_nhds_basis ch t₀ (Set.univ : Set (OSub r)) isOpen_univ trivial)

/-- The upper endpoint of the canonical basis cell around a parameter. -/
noncomputable def basisCellB {r : ℝ → Space} {c₀ : OSub r} (ch : OSub1Chart r c₀)
    (t₀ : ChartInterval ch.lo ch.hi) : ℝ :=
  Classical.choose (Classical.choose_spec
    (chartCell_nhds_basis ch t₀ (Set.univ : Set (OSub r)) isOpen_univ trivial))

/-- The canonical basis cell around a parameter: its coordinate interval
contains `t₀`, its lift is in the cell, and the interval embeds in the
chart's coordinate interval. -/
lemma basisCell_spec {r : ℝ → Space} {c₀ : OSub r} (ch : OSub1Chart r c₀)
    (t₀ : ChartInterval ch.lo ch.hi) :
    (t₀ : ℝ) ∈ Set.Ioo (basisCellA ch t₀) (basisCellB ch t₀) ∧
    oChartLift ch t₀ ∈ chartCell ch (basisCellA ch t₀) (basisCellB ch t₀) ∧
    Set.Ioo (basisCellA ch t₀) (basisCellB ch t₀) ⊆ Set.Ioo ch.lo ch.hi := by
  have hA := Classical.choose_spec (chartCell_nhds_basis ch t₀ (Set.univ : Set (OSub r)) isOpen_univ trivial)
  have hB := Classical.choose_spec hA
  rcases hB with ⟨htmem, hmem, hsubU, hsub⟩
  exact ⟨htmem, hmem, hsub⟩

/-- **S213 — the countable cover by chart cells.**  The whole trisecant
set is covered by countably many chart cells: at each class `x` choose
the canonical basis cell of its own chart, giving an open cover; the
Lindelöf property of the second-countable trisecant set
(`IsLindelof.elim_countable_subcover` on `univ`) extracts a COUNTABLE
subcover, each member open and interval-charted (the sub-interval of the
chart via `chartCellHomeo`). -/
theorem osub_countable_chartCell_cover {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r) :
    ∃ R : Set (OSub r), R.Countable ∧
      (∀ y : OSub r, y ∈ R → IsOpen (chartCell (oChartAtClass h hqf hgp y)
        (basisCellA (oChartAtClass h hqf hgp y)
          (chParam (oChartAtClass h hqf hgp y) y (oChartAtClass h hqf hgp y).c₀_mem))
        (basisCellB (oChartAtClass h hqf hgp y)
          (chParam (oChartAtClass h hqf hgp y) y (oChartAtClass h hqf hgp y).c₀_mem)))) ∧
      (∀ y : OSub r, y ∈ R → Nonempty (ChartInterval
        (basisCellA (oChartAtClass h hqf hgp y)
          (chParam (oChartAtClass h hqf hgp y) y (oChartAtClass h hqf hgp y).c₀_mem))
        (basisCellB (oChartAtClass h hqf hgp y)
          (chParam (oChartAtClass h hqf hgp y) y (oChartAtClass h hqf hgp y).c₀_mem)) ≃ₜ
          {c : OSub r // c ∈ chartCell (oChartAtClass h hqf hgp y)
            (basisCellA (oChartAtClass h hqf hgp y)
              (chParam (oChartAtClass h hqf hgp y) y (oChartAtClass h hqf hgp y).c₀_mem))
            (basisCellB (oChartAtClass h hqf hgp y)
              (chParam (oChartAtClass h hqf hgp y) y (oChartAtClass h hqf hgp y).c₀_mem))})) ∧
      (∀ x : OSub r, ∃ y : OSub r, y ∈ R ∧
        x ∈ chartCell (oChartAtClass h hqf hgp y)
          (basisCellA (oChartAtClass h hqf hgp y)
            (chParam (oChartAtClass h hqf hgp y) y (oChartAtClass h hqf hgp y).c₀_mem))
          (basisCellB (oChartAtClass h hqf hgp y)
            (chParam (oChartAtClass h hqf hgp y) y (oChartAtClass h hqf hgp y).c₀_mem))) := by
  classical
  let U : OSub r → Set (OSub r) := fun y =>
    chartCell (oChartAtClass h hqf hgp y)
      (basisCellA (oChartAtClass h hqf hgp y)
        (chParam (oChartAtClass h hqf hgp y) y (oChartAtClass h hqf hgp y).c₀_mem))
      (basisCellB (oChartAtClass h hqf hgp y)
        (chParam (oChartAtClass h hqf hgp y) y (oChartAtClass h hqf hgp y).c₀_mem))
  have hUopen : ∀ y : OSub r, IsOpen (U y) := by
    intro y
    dsimp [U]
    exact isOpen_chartCell _ _ _
  have hcoverU : Set.univ ⊆ ⋃ y : OSub r, U y := by
    intro x hx
    have hspec := basisCell_spec (oChartAtClass h hqf hgp x)
      (chParam (oChartAtClass h hqf hgp x) x (oChartAtClass h hqf hgp x).c₀_mem)
    have hmem : x ∈ chartCell (oChartAtClass h hqf hgp x)
        (basisCellA (oChartAtClass h hqf hgp x)
          (chParam (oChartAtClass h hqf hgp x) x (oChartAtClass h hqf hgp x).c₀_mem))
        (basisCellB (oChartAtClass h hqf hgp x)
          (chParam (oChartAtClass h hqf hgp x) x (oChartAtClass h hqf hgp x).c₀_mem)) := by
      -- oChartLift ch (chParam ch x c₀_mem) = x (chParam_lift), so hspec.2.1 gives membership
      simpa [chParam_lift] using hspec.2.1
    exact Set.mem_iUnion.mpr ⟨x, by simpa [U] using hmem⟩
  rcases IsLindelof.elim_countable_subcover (s := (Set.univ : Set (OSub r)))
      (U := U) (by exact isLindelof_univ) hUopen hcoverU with ⟨R, hRcount, hRcov⟩
  refine ⟨R, hRcount, ?_, ?_, ?_⟩
  · intro y hy
    exact hUopen y
  · intro y hy
    have hspec := basisCell_spec (oChartAtClass h hqf hgp y)
      (chParam (oChartAtClass h hqf hgp y) y (oChartAtClass h hqf hgp y).c₀_mem)
    exact ⟨chartCellHomeo (oChartAtClass h hqf hgp y) hspec.2.2⟩
  · intro x
    have hxuniv : x ∈ ⋃ y ∈ R, U y := by
      exact hRcov (Set.mem_univ x)
    rcases Set.mem_iUnion₂.mp hxuniv with ⟨y, hyR, hyU⟩
    refine ⟨y, hyR, ?_⟩
    simpa [U] using hyU

end LeanEval.KnotTheory.Quadrisecant
