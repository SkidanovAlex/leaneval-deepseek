import Mathlib
import Submission.OChartExhaustion

set_option linter.style.haveILetI false

open LeanEval.KnotTheory.Quadrisecant
open Set
open scoped Real Topology unitInterval

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

set_option maxHeartbeats 800000

/-!
# Chart traces of the trisecant set: path-connected open sets with interval
coordinates (S114 — the instantiation input of the walk/exhaustion
machinery)

`OSubChart.lean` (S97/S98) gave every trisecant class an interval chart
(`OSub1Chart`): an open real interval `(lo,hi)` homeomorphic to an open
trace of `O`.  This module records the elementary consequences used by the
component-exhaustion ordering (S113's `ConnectedWalk` instantiation, next
slice):

1. **the open real interval is path-connected** —
   `chartInterval_pathConnected`: for `lo < hi`, the subtype
   `{t : ℝ // t ∈ Set.Ioo lo hi}` is a path-connected space (straight-line
   paths between parameters, staying inside the open interval by
   convexity — elementary real arithmetic);
2. **the trace of a chart** — `chartTrace ch` (the set of classes of
   `OSub r` whose band value lies in the trace set `W` of the chart),
   `chartTrace_eq_range` (the trace is exactly the range of the chart's
   class map `t ↦ (ch.homeo t).1`), **`chartTrace_pathConnected`** (the
   trace is path-connected: it is the continuous image of the
   path-connected interval), **`chartTraceHomeo`** (the interval
   parametrisation of the trace — the chart homeo re-read onto the trace
   subtype), and `isOpen_chartTrace`;
3. **the chart-trace instance over the S107 cover** — `oChartTrace_pathConnected`
   (every `OChartTraceSet h hqf hgp x` is path-connected: it is the trace
   of the chosen chart at `x`).

These are exactly the hypotheses that `ConnectedWalk.exists_overlap_walk` /
`exists_pathConnected_open_exhaustion` (S113) need to turn the S107
countable chart-trace cover of a component into an increasing exhaustion
by path-connected open sets (each chart trace is homeomorphic to an open
interval of `ℝ`, hence path-connected) — the topological skeleton of the
interval-chain-ordering construction of the component classification
(brick (b) remainder).

Everything here is elementary and verified (no axioms, no `sorry`).
-/

/-! ## 1. Path-connectedness of open intervals of ℝ -/

/-- The segment between two reals of `[a,b]` stays inside `[a,b]`. -/
private lemma seg_mem_Icc {a b : ℝ} (hab : a ≤ b) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    a ≤ (1 - t) * a + t * b ∧ (1 - t) * a + t * b ≤ b := by
  constructor
  · have h : (1 - t) * a + t * b - a = t * (b - a) := by ring
    rw [← sub_nonneg, h]
    exact mul_nonneg ht0 (sub_nonneg.mpr hab)
  · have h : b - ((1 - t) * a + t * b) = (1 - t) * (b - a) := by ring
    rw [← sub_nonneg, h]
    exact mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hab)

/-- A convex combination of two points of an open interval lies in the
interval. -/
private lemma seg_mem_Ioo {lo hi a b : ℝ} (ha : a ∈ Set.Ioo lo hi) (hb : b ∈ Set.Ioo lo hi)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * a + t * b ∈ Set.Ioo lo hi := by
  rcases ha with ⟨halo, hahi⟩
  rcases hb with ⟨hblo, hbhi⟩
  by_cases hab : a ≤ b
  · rcases seg_mem_Icc hab ht0 ht1 with ⟨h1, h2⟩
    constructor
    · exact lt_of_lt_of_le halo h1
    · exact lt_of_le_of_lt h2 hbhi
  · have hba : b ≤ a := le_of_lt (lt_of_not_ge hab)
    -- the combination is the convex combination of `b` and `a` with
    -- complementary weight `1 - t`
    have hu0 : 0 ≤ 1 - t := sub_nonneg.mpr ht1
    have hu1 : 1 - t ≤ 1 := by linarith
    rcases seg_mem_Icc hba hu0 hu1 with ⟨h1, h2⟩
    have h1' : b ≤ (1 - t) * a + t * b := by
      convert h1 using 1; ring
    have h2' : (1 - t) * a + t * b ≤ a := by
      convert h2 using 1; ring
    constructor
    · exact lt_of_lt_of_le hblo h1'
    · exact lt_of_le_of_lt h2' hahi

/-- An open interval of `ℝ`, as a subtype, is path-connected whenever it is
nonempty (`lo < hi`): join two parameters by the straight-line segment,
which stays inside the open interval. -/
lemma chartInterval_pathConnected {lo hi : ℝ} (hlt : lo < hi) :
    PathConnectedSpace {t : ℝ // t ∈ Set.Ioo lo hi} := by
  refine ⟨?_, ?_⟩
  · refine ⟨⟨(lo + hi) / 2, ?_⟩⟩
    constructor
    · linarith
    · linarith
  · intro x y
    let p : I → {t : ℝ // t ∈ Set.Ioo lo hi} := fun s =>
      ⟨(1 - (s : ℝ)) * (x : ℝ) + (s : ℝ) * (y : ℝ),
        seg_mem_Ioo x.2 y.2 (unitInterval.nonneg s) (unitInterval.le_one s)⟩
    have hcont : Continuous p := by
      dsimp [p]
      exact Continuous.subtype_mk (by fun_prop)
        (fun s => seg_mem_Ioo x.2 y.2 (unitInterval.nonneg s) (unitInterval.le_one s))
    refine ⟨Path.mk ⟨p, hcont⟩ ?_ ?_⟩
    · apply Subtype.ext
      simp [p]
    · apply Subtype.ext
      simp [p]

/-! ## 2. Chart traces: interval-coordinates, openness, path-connectedness -/

/-- The trace of a chart: the classes of `OSub r` whose band value lies in
the trace set `W` of the chart. -/
def chartTrace {r : ℝ → Space} {c₀ : OSub r} (ch : OSub1Chart r c₀) : Set (OSub r) :=
  {y : OSub r | (y : OpenMobius) ∈ ch.W}

/-- The trace of a chart is exactly the range of its class map (the chart
homeo read into `OSub r`). -/
lemma chartTrace_eq_range {r : ℝ → Space} {c₀ : OSub r} (ch : OSub1Chart r c₀) :
    chartTrace ch = Set.range (fun t : ChartInterval ch.lo ch.hi => (ch.homeo t).1) := by
  ext y
  constructor
  · intro hy
    rcases ch.homeo.surjective ⟨y, hy⟩ with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    have hv := congrArg (fun z : {c : OSub r // (c : OpenMobius) ∈ ch.W} => (z : OSub r)) ht
    simpa using hv
  · rintro ⟨t, rfl⟩
    exact (ch.homeo t).2

/-- The trace of a chart is open in `OSub r`. -/
lemma isOpen_chartTrace {r : ℝ → Space} {c₀ : OSub r} (ch : OSub1Chart r c₀) :
    IsOpen (chartTrace ch) := by
  dsimp [chartTrace]
  exact ch.W_open.preimage continuous_subtype_val

/-- Each chart trace is path-connected: the chart parametrises it by the
open real interval `(ch.lo, ch.hi)`, and the continuous image of a
path-connected space is path-connected. -/
lemma chartTrace_pathConnected {r : ℝ → Space} {c₀ : OSub r} (ch : OSub1Chart r c₀) :
    IsPathConnected (chartTrace ch) := by
  have hlt : ch.lo < ch.hi := by
    exact lt_trans ch.x₀_mem.1 ch.x₀_mem.2
  letI := chartInterval_pathConnected hlt
  have hcont : Continuous (fun t : ChartInterval ch.lo ch.hi => (ch.homeo t).1) := by
    exact continuous_subtype_val.comp ch.homeo.continuous
  rw [chartTrace_eq_range ch]
  exact isPathConnected_range hcont

/-- The interval parametrisation of a chart trace: the chart homeo re-read
as a homeomorphism onto the trace subtype. -/
noncomputable def chartTraceHomeo {r : ℝ → Space} {c₀ : OSub r} (ch : OSub1Chart r c₀) :
    ChartInterval ch.lo ch.hi ≃ₜ {c : OSub r // c ∈ chartTrace ch} :=
  ch.homeo

/-! ## 3. The S107 chart-trace cover instance -/

/-- Each chart trace of the trisecant-set cover (`OChartTraceSet`, the
trace of the chosen interval chart at a class of the S107 countable cover)
is path-connected. -/
lemma oChartTrace_pathConnected {r : ℝ → Space} {h : IsSmoothKnot r}
    {hqf : QuadrisecantFree r} {hgp : TorusGeneralPositionTransverse r} (x : OSub r) :
    IsPathConnected (OChartTraceSet h hqf hgp x) := by
  have hpc := chartTrace_pathConnected (oChartAtClass h hqf hgp x)
  simpa [OChartTraceSet, chartTrace] using hpc


/-! ## 4. Traces lie in the connected component of their centre -/

/-- The trace of a chart is contained in the connected component of the
chart's centre class: the trace is path-connected (hence connected) and
contains its centre. -/
lemma chartTrace_subset_connectedComponent {r : ℝ → Space} {c₀ : OSub r}
    (ch : OSub1Chart r c₀) : chartTrace ch ⊆ connectedComponent c₀ := by
  exact (chartTrace_pathConnected ch).isConnected.isPreconnected.subset_connectedComponent
    ch.c₀_mem

end LeanEval.KnotTheory.Quadrisecant
