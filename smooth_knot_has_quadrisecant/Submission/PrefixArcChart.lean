import Mathlib
import Submission.AlignedCover

open LeanEval.KnotTheory.Quadrisecant
open Set
open scoped Real Topology unitInterval

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

set_option maxHeartbeats 1600000

/-!
# Milestone-2 (iv) step 6, brick (b) — the per-length arc datum is an
open interval-charted subset of the component (S139)

The S138 datum (`componentWalk_arcs_at_every_length`) provides, at every
prefix length of a walk, an injective continuous arc of trisecant classes
anchored at the orbit class, inside the component and the walk partial
union.  The missing interval-chart content — that the arc's range is an
OPEN subset of `OSub r` — is proved here.  The arc map factors as the
chart lift of the first walk chart over the open parameter cell: the
cell `{t | (t : ℝ) ∈ Ioo a b}` is open in the chart-interval space (a
real preimage of an open interval), the chart homeo is open, and the
trace subtype is an open set of `OSub r` (`chartTrace ch` is open), so
its projection is an open map (`IsOpen.isOpenMap_subtype_val`): the
range of the chart lift over the cell is open (`isOpen_lift_cell`).

Content (namespace LeanEval.KnotTheory.Quadrisecant):
1. `isOpen_paramCell` — the open parameter cell (real preimage of
   `Ioo a b` in the chart-interval space);
2. `isOpen_lift_cell` — the chart-lift image of a parameter cell is open
   in `OSub r` (cell open; chart homeo open; trace-subtype projection
   open);
3. `walkAlignedArcMap_range_eq_liftCell` — the range of the aligned arc
   equals the chart-lift image of its parameter cell (the classes whose
   `ch 0`-parameter lies in the aligned start interval);
4. **`walkAligned_arc_openSet`** — the S139 headline: from walk overlap
   data, an orbit `htr` through the first `n` junction pieces, and the
   first walk class in the component of `c₀`, there is datum data `sub`
   whose aligned start interval contains the orbit parameter, whose arc
   map is injective, continuous, has OPEN range, whose range lies in the
   component of `c₀` and in the walk partial union
   `⋃_{m < n+2} OChartTraceSet (cl (e m))`, and contains the orbit
   class: the per-length arc datum turned into a covering interval chart
   (the `Eₙ ⊆ Uₙ` covering of an exhaustion step by this chart's range
   is the ordering slice — see the ROADMAP session log S139).

Everything here is elementary and verified (no axioms, no `sorry`).
-/

/-- The open cell of chart parameters whose real values lie in `(a,b)`
(open in the chart-interval subspace: preimage of `Ioo a b` under the
continuous real projection). -/
lemma isOpen_paramCell {lo hi a b : ℝ} :
    IsOpen ({t : ChartInterval lo hi | (t : ℝ) ∈ Set.Ioo a b} : Set (ChartInterval lo hi)) := by
  exact isOpen_Ioo.preimage (continuous_subtype_val : Continuous (fun t : ChartInterval lo hi => (t : ℝ)))

/-- **The chart-lift image of a parameter cell is open.**  The classes of
the chart's trace whose parameter lies in the open cell `(a,b)` form an
open subset of `OSub r`: the cell is open in the chart-interval space
(real preimage of `Ioo a b`), the chart homeo sends it to an open subset
of the trace subtype, and the trace subtype — being the open
`chartTrace ch` — projects to an open set of `OSub r`. -/
lemma isOpen_lift_cell {r : ℝ → Space} {c₀ : OSub r} (ch : OSub1Chart r c₀)
    {a b : ℝ} :
    IsOpen (((fun t : ChartInterval ch.lo ch.hi => oChartLift ch t) ''
      {t : ChartInterval ch.lo ch.hi | (t : ℝ) ∈ Set.Ioo a b}) : Set (OSub r)) := by
  let cell : Set (ChartInterval ch.lo ch.hi) := {t | (t : ℝ) ∈ Set.Ioo a b}
  have hcellOpen : IsOpen cell := by
    dsimp [cell]
    exact isOpen_paramCell
  let T : Type := {c : OSub r // (c : OpenMobius) ∈ ch.W}
  have hvalOpen : IsOpenMap (fun t : T => (t : OSub r)) := by
    have hs : IsOpen ({c : OSub r | (c : OpenMobius) ∈ ch.W} : Set (OSub r)) := by
      simpa [chartTrace] using (isOpen_chartTrace ch)
    exact hs.isOpenMap_subtype_val
  have himgHomeo : IsOpen (ch.homeo.toFun '' cell) :=
    ch.homeo.isOpenMap cell hcellOpen
  have hσcell : (fun t : ChartInterval ch.lo ch.hi => oChartLift ch t) '' cell =
      (fun t : T => (t : OSub r)) '' (ch.homeo.toFun '' cell) := by
    ext c
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨ch.homeo t, ⟨t, ht, rfl⟩, ?_⟩
      change ((ch.homeo t : T) : OSub r) = oChartLift ch t
      rfl
    · rintro ⟨w, hw, rfl⟩
      rcases hw with ⟨t, ht, hwt⟩
      refine ⟨t, ht, ?_⟩
      change oChartLift ch t = (w : OSub r)
      rw [← hwt]
      rfl
  rw [hσcell]
  exact hvalOpen (ch.homeo.toFun '' cell) himgHomeo

/-- The range of the aligned arc equals the parameter cell of the first
walk chart: the classes whose `ch 0`-parameter lies in the aligned start
interval `(a,b)` (where `a,b` are the datum-piece bounds of `sub 0`). -/
lemma walkAlignedArcMap_range_eq_liftCell {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (sub : (i : ℕ) → SubDatum (walkJunctionPiece h hqf hgp cl e hoverlap i)) :
    Set.range (walkAlignedArcMap h hqf hgp cl e hoverlap sub) =
      (fun t : ChartInterval (walkChart h hqf hgp cl e 0).lo (walkChart h hqf hgp cl e 0).hi =>
        oChartLift (walkChart h hqf hgp cl e 0) t) ''
        {t : ChartInterval (walkChart h hqf hgp cl e 0).lo (walkChart h hqf hgp cl e 0).hi |
          (t : ℝ) ∈ Set.Ioo (datumPiece (sub 0)).lo (datumPiece (sub 0)).hi} := by
  let ch := walkChart h hqf hgp cl e 0
  let a : ℝ := (datumPiece (sub 0)).lo
  let b : ℝ := (datumPiece (sub 0)).hi
  ext c
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨⟨(u : ℝ), datumPiece_chartSubset h hqf hgp cl e hoverlap 0 (sub 0) u.2⟩, ?_, ?_⟩
    · change (u : ℝ) ∈ Set.Ioo a b
      dsimp [a, b]
      exact u.2
    · change oChartLift ch
          ⟨(u : ℝ), datumPiece_chartSubset h hqf hgp cl e hoverlap 0 (sub 0) u.2⟩ = c
      dsimp [ch, walkAlignedArcMap] at hu ⊢
      exact hu
  · rintro ⟨t, ht, htσ⟩
    have htcell : (t : ℝ) ∈ Set.Ioo a b := by
      simpa using ht
    let u : ChartInterval a b := ⟨(t : ℝ), htcell⟩
    have hemb : (⟨(u : ℝ), datumPiece_chartSubset h hqf hgp cl e hoverlap 0 (sub 0) u.2⟩ :
        ChartInterval ch.lo ch.hi) = t := by
      apply Subtype.ext
      change (u : ℝ) = (t : ℝ)
      rfl
    refine ⟨u, ?_⟩
    change oChartLift ch
        ⟨(u : ℝ), datumPiece_chartSubset h hqf hgp cl e hoverlap 0 (sub 0) u.2⟩ = c
    rw [hemb]
    dsimp [ch] at htσ ⊢
    exact htσ

/-- **The per-length arc datum is an open interval-charted subset of the
component.**  From walk overlap data, an orbit `htr` through the first
`n` junction pieces, and the first walk class in the component of `c₀`,
there is datum data `sub` whose aligned start interval contains the orbit
parameter and whose arc map is injective, continuous, has OPEN range in
`OSub r` (the range is a parameter cell of the first chart's trace), and
whose range lies in the component of `c₀` and in the walk partial union
`⋃_{m < n+2} OChartTraceSet (cl (e m))`, and contains the orbit class. -/
theorem walkAligned_arc_openSet {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (c₀ : OSub r) (hc0 : cl (e 0) ∈ connectedComponent c₀) (n : ℕ)
    (x₀ : ChartInterval (walkJunctionPiece h hqf hgp cl e hoverlap 0).lo
      (walkJunctionPiece h hqf hgp cl e hoverlap 0).hi)
    (htr : transports (walkJunctionPiece h hqf hgp cl e hoverlap 0)
      (chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) x₀) :
    ∃ sub : (i : ℕ) → SubDatum (walkJunctionPiece h hqf hgp cl e hoverlap i),
      ((x₀ : ℝ) ∈ Set.Ioo (datumPiece (sub 0)).lo (datumPiece (sub 0)).hi) ∧
      Function.Injective (walkAlignedArcMap h hqf hgp cl e hoverlap sub) ∧
      Continuous (walkAlignedArcMap h hqf hgp cl e hoverlap sub) ∧
      IsOpen (Set.range (walkAlignedArcMap h hqf hgp cl e hoverlap sub)) ∧
      (∀ x : ChartInterval (datumPiece (sub 0)).lo (datumPiece (sub 0)).hi,
        walkAlignedArcMap h hqf hgp cl e hoverlap sub x ∈ connectedComponent c₀) ∧
      (∀ x : ChartInterval (datumPiece (sub 0)).lo (datumPiece (sub 0)).hi,
        walkAlignedArcMap h hqf hgp cl e hoverlap sub x ∈
          ⋃ m ∈ Set.Iio (n + 2), OChartTraceSet h hqf hgp (cl (e m))) ∧
      oChartLift (walkChart h hqf hgp cl e 0)
          ⟨(x₀ : ℝ), walkJunction_subset h hqf hgp cl e hoverlap 0 x₀.2⟩ ∈
        Set.range (walkAlignedArcMap h hqf hgp cl e hoverlap sub) := by
  rcases walkAligned_arc_subset_walkUnion h hqf hgp cl e hoverlap c₀ hc0 n x₀ htr with
    ⟨sub, hx₀mem, hinj, hcont, hC, hP⟩
  refine ⟨sub, hx₀mem, hinj, hcont, ?_, hC, hP, ?_⟩
  · rw [walkAlignedArcMap_range_eq_liftCell h hqf hgp cl e hoverlap sub]
    exact isOpen_lift_cell (walkChart h hqf hgp cl e 0)
  · refine ⟨⟨(x₀ : ℝ), hx₀mem⟩, ?_⟩
    exact walkAlignedArcMap_at_orbitClass h hqf hgp cl e hoverlap sub x₀ hx₀mem

/-! ## S140a — the per-length arc datum IS an interval-chart of its
range (`walkAlignedArcMap_homeo_range`)

S139 proved the range of the aligned arc is open; this section upgrades
the datum to a genuine interval-chart: the arc map is continuous and
injective (S130/S132) and OPEN (the chart lift is an open map — the
trace-subtype projection after the chart homeo — and the sub-piece
embedding into the chart interval is an open map onto its parameter
cell), so it is a homeomorphism onto its range
(`homeo_range_of_continuous_injective_isOpenMap`, one line through
`Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap` +
`toHomeomorph`).  This is the T1 piece of the ROADMAP S140 ordering
specification: each per-length datum provides an explicit interval-chart
`ChartInterval a b ≃ₜ {c : OSub r // c ∈ range arc}` of an open cell
inside the component. -/

/-- Continuous + injective + open map ⇒ homeo onto the range. -/
noncomputable def homeo_range_of_continuous_injective_isOpenMap {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)
    (hcont : Continuous f) (hinj : Function.Injective f) (hopen : IsOpenMap f) :
    X ≃ₜ {y : Y // y ∈ Set.range f} :=
  (Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hcont hinj hopen).isEmbedding.toHomeomorph

/-- The chart lift is an open map: `val ∘ ch.homeo` with the trace subtype
open and the homeo open. -/
lemma isOpenMap_oChartLift {r : ℝ → Space} {c₀ : OSub r} (ch : OSub1Chart r c₀) :
    IsOpenMap (fun t : ChartInterval ch.lo ch.hi => oChartLift ch t) := by
  let T : Type := {c : OSub r // (c : OpenMobius) ∈ ch.W}
  have hvalOpen : IsOpenMap (fun t : T => (t : OSub r)) := by
    have hs : IsOpen ({c : OSub r | (c : OpenMobius) ∈ ch.W} : Set (OSub r)) := by
      simpa [chartTrace] using (isOpen_chartTrace ch)
    exact hs.isOpenMap_subtype_val
  change IsOpenMap (fun t : ChartInterval ch.lo ch.hi => ((ch.homeo t : T) : OSub r))
  exact IsOpenMap.comp hvalOpen ch.homeo.isOpenMap

/-- The open parameter cell `{t : ChartInterval lo hi // (t : ℝ) ∈ Ioo a
b}` is homeomorphic to `ChartInterval a b` (for `(a,b) ⊆ (lo,hi)`): the
explicit sub-piece embedding with its real-value inverse. -/
noncomputable def paramCellHomeo {lo hi a b : ℝ} (hsub : Set.Ioo a b ⊆ Set.Ioo lo hi) :
    ChartInterval a b ≃ₜ {t : ChartInterval lo hi // (t : ℝ) ∈ Set.Ioo a b} where
  toFun := fun u => ⟨(⟨(u : ℝ), hsub u.2⟩ : ChartInterval lo hi), (by
    change (u : ℝ) ∈ Set.Ioo a b
    exact u.2)⟩
  invFun := fun t => ⟨(t.1 : ℝ), t.2⟩
  left_inv := by
    intro u
    apply Subtype.ext
    rfl
  right_inv := by
    intro t
    apply Subtype.ext
    apply Subtype.ext
    rfl
  continuous_toFun := by
    exact Continuous.subtype_mk
      (Continuous.subtype_mk continuous_subtype_val (fun u => hsub u.2))
      (fun u => by change (u : ℝ) ∈ Set.Ioo a b; exact u.2)
  continuous_invFun := by
    exact Continuous.subtype_mk
      (continuous_subtype_val.comp continuous_subtype_val)
      (fun t => t.2)

/-- The sub-piece embedding into the chart interval is an open map (the
image is the open parameter cell). -/
lemma isOpenMap_paramEmbedding {lo hi a b : ℝ} (hsub : Set.Ioo a b ⊆ Set.Ioo lo hi) :
    IsOpenMap (fun u : ChartInterval a b => (⟨(u : ℝ), hsub u.2⟩ : ChartInterval lo hi)) := by
  have hs : IsOpen ({t : ChartInterval lo hi | (t : ℝ) ∈ Set.Ioo a b} : Set (ChartInterval lo hi)) := by
    exact isOpen_Ioo.preimage (continuous_subtype_val : Continuous (fun t : ChartInterval lo hi => (t : ℝ)))
  have hvalOpen : IsOpenMap (fun t : {t : ChartInterval lo hi // (t : ℝ) ∈ Set.Ioo a b} =>
      (t : ChartInterval lo hi)) := hs.isOpenMap_subtype_val
  let h := paramCellHomeo hsub
  have hcomp : IsOpenMap (fun u : ChartInterval a b =>
      ((h u : {t : ChartInterval lo hi // (t : ℝ) ∈ Set.Ioo a b}).1 : ChartInterval lo hi)) :=
    IsOpenMap.comp hvalOpen h.isOpenMap
  convert hcomp using 1
  funext u
  rfl

/-- **The aligned arc is a homeo onto its range.**  The arc map of an
aligned datum (walk data + sub) is continuous and injective (S130/S132)
and open (lift after the cell embedding, both open maps), hence a
homeomorphism onto its range — the per-length interval-chart of its open
cell. -/
noncomputable def walkAlignedArcMap_homeo_range {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (sub : (i : ℕ) → SubDatum (walkJunctionPiece h hqf hgp cl e hoverlap i)) :
    ChartInterval (datumPiece (sub 0)).lo (datumPiece (sub 0)).hi ≃ₜ
      {c : OSub r // c ∈ Set.range (walkAlignedArcMap h hqf hgp cl e hoverlap sub)} := by
  let a : ℝ := (datumPiece (sub 0)).lo
  let b : ℝ := (datumPiece (sub 0)).hi
  let emb : ChartInterval a b → ChartInterval (walkChart h hqf hgp cl e 0).lo
      (walkChart h hqf hgp cl e 0).hi := fun u =>
    ⟨(u : ℝ), datumPiece_chartSubset h hqf hgp cl e hoverlap 0 (sub 0) u.2⟩
  have harc : walkAlignedArcMap h hqf hgp cl e hoverlap sub =
      (fun t : ChartInterval (walkChart h hqf hgp cl e 0).lo (walkChart h hqf hgp cl e 0).hi =>
        oChartLift (walkChart h hqf hgp cl e 0) t) ∘ emb := by
    funext u
    rfl
  have hopen : IsOpenMap (walkAlignedArcMap h hqf hgp cl e hoverlap sub) := by
    rw [harc]
    exact IsOpenMap.comp (isOpenMap_oChartLift (walkChart h hqf hgp cl e 0))
      (isOpenMap_paramEmbedding (datumPiece_chartSubset h hqf hgp cl e hoverlap 0 (sub 0)))
  exact homeo_range_of_continuous_injective_isOpenMap
    (walkAlignedArcMap h hqf hgp cl e hoverlap sub)
    (continuous_walkAlignedArcMap h hqf hgp cl e hoverlap sub)
    (walkAlignedArcMap_injective h hqf hgp cl e hoverlap sub)
    hopen


/-! ## S140b — compatibility of nested per-length cell charts

The T2 increasing family needs the successive cell charts to be
compatible.  Since every per-length arc is the `ch 0`-lift over its
aligned start interval, the compatibility between a length-`n` cell and
a length-`(n+1)` cell whose start intervals NEST is purely parametric:
the class maps agree through the real-value reindexing
(`walkAlignedArcMap_eq_of_nested`), the ranges nest
(`walkAlignedArcMap_nested_range_mem`), and the change-of-chart triangle
is the interval reindexing — going up the inner chart, embedding the
range, and coming back down the outer chart's inverse equals
`u ↦ ⟨(u : ℝ), hI u.2⟩` (`walkAligned_changeChart_of_nested`).  This is
the compatibility core of the assembly; the NESTING hypothesis `hI` is
genuine data (per the S106 scoping note, choosing nested sub-data across
consecutive lengths — the forward-consistent backward shrink — is the
S140c ordering step, not assumed here). -/

/-- **Nested arcs agree through the parameter reindexing.**  For two
aligned datums of the same walk whose start intervals nest
(`Ioo a' b' ⊆ Ioo a b`), the class maps agree: the inner arc at a
parameter equals the outer arc at the reindexed parameter — both are the
`ch 0`-lift of the same real parameter. -/
lemma walkAlignedArcMap_eq_of_nested {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (sub sub' : (i : ℕ) → SubDatum (walkJunctionPiece h hqf hgp cl e hoverlap i))
    (hI : Set.Ioo (datumPiece (sub' 0)).lo (datumPiece (sub' 0)).hi ⊆
      Set.Ioo (datumPiece (sub 0)).lo (datumPiece (sub 0)).hi) :
    ∀ u : ChartInterval (datumPiece (sub' 0)).lo (datumPiece (sub' 0)).hi,
      walkAlignedArcMap h hqf hgp cl e hoverlap sub' u =
        walkAlignedArcMap h hqf hgp cl e hoverlap sub ⟨(u : ℝ), hI u.2⟩ := by
  intro u
  unfold walkAlignedArcMap
  congr 1

/-- **Nested start intervals give nested ranges.**  The inner arc's range
is contained in the outer arc's range (both are parameter cells of the
first chart's trace). -/
lemma walkAlignedArcMap_nested_range_mem {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (sub sub' : (i : ℕ) → SubDatum (walkJunctionPiece h hqf hgp cl e hoverlap i))
    (hI : Set.Ioo (datumPiece (sub' 0)).lo (datumPiece (sub' 0)).hi ⊆
      Set.Ioo (datumPiece (sub 0)).lo (datumPiece (sub 0)).hi) :
    ∀ u : ChartInterval (datumPiece (sub' 0)).lo (datumPiece (sub' 0)).hi,
      walkAlignedArcMap h hqf hgp cl e hoverlap sub' u ∈
        Set.range (walkAlignedArcMap h hqf hgp cl e hoverlap sub) := by
  intro u
  refine ⟨⟨(u : ℝ), hI u.2⟩, ?_⟩
  exact (walkAlignedArcMap_eq_of_nested h hqf hgp cl e hoverlap sub sub' hI u).symm

/-- **Change-of-chart between nested per-length cell charts.**  Let
`φ := walkAlignedArcMap_homeo_range … sub` (length `n`) and
`φ' := walkAlignedArcMap_homeo_range … sub'` (length `n+1`) be the cell
charts of two aligned datums with nested start intervals
(`hI : Ioo a' b' ⊆ Ioo a b`).  Then for an inner parameter `u`, going
`φ'` up to the inner range, embedding into the outer range, and coming
back with `φ.symm` is exactly the interval reindexing `u ↦ ⟨(u : ℝ), hI
u.2⟩`: the restriction of the `n+1` chart to the inner interval agrees
with the `n` chart up to the change-of-chart map (the two cell
coordinates of the same class are the same real parameter). -/
lemma walkAligned_changeChart_of_nested {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (sub sub' : (i : ℕ) → SubDatum (walkJunctionPiece h hqf hgp cl e hoverlap i))
    (hI : Set.Ioo (datumPiece (sub' 0)).lo (datumPiece (sub' 0)).hi ⊆
      Set.Ioo (datumPiece (sub 0)).lo (datumPiece (sub 0)).hi)
    (u : ChartInterval (datumPiece (sub' 0)).lo (datumPiece (sub' 0)).hi) :
    (walkAlignedArcMap_homeo_range h hqf hgp cl e hoverlap sub).symm
        ⟨walkAlignedArcMap h hqf hgp cl e hoverlap sub' u,
          walkAlignedArcMap_nested_range_mem h hqf hgp cl e hoverlap sub sub' hI u⟩ =
      ⟨(u : ℝ), hI u.2⟩ := by
  let φ := walkAlignedArcMap_homeo_range h hqf hgp cl e hoverlap sub
  apply φ.injective
  calc
    φ (φ.symm ⟨walkAlignedArcMap h hqf hgp cl e hoverlap sub' u,
          walkAlignedArcMap_nested_range_mem h hqf hgp cl e hoverlap sub sub' hI u⟩)
        = ⟨walkAlignedArcMap h hqf hgp cl e hoverlap sub' u,
            walkAlignedArcMap_nested_range_mem h hqf hgp cl e hoverlap sub sub' hI u⟩ := by
          exact φ.apply_symm_apply _
    _ = φ ⟨(u : ℝ), hI u.2⟩ := by
          apply Subtype.ext
          change walkAlignedArcMap h hqf hgp cl e hoverlap sub' u =
            walkAlignedArcMap h hqf hgp cl e hoverlap sub ⟨(u : ℝ), hI u.2⟩
          exact walkAlignedArcMap_eq_of_nested h hqf hgp cl e hoverlap sub sub' hI u


/-! ## S140d — the arc theorems relativized to a GIVEN datum
(`alignedData_reaches_end`, `alignedData_arc_openSet`)

The S139/S140a arc theorems re-choose their datum internally; this
section restates them for a GIVEN datum of the `exists_walk_aligned_subdata_within`
shape (S140c output: `d0 sub`, `sub 0 = d0`, `x₀` in the head interval,
forward totality `htot`).  The genuinely new content is the datum-
relative REACH (`alignedData_reaches_end`): the inner half of S129
(`walkAligned_reaches_end`) run on the given datum — totality transported
to the head piece by `transports_congr_piece` through `hpp : datumPiece
(sub 0) = datumPiece d0`, then `chain_transport_class_coordinate` on the
datum family with the datum-level `hsub`/`hsem`.  Everything else
(injectivity, continuity, openness of the range, the component and
partial-union containments, the anchor) is the S130/S132/S139 content
read off the given `sub`. -/

/-- **Datum-relative reach.**  Given datum data `d0 sub` with
`sub 0 = d0` and forward totality from the head through the `n`-tail
chain of the datum family, every class of the aligned start interval is
reached in the `(n+1)`-th walk chart: `∃ y : OChartTransitionDomain
(ch (0+n+1)) (ch 0)` with the class equality — the inner half of S129
`walkAligned_reaches_end` run on a GIVEN datum (no orbit; the totality
supplies the transport). -/
theorem alignedData_reaches_end {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty) (n : ℕ)
    (d0 : SubDatum (walkJunctionPiece h hqf hgp cl e hoverlap 0))
    (sub : (i : ℕ) → SubDatum (walkJunctionPiece h hqf hgp cl e hoverlap i))
    (hsub0 : sub 0 = d0)
    (htot : ∀ y : ChartInterval (datumPiece d0).lo (datumPiece d0).hi,
      transports (datumPiece d0)
        (chainTail (fun i => datumPiece (sub i)) 0 n) y) :
    ∀ x : ChartInterval (datumPiece (sub 0)).lo (datumPiece (sub 0)).hi,
      ∃ y : OChartTransitionDomain (walkChart h hqf hgp cl e (0 + n + 1))
          (walkChart h hqf hgp cl e 0),
        oChartLift (walkChart h hqf hgp cl e (0 + n + 1)) y.1 =
          oChartLift (walkChart h hqf hgp cl e 0)
            ⟨(x : ℝ), datumPiece_chartSubset h hqf hgp cl e hoverlap 0 (sub 0) x.2⟩ := by
  intro x
  have hpp : datumPiece (sub 0) = datumPiece d0 := by
    rw [hsub0]
  have htrx : transports (datumPiece (sub 0))
      (chainTail (fun i => datumPiece (sub i)) 0 n) x :=
    (transports_congr_piece (p := datumPiece (sub 0)) (p' := datumPiece d0)
      (rest := chainTail (fun i => datumPiece (sub i)) 0 n) hpp x).mpr
      (htot ((congrArg (fun m : MonoPiece => ChartInterval m.lo m.hi) hpp) ▸ x))
  rcases chain_transport_class_coordinate (ch := walkChart h hqf hgp cl e)
      (p := fun i => datumPiece (sub i))
      (hsub := fun i => datumPiece_chartSubset h hqf hgp cl e hoverlap i (sub i))
      (hsem := fun i u => datumPiece_semantics h hqf hgp cl e hoverlap i (sub i) u)
      0 n ⟨x, htrx⟩ with ⟨y, hy⟩
  exact ⟨y, hy.1⟩

/-- **Single-level arc package for a given datum.**  With datum data
`d0 sub` (`sub 0 = d0`, `x₀` in the aligned start interval, forward
totality) and the first walk class in the component of `c₀`, the arc of
THIS `sub` is injective, continuous, has OPEN range, its range lies in
the component of `c₀` and in the walk partial union
`⋃_{m < n+2} OChartTraceSet (cl (e m))`, and contains the orbit class —
the S139 package relativized to a given (e.g. nested, S140c) datum. -/
theorem alignedData_arc_openSet {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (c₀ : OSub r) (hc0 : cl (e 0) ∈ connectedComponent c₀) (n : ℕ)
    (x₀ : ChartInterval (walkJunctionPiece h hqf hgp cl e hoverlap 0).lo
      (walkJunctionPiece h hqf hgp cl e hoverlap 0).hi)
    (d0 : SubDatum (walkJunctionPiece h hqf hgp cl e hoverlap 0))
    (sub : (i : ℕ) → SubDatum (walkJunctionPiece h hqf hgp cl e hoverlap i))
    (hsub0 : sub 0 = d0)
    (hx₀mem : (x₀ : ℝ) ∈ Set.Ioo (datumPiece (sub 0)).lo (datumPiece (sub 0)).hi)
    (htot : ∀ y : ChartInterval (datumPiece d0).lo (datumPiece d0).hi,
      transports (datumPiece d0)
        (chainTail (fun i => datumPiece (sub i)) 0 n) y) :
    Function.Injective (walkAlignedArcMap h hqf hgp cl e hoverlap sub) ∧
    Continuous (walkAlignedArcMap h hqf hgp cl e hoverlap sub) ∧
    IsOpen (Set.range (walkAlignedArcMap h hqf hgp cl e hoverlap sub)) ∧
    (∀ x : ChartInterval (datumPiece (sub 0)).lo (datumPiece (sub 0)).hi,
      walkAlignedArcMap h hqf hgp cl e hoverlap sub x ∈ connectedComponent c₀) ∧
    (∀ x : ChartInterval (datumPiece (sub 0)).lo (datumPiece (sub 0)).hi,
      walkAlignedArcMap h hqf hgp cl e hoverlap sub x ∈
        ⋃ m ∈ Set.Iio (n + 2), OChartTraceSet h hqf hgp (cl (e m))) ∧
    oChartLift (walkChart h hqf hgp cl e 0)
        ⟨(x₀ : ℝ), walkJunction_subset h hqf hgp cl e hoverlap 0 x₀.2⟩ ∈
      Set.range (walkAlignedArcMap h hqf hgp cl e hoverlap sub) := by
  refine ⟨walkAlignedArcMap_injective h hqf hgp cl e hoverlap sub,
    continuous_walkAlignedArcMap h hqf hgp cl e hoverlap sub, ?_, ?_, ?_, ?_⟩
  · rw [walkAlignedArcMap_range_eq_liftCell h hqf hgp cl e hoverlap sub]
    exact isOpen_lift_cell (walkChart h hqf hgp cl e 0)
  · intro x
    have hT : walkAlignedArcMap h hqf hgp cl e hoverlap sub x ∈
        OChartTraceSet h hqf hgp (cl (e 0)) := by
      change oChartLift (walkChart h hqf hgp cl e 0)
          ⟨(x : ℝ), datumPiece_chartSubset h hqf hgp cl e hoverlap 0 (sub 0) x.2⟩ ∈
          chartTrace (walkChart h hqf hgp cl e 0)
      exact (mem_chartTrace (walkChart h hqf hgp cl e 0)
        (oChartLift (walkChart h hqf hgp cl e 0)
          ⟨(x : ℝ), datumPiece_chartSubset h hqf hgp cl e hoverlap 0 (sub 0) x.2⟩)).mpr
        (oChartLift_mem_W (walkChart h hqf hgp cl e 0)
          ⟨(x : ℝ), datumPiece_chartSubset h hqf hgp cl e hoverlap 0 (sub 0) x.2⟩)
    exact OChartTrace_subset_component c₀ (cl (e 0)) hc0 hT
  · intro x
    rcases alignedData_reaches_end h hqf hgp cl e hoverlap n d0 sub hsub0 htot x with ⟨y, hy⟩
    have htr : walkAlignedArcMap h hqf hgp cl e hoverlap sub x ∈
        chartTrace (walkChart h hqf hgp cl e (0 + n + 1)) := by
      change oChartLift (walkChart h hqf hgp cl e 0)
          ⟨(x : ℝ), datumPiece_chartSubset h hqf hgp cl e hoverlap 0 (sub 0) x.2⟩ ∈
          chartTrace (walkChart h hqf hgp cl e (0 + n + 1))
      rw [← hy]
      exact (mem_chartTrace (walkChart h hqf hgp cl e (0 + n + 1))
        (oChartLift (walkChart h hqf hgp cl e (0 + n + 1)) y.1)).mpr
        (oChartLift_mem_W (walkChart h hqf hgp cl e (0 + n + 1)) y.1)
    have hfar : walkAlignedArcMap h hqf hgp cl e hoverlap sub x ∈
        OChartTraceSet h hqf hgp (cl (e (0 + n + 1))) := by
      simpa [OChartTraceSet, chartTrace, walkChart] using htr
    exact Set.mem_iUnion₂.mpr ⟨0 + n + 1, Set.mem_Iio.mpr (by omega), hfar⟩
  · refine ⟨⟨(x₀ : ℝ), hx₀mem⟩, ?_⟩
    exact walkAlignedArcMap_at_orbitClass h hqf hgp cl e hoverlap sub x₀ hx₀mem




/-! ## S189 — nested per-length reindexing (the first overlap-and-reindex
lemma of the `Uₙ` assembly)

Corollaries of the S140b change-of-chart (`walkAligned_changeChart_of_nested`):
for two aligned datums of the same walk with NESTED start intervals, the
consecutive-length change of chart at an inner-range class is the REAL
IDENTITY reindexing — `walkAligned_changeChart_reindex_val` — hence
real-monotone in one direction (`walkAligned_changeChart_monotone`,
`MonotoneDirectionOn` with the start coordinate).  These are the
coordinate-compatibility conjuncts of the S140 T2 increasing family at a
single pair of consecutive lengths; the `Uₙ` assembly chains them over
consecutive lengths (the nesting hypothesis `hI` at each level being the
S140c-chosen nested sub-data).  Everything here is verified (no axioms,
no `sorry`).
-/
/-- **S189 — nested per-length reindexing is the real identity (the
overlap-and-reindex lemma).**  For two aligned datums of the same walk
with NESTED start intervals (`hI : (a',b') ⊆ (a,b)`), the change of
chart between the length-`n+1` arc chart `φ'` and the length-`n` arc
chart `φ` at an inner-range class is the real reindexing: the `φ`-
coordinate (read back through `φ.symm`) equals the `φ'`-coordinate
itself (`(u : ℝ)`) — the two cell coordinates of the same class agree as
real parameters.  This is the consecutive-length compatibility core of
the `Uₙ` assembly (S140 T2 coordinate-compatibility conjunct at one pair
of consecutive lengths; proof obligation: `walkAligned_changeChart_of_nested`,
S140b). -/
lemma walkAligned_changeChart_reindex_val {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (sub sub' : (i : ℕ) → SubDatum (walkJunctionPiece h hqf hgp cl e hoverlap i))
    (hI : Set.Ioo (datumPiece (sub' 0)).lo (datumPiece (sub' 0)).hi ⊆
      Set.Ioo (datumPiece (sub 0)).lo (datumPiece (sub 0)).hi)
    (u : ChartInterval (datumPiece (sub' 0)).lo (datumPiece (sub' 0)).hi) :
    (((walkAlignedArcMap_homeo_range h hqf hgp cl e hoverlap sub).symm
        ⟨walkAlignedArcMap h hqf hgp cl e hoverlap sub' u,
          walkAlignedArcMap_nested_range_mem h hqf hgp cl e hoverlap sub sub' hI u⟩
        : ChartInterval (datumPiece (sub 0)).lo (datumPiece (sub 0)).hi) : ℝ)
      = (u : ℝ) := by
  have h := walkAligned_changeChart_of_nested h hqf hgp cl e hoverlap sub sub' hI u
  rw [h]

/-- **The consecutive-length change-of-chart is real-monotone (the
monotone coordinate-compatibility conjunct).**  With the inner start
coordinate `u ↦ (u : ℝ)` as coordinate, the outer-chart coordinate of an
inner class is monotone in one direction (increasing) — the two per-
length coordinates order the same classes identically on the nested
overlap. -/
lemma walkAligned_changeChart_monotone {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (sub sub' : (i : ℕ) → SubDatum (walkJunctionPiece h hqf hgp cl e hoverlap i))
    (hI : Set.Ioo (datumPiece (sub' 0)).lo (datumPiece (sub' 0)).hi ⊆
      Set.Ioo (datumPiece (sub 0)).lo (datumPiece (sub 0)).hi) :
    MonotoneDirectionOn
      (fun u : ChartInterval (datumPiece (sub' 0)).lo (datumPiece (sub' 0)).hi => (u : ℝ))
      (fun u : ChartInterval (datumPiece (sub' 0)).lo (datumPiece (sub' 0)).hi =>
        (((walkAlignedArcMap_homeo_range h hqf hgp cl e hoverlap sub).symm
          ⟨walkAlignedArcMap h hqf hgp cl e hoverlap sub' u,
            walkAlignedArcMap_nested_range_mem h hqf hgp cl e hoverlap sub sub' hI u⟩
          : ChartInterval (datumPiece (sub 0)).lo (datumPiece (sub 0)).hi) : ℝ)) := by
  left
  intro a b hab
  change (((walkAlignedArcMap_homeo_range h hqf hgp cl e hoverlap sub).symm
        ⟨walkAlignedArcMap h hqf hgp cl e hoverlap sub' a,
          walkAlignedArcMap_nested_range_mem h hqf hgp cl e hoverlap sub sub' hI a⟩
        : ChartInterval (datumPiece (sub 0)).lo (datumPiece (sub 0)).hi) : ℝ) <
      (((walkAlignedArcMap_homeo_range h hqf hgp cl e hoverlap sub).symm
        ⟨walkAlignedArcMap h hqf hgp cl e hoverlap sub' b,
          walkAlignedArcMap_nested_range_mem h hqf hgp cl e hoverlap sub sub' hI b⟩
        : ChartInterval (datumPiece (sub 0)).lo (datumPiece (sub 0)).hi) : ℝ)
  rw [walkAligned_changeChart_reindex_val h hqf hgp cl e hoverlap sub sub' hI a,
      walkAligned_changeChart_reindex_val h hqf hgp cl e hoverlap sub sub' hI b]
  exact hab
end LeanEval.KnotTheory.Quadrisecant
