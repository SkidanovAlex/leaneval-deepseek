import Mathlib
import Submission.PrefixArcChart

open LeanEval.KnotTheory.Quadrisecant
open Set
open scoped Real Topology

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

noncomputable section
namespace LeanEval.KnotTheory.Quadrisecant

/-!
# S184 — trace-overlap local arcs (module Submission/TraceOverlap.lean)

The first lemma of the O-side/walk instantiation of the chain-overlap
hypothesis (ROADMAP S183 NEXT item (i)).  The trisecant-set chart traces
(`chartTrace ch` of an `OSub1Chart`, each homeomorphic to an open real
interval via the chart homeo) overlap in open sets of the class space; the
CONTENT of every "the overlap is connected" statement is that overlap
components are open arcs, and this module proves the local half:

- **`traceOverlap_localArc`** — every class `c` lying in the traces of
  two interval charts `ch₀ ch₁` carries an open arc: an open interval-
  shaped set `V` (open in `OSub r`) inside the intersection
  `chartTrace ch₀ ∩ chartTrace ch₁`, homeomorphic to `ChartInterval lo
  hi`.  `V` is the chart-lift image of an `OChartMonotoneNbhd` cell
  (OChartGlue S98) around the parameter of `c` — an open interval of
  `ch₀`-coordinates all inside the transition domain `ch₀ → ch₁` on
  which the coordinate relabelling is strictly monotone.  Proof: the
  parameter `t₀ = ch₀.homeo.symm ⟨c,…⟩`; the monotone nbhd `nb`;
  `V := range (u ↦ oChartLift ch₀ ⟨(u : ℝ), nb.subset u.2⟩)`; openness
  (`f` is the composition of the open cell embedding
  `isOpenMap_paramEmbedding` and the open chart lift
  `isOpenMap_oChartLift`, so its range is open), the trace-subset
  clauses (lift stays in `ch₀.W`; `nb.dom` puts it in `ch₁.W`), and the
  homeomorphism `ChartInterval nb.lo nb.hi ≃ₜ {y // y ∈ V}` via
  `homeo_range_of_continuous_injective_isOpenMap` (continuity:
  `continuous_oChartLift`; injectivity: `oChartLift_injective` S100;
  open map: the composition above).

STATUS / honest note (recorded per the S106 policy): this gives the LOCAL
arc structure of trace overlaps.  The full prefix-overlap connectivity
hypothesis of S183's finite-chain engine
(`ConnectedSpace {x // x ∈ P'_k ∩ T (k+1)}`) is NOT yet derivable from
the walk data: the walk (`component_trace_walk`, S115) guarantees only
NONEMPTY successive trace intersections (`hoverlap`), and without the
interval/circle dichotomy of the component one cannot rule out trace
overlaps with several components (a wrapping trace can touch a prefix in
two places).  The components of the trisecant-set component C are still
to be classified (the dichotomy); the prefix-overlap connectivity must be
supplied by the interval-chain ordering machinery of the sweep (S139
aligned arc charts / S147-T), i.e. by establishing that the walk advances
monotonically along a non-wrapping arc — this is the ordering slice the
S183 engine waits for.  Everything here is verified (no axioms, no
`sorry`).
-/
/-- **S184 — the trace-overlap local arc**: every class `c` lying in the
traces of two interval charts `ch₀ ch₁` carries an open arc (open
interval-shaped set `V`, open in `OSub r`) inside the intersection
`chartTrace ch₀ ∩ chartTrace ch₁`, homeomorphic to an open real interval
`ChartInterval lo hi`.  `V` is the chart-lift image of the monotone cell
around the parameter of `c` (`OChartMonotoneNbhd`, OChartGlue S98) — an
open interval of `ch₀`-coordinates on which the transition to `ch₁` is
monotone.  This is the local content of every overlap-connectivity
statement in the walk geometry: connected overlap components are unions
of such open arcs, and the component of a shared class is itself an open
arc of each trace. -/
theorem traceOverlap_localArc {r : ℝ → Space} {c₀ c₁ : OSub r}
    (ch₀ : OSub1Chart r c₀) (ch₁ : OSub1Chart r c₁)
    (c : OSub r) (hc₀ : c ∈ chartTrace ch₀) (hc₁ : c ∈ chartTrace ch₁) :
    ∃ (lo hi : ℝ) (V : Set (OSub r)),
      c ∈ V ∧ IsOpen V ∧ V ⊆ chartTrace ch₀ ∩ chartTrace ch₁ ∧
      Nonempty (V ≃ₜ ChartInterval lo hi) := by
  classical
  let t₀ : ChartInterval ch₀.lo ch₀.hi := ch₀.homeo.symm ⟨c, by simpa [chartTrace] using hc₀⟩
  have hc₀_param : oChartLift ch₀ t₀ = c := by
    dsimp [t₀]
    exact oChartLift_eq_of_homeo ch₀ ⟨c, by simpa [chartTrace] using hc₀⟩
  let x₀ : OChartTransitionDomain ch₀ ch₁ := ⟨t₀, by
    have hc₁W : (c : OpenMobius) ∈ ch₁.W := by simpa [chartTrace] using hc₁
    simpa [hc₀_param] using hc₁W⟩
  rcases (exists_oChartMonotoneNbhd ch₀ ch₁ x₀) with ⟨nb⟩
  let f : ChartInterval nb.lo nb.hi → OSub r := fun u =>
    oChartLift ch₀ ⟨(u : ℝ), nb.subset u.2⟩
  let V : Set (OSub r) := Set.range f
  refine ⟨nb.lo, nb.hi, V, ?_, ?_, ?_, ?_⟩
  · -- c ∈ V
    have hx₀mem : ((x₀.1 : ChartInterval ch₀.lo ch₀.hi) : ℝ) ∈ Set.Ioo nb.lo nb.hi := nb.x₀_mem
    have ht₀cell : (t₀ : ℝ) ∈ Set.Ioo nb.lo nb.hi := by simpa [x₀] using hx₀mem
    refine ⟨⟨(t₀ : ℝ), ht₀cell⟩, ?_⟩
    dsimp [V, f]
    have hpar : (⟨((t₀ : ℝ) : ℝ), nb.subset ht₀cell⟩ : ChartInterval ch₀.lo ch₀.hi) = t₀ := by
      apply Subtype.ext
      rfl
    rw [hpar]
    exact hc₀_param
  · -- IsOpen V (f is a continuous open map, so its range is open)
    have hopenf : IsOpenMap f := by
      dsimp [f]
      change IsOpenMap ((fun t : ChartInterval ch₀.lo ch₀.hi => oChartLift ch₀ t) ∘
        (fun u : ChartInterval nb.lo nb.hi => (⟨(u : ℝ), nb.subset u.2⟩ : ChartInterval ch₀.lo ch₀.hi)))
      exact IsOpenMap.comp (isOpenMap_oChartLift ch₀)
        (isOpenMap_paramEmbedding (lo := ch₀.lo) (hi := ch₀.hi) nb.subset)
    have hVopen' : IsOpen (Set.range f) := by
      rw [← Set.image_univ]
      exact hopenf Set.univ isOpen_univ
    simpa [V] using hVopen'
  · -- V ⊆ chartTrace ch₀ ∩ chartTrace ch₁
    intro y hy
    rcases hy with ⟨u, hu⟩
    constructor
    · have hm := oChartLift_mem_W ch₀ ⟨(u : ℝ), nb.subset u.2⟩
      rw [← hu]
      simpa [chartTrace] using hm
    · have hd := nb.dom ⟨(u : ℝ), nb.subset u.2⟩ u.2
      rw [← hu]
      simpa [chartTrace] using hd
  · -- Nonempty (V ≃ₜ ChartInterval nb.lo nb.hi)
    have hcontf : Continuous f := by
      dsimp [f]
      change Continuous ((fun t : ChartInterval ch₀.lo ch₀.hi => oChartLift ch₀ t) ∘
        (fun u : ChartInterval nb.lo nb.hi => (⟨(u : ℝ), nb.subset u.2⟩ : ChartInterval ch₀.lo ch₀.hi)))
      exact Continuous.comp (continuous_oChartLift ch₀)
        (Continuous.subtype_mk continuous_subtype_val (fun u => nb.subset u.2))
    have hinf : Function.Injective f := by
      intro u v huv
      have hlift : oChartLift ch₀ ⟨(u : ℝ), nb.subset u.2⟩ = oChartLift ch₀ ⟨(v : ℝ), nb.subset v.2⟩ := by
        dsimp [f] at huv
        exact huv
      have hparam : (⟨(u : ℝ), nb.subset u.2⟩ : ChartInterval ch₀.lo ch₀.hi) = ⟨(v : ℝ), nb.subset v.2⟩ :=
        oChartLift_injective ch₀ hlift
      have hval : (u : ℝ) = (v : ℝ) :=
        congrArg (fun z : ChartInterval ch₀.lo ch₀.hi => (z : ℝ)) hparam
      apply Subtype.ext
      exact hval
    have hopenf : IsOpenMap f := by
      dsimp [f]
      change IsOpenMap ((fun t : ChartInterval ch₀.lo ch₀.hi => oChartLift ch₀ t) ∘
        (fun u : ChartInterval nb.lo nb.hi => (⟨(u : ℝ), nb.subset u.2⟩ : ChartInterval ch₀.lo ch₀.hi)))
      exact IsOpenMap.comp (isOpenMap_oChartLift ch₀)
        (isOpenMap_paramEmbedding (lo := ch₀.lo) (hi := ch₀.hi) nb.subset)
    have hhomeo : ChartInterval nb.lo nb.hi ≃ₜ {y : OSub r // y ∈ Set.range f} :=
      homeo_range_of_continuous_injective_isOpenMap f hcontf hinf hopenf
    dsimp [V]
    exact ⟨hhomeo.symm⟩
end LeanEval.KnotTheory.Quadrisecant
