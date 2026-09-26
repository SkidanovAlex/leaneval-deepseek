import Mathlib
import Submission.ChartTracePath
import Submission.OChartGlue
import Submission.ChainTransport

open LeanEval.KnotTheory.Quadrisecant
open Set
open scoped Real Topology unitInterval

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

set_option maxHeartbeats 800000

/-!
# Interval-coordinate charts over overlapping traces: the monotone
overlap hinge of the interval-chain glueing (S116)

With the component chart-trace walk in hand (`ComponentWalk.component_trace_walk`,
S115: an overlap walk of the S107 chart-trace cover of a component, whose
partial unions are path-connected open sets exhausting the component),
the next brick of the interval-chain-ordering construction is the glueing
of the per-trace interval coordinates (`chartTraceHomeo`, S114)
monotonically along the walk (S102–S111 machinery).  This module states
and proves the HINGE of that glueing — the local statement that makes the
inductive construction possible:

**`oChart_trace_overlap_monotoneNbhd`**: for two interval charts of the
trisecant set whose traces overlap at a class `z`, there is an
`OChartMonotoneNbhd` (S102) at the `ch₁`-coordinate of `z` — an open
interval piece of the first chart's parameter interval around that
coordinate — on which the real coordinate relabelling to the second chart
(`oChartTransitionOnInterval`) is strictly monotone in one direction
(`nb.monotone`, the S104 `MonotoneOnPiece`-style disjunction), continuous
(`continuous_oChartTransitionOnInterval`) and injective
(`injective_oChartTransitionOnInterval`), and moreover:

- every parameter of the piece describes a trisecant class lying in BOTH
  traces (`nb.dom` gives the `ch₂`-trace membership, packaged as
  `mem_chartTrace`), and
- the relabelling value is the `ch₂`-coordinate of the SAME class as the
  corresponding `ch₁`-parameter (`oChartNbhd_piece_coordinate`, S102) —
  so the two interval coordinates are order-compatible on the overlap
  piece: they agree up to a strictly monotone relabelling, in either
  direction, of the same classes.

Supporting content: `oChartTraceOverlapParam` (the `ch₁`-coordinate of an
overlap class, packaged into the transition domain, with its lift lemma),
`mem_chartTrace`, and the `MonoPiece` builder
`oChartJunctionMonoPiece` (turning a hinge neighbourhood into the
`ChainTransport.MonoPiece` datum of the S111 finite-chain engine, so
`chain_transport_monotone_direction`/`chain_transport_injective` apply to
chains of walk-adjacent traces).

The immediate use: applied at each junction of the component walk
(S115), the hinge gives the per-junction monotone piece; the S111 engine
then transports a starting chart's coordinate monotonically and
injectively along any finite stretch of the walk over which the pieces
align, and the class-coordinate content of the hinge identifies the
transported value with the final chart's coordinate of the same class —
the monotone interval-charted open sets `Uₙ` of the exhaustion
construction are built by induction along the walk.

Everything here is elementary and verified (no axioms, no `sorry`).
-/

/-- Membership in a chart trace, unfolded to the trace set `W`. -/
lemma mem_chartTrace {r : ℝ → Space} {c₀ : OSub r} (ch : OSub1Chart r c₀) (y : OSub r) :
    y ∈ chartTrace ch ↔ (y : OpenMobius) ∈ ch.W := by
  rfl

/-- A trace membership, read at the band level. -/
private lemma mem_trace_W {r : ℝ → Space} {c₀ : OSub r} (ch : OSub1Chart r c₀) {z : OSub r}
    (hz : z ∈ chartTrace ch) : (z : OpenMobius) ∈ ch.W :=
  (mem_chartTrace ch z).mp hz

/-- The `ch₁`-coordinate of a class `z` lying in the overlap of the traces
of `ch₁` and `ch₂`, packaged into the transition domain `ch₁ → ch₂`. -/
noncomputable def oChartTraceOverlapParam {r : ℝ → Space} {c₁₀ c₂₀ : OSub r}
    (ch₁ : OSub1Chart r c₁₀) (ch₂ : OSub1Chart r c₂₀) (z : OSub r)
    (hz₁ : z ∈ chartTrace ch₁) (hz₂ : z ∈ chartTrace ch₂) :
    OChartTransitionDomain ch₁ ch₂ :=
  Classical.choose (exists_oChartTransitionParam_of_mem_both ch₁ ch₂ z
    (mem_trace_W ch₁ hz₁) (mem_trace_W ch₂ hz₂))

/-- The overlap parameter describes the overlap class `z`. -/
lemma oChartTraceOverlapParam_lift {r : ℝ → Space} {c₁₀ c₂₀ : OSub r}
    (ch₁ : OSub1Chart r c₁₀) (ch₂ : OSub1Chart r c₂₀) (z : OSub r)
    (hz₁ : z ∈ chartTrace ch₁) (hz₂ : z ∈ chartTrace ch₂) :
    oChartLift ch₁ (oChartTraceOverlapParam ch₁ ch₂ z hz₁ hz₂).1 = z := by
  exact Classical.choose_spec (exists_oChartTransitionParam_of_mem_both ch₁ ch₂ z
    (mem_trace_W ch₁ hz₁) (mem_trace_W ch₂ hz₂))

/-- **The monotone-coordinate overlap hinge.**  For two interval charts of
the trisecant set whose traces overlap at a class `z`, there is an
`OChartMonotoneNbhd` (S102) at the `ch₁`-coordinate of `z`: an open
interval piece of the first chart's parameter interval around that
coordinate on which the real coordinate relabelling to the second chart is
strictly monotone in one direction, continuous and injective, and on which
every parameter describes a class lying in both traces whose `ch₂`-
coordinate is the relabelling value (`oChartNbhd_piece_coordinate`): the
two interval coordinates are order-compatible on the overlap piece. -/
theorem oChart_trace_overlap_monotoneNbhd {r : ℝ → Space} {c₁₀ c₂₀ : OSub r}
    (ch₁ : OSub1Chart r c₁₀) (ch₂ : OSub1Chart r c₂₀) (z : OSub r)
    (hz₁ : z ∈ chartTrace ch₁) (hz₂ : z ∈ chartTrace ch₂) :
    ∃ nb : OChartMonotoneNbhd ch₁ ch₂ (oChartTraceOverlapParam ch₁ ch₂ z hz₁ hz₂),
      ∀ u : ChartInterval nb.lo nb.hi,
        oChartLift ch₁ ⟨(u : ℝ), nb.subset u.2⟩ ∈ chartTrace ch₂ ∧
        ∃ y : OChartTransitionDomain ch₂ ch₁,
          oChartLift ch₂ y.1 = oChartLift ch₁ ⟨(u : ℝ), nb.subset u.2⟩ ∧
          (((y : OChartTransitionDomain ch₂ ch₁) : ChartInterval ch₂.lo ch₂.hi) : ℝ) =
            oChartTransitionOnInterval ch₁ ch₂ nb.subset nb.dom u := by
  let x₀ : OChartTransitionDomain ch₁ ch₂ :=
    oChartTraceOverlapParam ch₁ ch₂ z hz₁ hz₂
  rcases exists_oChartMonotoneNbhd ch₁ ch₂ x₀ with ⟨nb⟩
  refine ⟨nb, ?_⟩
  intro u
  have hdom : (oChartLift ch₁ ⟨(u : ℝ), nb.subset u.2⟩ : OpenMobius) ∈ ch₂.W :=
    nb.dom ⟨(u : ℝ), nb.subset u.2⟩ u.2
  constructor
  · exact (mem_chartTrace ch₂ _).mpr hdom
  · exact oChartNbhd_piece_coordinate ch₁ ch₂ x₀ nb u

/-- **The monotone piece at a trace-overlap junction.**  The hinge
neighbourhood at an overlap class, turned into the `MonoPiece` datum of
the S111 finite-chain transport engine (its coordinate map is the S102
interval-piece transition, monotone in one direction by `nb.monotone`). -/
noncomputable def oChartJunctionMonoPiece {r : ℝ → Space} {c₁₀ c₂₀ : OSub r}
    (ch₁ : OSub1Chart r c₁₀) (ch₂ : OSub1Chart r c₂₀) (z : OSub r)
    (hz₁ : z ∈ chartTrace ch₁) (hz₂ : z ∈ chartTrace ch₂)
    (nb : OChartMonotoneNbhd ch₁ ch₂ (oChartTraceOverlapParam ch₁ ch₂ z hz₁ hz₂)) :
    MonoPiece where
  lo := nb.lo
  hi := nb.hi
  τ := oChartTransitionOnInterval ch₁ ch₂ nb.subset nb.dom
  hmono := nb.monotone

/-- The coordinate map of the junction piece is monotone in one direction
(the S104 predicate form). -/
lemma oChartJunctionMonoPiece_monotone {r : ℝ → Space} {c₁₀ c₂₀ : OSub r}
    (ch₁ : OSub1Chart r c₁₀) (ch₂ : OSub1Chart r c₂₀) (z : OSub r)
    (hz₁ : z ∈ chartTrace ch₁) (hz₂ : z ∈ chartTrace ch₂)
    (nb : OChartMonotoneNbhd ch₁ ch₂ (oChartTraceOverlapParam ch₁ ch₂ z hz₁ hz₂)) :
    MonotoneOnPiece (oChartJunctionMonoPiece ch₁ ch₂ z hz₁ hz₂ nb).τ :=
  (oChartJunctionMonoPiece ch₁ ch₂ z hz₁ hz₂ nb).hmono

end LeanEval.KnotTheory.Quadrisecant
