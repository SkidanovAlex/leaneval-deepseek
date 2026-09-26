import Mathlib
import Submission.IntervalChainU
import Submission.ChainTransport
import Submission.ComponentWalk

open LeanEval.KnotTheory.Quadrisecant
open Set
open scoped Real Topology unitInterval

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

set_option maxHeartbeats 800000

/-!
# Milestone-2 (iv) step 6, brick (b) — the interval-charted covering of
the component: finite-chain prefix transport over the walk, packaged
(interval-charted `Uₙ` input interface)

`ChainTransport.lean` (S111) proved the pure iterated-transport engine
over chains of aligned monotone pieces (`chain_transport_monotone_direction`,
`chain_transport_injective`); `IntervalChainU.lean` (S119) proved the FULL
finite-chain identification (`chain_transport_class_coordinate`: the
transported value over the pieces `p k, …, p (k+n)` is the
`ch (k+n+1)`-coordinate of the same class as the `ch k`-parameter);
`IntervalChartU.lean` (S116) proved the per-junction hinge
(`oChart_trace_overlap_monotoneNbhd`, `oChartJunctionMonoPiece`) over the
chart-trace overlap walk of `ComponentWalk.lean` (S115).  This module is
the packaged INPUT INTERFACE of the interval-chain exhaustion: it

1. **packages the engine** — `chain_prefix_transport_summary`: over a
   prefix `p k :: chainTail p k n` of an aligned piece chain (hypotheses
   `hsub`, `hsem` of S119) the chain value is monotone in one direction
   with respect to the starting parameter coordinate, injective, and is
   the class-coordinate transport (the genuine `ch (k+n+1)`-coordinate of
   the same trisecant class as the starting parameter) — the three
   conjuncts the exhaustion reads off from each prefix;
2. **instantiates the engine on the walk data** (the bridge from the S115
   component walk to the S119 hypotheses): given the walk enumeration
   `cl : ℕ → OSub r`, `e : ℕ → ℕ` with consecutive trace overlaps
   (`hoverlap`), it builds the walk charts
   `walkChart h hqf hgp cl e i = oChartAtClass … (cl (e i))`, the overlap
   classes `walkOverlapClass` (with their trace memberships
   `walkOverlapClass_mem_left/right`), the monotone junction
   neighbourhoods `walkJunctionNbhd` (S116 hinge choices), the junction
   pieces `walkJunctionPiece` (`MonoPiece`s), and proves the two
   hypothesis families of S119 for them: `walkJunction_subset` (each
   piece interval embeds into the left chart interval) and
   `walkJunction_semantics` (each piece parameter's class stays in the
   next trace and the piece value is the next chart's coordinate of the
   same class);
3. **combines them** — `walk_prefix_summary`: from the S115 walk overlap
   data alone, for every prefix of `n+1` junctions starting at walk
   position `0`, the chain value over the prefix is monotone in one
   direction with respect to the start parameter, injective, and equals
   the `ch (n+1)`-coordinate of the same class (the `k = 0` instance the
   interval-charted `Uₙ` covering will consume).

The next slice (recorded in the ROADMAP): the ALIGNMENT (shrinking)
construction — choosing the junction pieces so that every transport lands
in the next piece over the whole finite stretch (the S106 backward
shrinking from the last junction) — and then the covering lemma
(`Eₙ`/partial-union ⊆ interval-charted open `Uₙ` with the monotone
injective coordinate), built on this interface.  Everything here is
elementary and verified (no axioms, no `sorry`).
-/

/-- **Packaged finite-chain prefix transport.**  Over a prefix
`p k :: chainTail p k n` of an aligned piece chain (charts `ch`, pieces
`p`, interval embeddings `hsub` and class-coordinate semantics `hsem` —
the S119 hypotheses), the chain value is monotone in one direction with
respect to the starting parameter coordinate, injective, and is the class
coordinate transport: for every start parameter whose transport through
the tail exists, the transported value is the `ch (k+n+1)`-coordinate of
the same class as the `ch k`-parameter.  (Monotonicity/injectivity: S111;
class-coordinate identification: S119; packaged here for the exhaustion.) -/
theorem chain_prefix_transport_summary {r : ℝ → Space} {c : ℕ → OSub r}
    (ch : (i : ℕ) → OSub1Chart r (c i)) (p : ℕ → MonoPiece)
    (hsub : ∀ i, Set.Ioo (p i).lo (p i).hi ⊆ Set.Ioo (ch i).lo (ch i).hi)
    (hsem : ∀ i (u : ChartInterval (p i).lo (p i).hi),
        oChartLift (ch i) ⟨(u : ℝ), hsub i u.2⟩ ∈ chartTrace (ch (i + 1)) ∧
        ∃ y : OChartTransitionDomain (ch (i + 1)) (ch i),
          oChartLift (ch (i + 1)) y.1 = oChartLift (ch i) ⟨(u : ℝ), hsub i u.2⟩ ∧
          (y.1 : ℝ) = (p i).τ u)
    (k n : ℕ) :
    MonotoneDirectionOn
        (fun x : ChainDomain (p k :: chainTail p k n) => (x.1 : ℝ))
        (fun x : ChainDomain (p k :: chainTail p k n) =>
          chainValue (p k :: chainTail p k n) x) ∧
    Function.Injective
        (fun x : ChainDomain (p k :: chainTail p k n) =>
          chainValue (p k :: chainTail p k n) x) ∧
    ∀ x : {x : ChartInterval (p k).lo (p k).hi // transports (p k) (chainTail p k n) x},
      ∃ y : OChartTransitionDomain (ch (k + n + 1)) (ch k),
        oChartLift (ch (k + n + 1)) y.1 =
          oChartLift (ch k) ⟨(x.1 : ℝ), hsub k x.1.2⟩ ∧
        (y.1 : ℝ) = chainValue (p k :: chainTail p k n) ⟨x.1, x.2⟩ := by
  constructor
  · have hmono : MonotoneDirectionOn (chainCoord (p k :: chainTail p k n))
        (chainValue (p k :: chainTail p k n)) :=
      chain_transport_monotone_direction (p k :: chainTail p k n)
    change MonotoneDirectionOn
        (fun x : ChainDomain (p k :: chainTail p k n) => (x.1 : ℝ))
        (chainValue (p k :: chainTail p k n)) at hmono
    exact hmono
  · constructor
    · exact chain_transport_injective (p k :: chainTail p k n)
    · intro x
      exact chain_transport_class_coordinate ch p hsub hsem k n x

/-! ## 2. The walk instantiation (S115 walk data → S119 hypotheses) -/

/-- The walk chart at position `i`: the interval chart of `O` centred at
the walk class `cl (e i)`. -/
def walkChart {r : ℝ → Space} (h : IsSmoothKnot r) (hqf : QuadrisecantFree r)
    (hgp : TorusGeneralPositionTransverse r) (cl : ℕ → OSub r) (e : ℕ → ℕ) (i : ℕ) :
    OSub1Chart r (cl (e i)) :=
  oChartAtClass h hqf hgp (cl (e i))

/-- The overlap class at walk junction `i`: an element of the intersection
of the traces of the walk charts `i` and `i+1` (chosen from the walk
overlap data `hoverlap`). -/
noncomputable def walkOverlapClass {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty) (i : ℕ) : OSub r :=
  Classical.choose (hoverlap i)

/-- The overlap class at walk junction `i` lies in the left trace
(`chartTrace (walkChart … i)`). -/
lemma walkOverlapClass_mem_left {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty) (i : ℕ) :
    walkOverlapClass h hqf hgp cl e hoverlap i ∈ chartTrace (walkChart h hqf hgp cl e i) := by
  have hmem := (Classical.choose_spec (hoverlap i)).1
  simpa [walkOverlapClass, walkChart, OChartTraceSet, chartTrace] using hmem

/-- The overlap class at walk junction `i` lies in the right trace
(`chartTrace (walkChart … (i+1))`). -/
lemma walkOverlapClass_mem_right {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty) (i : ℕ) :
    walkOverlapClass h hqf hgp cl e hoverlap i ∈ chartTrace (walkChart h hqf hgp cl e (i + 1)) := by
  have hmem := (Classical.choose_spec (hoverlap i)).2
  simpa [walkOverlapClass, walkChart, OChartTraceSet, chartTrace] using hmem

/-- The monotone junction neighbourhood at walk junction `i`: the S116
hinge instance (`oChart_trace_overlap_monotoneNbhd`) at the overlap class
between the walk charts `i` and `i+1`. -/
noncomputable def walkJunctionNbhd {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty) (i : ℕ) :
    OChartMonotoneNbhd (walkChart h hqf hgp cl e i) (walkChart h hqf hgp cl e (i + 1))
      (oChartTraceOverlapParam (walkChart h hqf hgp cl e i) (walkChart h hqf hgp cl e (i + 1))
        (walkOverlapClass h hqf hgp cl e hoverlap i)
        (walkOverlapClass_mem_left h hqf hgp cl e hoverlap i)
        (walkOverlapClass_mem_right h hqf hgp cl e hoverlap i)) :=
  Classical.choose (oChart_trace_overlap_monotoneNbhd
    (walkChart h hqf hgp cl e i) (walkChart h hqf hgp cl e (i + 1))
    (walkOverlapClass h hqf hgp cl e hoverlap i)
    (walkOverlapClass_mem_left h hqf hgp cl e hoverlap i)
    (walkOverlapClass_mem_right h hqf hgp cl e hoverlap i))

/-- The monotone junction piece at walk junction `i`: the S116 MonoPiece
instance (coordinate map `oChartTransitionOnInterval` of the junction
neighbourhood, monotone in one direction). -/
noncomputable def walkJunctionPiece {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty) (i : ℕ) : MonoPiece :=
  oChartJunctionMonoPiece (walkChart h hqf hgp cl e i) (walkChart h hqf hgp cl e (i + 1))
    (walkOverlapClass h hqf hgp cl e hoverlap i)
    (walkOverlapClass_mem_left h hqf hgp cl e hoverlap i)
    (walkOverlapClass_mem_right h hqf hgp cl e hoverlap i)
    (walkJunctionNbhd h hqf hgp cl e hoverlap i)

/-- **Walk `hsub` instance:** the walk junction piece interval embeds into
the left walk chart interval (the S119 hypothesis `hsub` at `i`, from the
neighbourhood's own subset). -/
lemma walkJunction_subset {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty) (i : ℕ) :
    Set.Ioo (walkJunctionPiece h hqf hgp cl e hoverlap i).lo
      (walkJunctionPiece h hqf hgp cl e hoverlap i).hi ⊆
    Set.Ioo (walkChart h hqf hgp cl e i).lo (walkChart h hqf hgp cl e i).hi := by
  change Set.Ioo (walkJunctionNbhd h hqf hgp cl e hoverlap i).lo
      (walkJunctionNbhd h hqf hgp cl e hoverlap i).hi ⊆
    Set.Ioo (walkChart h hqf hgp cl e i).lo (walkChart h hqf hgp cl e i).hi
  exact (walkJunctionNbhd h hqf hgp cl e hoverlap i).subset

/-- **Walk `hsem` instance:** every walk junction piece parameter describes
a trisecant class lying in the next walk trace, and the piece value is the
next chart's coordinate of the same class (the S119 hypothesis `hsem` at
`i` — the S116 hinge conjuncts on the walk data). -/
lemma walkJunction_semantics {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty) (i : ℕ)
    (u : ChartInterval (walkJunctionPiece h hqf hgp cl e hoverlap i).lo
      (walkJunctionPiece h hqf hgp cl e hoverlap i).hi) :
    oChartLift (walkChart h hqf hgp cl e i)
        ⟨(u : ℝ), walkJunction_subset h hqf hgp cl e hoverlap i u.2⟩ ∈
        chartTrace (walkChart h hqf hgp cl e (i + 1)) ∧
    ∃ y : OChartTransitionDomain (walkChart h hqf hgp cl e (i + 1))
        (walkChart h hqf hgp cl e i),
      oChartLift (walkChart h hqf hgp cl e (i + 1)) y.1 =
        oChartLift (walkChart h hqf hgp cl e i)
          ⟨(u : ℝ), walkJunction_subset h hqf hgp cl e hoverlap i u.2⟩ ∧
      (y.1 : ℝ) = (walkJunctionPiece h hqf hgp cl e hoverlap i).τ u := by
  have hspec := Classical.choose_spec (oChart_trace_overlap_monotoneNbhd
    (walkChart h hqf hgp cl e i) (walkChart h hqf hgp cl e (i + 1))
    (walkOverlapClass h hqf hgp cl e hoverlap i)
    (walkOverlapClass_mem_left h hqf hgp cl e hoverlap i)
    (walkOverlapClass_mem_right h hqf hgp cl e hoverlap i))
  change ∀ u : ChartInterval (walkJunctionNbhd h hqf hgp cl e hoverlap i).lo
      (walkJunctionNbhd h hqf hgp cl e hoverlap i).hi,
      oChartLift (walkChart h hqf hgp cl e i)
          ⟨(u : ℝ), (walkJunctionNbhd h hqf hgp cl e hoverlap i).subset u.2⟩ ∈
          chartTrace (walkChart h hqf hgp cl e (i + 1)) ∧
      ∃ y : OChartTransitionDomain (walkChart h hqf hgp cl e (i + 1))
          (walkChart h hqf hgp cl e i),
        oChartLift (walkChart h hqf hgp cl e (i + 1)) y.1 =
          oChartLift (walkChart h hqf hgp cl e i)
            ⟨(u : ℝ), (walkJunctionNbhd h hqf hgp cl e hoverlap i).subset u.2⟩ ∧
        (y.1 : ℝ) = oChartTransitionOnInterval (walkChart h hqf hgp cl e i)
            (walkChart h hqf hgp cl e (i + 1))
            (walkJunctionNbhd h hqf hgp cl e hoverlap i).subset
            (walkJunctionNbhd h hqf hgp cl e hoverlap i).dom u at hspec
  have hinst := hspec u
  constructor
  · rcases hinst with ⟨hin, y, hy⟩
    simpa [walkJunctionPiece, oChartJunctionMonoPiece] using hin
  · rcases hinst with ⟨hin, y, hy⟩
    refine ⟨y, hy.1, ?_⟩
    simpa [walkJunctionPiece, oChartJunctionMonoPiece] using hy.2

/-! ## 3. The walk-prefix summary (S115 walk data → S111/S119 output) -/

/-- **Walk-prefix transport summary.**  From the walk overlap data alone
(charts `walkChart`, pieces `walkJunctionPiece` at every junction), for
every prefix of `n+1` junctions starting at walk position `0`, the chain
value over the prefix is monotone in one direction with respect to the
starting parameter coordinate, injective, and is the class-coordinate
transport: every start parameter whose transport through the prefix
exists is sent to the `ch (n+1)`-coordinate of the same trisecant class
as its `ch 0`-parameter (the `k = 0` instance of
`chain_prefix_transport_summary` instantiated with the walk data — the
interval-charted `Uₙ` covering consumes exactly this shape). -/
theorem walk_prefix_summary {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty) (n : ℕ) :
    MonotoneDirectionOn
        (fun x : ChainDomain (walkJunctionPiece h hqf hgp cl e hoverlap 0 ::
            chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) => (x.1 : ℝ))
        (fun x : ChainDomain (walkJunctionPiece h hqf hgp cl e hoverlap 0 ::
            chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) =>
          chainValue (walkJunctionPiece h hqf hgp cl e hoverlap 0 ::
            chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) x) ∧
    Function.Injective
        (fun x : ChainDomain (walkJunctionPiece h hqf hgp cl e hoverlap 0 ::
            chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) =>
          chainValue (walkJunctionPiece h hqf hgp cl e hoverlap 0 ::
            chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) x) ∧
    ∀ x : {x : ChartInterval (walkJunctionPiece h hqf hgp cl e hoverlap 0).lo
            (walkJunctionPiece h hqf hgp cl e hoverlap 0).hi //
            transports (walkJunctionPiece h hqf hgp cl e hoverlap 0)
              (chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) x},
      ∃ y : OChartTransitionDomain (walkChart h hqf hgp cl e (0 + n + 1))
            (walkChart h hqf hgp cl e 0),
        oChartLift (walkChart h hqf hgp cl e (0 + n + 1)) y.1 =
          oChartLift (walkChart h hqf hgp cl e 0)
            ⟨(x.1 : ℝ), walkJunction_subset h hqf hgp cl e hoverlap 0 x.1.2⟩ ∧
        (y.1 : ℝ) = chainValue (walkJunctionPiece h hqf hgp cl e hoverlap 0 ::
            chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) ⟨x.1, x.2⟩ := by
  exact chain_prefix_transport_summary
    (ch := walkChart h hqf hgp cl e)
    (p := walkJunctionPiece h hqf hgp cl e hoverlap)
    (hsub := fun i => walkJunction_subset h hqf hgp cl e hoverlap i)
    (hsem := fun i u => walkJunction_semantics h hqf hgp cl e hoverlap i u) 0 n

end LeanEval.KnotTheory.Quadrisecant
