import Mathlib
import ChallengeDeps
import Submission.ComponentChart
import Submission.ComponentMiddle
import Submission.ComponentIntervalSide
import Submission.Pi1Mobius
import Submission.Commons.Topology.AddCircle.circleMap_lift_advance

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedVariables false

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-!
# S253 — the pinned winding-data interfaces of the ONCE/TWICE branches
(VERIFIED, sorry-free)

The component classification (S242 interval, S249 compact circle), the
embedded-circle realization (S250/S251) and the continuous unique-middle
selection μ (S252, `componentMiddle`) reduce each winding branch to ONE
geometric measurement — the middle's real-lift advance per circuit of the
component — whose data shape this module pins down as ready-to-consume
targets, together with the pure-assembly contradictions that close each
branch once the geometry supplies the data:

1. **`no_onceWinding_advance`** (VERIFIED) — the ONCE contradiction,
   pinned in its final geometric form: if the middle selection of a
   circular component (chart `χ : AddCircle T ≃ₜ TrisecantComponent r
   c₀`, middle = `componentMiddle c₀ ∘ χ`) admitted a continuous real
   lift `mhat` advancing by HALF a knot period per circuit
   (`mhat (t + T) = mhat t + halfPeriod`), then `False`.  Proof: `mhat` is a
   lift of the genuine middle function of the class, and the class is
   `T`-periodic in `t` (`(t + T : AddCircle T) = (t : AddCircle T)`), so
   `(mhat (t + T) : AddCircle period) = (mhat t : AddCircle period)`; but the
   half-period advance says the circle value advances by
   `(halfPeriod : AddCircle period) ≠ 0` (`Pi1Mobius.halfPeriod_ne_zero_circle`).
   (Kuperberg: a once-winding component would force exactly this
   half-period advance with the sheets swapped; the formal geometry that
   DERIVES the lift `mhat` from a once-winding circular component is the
   Layer-C brick-(c) real-lift bookkeeping, recorded.)
2. **`TwiceWindingAdvancingLift`** (VERIFIED def) — the TWICE data shape
   (item (iii)): a continuous real lift `G` of the middle selection
   `componentMiddle c₀ ∘ χ` advancing a FULL knot period per circuit
   (`G (t + T) = G t + period`).  This is exactly the `G`/`hadv`/
   `hcompat` datum consumed by `no_twiceWinding_data` (S248).
3. **`no_twiceWinding_component_of_lift`** (VERIFIED) — the TWICE
   contradiction assembled from the item-(iii) datum: item (i) (`χ`, S249
   + the `Circle ≃ₜ`-to-`AddCircle` reparametrisation (4)), item (ii)
   (`componentMiddle` continuous + membership, S252) and the advancing
   lift (2) feed `no_twiceWinding_data` (S248) with no further analysis.
4. **`addCircleHomeo_of_circleHomeo`** and
   **`trisecantComponent_compactSide_addCircle`** (VERIFIED) — the
   reparametrisation bridge (item (i) in `AddCircle` form): the S249
   output `Circle ≃ₜ TrisecantComponent r c₀` composes with
   `Pi1Mobius.paramCircleHomeo : AddCircle period ≃ₜ Circle` to a chart
   `AddCircle period ≃ₜ TrisecantComponent r c₀` (circuit length
   `T = period > 0`);
5. **`componentMiddle_lift_advance`** (VERIFIED) — the middle selection on
   a circular component has an INTEGER degree: fleet L66
   (`Commons.Topology.AddCircle.circleMap_lift_advance`) instanced at the
   continuous `T`-periodic circle map `componentMiddle c₀ ∘ χ` gives a
   continuous real lift with advance `G (t + T) = G t + (k : ℝ) * period`
   for some `k : ℤ`.  This is the formal "integer lift advance" degree
   fact of the ONCE analysis (S246) and the carrier of the TWICE
   measurement (the twice-winding geometry will pin `k = 1`, giving
   `TwiceWindingAdvancingLift`).

STATUS after S253: both winding branches are pure assembly away from their
geometric measurements — ONCE needs the half-period advancing lift `mhat`
derived from a once-winding component; TWICE needs the full-period
advancing lift `G` (`TwiceWindingAdvancingLift`) derived from a
twice-winding component.  Both derivations are the Layer-C brick-(c)
real-lift bookkeeping on the ordered double cover (the component's winding
parity `lift_loop_end_even_or_odd`/`lift_from_swap_ends_swapped`,
ComponentPath) — recorded, not yet formalised.
-/

/-- **The ONCE contradiction, pinned (S253)**: no continuous real lift of
the middle selection of a circular component advances by HALF a knot period
per circuit.  A continuous `mhat : ℝ → ℝ` with `mhat (t + T) = mhat t +
halfPeriod` whose circle values are the canonical middles of the classes
`χ (t : AddCircle T)` is impossible: the class is `T`-periodic
(`(t + T : AddCircle T) = (t : AddCircle T)`, so `componentMiddle` is the
same at `t` and `t + T`), which forces the circle value of `mhat` to return
at `t + T`; but the half-period advance shifts it by the non-zero element
`(halfPeriod : AddCircle period)` (`halfPeriod_ne_zero_circle`).  This is
the analytic core of the once-winding jump (Kuperberg: a ±g component has
its endpoints advance half way around with a swap, trapping the middle into
this half-period advance). -/
theorem no_onceWinding_advance {r : ℝ → Space} (c₀ : OSub r) {T : ℝ}
    (χ : AddCircle T ≃ₜ TrisecantComponent r c₀) {mhat : ℝ → ℝ}
    (hmc : Continuous mhat) (hadv : ∀ t : ℝ, mhat (t + T) = mhat t + halfPeriod)
    (hcompat : ∀ t : ℝ, (mhat t : AddCircle period) =
      componentMiddle c₀ (χ (t : AddCircle T))) : False := by
  have hper : (mhat T : AddCircle period) = (mhat 0 : AddCircle period) := by
    calc
      (mhat T : AddCircle period) = componentMiddle c₀ (χ (T : AddCircle T)) := by
        simpa using (hcompat T)
      _ = componentMiddle c₀ (χ (0 : AddCircle T)) := by
        congr 1
        -- (T : AddCircle T) = (0 : AddCircle T) since T ≡ 0 mod T
        rw [AddCircle.coe_period]
      _ = (mhat 0 : AddCircle period) := by
        exact (hcompat 0).symm
  have hadv0 : (mhat T : AddCircle period) =
      (mhat 0 : AddCircle period) + (halfPeriod : AddCircle period) := by
    calc
      (mhat T : AddCircle period) = (mhat 0 + halfPeriod : ℝ) := by
        congr 1
        simpa using (hadv 0)
      _ = (mhat 0 : AddCircle period) + (halfPeriod : AddCircle period) := by
        rw [AddCircle.coe_add]
  have hz' : (mhat 0 : AddCircle period) + (halfPeriod : AddCircle period) =
      (mhat 0 : AddCircle period) := hadv0.symm.trans hper
  have hzero : (halfPeriod : AddCircle period) = 0 := by
    apply add_left_cancel (a := (mhat 0 : AddCircle period))
    exact hz'.trans (add_zero (mhat 0 : AddCircle period)).symm
  exact halfPeriod_ne_zero_circle hzero

/-- **The TWICE data shape — item (iii) (S253)**: a continuous real lift
`G` of the middle selection `componentMiddle c₀` over the circular
component chart `χ : AddCircle T ≃ₜ TrisecantComponent r c₀` that advances
a FULL knot period per circuit: `G (t + T) = G t + period`.  This is the
measurement datum that the twice-winding geometry (a ±2g circular
component: the ordered double-cover lift is closed and each chord endpoint
winds once around the knot, trapping the middle into the same full-period
advance) must supply — it is consumed verbatim by `no_twiceWinding_data`
(S248). -/
def TwiceWindingAdvancingLift {r : ℝ → Space} (c₀ : OSub r) {T : ℝ}
    (χ : AddCircle T ≃ₜ TrisecantComponent r c₀) : Prop :=
  ∃ G : ℝ → ℝ, Continuous G ∧
    (∀ t : ℝ, G (t + T) = G t + period) ∧
    (∀ t : ℝ, (G t : AddCircle period) =
      componentMiddle c₀ (χ (t : AddCircle T)))

/-- **The TWICE contradiction from the item-(iii) datum (S253)**:
`no_twiceWinding_data` (S248) fed by item (i) (`χ`), item (ii)
(`componentMiddle` continuous — `componentMiddle_continuous` S252 — with
membership `componentMiddle_mem_middleSet`) and the item-(iii) datum
(`TwiceWindingAdvancingLift`).  The twice-winding geometry is reduced to
deriving the advancing lift. -/
theorem no_twiceWinding_component_of_lift {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (c₀ : OSub r) {T : ℝ} (hT : 0 < T)
    (χ : AddCircle T ≃ₜ TrisecantComponent r c₀)
    (hTw : TwiceWindingAdvancingLift c₀ χ) : False := by
  rcases hTw with ⟨G, hGc, hadv, hcompat⟩
  exact no_twiceWinding_data h c₀ hT χ (componentMiddle c₀)
    (componentMiddle_continuous h hqf hgp c₀)
    (fun z => componentMiddle_mem_middleSet c₀ z) hGc hadv hcompat

/-- **The circle-chart reparametrisation (S253)**: a `Circle ≃ₜ X` chart
reparametrises to the knot-parameter circle `AddCircle period ≃ₜ X`
through `Pi1Mobius.paramCircleHomeo` (whose codomain is `Circle`), so
item (i) charts are available in the `AddCircle` form that the winding
data (`TwiceWindingAdvancingLift`, `no_onceWinding_advance`) and
`no_twiceWinding_data` consume. -/
noncomputable def addCircleHomeo_of_circleHomeo {X : Type*} [TopologicalSpace X]
    (χC : Circle ≃ₜ X) : AddCircle period ≃ₜ X :=
  paramCircleHomeo.trans χC

/-- **The compact side in `AddCircle` form (S253)**: a compact connected
component of the trisecant set is homeomorphic to the knot-parameter
circle `AddCircle period` (circuit length `period > 0`) — the S249
`trisecantComponent_compactSide` output reparametrised by
`addCircleHomeo_of_circleHomeo`. -/
theorem trisecantComponent_compactSide_addCircle {r : ℝ → Space}
    (h : IsSmoothKnot r) (hqf : QuadrisecantFree r)
    (hgp : TorusGeneralPositionTransverse r) (c₀ : OSub r)
    (hcmp : IsCompact (connectedComponent c₀ : Set (OSub r))) :
    Nonempty (AddCircle period ≃ₜ TrisecantComponent r c₀) := by
  rcases trisecantComponent_compactSide h hqf hgp c₀ hcmp with ⟨χC⟩
  exact ⟨addCircleHomeo_of_circleHomeo χC⟩


/-- **The middle selection on a circular component has an integer degree
(S253)**: for a circular component chart `χ : AddCircle T ≃ₜ
TrisecantComponent r c₀` the middle selection `componentMiddle c₀ ∘ χ` is
a continuous circle map, hence (fleet
`Commons.Topology.AddCircle.circleMap_lift_advance`) admits a continuous
real lift whose advance over one circuit is an integer multiple of the knot
period: `G (t + T) = G t + (k : ℝ) * period`.  This is the formal
"integer lift advance" degree fact of the ONCE analysis (S246) and the
carrier of the TWICE measurement: the twice-winding geometry will pin
`k = 1` (the full-period advance of `TwiceWindingAdvancingLift`). -/
theorem componentMiddle_lift_advance {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (c₀ : OSub r) {T : ℝ} (χ : AddCircle T ≃ₜ TrisecantComponent r c₀) :
    ∃ G : ℝ → ℝ, Continuous G ∧
      (∀ t : ℝ, (G t : AddCircle period) =
        componentMiddle c₀ (χ (t : AddCircle T))) ∧
      ∃ k : ℤ, ∀ t : ℝ, G (t + T) = G t + (k : ℝ) * period := by
  let f : ℝ → AddCircle period := fun t =>
    componentMiddle c₀ (χ (t : AddCircle T))
  have hfcont : Continuous f := by
    dsimp [f]
    exact (componentMiddle_continuous h hqf hgp c₀).comp
      (χ.continuous.comp (AddCircle.continuous_mk' T))
  have hfper : ∀ t : ℝ, f (t + T) = f t := by
    intro t
    dsimp [f]
    congr 1
    simp [AddCircle.coe_period]
  rcases Commons.Topology.AddCircle.circleMap_lift_advance T period
      period_ne_zero hfcont hfper with ⟨G, hGc, hGl, k, hk⟩
  exact ⟨G, hGc, hGl, k, hk⟩



/-! ## S254 — the `k ≠ 0` TWICE contradiction assembled at component level
(VERIFIED, sorry-free) — S253b sub-problem 5(b), the fallback
simplification of the winding measurement

The S254 generalisation in ParameterWinding
(`surj_of_lift_advance_zsmul` / `knotParam_surj_of_lift_advance_zsmul` /
`twiceWinding_middle_contradiction_zsmul`) makes the TWICE branch solvable
from a strictly weaker measurement than the full-period advance of
`TwiceWindingAdvancingLift` (S253): it is enough that the middle selection
of the circular component has ANY nonzero integer degree.  This section
pins that fact in component form:

* **`no_twiceWinding_component_of_lift_zsmul`** (VERIFIED) — the S253
  `no_twiceWinding_component_of_lift` mirror for `k ≠ 0`: a continuous
  real lift `G` of the middle selection `componentMiddle c₀ ∘ χ` advancing
  by the nonzero integer multiple `k` of the knot period per circuit
  (`G (t + T) = G t + (k : ℝ) * period`) is impossible — the k≠0
  surjectivity contradiction fed by `componentMiddle_mem_middleSet` through
  the `MiddlePointsOnClass_subset_MiddleCovered` bridge.  Note that
  continuity of `componentMiddle` is NOT needed here (the lift `G` carries
  the regularity): the hypotheses are `IsSmoothKnot r` (for the extremal
  `exists_uncovered_middle` contradiction), the component chart `χ`, and
  the lift datum.

STATUS after S254 (ComponentWindingData): the TWICE branch now closes from
either measurement — the exact full-period advance
(`TwiceWindingAdvancingLift`, S253, `no_twiceWinding_component_of_lift`) or
the weaker nonzero-degree advance (this section).  What remains for the
TWICE branch is purely the geometric derivation of the measurement from a
twice-winding circular component (the Layer-C brick-(c) real-lift
bookkeeping; the weaker form needs only "the middle map of a twice-winding
component has nonzero degree" = "μ∘χ is not null-homotopic").  Tree green;
TWO documented sorries; no children pending.
-/

/-- **The `k ≠ 0` TWICE contradiction at component level (VERIFIED)**:
a continuous real lift `G` of the middle selection of a circular component
(chart `χ : AddCircle T ≃ₜ TrisecantComponent r c₀`, middle =
`componentMiddle c₀ ∘ χ`) advancing by ANY nonzero integer multiple `k` of
the knot period per circuit (`G (t + T) = G t + (k : ℝ) * period`,
`0 < T`) is impossible — `knotParam_surj_of_lift_advance_zsmul` (S254)
makes `t ↦ (G t : AddCircle period)` surjective and
`middle_surjective_contradiction` collides it with
`TrisecantStructure.exists_uncovered_middle`, with each `G`-value a genuine
middle via `componentMiddle_mem_middleSet` (S252) + the
`MiddlePointsOnClass_subset_MiddleCovered` bridge (S248).  This is the
fallback TWICE measurement of S253b sub-problem 5: the twice-winding
geometry only needs to produce `k ≠ 0` (that the middle map of the
component is not null-homotopic), not the exact full-period `k = 1`. -/
theorem no_twiceWinding_component_of_lift_zsmul {r : ℝ → Space} (h : IsSmoothKnot r)
    (c₀ : OSub r) {T : ℝ} (hT : 0 < T)
    (χ : AddCircle T ≃ₜ TrisecantComponent r c₀)
    {k : ℤ} (hk : k ≠ 0) {G : ℝ → ℝ} (hG : Continuous G)
    (hadv : ∀ t : ℝ, G (t + T) = G t + (k : ℝ) * period)
    (hcompat : ∀ t : ℝ, (G t : AddCircle period) =
      componentMiddle c₀ (χ (t : AddCircle T))) : False := by
  exact twiceWinding_middle_contradiction_zsmul h hT hk hG hadv (by
    intro t
    rw [hcompat t]
    exact MiddlePointsOnClass_subset_MiddleCovered (r := r)
      (((χ (t : AddCircle T) : TrisecantComponent r c₀) : OSub r) : OpenMobius)
      (componentMiddle_mem_middleSet c₀ (χ (t : AddCircle T))))



/-! ## S255 — the middle selection of every circular component has DEGREE
ZERO (VERIFIED, sorry-free) — the structural conclusion both winding
branches contradict

Assembling S253 (`componentMiddle_lift_advance`: the middle selection of a
circular component has an integer degree `k`) with S254
(`no_twiceWinding_component_of_lift_zsmul`: a `k ≠ 0` degree is already
impossible) gives the formal statement that the geometry must contradict:

* **`componentMiddle_has_periodic_lift`** (VERIFIED) — for a circular
  component chart `χ : AddCircle T ≃ₜ TrisecantComponent r c₀` under the
  full hypotheses (`IsSmoothKnot`, `QuadrisecantFree`,
  `TorusGeneralPositionTransverse`, `0 < T`), the middle selection
  `componentMiddle c₀ ∘ χ` admits a continuous real lift that is
  `T`-PERIODIC: `G (t + T) = G t` with `(G t : AddCircle period) =
  componentMiddle c₀ (χ (t : AddCircle T))` — i.e. its degree is `0`.
  Proof: take the degree-`k` lift of `componentMiddle_lift_advance`; if
  `k ≠ 0`, S254's contradiction closes; hence `k = 0` and the advance is
  trivial.

STATUS after S255: the two winding branches are each reduced to a
contradiction with an established structural fact — (TWICE) the winding
geometry of a twice-winding component would produce a lift of the middle
selection with degree `k = ±1` (full-period advance,
`TwiceWindingAdvancingLift` S253) or at least `k ≠ 0`, contradicting
`componentMiddle_has_periodic_lift` (this section; equivalently the S254 /
S253 component contradictions directly); (ONCE) the once-winding endpoint
swap avatar would produce the half-period advancing lift of
`no_onceWinding_advance`, impossible by the pure periodicity argument
already recorded there.  What remains is the Layer-C brick-(c) geometric
derivation (sub-problems 1–4 of S253b: the ordered double-cover lift over
the component circle and the endpoint real lifts, then the trapped-middle
measurement).  Tree green; TWO documented sorries; no children pending.
-/

/-- **The middle selection of a circular component has degree zero
(VERIFIED)**: under the full hypotheses, the middle selection
`componentMiddle c₀ ∘ χ` of a circular component (chart `χ : AddCircle T
≃ₜ TrisecantComponent r c₀`, `0 < T`) admits a continuous `T`-periodic
real lift — the integer degree of `componentMiddle_lift_advance` (S253)
must be `0`, since a nonzero degree would make the middle family
surjective (S254 `no_twiceWinding_component_of_lift_zsmul`, the `k ≠ 0`
generalisation) and collide with the extremal
`TrisecantStructure.exists_uncovered_middle`.  This is the structural fact
that the twice-winding geometry (full-period or nonzero-degree advance)
and the once-winding avatar (half-period advance) both contradict. -/
theorem componentMiddle_has_periodic_lift {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (c₀ : OSub r) {T : ℝ} (hT : 0 < T)
    (χ : AddCircle T ≃ₜ TrisecantComponent r c₀) :
    ∃ G : ℝ → ℝ, Continuous G ∧
      (∀ t : ℝ, (G t : AddCircle period) =
        componentMiddle c₀ (χ (t : AddCircle T))) ∧
      (∀ t : ℝ, G (t + T) = G t) := by
  rcases componentMiddle_lift_advance h hqf hgp c₀ χ with ⟨G, hGc, hGl, k, hk⟩
  by_cases hk0 : k = 0
  · refine ⟨G, hGc, hGl, ?_⟩
    intro t
    have h := hk t
    rw [hk0] at h
    simpa using h
  · exfalso
    exact no_twiceWinding_component_of_lift_zsmul (r := r) h c₀ hT χ hk0 hGc hk hGl

end LeanEval.KnotTheory.Quadrisecant
