import Mathlib
import ChallengeDeps
import Submission.ComponentChart
import Submission.ComponentMiddle
import Submission.ComponentPath
import Submission.Commons.Topology.AddCircle.circleMap_lift_advance

open LeanEval.KnotTheory.Quadrisecant
open Filter
open AddSubgroup
open scoped Real Topology unitInterval

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedVariables false

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-!
# S256 — the component loop: a circular component chart is a loop of `O`
(VERIFIED, sorry-free) — S253b sub-problem 1, unit-interval form

The two halves of the winding analysis are (a) the AddCircle charts of a
circular component — `trisecantComponent_compactSide` (S249) +
`addCircleHomeo_of_circleHomeo` (S253) give `χ : AddCircle T ≃ₜ
TrisecantComponent r c₀`, `T = period` — and (b) the double-cover
monodromy/parity machinery over paths in `O` (`ComponentPath`:
`exists_lift_orderedData_of_bandPath`, `lift_loop_end_in_fiber`,
`lift_loop_end_even_or_odd`, `lift_from_swap_ends_swapped`), which lifts
paths `γ : Path x y` between trisecant classes through the ordered double
cover `mobiusCover : OrderedPairs → OpenMobius`.  This module is the
bridge: it runs the circular chart around one full circuit as a genuine
loop of `O`, so the parity dichotomy applies to a *circular component*:

1. **`componentLoopBase`** — the class underlying the `0` element of the
   chart (an `OSub r` trisecant class of the component);
2. **`componentLoop`** — the loop `γ : Path b b`, `b = componentLoopBase
   c₀ χ`, tracing the whole circle once: `γ t = χ (t·T : AddCircle T)`
   for `t ∈ I` (source `t = 0 ↦ χ 0 = b`; target `t = 1 ↦ χ T = χ 0` by
   `AddCircle.coe_period`, the full circuit).  Continuity is the chart
   homeomorphism over the continuous real parametrisation `t ↦ t·T`;
3. **`componentLoop_val`** — the pointwise identity `γ t = χ (t·T)`
   (definitional);
4. **`exists_ordered_rep_of_component_loopBase`** — every base class of
   the loop has an ordered representative `p₀` (`mobiusCover p₀ = b`,
   from `b ∈ trisecantSet r`);
5. **`component_loop_parity`** — **the parity dichotomy of a circular
   component** (the unit-interval half of S253b sub-problem 1): the
   component loop lifts to an ordered-pair path `Γ` over the full circuit
   with `Γ 1 = p₀` (EVEN / null monodromy — the twice-winding branch:
   the ordered lift closes up, so the endpoints wind once each around the
   knot per circuit) or `Γ 1 = swapOrdered p₀` (ODD / essential
   monodromy — the once-winding branch: the sheets are swapped after one
   circuit) — `lift_loop_end_even_or_odd` instanced at the component loop.

STATUS after S256: the parity classification now applies directly to
circular components given by the S249/S253 charts — the next Layer-C
brick-(c) steps are the periodic extension of the ordered lift to all of
`ℝ` (in the even case: `Γ (t + T) = Γ t` descends to the whole circle,
and the endpoint real lifts `â`, `b̂` of `S253b` sub-problem 2), the middle
real lift (S255 says its degree is `0`), and the trapped-middle
measurement (sub-problems 3–4).  Tree green; TWO documented sorries; no
children pending.
-/

/-- **The base class of the component loop (VERIFIED)**: the trisecant
class of `O` underlying the `0` element of the circular chart
`χ : AddCircle T ≃ₜ TrisecantComponent r c₀` — a point of the component of
`c₀`, read back into the subtype `OSub r` of trisecant classes.  The loop
of the component (below) starts and ends at this class. -/
noncomputable def componentLoopBase {r : ℝ → Space} (c₀ : OSub r) {T : ℝ}
    (χ : AddCircle T ≃ₜ TrisecantComponent r c₀) : OSub r :=
  ((χ (0 : AddCircle T) : TrisecantComponent r c₀) : OSub r)

/-- **The component loop (VERIFIED)**: a circular component chart
`χ : AddCircle T ≃ₜ TrisecantComponent r c₀` runs once around the whole
component over the unit interval by `t ↦ χ (t·T : AddCircle T)`: a loop
`γ : Path b b` of `O` based at `b = componentLoopBase c₀ χ` (source:
`(0 : I) ↦ χ 0 = b`; target: `(1 : I) ↦ χ T = χ 0` since
`(T : AddCircle T) = 0` — the full circuit).  This is the bridge between
the AddCircle charts (S249/S253) and the path/parity machinery of
`ComponentPath` (`Path`, `bandCMap`, `lift_loop_end_even_or_odd`), which
lifts paths between trisecant classes through the ordered double cover. -/
noncomputable def componentLoop {r : ℝ → Space} (c₀ : OSub r) {T : ℝ}
    (χ : AddCircle T ≃ₜ TrisecantComponent r c₀) :
    Path (componentLoopBase c₀ χ) (componentLoopBase c₀ χ) := by
  refine Path.mk
    ⟨fun t : I => ((χ (((t : ℝ) * T) : AddCircle T) : TrisecantComponent r c₀) : OSub r), ?_⟩ ?_ ?_
  · -- continuity: χ over the continuous real parametrisation t ↦ t·T
    have hpar : Continuous (fun t : I => (t : ℝ) * T) :=
      (continuous_subtype_val : Continuous (fun t : I => (t : ℝ))).mul continuous_const
    exact (continuous_subtype_val.comp
      ((χ.continuous.comp ((AddCircle.continuous_mk' T).comp hpar))))
  · -- source: t = 0 ↦ χ ((0 : ℝ) * T) = χ 0 = b
    apply congrArg (fun z : TrisecantComponent r c₀ => (z : OSub r))
    apply congrArg χ
    simp
  · -- target: t = 1 ↦ χ (T) = χ 0 (full circuit)
    apply congrArg (fun z : TrisecantComponent r c₀ => (z : OSub r))
    apply congrArg χ
    simp [AddCircle.coe_period]

/-- **The pointwise value of the component loop (VERIFIED)**: at
`t : I` the loop reads the chart at `(t·T : AddCircle T)`, then projects
to the trisecant class subtype (definitional). -/
lemma componentLoop_val {r : ℝ → Space} (c₀ : OSub r) {T : ℝ}
    (χ : AddCircle T ≃ₜ TrisecantComponent r c₀) (t : I) :
    ((componentLoop c₀ χ : Path (componentLoopBase c₀ χ) (componentLoopBase c₀ χ)) t : OSub r) =
      ((χ (((t : ℝ) * T) : AddCircle T) : TrisecantComponent r c₀) : OSub r) := by
  rfl

/-- **An ordered representative of the component loop base (VERIFIED)**:
the base class `b = componentLoopBase c₀ χ` is a trisecant class
(`b ∈ trisecantSet r` — `OSub` membership), so it has an ordered
representative `p₀ : OrderedPairs` with `mobiusCover p₀ = b`.  This is
the starting lift of the parity analysis of the component loop. -/
lemma exists_ordered_rep_of_component_loopBase {r : ℝ → Space} (c₀ : OSub r) {T : ℝ}
    (χ : AddCircle T ≃ₜ TrisecantComponent r c₀) :
    ∃ p₀ : OrderedPairs, mobiusCover p₀ = ((componentLoopBase c₀ χ) : OpenMobius) := by
  let b : OSub r := componentLoopBase c₀ χ
  have hb : HasMiddleOnClass r (b : OpenMobius) := by
    exact b.2
  rcases hb with ⟨m, p, hp, hm⟩
  refine ⟨p, ?_⟩
  simpa [b] using hp

/-- **The parity dichotomy of a circular component (VERIFIED)**: the
component loop (S256) lifts through the ordered double cover to a
continuous path `Γ : C(I, OrderedPairs)` of ordered chords over the full
circuit, starting at the chosen representative `p₀` of the base class and
ending at one of the two representatives of the base class — `Γ 1 = p₀`
(EVEN / null monodromy — a twice-winding component: the ordered lift is
closed after one circuit, each chord endpoint travels once around the
knot) or `Γ 1 = swapOrdered p₀` (ODD / essential monodromy — a
once-winding component: the two sheets are exchanged after one circuit).
This is `ComponentPath.lift_loop_end_even_or_odd` instanced at the
component loop — the unit-interval half of S253b sub-problem 1. -/
theorem component_loop_parity {r : ℝ → Space} (c₀ : OSub r) {T : ℝ}
    (χ : AddCircle T ≃ₜ TrisecantComponent r c₀) (p₀ : OrderedPairs)
    (hp₀ : mobiusCover p₀ = ((componentLoopBase c₀ χ) : OpenMobius)) :
    ∃ Γ : C(I, OrderedPairs), mobiusCover ∘ Γ = bandCMap (componentLoop c₀ χ) ∧
      Γ 0 = p₀ ∧ (Γ 1 = p₀ ∨ Γ 1 = swapOrdered p₀) :=
  lift_loop_end_even_or_odd (componentLoop c₀ χ) p₀ hp₀


/-! ## S257 — the ordered lift over the whole component circle (VERIFIED,
sorry-free) — S253b sub-problem 1 COMPLETE

Sub-problem 1 of the S253b brick-(c) decomposition asks for the pullback of
the ordered double cover along the class map of a circular component over a
real parametrisation of the whole circle.  The S256 component loop gives
the unit-interval form (the `Path`-level parity dichotomy
`component_loop_parity`); this section gives the genuine `ℝ`-level
statement, with the periodic/swap-advance dichotomy of the lift in
"advance" form:

* **`componentClassMap`** — the continuous class map of the circular
  component over `ℝ`: `u ↦ χ (u : AddCircle T)` projected into the band
  (`C(ℝ, OpenMobius)`);
* **`componentClassMap_periodic`** — the class map is `T`-periodic:
  `componentClassMap χ (u + T) = componentClassMap χ u` (the chart's class
  returns after a full circuit: `(u + T : AddCircle T) = (u : AddCircle
  T)`, the coercion of the real sum reducing to the `AddCircle` sum whose
  second term vanishes by `AddCircle.coe_period`);
* **`component_ordered_lift_real`** — **THE ordered lift over the whole
  component circle**: since `mobiusCover : OrderedPairs → OpenMobius` is a
  covering map (`isCoveringMap_mobiusCover`, SecantSpace) and `ℝ` is
  simply connected and locally path-connected, the class map lifts
  (`IsCoveringMap.existsUnique_continuousMap_lifts`): there is a
  continuous `sig : C(ℝ, OrderedPairs)` with `sig 0 = p₀` and
  `mobiusCover ∘ sig = componentClassMap c₀ χ`, whose behaviour over one
  circuit is either EVEN — `sig (u + T) = sig u` for all `u` (the ordered
  lift is `T`-periodic, closed: the endpoints of the ordered chord wind
  once each around the knot per circuit — the twice-winding branch) — or
  ODD — `sig (u + T) = swapOrdered (sig u)` for all `u` (the two sheets
  are exchanged per circuit — the once-winding branch).  Proof: the
  endpoint `sig T` lies in the fibre `{p₀, swapOrdered p₀}` of the base
  class (`mobiusCover (sig T) = mobiusCover p₀` since the class returns),
  and in the closed case the shifted lift `u ↦ sig (u + T)` agrees with
  `sig` at `0` (a continuous lift of the same `T`-periodic class map,
  hence equal by `IsCoveringMap.eq_of_comp_eq` over the connected line),
  while in the swapped case it agrees at `0` with `u ↦ swapOrdered (sig
  u)` (which also lifts the class map by `mobiusCover_swap`).

STATUS after S257: S253b sub-problem 1 is DONE in its genuine real-line
form — the ordered double-cover lift over the whole component circle with
the even/odd advance dichotomy (in the "advance" phrasing that the winding
measurement consumes).  Remaining brick-(c) content: sub-problem 2 (the
endpoint real lifts â, b̂ of `sig u = (â u, b̂ u)` via the `AddCircle`-of-
the-parameter-circle covering — the ±2g meaning pins their advances to
`±period` in the even case), sub-problem 3 (the middle real lift — S255
already fixes its degree at 0), sub-problem 4 (the trapped-middle
measurement connecting the endpoints' winding to the middle).  Tree green;
TWO documented sorries; no children pending.
-/

/-- **The class map of a circular component over the real line (VERIFIED)**:
a circular component chart `χ : AddCircle T ≃ₜ TrisecantComponent r c₀`
read along the real parametrisation `u ↦ χ (u : AddCircle T)` and
projected into the open Möbius band — a continuous map
`C(ℝ, OpenMobius)` (the chart homeomorphism over the continuous quotient
map, then the two subtype projections). -/
noncomputable def componentClassMap {r : ℝ → Space} (c₀ : OSub r) {T : ℝ}
    (χ : AddCircle T ≃ₜ TrisecantComponent r c₀) : C(ℝ, OpenMobius) :=
  ⟨fun u : ℝ => ((χ (u : AddCircle T) : TrisecantComponent r c₀) : OpenMobius), by
    exact (continuous_subtype_val.comp
      (continuous_subtype_val.comp (χ.continuous.comp (AddCircle.continuous_mk' T))))⟩

/-- **The class map is `T`-periodic (VERIFIED)**: after one full circuit
(`u ↦ u + T`) the chart returns to the same trisecant class:
`componentClassMap χ (u + T) = componentClassMap χ u` — the coercion of
the real sum `(u + T : ℝ)` into `AddCircle T` reduces to the `AddCircle`
sum `(u : AddCircle T) + (T : AddCircle T)`, and the second term vanishes
by `AddCircle.coe_period`. -/
lemma componentClassMap_periodic {r : ℝ → Space} (c₀ : OSub r) {T : ℝ}
    (χ : AddCircle T ≃ₜ TrisecantComponent r c₀) (u : ℝ) :
    componentClassMap c₀ χ (u + T) = componentClassMap c₀ χ u := by
  dsimp [componentClassMap]
  apply congrArg (fun z : TrisecantComponent r c₀ => (z : OpenMobius))
  apply congrArg χ
  -- the coercion of (u + T) reduces to the AddCircle sum (u : AddCircle T) + (T : AddCircle T);
  -- the second term vanishes by AddCircle.coe_period
  rw [AddCircle.coe_period]
  simp

/-- **The ordered lift over the whole component circle (VERIFIED)** —
S253b sub-problem 1: the class map of a circular component
(`componentClassMap c₀ χ`, `T`-periodic) lifts through the ordered double
cover `mobiusCover : OrderedPairs → OpenMobius` (a covering map; `ℝ`
simply connected and locally path connected) to a continuous
`sig : C(ℝ, OrderedPairs)` with `sig 0 = p₀` (the chosen representative of
the base class) and `mobiusCover ∘ sig = componentClassMap c₀ χ`.  Over
one circuit the lift is either EVEN — `sig (u + T) = sig u` (the ordered
lift is `T`-periodic/closed; each chord endpoint winds once around the
knot — the twice-winding branch) — or ODD —
`sig (u + T) = swapOrdered (sig u)` (the two sheets of the double cover
are exchanged — the once-winding branch).  Proof: `sig T` lies in the
fibre `{p₀, swapOrdered p₀}` of the base class (the class map returns at
`T`), and the even/odd advance follows by uniqueness of continuous lifts
(`IsCoveringMap.eq_of_comp_eq` over the connected real line) comparing the
shifted lift `u ↦ sig (u + T)` with `sig` / with `u ↦ swapOrdered (sig u)`
(which also lifts the class map by `mobiusCover_swap`). -/
theorem component_ordered_lift_real {r : ℝ → Space} (c₀ : OSub r) {T : ℝ}
    (χ : AddCircle T ≃ₜ TrisecantComponent r c₀) (p₀ : OrderedPairs)
    (hp₀ : mobiusCover p₀ = (componentClassMap c₀ χ 0 : OpenMobius)) :
    ∃ sig : C(ℝ, OrderedPairs), sig 0 = p₀ ∧
      mobiusCover ∘ sig = componentClassMap c₀ χ ∧
      ((∀ u : ℝ, sig (u + T) = sig u) ∨ (∀ u : ℝ, sig (u + T) = swapOrdered (sig u))) := by
  rcases (isCoveringMap_mobiusCover.existsUnique_continuousMap_lifts
      (componentClassMap c₀ χ) (0 : ℝ) p₀ hp₀) with ⟨sig, hsig0c⟩
  have hsig0and : sig 0 = p₀ ∧ mobiusCover ∘ sig = componentClassMap c₀ χ := by
    simpa using hsig0c.1
  have hsig0 : sig 0 = p₀ := hsig0and.1
  have hσl' : mobiusCover ∘ sig = componentClassMap c₀ χ := hsig0and.2
  have hsigend : sig T = p₀ ∨ sig T = swapOrdered p₀ := by
    have hm : mobiusCover (sig T) = mobiusCover p₀ := by
      calc
        mobiusCover (sig T) = componentClassMap c₀ χ T := by
          exact congrFun hσl' T
        _ = componentClassMap c₀ χ 0 := by
          have h0 : (0 : ℝ) + T = T := by ring
          simpa [h0] using (componentClassMap_periodic c₀ χ 0)
        _ = mobiusCover p₀ := hp₀.symm
    have hfib : sig T ∈ ({p₀, swapOrdered p₀} : Set OrderedPairs) := by
      rw [← mobiusCover_fiber p₀]
      exact hm
    simpa using hfib
  rcases hsigend with hsigT | hsigT
  · refine ⟨sig, hsig0, hσl', Or.inl ?_⟩
    intro u
    have hτcont : Continuous (fun u : ℝ => sig (u + T)) :=
      sig.continuous.comp (continuous_id.add continuous_const)
    have hτlift : (mobiusCover ∘ fun u : ℝ => sig (u + T)) = componentClassMap c₀ χ := by
      funext u
      calc
        mobiusCover (sig (u + T)) = componentClassMap c₀ χ (u + T) := congrFun hσl' (u + T)
        _ = componentClassMap c₀ χ u := componentClassMap_periodic c₀ χ u
    have heq : (fun u : ℝ => sig (u + T)) = sig :=
      isCoveringMap_mobiusCover.eq_of_comp_eq hτcont sig.continuous
        (hτlift.trans hσl'.symm) 0 (by
          rw [zero_add]
          exact hsigT.trans hsig0.symm)
    exact congrFun heq u
  · refine ⟨sig, hsig0, hσl', Or.inr ?_⟩
    intro u
    have hτcont : Continuous (fun u : ℝ => sig (u + T)) :=
      sig.continuous.comp (continuous_id.add continuous_const)
    have hρcont : Continuous (fun u : ℝ => swapOrdered (sig u)) :=
      continuous_swapOrdered.comp sig.continuous
    have hτlift : (mobiusCover ∘ fun u : ℝ => sig (u + T)) = componentClassMap c₀ χ := by
      funext u
      calc
        mobiusCover (sig (u + T)) = componentClassMap c₀ χ (u + T) := congrFun hσl' (u + T)
        _ = componentClassMap c₀ χ u := componentClassMap_periodic c₀ χ u
    have hρlift : (mobiusCover ∘ fun u : ℝ => swapOrdered (sig u)) = componentClassMap c₀ χ := by
      funext u
      calc
        mobiusCover (swapOrdered (sig u)) = mobiusCover (sig u) := mobiusCover_swap (sig u)
        _ = componentClassMap c₀ χ u := congrFun hσl' u
    have heq : (fun u : ℝ => sig (u + T)) = (fun u : ℝ => swapOrdered (sig u)) :=
      isCoveringMap_mobiusCover.eq_of_comp_eq hτcont hρcont
        (hτlift.trans hρlift.symm) 0 (by
          rw [zero_add]
          rw [hsig0]
          exact hsigT)
    exact congrFun heq u


/-! ## S258 — the endpoint real lifts of an EVEN ordered lift (VERIFIED,
sorry-free) — S253b sub-problem 2 (existence and integer advances)

Given the EVEN (twice-winding) ordered lift `sig : C(ℝ, OrderedPairs)`
over the whole component circle (`sig (u + T) = sig u`, S257), each chord
endpoint is a continuous `T`-periodic map into the parameter circle
`AddCircle period`, so by the covering lift/degree theorem (fleet L66,
`Commons.Topology.AddCircle.circleMap_lift_advance`) each endpoint admits
a continuous real lift whose per-circuit advance is an integer multiple of
the knot period:

* **`continuous_ordered_endpoint1` / `continuous_ordered_endpoint2`**
  (VERIFIED) — the endpoint projections `u ↦ (sig u).1.1` and
  `u ↦ (sig u).1.2` of an ordered lift are continuous (subtype + product
  projections over the continuous `sig`);
* **`component_endpoints_lift_even`** (VERIFIED) — for an even ordered
  lift `sig` of the class map of a circular component chart `χ` (`sig (u +
  T) = sig u`), there are continuous real lifts `a b : ℝ → ℝ` of the two
  endpoints (`(a u : AddCircle period) = (sig u).1.1`,
  `(b u : AddCircle period) = (sig u).1.2`) with integer per-circuit
  advances: `a (u + T) = a u + (ka : ℝ) * period` and
  `b (u + T) = b u + (kb : ℝ) * period` for integers `ka kb` (the formal
  "endpoint winding numbers" of the even branch — the ±2g measurement
  pins them to `±period`).

STATUS after S258: sub-problem 2 (existence + integer advances of the
endpoint real lifts in the even branch) is verified.  Remaining brick-(c)
content: sub-problems 3–4 — the middle real lift along the same
parametrisation (its degree is already pinned at 0 by S255
`componentMiddle_has_periodic_lift`) and the trapped-middle measurement
(the strict-betweenness real-lift lemma: for a genuine ordered chord with
real lifts `a`, `b`, the middle's real lift stays strictly between `a` and
`b` pointwise; combining the endpoint advances `ka`, `kb` with the middle
degree `0` then yields the TWICE contradiction via S253/S254/S255 — the
remaining analytic core of brick (c)).  Tree green; TWO documented
sorries; no children pending.
-/

/-- **Endpoint-1 projection continuity (VERIFIED)**: for a continuous
ordered-pair lift `sig : C(ℝ, OrderedPairs)`, the first endpoint
`u ↦ (sig u).1.1` is a continuous map into the parameter circle (the
covering double cover's ordered chord data read as the first parameter of
the unordered pair). -/
lemma continuous_ordered_endpoint1 {sig : C(ℝ, OrderedPairs)} :
    Continuous (fun u : ℝ => (sig u).1.1) := by
  exact (continuous_fst.comp (continuous_subtype_val.comp sig.continuous))

/-- **Endpoint-2 projection continuity (VERIFIED)**: for a continuous
ordered-pair lift `sig : C(ℝ, OrderedPairs)`, the second endpoint
`u ↦ (sig u).1.2` is continuous. -/
lemma continuous_ordered_endpoint2 {sig : C(ℝ, OrderedPairs)} :
    Continuous (fun u : ℝ => (sig u).1.2) := by
  exact (continuous_snd.comp (continuous_subtype_val.comp sig.continuous))

/-- **The endpoint real lifts of an EVEN ordered lift (VERIFIED)** —
S253b sub-problem 2: for an EVEN (twice-winding) ordered lift `sig` of the
class map of a circular component (`sig (u + T) = sig u` — S257), each
chord endpoint is a continuous `T`-periodic circle map, hence (fleet L66,
`Commons.Topology.AddCircle.circleMap_lift_advance`) has a continuous real
lift with an integer per-circuit advance: `a` over the first endpoint
(`(a u : AddCircle period) = (sig u).1.1`) and `b` over the second
(`(b u : AddCircle period) = (sig u).1.2`), with
`a (u + T) = a u + (ka : ℝ) * period`, `b (u + T) = b u + (kb : ℝ) *
period` for integers `ka kb` — the formal endpoint winding numbers that
the twice-winding geometry pins to `±period` per circuit. -/
theorem component_endpoints_lift_even {r : ℝ → Space} (c₀ : OSub r) {T : ℝ}
    (χ : AddCircle T ≃ₜ TrisecantComponent r c₀) {sig : C(ℝ, OrderedPairs)}
    (_hσl : mobiusCover ∘ sig = componentClassMap c₀ χ)
    (heven : ∀ u : ℝ, sig (u + T) = sig u) :
    ∃ a b : ℝ → ℝ,
      Continuous a ∧ Continuous b ∧
      (∀ u : ℝ, (a u : AddCircle period) = (sig u).1.1) ∧
      (∀ u : ℝ, (b u : AddCircle period) = (sig u).1.2) ∧
      (∃ ka : ℤ, ∀ u : ℝ, a (u + T) = a u + (ka : ℝ) * period) ∧
      (∃ kb : ℤ, ∀ u : ℝ, b (u + T) = b u + (kb : ℝ) * period) := by
  let f1 : ℝ → AddCircle period := fun u => (sig u).1.1
  have hf1c : Continuous f1 := continuous_ordered_endpoint1
  have hf1per : ∀ u : ℝ, f1 (u + T) = f1 u := by
    intro u
    dsimp [f1]
    apply congrArg (fun q : OrderedPairs => q.1.1)
    exact heven u
  rcases Commons.Topology.AddCircle.circleMap_lift_advance T period period_ne_zero
      (f := f1) hf1c hf1per with ⟨a, hAc, hAl, ka, hak⟩
  let f2 : ℝ → AddCircle period := fun u => (sig u).1.2
  have hf2c : Continuous f2 := continuous_ordered_endpoint2
  have hf2per : ∀ u : ℝ, f2 (u + T) = f2 u := by
    intro u
    dsimp [f2]
    apply congrArg (fun q : OrderedPairs => q.1.2)
    exact heven u
  rcases Commons.Topology.AddCircle.circleMap_lift_advance T period period_ne_zero
      (f := f2) hf2c hf2per with ⟨b, hBc, hBl, kb, hbk⟩
  refine ⟨a, b, hAc, hBc, ?_, ?_, ?_, ?_⟩
  · intro u
    simpa [f1] using (hAl u)
  · intro u
    simpa [f2] using (hBl u)
  · exact ⟨ka, hak⟩
  · exact ⟨kb, hbk⟩


/-! ## S259 — the ordered lift's chord carries the canonical middle
(VERIFIED, sorry-free) — the sig–μ connection of S253b sub-problems 3–4

The ordered lift `sig` of S257 is a continuous family of ordered chords
covering the class map of the circular component; the canonical middle
selection `componentMiddle` (S252) is the unique middle of each class.  The
bridge between them — needed by the trapped-middle measurement (S253b
sub-problem 4) — is that the canonical middle of the class `χ (u : AddCircle
T)` is a genuine middle of the chord `sig u`:

* **`componentMiddle_middle_of_ordered_lift`** (VERIFIED, unconditional)
  — for an ordered lift `sig` of the class map (`mobiusCover ∘ sig =
  componentClassMap c₀ χ`, S257): for every `u : ℝ`,
  `IsMiddleOnChord r (sig u).1.1 (sig u).1.2
  (componentMiddle c₀ (χ (u : AddCircle T)))` — the middle membership
  `componentMiddle_mem_middleSet` (S252, unconditional) provides some
  chord of the class whose strict middle the canonical middle is, and
  `middleOnChord_of_mobiusCover_eq` (representative independence:
  middle-ness depends only on the unordered class, not the ordered
  representative) transfers it to the specific representative `sig u` of
  the same class (`congrFun hσl u`).

STATUS after S259: with the ordered lift `sig` (S257), its endpoint real
lifts with integer advances (S258, even branch), the degree-0 periodic
middle lift (S255) and this sig–μ bridge, the inputs of the trapped-middle
measurement are all formalised except the measurement itself (S253b
sub-problem 4: strict betweenness in real lifts + the winding comparison)
and its ONCE counterpart (`no_onceWinding_advance` is pinned, S253).  Tree
green; TWO documented sorries; no children pending.
-/

/-- **The ordered lift's chord carries the canonical middle (VERIFIED)**:
if `sig : C(ℝ, OrderedPairs)` is a continuous lift of the class map of the
circular component chart `χ` (`mobiusCover ∘ sig = componentClassMap c₀
χ`, S257), then for every `u : ℝ` the canonical middle of the class
`χ (u : AddCircle T)` is a strict middle of the ordered chord `sig u`:
`IsMiddleOnChord r (sig u).1.1 (sig u).1.2 (componentMiddle c₀ (χ (u :
AddCircle T)))`.  Proof: `componentMiddle_mem_middleSet` (S252,
unconditional) gives some chord of the class whose middle the canonical
middle is, and the representative-independence lemma
`middleOnChord_of_mobiusCover_eq` (middle-ness depends only on the
unordered class) transfers it to the representative `sig u` (same class by
`congrFun hσl u`).  This is the `sig`–`μ` connection consumed by the
trapped-middle measurement of S253b sub-problems 3–4. -/
theorem componentMiddle_middle_of_ordered_lift {r : ℝ → Space} (c₀ : OSub r) {T : ℝ}
    (χ : AddCircle T ≃ₜ TrisecantComponent r c₀) {sig : C(ℝ, OrderedPairs)}
    (hσl : mobiusCover ∘ sig = componentClassMap c₀ χ) :
    ∀ u : ℝ, IsMiddleOnChord r (sig u).1.1 (sig u).1.2
      (componentMiddle c₀ (χ (u : AddCircle T))) := by
  intro u
  let z : TrisecantComponent r c₀ := χ (u : AddCircle T)
  let cl : OpenMobius := ((z : OSub r) : OpenMobius)
  have hmem : componentMiddle c₀ z ∈ MiddlePointsOnClass r cl := by
    simpa [z, cl] using (componentMiddle_mem_middleSet c₀ z)
  rcases (mem_MiddlePointsOnClass_iff r cl (componentMiddle c₀ z)).mp hmem with ⟨pw, hpw, hmi⟩
  have hcl : cl = componentClassMap c₀ χ u := by
    dsimp [cl, z, componentClassMap]
  have hsig : mobiusCover (sig u) = cl := by
    calc
      mobiusCover (sig u) = componentClassMap c₀ χ u := by
        exact congrFun hσl u
      _ = cl := hcl.symm
  have hpq : mobiusCover (sig u) = mobiusCover pw := by
    calc
      mobiusCover (sig u) = cl := hsig
      _ = mobiusCover pw := hpw.symm
  exact (middleOnChord_of_mobiusCover_eq (sig u) pw hpq).mpr hmi


/-! ## S260 — the middle lift is trapped on the endpoint chord: real strict
betweenness (VERIFIED, sorry-free) — S253b sub-problem 3's core statement

With the endpoint real lifts `a b : ℝ → ℝ` of an ordered lift `sig` of the
class map (S258), the degree-0 periodic real lift `mhat` of the middle
selection (S255), and the `sig`–`μ` bridge (S259: the canonical middle of
the class is a strict middle of the ordered chord `sig u`), the real form
of "the middle is trapped between the endpoints" is:

* **`componentMiddle_real_betweenness`** (VERIFIED) — for every `u : ℝ`,
  the middle knot point lies strictly inside the chord joining the two
  endpoint knot points, in the *real* parametrisation:
  `r (mhat u) ∈ openSegment ℝ (r (a u)) (r (b u))`.  Proof: S259 gives
  `IsMiddleOnChord r (sig u).1.1 (sig u).1.2 (componentMiddle c₀ (χ (u :
  AddCircle T)))`; the endpoint/middle compatibility (S258's `a`, `b`
  lifting the chord, `mhat` lifting the middle) rewrites the chord to the
  real lifts, and `IsMiddleOnChord_iff_real` (MiddleConvergence: on real
  representatives the strict-middle condition is exactly the real
  open-segment condition, `knotMap_eq_r`) converts the circle-level
  statement into the real segment membership.

STATUS after S260: sub-problem 3's statement — the real strict betweenness
of the middle lift on the endpoint chord — is verified in the form that
the trapped-middle measurement consumes (the middle's knot point lies on
the open segment between the endpoint knot points, as real-lift functions
of the component parameter).  The genuinely open analytic content remains
S253b sub-problem 4: deriving the middle's winding (nonzero degree in the
TWICE branch / the half-period avatar in the ONCE branch) from this
trapped-betweenness together with the endpoint windings `ka`, `kb` (S258)
and the structure of the knot/chord family — the bridge from "trapped on
the chord" to "the parameter m̂ advances" needs the model geometry
(ChordParam / the trisecant 1-manifold structure: the middle is a smooth
local function of the chord) recorded in ROADMAP S260.  Tree green; TWO
documented sorries; no children pending.
-/

/-- **The middle lift is trapped on the endpoint chord — real strict
betweenness (VERIFIED)**: let `sig : C(ℝ, OrderedPairs)` be an ordered
lift of the class map of a circular component chart `χ` (S257), with real
endpoint lifts `a b : ℝ → ℝ` (`(a u : AddCircle period) = (sig u).1.1`,
`(b u : AddCircle period) = (sig u).1.2`) and a real middle lift `mhat`
(`(mhat u : AddCircle period) = componentMiddle c₀ (χ (u : AddCircle
T))`, S255).  Then for every `u : ℝ` the middle knot point lies strictly
inside the chord between the two endpoint knot points, in the real
parametrisation: `r (mhat u) ∈ openSegment ℝ (r (a u)) (r (b u))`.
Proof: `componentMiddle_middle_of_ordered_lift` (S259) makes the canonical
middle of the class a strict middle of the ordered chord `sig u`
(`IsMiddleOnChord r (sig u).1.1 (sig u).1.2 ...`); the endpoint/middle
real-lift compatibilities rewrite the chord to `a u`, `b u`, `mhat u`;
and `IsMiddleOnChord_iff_real` (MiddleConvergence) converts the
circle-level strict-middle condition on real representatives into the real
open-segment condition (`knotMap_eq_r`).  This is the formal statement of
"the middle is trapped between the endpoints" on each sheet of the real
parametrisation — the input of the trapped-middle winding measurement
(S253b sub-problem 4). -/
theorem componentMiddle_real_betweenness {r : ℝ → Space} (h : IsSmoothKnot r)
    (c₀ : OSub r) {T : ℝ} (χ : AddCircle T ≃ₜ TrisecantComponent r c₀)
    {sig : C(ℝ, OrderedPairs)} (hσl : mobiusCover ∘ sig = componentClassMap c₀ χ)
    {a b mhat : ℝ → ℝ}
    (ha : ∀ u : ℝ, (a u : AddCircle period) = (sig u).1.1)
    (hb : ∀ u : ℝ, (b u : AddCircle period) = (sig u).1.2)
    (hm : ∀ u : ℝ, (mhat u : AddCircle period) =
      componentMiddle c₀ (χ (u : AddCircle T))) :
    ∀ u : ℝ, r (mhat u) ∈ openSegment ℝ (r (a u)) (r (b u)) := by
  intro u
  have hmid : IsMiddleOnChord r ((a u : ℝ) : AddCircle period)
      ((b u : ℝ) : AddCircle period) ((mhat u : ℝ) : AddCircle period) := by
    have h259 := componentMiddle_middle_of_ordered_lift c₀ χ hσl u
    -- h259 : IsMiddleOnChord r (sig u).1.1 (sig u).1.2 (componentMiddle c₀ (χ (u : AddCircle T)))
    -- rewrite the circle elements to a u / b u / mhat u
    simpa [← ha u, ← hb u, ← hm u] using h259
  exact (IsMiddleOnChord_iff_real h (a u) (b u) (mhat u)).mp hmid


/-! ## S261 — the ONCE-case first beat: on the odd-advance branch the
endpoint lifts travel and SWITCH (VERIFIED, sorry-free)

Kuperberg's once-case: if the circular component `C` winds once around the
Möbius band `M`, "the endpoints travel half way around S¹ and then switch
places".  In the S257 dichotomy the once-winding branch is the ODD
advance: `sig (u + T) = swapOrdered (sig u)` — the ordered lift of the
chord after one circuit is the same unordered chord with its two endpoints
exchanged.  This section formalises the "switch" beat:

1. **`component_endpoints_lift`** (VERIFIED) — any ordered lift `sig`
   (either branch) admits continuous real lifts `a b : ℝ → ℝ` of its two
   chord endpoints over the whole real line (`(a u : AddCircle period) =
   (sig u).1.1`, `(b u : AddCircle period) = (sig u).1.2`) — the `AddCircle
   period` covering lift of the continuous endpoint projections (S258's
   `continuous_ordered_endpoint1/2` + ℝ simply connected).  (S258's even
   case additionally gave integer advances from periodicity; the odd case
   needs no periodicity for existence.)
2. **`component_ordered_endpoint_switch_odd`** (VERIFIED) — the
   circle-level switch: on the odd branch the endpoint classes exchange
   after one circuit: `(sig (u+T)).1.1 = (sig u).1.2` and
   `(sig (u+T)).1.2 = (sig u).1.1`.
3. **`component_endpoint_switch_odd`** (VERIFIED) — the real-lift switch
   with integer offsets: on the odd branch, continuous real endpoint
   lifts `a b` satisfy `a (u + T) = b u + (ka : ℝ) * period` and
   `b (u + T) = a u + (kb : ℝ) * period` for fixed integers `ka kb` — over
   one circuit each endpoint continues along the OTHER endpoint's curve,
   shifted by a constant integer number of knot periods.  Proof: the class
   of `a (u + T)` equals the class of `b u` (the circle-level switch), so
   the continuous real function `φ (u) = a (u + T) − b u` takes values in
   the discrete subgroup `period·ℤ` and is constant on the connected real
   line (`PreconnectedSpace.constant` through the
   `zmultiples period`-valued lift, as in fleet L66), giving the fixed
   integer `ka`; symmetrically for `b` (`γ (u) = b (u + T) − a u`).

STATUS after S261: the once-case "endpoints … switch places" beat is
verified in the odd branch (the "half way around" half is the S253 ONCE
avatar: `no_onceWinding_advance` pins that the trapped middle would need a
HALF-period advancing lift, which is impossible by the pure periodicity
argument).  The next beat of the once-case — from the switch + the real
trappedness (S260) to the contradiction for a supposed continuous middle
lift — and the separate twice-case (closed `sig` + endpoint advances `ka
kb` of S258 against the degree-zero middle of S255) remain the brick-(c)
sub-problem 4 content.  Tree green; TWO documented sorries; no children
pending.
-/

/-- **Real endpoint lifts over the whole line (VERIFIED)**: for an ordered
lift `sig : C(ℝ, OrderedPairs)` of the class map of a circular component
chart (either advance branch), the two chord endpoints are continuous maps
into the parameter circle, hence lift over the simply-connected real line
through the `AddCircle period` covering: there are continuous real lifts
`a b : ℝ → ℝ` with `(a u : AddCircle period) = (sig u).1.1` and
`(b u : AddCircle period) = (sig u).1.2` for every `u`.  (The even case
S258 additionally derived integer per-circuit advances from the
periodicity of the endpoint circle maps; this existence fact needs no
periodicity.) -/
theorem component_endpoints_lift {r : ℝ → Space} (c₀ : OSub r) {T : ℝ}
    (χ : AddCircle T ≃ₜ TrisecantComponent r c₀) {sig : C(ℝ, OrderedPairs)}
    (_hσl : mobiusCover ∘ sig = componentClassMap c₀ χ) :
    ∃ a b : ℝ → ℝ, Continuous a ∧ Continuous b ∧
      (∀ u : ℝ, (a u : AddCircle period) = (sig u).1.1) ∧
      (∀ u : ℝ, (b u : AddCircle period) = (sig u).1.2) := by
  let f1 : C(ℝ, AddCircle period) := ⟨fun u => (sig u).1.1, continuous_ordered_endpoint1⟩
  obtain ⟨e1, he1⟩ : ∃ e1 : ℝ, (e1 : AddCircle period) = f1 0 := by
    simpa using (QuotientAddGroup.mk_surjective (s := zmultiples period) (f1 0))
  rcases (AddCircle.isCoveringMap_coe (𝕜 := ℝ) period).existsUnique_continuousMap_lifts
      f1 (0 : ℝ) e1 (by simpa [f1] using he1) with ⟨aC, ha0⟩
  have ha0c : aC 0 = e1 ∧ (QuotientAddGroup.mk ∘ aC : ℝ → AddCircle period) = f1 := by
    simpa using ha0.1
  let f2 : C(ℝ, AddCircle period) := ⟨fun u => (sig u).1.2, continuous_ordered_endpoint2⟩
  obtain ⟨e2, he2⟩ : ∃ e2 : ℝ, (e2 : AddCircle period) = f2 0 := by
    simpa using (QuotientAddGroup.mk_surjective (s := zmultiples period) (f2 0))
  rcases (AddCircle.isCoveringMap_coe (𝕜 := ℝ) period).existsUnique_continuousMap_lifts
      f2 (0 : ℝ) e2 (by simpa [f2] using he2) with ⟨bC, hb0⟩
  have hb0c : bC 0 = e2 ∧ (QuotientAddGroup.mk ∘ bC : ℝ → AddCircle period) = f2 := by
    simpa using hb0.1
  refine ⟨fun u => aC u, fun u => bC u, aC.continuous, bC.continuous, ?_, ?_⟩
  · intro u
    simpa [f1] using (congrFun ha0c.2 u)
  · intro u
    simpa [f2] using (congrFun hb0c.2 u)

/-- **The circle-level endpoint switch on the odd branch (VERIFIED)**: if
the ordered lift is ODD — `sig (u + T) = swapOrdered (sig u)` — then after
one circuit the two ordered endpoint classes have exchanged places:
`(sig (u+T)).1.1 = (sig u).1.2` and `(sig (u+T)).1.2 = (sig u).1.1`
(definitional from `swapOrdered`).  This is the "the endpoints … switch
places" beat of Kuperberg's once-winding case at the level of the chord. -/
lemma component_ordered_endpoint_switch_odd {T : ℝ} {sig : C(ℝ, OrderedPairs)}
    (hodd : ∀ u : ℝ, sig (u + T) = swapOrdered (sig u)) (u : ℝ) :
    (sig (u + T)).1.1 = (sig u).1.2 ∧ (sig (u + T)).1.2 = (sig u).1.1 := by
  constructor
  · rw [hodd u]
    rfl
  · rw [hodd u]
    rfl

/-- **The endpoint real lifts switch with integer offsets on the odd
branch (VERIFIED)**: on the ODD advance branch (`sig (u + T) = swapOrdered
(sig u)`), continuous real endpoint lifts `a b` of the chord (`(a u :
AddCircle period) = (sig u).1.1`, `(b u : AddCircle period) = (sig u).1.2`)
satisfy `a (u + T) = b u + (ka : ℝ) * period` and
`b (u + T) = a u + (kb : ℝ) * period` for fixed integers `ka kb` — over
one circuit each endpoint continues along the OTHER endpoint's curve,
shifted by a constant integer number of knot periods.  Proof: the class of
`a (u + T)` equals the class of `b u` (the circle-level switch), so the
continuous real function `φ (u) = a (u + T) − b u` takes values in the
discrete subgroup `period·ℤ` and is constant on the connected real line
(`PreconnectedSpace.constant` through the `zmultiples period`-valued
continuous lift, exactly as in fleet L66), giving the fixed integer `ka`;
symmetrically `γ (u) = b (u + T) − a u` gives `kb`.  This is the
real-lift form of "the endpoints … switch places" (Kuperberg's
once-winding case). -/
theorem component_endpoint_switch_odd {r : ℝ → Space} (c₀ : OSub r) {T : ℝ}
    (χ : AddCircle T ≃ₜ TrisecantComponent r c₀) {sig : C(ℝ, OrderedPairs)}
    (_hσl : mobiusCover ∘ sig = componentClassMap c₀ χ)
    (hodd : ∀ u : ℝ, sig (u + T) = swapOrdered (sig u))
    {a b : ℝ → ℝ} (hAc : Continuous a) (hBc : Continuous b)
    (ha : ∀ u : ℝ, (a u : AddCircle period) = (sig u).1.1)
    (hb : ∀ u : ℝ, (b u : AddCircle period) = (sig u).1.2) :
    ∃ ka kb : ℤ,
      (∀ u : ℝ, a (u + T) = b u + (ka : ℝ) * period) ∧
      (∀ u : ℝ, b (u + T) = a u + (kb : ℝ) * period) := by
  -- φ(u) = a(u+T) − b u takes values in period·ℤ (the switched class)
  let φ : ℝ → ℝ := fun u => a (u + T) - b u
  have hφ_mem : ∀ u : ℝ, φ u ∈ zmultiples period := by
    intro u
    rw [AddSubgroup.mem_zmultiples_iff]
    rw [← AddCircle.coe_eq_zero_iff (p := period)]
    dsimp [φ]
    rw [sub_eq_zero]
    calc
      (a (u + T) : AddCircle period) = (sig (u + T)).1.1 := ha (u + T)
      _ = (sig u).1.2 := by
        rw [hodd u]
        rfl
      _ = (b u : AddCircle period) := (hb u).symm
  have hφ_cont : Continuous φ := by
    dsimp [φ]
    exact (hAc.comp (continuous_id.add continuous_const)).sub hBc
  let ψ : ℝ → zmultiples period := fun u => ⟨φ u, hφ_mem u⟩
  have hψ_cont : Continuous ψ := Continuous.subtype_mk (f := φ) hφ_cont hφ_mem
  have hφ_const : ∀ u : ℝ, φ u = φ 0 := by
    intro u
    have hψc : ψ u = ψ 0 :=
      PreconnectedSpace.constant (α := ℝ) (Y := zmultiples period)
        (inferInstance : PreconnectedSpace ℝ) hψ_cont
    exact congrArg Subtype.val hψc
  have hφ0_mem : φ 0 ∈ zmultiples period := hφ_mem 0
  rcases (AddSubgroup.mem_zmultiples_iff.mp hφ0_mem) with ⟨ka, hka⟩
  have hka0 : φ 0 = (ka : ℝ) * period := hka.symm.trans (zsmul_eq_mul period ka)
  -- same for the second endpoint: γ(u) = b(u+T) − a u
  let γ : ℝ → ℝ := fun u => b (u + T) - a u
  have hγ_mem : ∀ u : ℝ, γ u ∈ zmultiples period := by
    intro u
    rw [AddSubgroup.mem_zmultiples_iff]
    rw [← AddCircle.coe_eq_zero_iff (p := period)]
    dsimp [γ]
    rw [sub_eq_zero]
    calc
      (b (u + T) : AddCircle period) = (sig (u + T)).1.2 := hb (u + T)
      _ = (sig u).1.1 := by
        rw [hodd u]
        rfl
      _ = (a u : AddCircle period) := (ha u).symm
  have hγ_cont : Continuous γ := by
    dsimp [γ]
    exact (hBc.comp (continuous_id.add continuous_const)).sub hAc
  let ω : ℝ → zmultiples period := fun u => ⟨γ u, hγ_mem u⟩
  have hω_cont : Continuous ω := Continuous.subtype_mk (f := γ) hγ_cont hγ_mem
  have hγ_const : ∀ u : ℝ, γ u = γ 0 := by
    intro u
    have hωc : ω u = ω 0 :=
      PreconnectedSpace.constant (α := ℝ) (Y := zmultiples period)
        (inferInstance : PreconnectedSpace ℝ) hω_cont
    exact congrArg Subtype.val hωc
  have hγ0_mem : γ 0 ∈ zmultiples period := hγ_mem 0
  rcases (AddSubgroup.mem_zmultiples_iff.mp hγ0_mem) with ⟨kb, hkb⟩
  have hkb0 : γ 0 = (kb : ℝ) * period := hkb.symm.trans (zsmul_eq_mul period kb)
  refine ⟨ka, kb, ?_, ?_⟩
  · intro u
    calc
      a (u + T) = b u + φ u := by dsimp [φ]; ring
      _ = b u + φ 0 := by rw [hφ_const u]
      _ = b u + (ka : ℝ) * period := by rw [hka0]
  · intro u
    calc
      b (u + T) = a u + γ u := by dsimp [γ]; ring
      _ = a u + γ 0 := by rw [hγ_const u]
      _ = a u + (kb : ℝ) * period := by rw [hkb0]

/-! ## S262 — the once-case double circuit: the ordered lift closes and the
endpoints share one advance over TWO circuits (VERIFIED, sorry-free)

The once-winding (odd) branch of S257 has `sig (u + T) = swapOrdered (sig
u)`: the ordered chord returns after one circuit with its endpoints
exchanged (S261).  The natural fundamental period of the ONCE avatar is
therefore the DOUBLE circuit — the double cover of the Möbius band over
which the swap cancels:

* **`component_endpoint_double_circuit_odd`** (VERIFIED) — on the odd
  branch, over two circuits the ordered lift CLOSES (`sig (u + T + T) =
  sig u`, by two swaps — `swapOrdered_involutive`), and both endpoint real
  lifts advance by the SAME integer multiple of the knot period:
  `a (u + T + T) = a u + (kd : ℝ) * period` and
  `b (u + T + T) = b u + (kd : ℝ) * period` with `kd = ka + kb` (the sum
  of the one-circuit switch offsets of S261, each endpoint's two-circuit
  advance being `ka` followed by `kb` or vice versa).  Proof: pure algebra
  on the S261 switch relations
  (`a (x + T) = b x + (ka : ℝ) * period`,
  `b (x + T) = a x + (kb : ℝ) * period`) applied twice.

This is the well-formed period structure of the once-case data: the
once-avatar lives on the double cover of the component, where it is
`2T`-periodic with the single combined endpoint advance `kd · period`.
NOTE (honest status of the ONCE geometry): the HALF-period avatar itself —
a real middle lift `mhat` with `mhat (u + T) = mhat u + halfPeriod` over a
SINGLE circuit — is NOT derivable from the S254–S262 data: the unique
continuous middle `componentMiddle c₀ ∘ χ` of a circular component is
`T`-periodic (S255 degree zero), and `no_onceWinding_advance` (S253) shows
no half-period-advancing lift of it exists at all.  Producing the
once-contradiction therefore requires a geometric input beyond the
abstract ordered-lift/endpoint data — the chord-DIRECTION (π_K) structure
of the knot (Kuperberg's "the middle is trapped between the endpoints,
which travel half way around and switch, so it must jump") or the
π₁(M) ≅ ℤ machinery — recorded as the open content of brick-(c)
sub-problem 4; S261–S262 supply the well-formed period/switch structure of
the once-data that those arguments will consume.  Tree green; TWO
documented sorries; no children pending.
-/

/-- **The once-case double circuit (VERIFIED)**: on the odd (once-winding)
branch (`sig (u + T) = swapOrdered (sig u)`), over TWO circuits the
ordered lift closes (`sig (u + T + T) = sig u` — the double cover of the
Möbius band, where the swap cancels by `swapOrdered_involutive`), and both
continuous real endpoint lifts advance by the SAME integer multiple of the
knot period: `a (u + T + T) = a u + (kd : ℝ) * period` and
`b (u + T + T) = b u + (kd : ℝ) * period`, with `kd = ka + kb` the sum of
the one-circuit switch offsets of S261.  Proof: two applications of the
S261 switch relations `a (x + T) = b x + (ka : ℝ) * period`,
`b (x + T) = a x + (kb : ℝ) * period`.  This is the well-formed period
structure of the once-case avatar (its natural fundamental period is the
double circuit). -/
theorem component_endpoint_double_circuit_odd {r : ℝ → Space} (c₀ : OSub r) {T : ℝ}
    (χ : AddCircle T ≃ₜ TrisecantComponent r c₀) {sig : C(ℝ, OrderedPairs)}
    (_hσl : mobiusCover ∘ sig = componentClassMap c₀ χ)
    (hodd : ∀ u : ℝ, sig (u + T) = swapOrdered (sig u))
    {a b : ℝ → ℝ} (hAc : Continuous a) (hBc : Continuous b)
    (ha : ∀ u : ℝ, (a u : AddCircle period) = (sig u).1.1)
    (hb : ∀ u : ℝ, (b u : AddCircle period) = (sig u).1.2) :
    ∃ kd : ℤ,
      (∀ u : ℝ, sig (u + T + T) = sig u) ∧
      (∀ u : ℝ, a (u + T + T) = a u + (kd : ℝ) * period) ∧
      (∀ u : ℝ, b (u + T + T) = b u + (kd : ℝ) * period) := by
  rcases component_endpoint_switch_odd c₀ χ _hσl hodd hAc hBc ha hb with ⟨ka, kb, hak, hbk⟩
  refine ⟨ka + kb, ?_, ?_, ?_⟩
  · intro u
    calc
      sig (u + T + T) = swapOrdered (sig (u + T)) := by rw [hodd (u + T)]
      _ = swapOrdered (swapOrdered (sig u)) := by rw [hodd u]
      _ = sig u := swapOrdered_involutive (sig u)
  · intro u
    calc
      a (u + T + T) = b (u + T) + (ka : ℝ) * period := hak (u + T)
      _ = (a u + (kb : ℝ) * period) + (ka : ℝ) * period := by rw [hbk u]
      _ = a u + ((ka + kb : ℤ) : ℝ) * period := by
        rw [Int.cast_add]
        ring
  · intro u
    calc
      b (u + T + T) = a (u + T) + (kb : ℝ) * period := hbk (u + T)
      _ = (b u + (ka : ℝ) * period) + (kb : ℝ) * period := by rw [hak u]
      _ = b u + ((ka + kb : ℤ) : ℝ) * period := by
        rw [Int.cast_add]
        ring

/-! ## S275 — the band loop of a trisecant component and ESSENTIALNESS:
odd parity ⟹ not null-homotopic (VERIFIED, sorry-free)
(Submission/ComponentLoop.lean)

(Where the S253b/S262 route stands: the winding measurement needs the
component-loop parity data (S256 `component_loop_parity`,
S257 `component_ordered_lift_real` — EVEN/closed or ODD/swapped ordered
lift per circuit) to be read as *essentiality in the band*: a circular
component whose ordered lift is ODD (the once-winding branch) is NOT
null-homotopic as a loop of the open Möbius band `OpenMobius`, i.e. it
represents a non-trivial element of `π₁(OpenMobius)` (≅ ℤ, Pi1OpenMobius)
— the covering-space content of the "winds once around M" phrase.  The
obstruction dichotomy (Layer C (d)) consumes exactly this: interval
components carry no essential loops at all (S244 `LoopsTrivial`), and a
component that obstructs all non-separating arcs must be an *essential*
circular component; this section supplies the bridge from the
measurable parity (S256/S257) to essentiality.  The proof is pure
covering-space theory: null-homotopy (homotopy rel endpoints to the
constant loop) forces the canonical ordered lift of the loop to close
(`liftPath` endpoint equality over a `HomotopyRel`, Mathlib
`Topology.Homotopy.Lifting`), while the ODD datum says that every lift
from `p₀` ends at `swapOrdered p₀ ≠ p₀` — `ordered_ne_swapOrdered`.)

Content (appended to Submission/ComponentLoop.lean as section S275,
namespace LeanEval.KnotTheory.Quadrisecant, sorry-free, `lake build`
rc=0):

- **`bandLoop`** (VERIFIED def) — the band loop underlying a loop `γ :
  Path c₀ c₀` of trisecant classes: the same points read in the open
  Möbius band as a `Path ((c₀ : OSub r) : OpenMobius) ((c₀ : OSub r) :
  OpenMobius)` (source/target by the two subtype projections of
  `γ.source`/`γ.target`); its continuous map is `bandCMap γ`
  (definitional);
- **`bandLoop_eq_bandCMap`** (VERIFIED) — `(bandLoop γ : C(I,
  OpenMobius)) = bandCMap γ` (the Path-to-continuous-map coercion is the
  bundled map);
- **`bandLoop_essential_of_oddLift`** (VERIFIED) — **THE theorem**: if a
  loop `γ : Path c₀ c₀` of trisecant classes admits an ordered lift
  `Γ : C(I, OrderedPairs)` over the ordered double cover
  (`mobiusCover ∘ Γ = bandCMap γ`, `Γ 0 = p₀`) whose endpoint is the
  *other* sheet `Γ 1 = swapOrdered p₀` (ODD monodromy — the once-winding
  datum), then the band loop `bandLoop γ` is NOT null-homotopic at its
  base class: `¬ Path.Homotopic (bandLoop γ) (Path.refl ((c₀ : OSub r) :
  OpenMobius))`.  Proof (contrapositive): a rel-endpoint homotopy to the
  constant loop would give, by the covering homotopy-lifting endpoint
  theorem (`IsCoveringMap.liftPath_apply_one_eq_of_homotopicRel` +
  `liftPath_const`), that the canonical lift from `p₀`
  (`IsCoveringMap.liftPath`, uniquely characterised by
  `eq_liftPath_iff'`) ends at `p₀`; but by `eq_liftPath_iff'` that
  canonical lift is exactly the given `Γ`, whose endpoint is
  `swapOrdered p₀` — contradicting `ordered_ne_swapOrdered`;
- **`component_loop_essential_of_odd`** (VERIFIED) — the instance for the
  circular components of the trisecant set: under the ODD branch of the
  S256 parity dichotomy (`component_loop_parity` at the chart
  `χ : AddCircle T ≃ₜ TrisecantComponent r c₀`, i.e. a lift ending at
  `swapOrdered p₀`), the component loop `componentLoop c₀ χ` is not
  null-homotopic in the band — the circular components that "wind once"
  (sheets swapped) are essential;
- **`bandLoop_even_of_null`** / **`component_loop_even_of_null`**
  (VERIFIED) — the complementary half: a *null-homotopic* band loop
  (homotopic rel endpoints to the constant loop at its base class) can
  only sit on the EVEN branch: its ordered lift closes, `Γ 1 = p₀` (the
  parity dichotomy of `lift_loop_end_even_or_odd` with the ODD branch
  excluded by the essentiality theorem).

STATUS after S275: the parity dichotomy of circular components (S256) is
now connected to essentiality in the band — the formal bridge from the
measurable once/twice winding data to the π₁(OpenMobius) ≅ ℤ /
obstruction vocabulary that Layer C (c)/(d) consumes.  (Deduplication
note for future sessions: the plane-model homeo `OpenMobius ≃ₜ
MobiusModel`, the core retraction `openMobiusCoreRetract`, the homotopy
equivalence to the core and `π₁(OpenMobius) ≅ ℤ` were all completed
earlier in `Submission/SecantModel.lean`, `OpenMobiusHomotopy.lean`,
`Pi1OpenMobius.lean` (fleet commons `pi1_circle_eq_int` /
`pi1_equiv_of_homotopyEquiv`); S263–S273 in `Pi1Mobius.lean` re-derived
the `π₁(AddCircle p) ≅ ℤ` engine and the transport pieces — both
versions are in the build and agree; do not rebuild them.)  Tree green
(`lake build Challenge Submission Solution` rc=0); TWO documented sorries
(Challenge.lean:5 stub, Submission.lean final placeholder); no children
pending.
-/

/-- **The band loop of a loop of trisecant classes (VERIFIED)**: a loop
`γ : Path c₀ c₀` in the subspace `OSub r` of trisecant classes reads as a
loop of the open Möbius band based at the class `(c₀ : OpenMobius)`, with
the same continuous map (`bandCMap γ`). -/
noncomputable def bandLoop {r : ℝ → Space} {c₀ : OSub r} (γ : Path c₀ c₀) :
    Path ((c₀ : OSub r) : OpenMobius) ((c₀ : OSub r) : OpenMobius) := by
  refine Path.mk (bandCMap γ) ?_ ?_
  · dsimp [bandCMap]
    exact congrArg (fun z : OSub r => (z : OpenMobius)) γ.source
  · dsimp [bandCMap]
    exact congrArg (fun z : OSub r => (z : OpenMobius)) γ.target

/-- The continuous map of the band loop is the band map of the original
loop (definitional). -/
lemma bandLoop_eq_bandCMap {r : ℝ → Space} {c₀ : OSub r} (γ : Path c₀ c₀) :
    (bandLoop γ : C(I, OpenMobius)) = bandCMap γ := rfl

/-- **Odd monodromy ⟹ essential (VERIFIED)**: a loop `γ : Path c₀ c₀` of
trisecant classes whose ordered lift over the double cover
`mobiusCover : OrderedPairs → OpenMobius` starts at `p₀` and ends at the
*other* representative `swapOrdered p₀` of the base class (ODD / sheet-
swapping monodromy — the once-winding datum of the parity dichotomy) is
not null-homotopic as a loop of the band: its band loop is not homotopic
(rel endpoints) to the constant loop at the base class.  Proof:
contrapositive — a rel-endpoint homotopy to the constant loop would force
the canonical lift from `p₀` to close at `p₀` (covering homotopy
lifting: `IsCoveringMap.liftPath_apply_one_eq_of_homotopicRel` +
`liftPath_const`), but that canonical lift is the given `Γ`
(`eq_liftPath_iff'`), whose endpoint `swapOrdered p₀` differs from `p₀`
(`ordered_ne_swapOrdered`). -/
theorem bandLoop_essential_of_oddLift {r : ℝ → Space} {c₀ : OSub r}
    (γ : Path c₀ c₀) (p₀ : OrderedPairs)
    (hp₀ : mobiusCover p₀ = ((c₀ : OSub r) : OpenMobius)) :
    (∃ Γ : C(I, OrderedPairs), mobiusCover ∘ Γ = bandCMap γ ∧ Γ 0 = p₀ ∧
      Γ 1 = swapOrdered p₀) →
      ¬ Path.Homotopic (bandLoop γ)
        (Path.refl ((c₀ : OSub r) : OpenMobius)) := by
  rintro ⟨Γ, hΓl, hΓ₀, hΓ1⟩ hnul
  let P := bandLoop γ
  have h₀ : (P : C(I, OpenMobius)) 0 = mobiusCover p₀ := by
    simp [P, bandLoop, bandCMap, hp₀]
  -- the canonical lift from p₀ of the band loop is exactly Γ
  have hΓeq : isCoveringMap_mobiusCover.liftPath (P : C(I, OpenMobius)) p₀ h₀ = Γ := by
    have hl : mobiusCover ∘ Γ = (P : C(I, OpenMobius)) := by
      rw [bandLoop_eq_bandCMap γ]
      exact hΓl
    exact ((isCoveringMap_mobiusCover.eq_liftPath_iff'
      (γ := (P : C(I, OpenMobius))) (e := p₀) (γ_0 := h₀) (Γ := Γ)).mpr
      ⟨hl, hΓ₀⟩).symm
  -- null-homotopy forces the canonical lift to end at p₀
  have hclose : isCoveringMap_mobiusCover.liftPath (P : C(I, OpenMobius)) p₀ h₀ 1 = p₀ := by
    let reflP : C(I, OpenMobius) :=
      (Path.refl ((c₀ : OSub r) : OpenMobius) : C(I, OpenMobius))
    have h₁ : (P : C(I, OpenMobius)) 0 = mobiusCover p₀ := h₀
    have h₂ : reflP 0 = mobiusCover p₀ := by
      simp [reflP, hp₀]
    have hrel : (P : C(I, OpenMobius)).HomotopicRel reflP {0, 1} := by
      exact hnul
    have hend := isCoveringMap_mobiusCover.liftPath_apply_one_eq_of_homotopicRel
      hrel p₀ h₁ h₂
    have hconst : isCoveringMap_mobiusCover.liftPath reflP p₀ h₂ =
        (ContinuousMap.const I p₀ : C(I, OrderedPairs)) := by
      exact isCoveringMap_mobiusCover.liftPath_const
        (x := ((c₀ : OSub r) : OpenMobius)) (by simp [hp₀])
    simpa [P, bandLoop, hconst] using hend
  -- hence Γ closes at p₀, contradicting the odd datum
  have hΓ1p : Γ 1 = p₀ := by
    have hfin := congrArg (fun f : C(I, OrderedPairs) => f 1) hΓeq
    rw [hclose] at hfin
    exact hfin.symm
  exact ordered_ne_swapOrdered p₀ (hΓ1p.symm.trans hΓ1)

/-- **A once-winding circular component is essential (VERIFIED)**: under
the ODD branch of the S256 parity dichotomy at a circular component chart
`χ : AddCircle T ≃ₜ TrisecantComponent r c₀` (the ordered lift of the
component loop ends at the swapped representative `swapOrdered p₀` after
one circuit), the component loop is not null-homotopic as a loop of the
band — the component winds around the open Möbius band essentially
(once-winding), rather than bounding a trivial/null loop. -/
theorem component_loop_essential_of_odd {r : ℝ → Space} (c₀ : OSub r) {T : ℝ}
    (χ : AddCircle T ≃ₜ TrisecantComponent r c₀) (p₀ : OrderedPairs)
    (hp₀ : mobiusCover p₀ = ((componentLoopBase c₀ χ) : OpenMobius)) :
    (∃ Γ : C(I, OrderedPairs),
      mobiusCover ∘ Γ = bandCMap (componentLoop c₀ χ) ∧ Γ 0 = p₀ ∧
        Γ 1 = swapOrdered p₀) →
      ¬ Path.Homotopic (bandLoop (componentLoop c₀ χ))
        (Path.refl ((componentLoopBase c₀ χ : OSub r) : OpenMobius)) := by
  exact bandLoop_essential_of_oddLift (componentLoop c₀ χ) p₀ hp₀

/-- **A null-homotopic band loop sits on the EVEN branch (VERIFIED)**: if
the band loop of a trisecant-class loop is null-homotopic (homotopic rel
endpoints to the constant loop at its base class), then the parity
dichotomy of `ComponentPath.lift_loop_end_even_or_odd` cannot return the
ODD sheet swap — the lift closes: `Γ 1 = p₀`.  This is the covering-space
half of "trivial loop ⟹ closed ordered lift" that classifies the even
branch (twice-winding vs null needs the π₁(OpenMobius) ≅ ℤ degree, whose
machinery lives in Pi1OpenMobius / Pi1Mobius). -/
theorem bandLoop_even_of_null {r : ℝ → Space} {c₀ : OSub r} (γ : Path c₀ c₀)
    (p₀ : OrderedPairs) (hp₀ : mobiusCover p₀ = ((c₀ : OSub r) : OpenMobius))
    (hnul : Path.Homotopic (bandLoop γ)
      (Path.refl ((c₀ : OSub r) : OpenMobius))) :
    ∃ Γ : C(I, OrderedPairs), mobiusCover ∘ Γ = bandCMap γ ∧ Γ 0 = p₀ ∧ Γ 1 = p₀ := by
  rcases lift_loop_end_even_or_odd γ p₀ hp₀ with ⟨Γ, hΓl, hΓ₀, hΓe⟩
  rcases hΓe with hΓ1 | hΓ1
  · exact ⟨Γ, hΓl, hΓ₀, hΓ1⟩
  · exfalso
    exact bandLoop_essential_of_oddLift γ p₀ hp₀ ⟨Γ, hΓl, hΓ₀, hΓ1⟩ hnul

/-- **The component-loop form of the even/null classification**: a
null-homotopic circular component loop has a CLOSED ordered lift after
one circuit (`Γ 1 = p₀`), i.e. the even (non-swapped) sheet behaviour. -/
theorem component_loop_even_of_null {r : ℝ → Space} (c₀ : OSub r) {T : ℝ}
    (χ : AddCircle T ≃ₜ TrisecantComponent r c₀) (p₀ : OrderedPairs)
    (hp₀ : mobiusCover p₀ = ((componentLoopBase c₀ χ) : OpenMobius))
    (hnul : Path.Homotopic (bandLoop (componentLoop c₀ χ))
      (Path.refl ((componentLoopBase c₀ χ : OSub r) : OpenMobius))) :
    ∃ Γ : C(I, OrderedPairs),
      mobiusCover ∘ Γ = bandCMap (componentLoop c₀ χ) ∧ Γ 0 = p₀ ∧ Γ 1 = p₀ := by
  exact bandLoop_even_of_null (componentLoop c₀ χ) p₀ hp₀ hnul

end LeanEval.KnotTheory.Quadrisecant
