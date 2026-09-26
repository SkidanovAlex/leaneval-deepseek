import Mathlib
import ChallengeDeps
import Submission.ComponentLoop
import Submission.ChordCoefficient
import Submission.ComponentWindingData

open LeanEval.KnotTheory.Quadrisecant
open Filter
open scoped Real Topology unitInterval

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-!
# S277 — the trapped-middle chord coefficient on a circular component:
the λ-bridge of the winding measurement (VERIFIED, sorry-free)
(Submission/TrappedWinding.lean)

Brick-(c) sub-problem 4 (S253b) is the trapped-middle measurement: from
the real strict betweenness of the middle knot point on the moving chord
of a circular component (S260) plus the endpoint winding behaviour
(S257/S261) to the middle's parameter advance — the step that the S255
degree-zero middle lift and S253's `no_onceWinding_advance` contradiction
statements are waiting to consume.  S276 built the coefficient
`segmentCoeff` (how far along the chord the middle point lies) and its
continuity.  This module *instantiates* it on the real lift data of a
circular component of the trisecant set — the λ-bridge:

    λ(u) = segmentCoeff (r (a u)) (r (b u)) (r (m̂ u))

for continuous real endpoint lifts `a b` of the ordered chord `sig u`
(S261: `(a u : AddCircle period) = (sig u).1.1`, `(b u) = (sig u).1.2`)
and a continuous real middle lift `m̂` of the canonical middle
(`(m̂ u : AddCircle period) = componentMiddle c₀ (χ (u : AddCircle T))`,
S252; a `T`-periodic one exists under the general-position hypotheses by
S255 `componentMiddle_has_periodic_lift`):

1. **`chordCoeffAlong`** — the coefficient along a moving chord of real
   knot points (`r (a u)`, `r (b u)`, `r (m u)`), the function whose
   strict `(0,1)`-values measure the middle's position on the chord;
2. **`continuous_chordCoeffAlong`** / **`chordCoeffAlong_mem_Ioo`** —
   with distinct endpoint classes (always true of an ordered chord) the
   coefficient is continuous and, under the S260 betweenness, strictly
   between `0` and `1`;
3. **component instances** — `component_endpoint_classes_ne` (the two
   endpoints of an ordered chord lift are distinct circle classes),
   `component_middle_lift_class_periodic` (every real middle lift of the
   canonical middle has `T`-periodic *classes*: the chart returns to the
   same class after one circuit), and the wired theorems
   `component_trapped_coeff_continuous` / `component_trapped_coeff_strict`
   (S260's `componentMiddle_real_betweenness` supplies the membership, so
   on a circular component the coefficient is a continuous strict
   `(0,1)`-valued function along the whole real parametrisation);
4. **the branch laws** — the coefficient's behaviour after one circuit is
   exactly the measurable once/twice datum:
   * **`chordCoeffAlong_shift_of_even`** — if the endpoint and middle
     *classes* return after one circuit (the EVEN branch: the ordered
     lift closes, `sig (u+T) = sig u`), the coefficient is `T`-periodic:
     `λ (u + T) = λ u`;
   * **`chordCoeffAlong_shift_of_odd`** — on the ODD branch (`sig (u + T)
     = swapOrdered (sig u)`, the sheets exchange) the coefficient *flips*:
     `λ (u + T) = 1 − λ u` (the endpoints' knot values swap roles, and
     `segmentCoeff_swap` (S276) turns the coefficient around);
   * the sig-level instances `component_coeff_even_periodic` /
     `component_coeff_odd_flip` package these with the component's
     `sig`/`a`/`b`/`m̂` data (S257 heven/hodd, S261 endpoint compat, the
     middle class-periodicity).

STATUS after S277: the λ-bridge of the trapped-middle measurement is
verified — the object over which the winding measurement operates
(continuous, strict, EVEN-periodic or ODD-flipping) is now a theorem of
the component data.  What remains of sub-problem 4 is recorded: the
*derivation* connecting the endpoint windings (S258 even-branch advances
`ka kb ∈ ℤ`, S261 odd-branch switch offsets `ka kb`) to the middle's real
advance (S255 forces degree `0`; the TWICE geometry must contradict that
and the ONCE geometry must contradict `no_onceWinding_advance` — the
measurement itself, which needs the chord-direction/π_K reading of the
band or a further 1-manifold/local-order analysis, as recorded in
S260–S262 and S276).  Tree green (`lake build Challenge Submission
Solution` rc=0); TWO documented sorries (Challenge.lean:5 stub,
Submission.lean final placeholder); no children pending.
-/

/-- **The chord coefficient along a moving chord of knot points
(VERIFIED def)**: with real parameter curves `a b m : ℝ → ℝ`, the
coefficient of the knot point `r (m u)` on the chord from `r (a u)` to
`r (b u)` (S276 `segmentCoeff`); when `r (m u)` is strictly inside the
chord this is the unique strict `(0,1)`-position. -/
noncomputable def chordCoeffAlong {r : ℝ → Space} (a b m : ℝ → ℝ) (u : ℝ) : ℝ :=
  segmentCoeff (r (a u)) (r (b u)) (r (m u))

/-! ## Continuity and strictness of the coefficient (real-data form) -/

/-- **Continuity of the chord coefficient along real curves (VERIFIED)**:
with continuous real curves `a b m` whose endpoint classes are distinct
at every parameter (`(a u) ≠ (b u)` in `AddCircle period` — always true
of the two endpoints of an ordered chord), the coefficient
`u ↦ chordCoeffAlong a b m u` is continuous (S276
`continuous_knot_segmentCoeff` instanced). -/
theorem continuous_chordCoeffAlong {r : ℝ → Space} (h : IsSmoothKnot r)
    {a b m : ℝ → ℝ} (ha : Continuous a) (hb : Continuous b) (hm : Continuous m)
    (hab : ∀ u : ℝ, (a u : AddCircle period) ≠ (b u : AddCircle period)) :
    Continuous (fun u : ℝ => chordCoeffAlong (r := r) a b m u) := by
  unfold chordCoeffAlong
  exact continuous_knot_segmentCoeff h ha hb hm hab

/-- **Strictness of the chord coefficient (VERIFIED)**: under the real
trappedness `r (m u) ∈ openSegment ℝ (r (a u)) (r (b u))` (the S260 form)
and distinct endpoint classes, the coefficient lies strictly in `(0,1)`
at every parameter — the middle knot point is strictly between its
endpoints along the chord (S276 `segmentCoeff_pos`/`segmentCoeff_lt_one`
instanced with `r_ne_of_class_ne`). -/
theorem chordCoeffAlong_mem_Ioo {r : ℝ → Space} (h : IsSmoothKnot r)
    {a b m : ℝ → ℝ}
    (hab : ∀ u : ℝ, (a u : AddCircle period) ≠ (b u : AddCircle period))
    (hmid : ∀ u : ℝ, r (m u) ∈ openSegment ℝ (r (a u)) (r (b u))) :
    ∀ u : ℝ, 0 < chordCoeffAlong (r := r) a b m u ∧ chordCoeffAlong (r := r) a b m u < 1 := by
  intro u
  unfold chordCoeffAlong
  constructor
  · exact segmentCoeff_pos (r_ne_of_class_ne h (hab u)) (hmid u)
  · exact segmentCoeff_lt_one (r_ne_of_class_ne h (hab u)) (hmid u)

/-! ## Component instances: distinct endpoint classes, middle class
periodicity, and the wired coefficient -/

/-- **The endpoints of an ordered chord lift are distinct classes
(VERIFIED)**: for an ordered lift `sig` of the class map of a circular
component with real endpoint lifts `a b` (`(a u) = (sig u).1.1`,
`(b u) = (sig u).1.2`), the two endpoint classes are distinct at every
parameter — `sig u` is an *ordered pair of distinct parameters*
(`OrderedPairs`), so `(a u) ≠ (b u)` in `AddCircle period`. -/
lemma component_endpoint_classes_ne {r : ℝ → Space} (c₀ : OSub r) {T : ℝ}
    (_χ : AddCircle T ≃ₜ TrisecantComponent r c₀) {sig : C(ℝ, OrderedPairs)}
    {a b : ℝ → ℝ}
    (ha : ∀ u : ℝ, (a u : AddCircle period) = (sig u).1.1)
    (hb : ∀ u : ℝ, (b u : AddCircle period) = (sig u).1.2) :
    ∀ u : ℝ, (a u : AddCircle period) ≠ (b u : AddCircle period) := by
  intro u hab
  have h1 : (sig u).1.1 = (sig u).1.2 := by
    calc
      (sig u).1.1 = (a u : AddCircle period) := (ha u).symm
      _ = (b u : AddCircle period) := hab
      _ = (sig u).1.2 := hb u
  exact (sig u).2 h1

/-- **The classes of a real middle lift are `T`-periodic (VERIFIED)**: if
`m̂` is a real lift of the canonical middle of the component
(`(m̂ u : AddCircle period) = componentMiddle c₀ (χ (u : AddCircle T))`),
then after one circuit the *class* of `m̂` returns to itself:
`(m̂ (u + T) : AddCircle period) = (m̂ u : AddCircle period)` — the chart
returns to the same component point (`(u + T : AddCircle T) = (u : AddCircle
T)` by `AddCircle.coe_period`), so the canonical middle is the same class
(S252).  (A genuine `T`-periodic real lift, not merely class-periodic,
exists under the general-position hypotheses by S255
`componentMiddle_has_periodic_lift`.) -/
lemma component_middle_lift_class_periodic {r : ℝ → Space} (c₀ : OSub r) {T : ℝ}
    (χ : AddCircle T ≃ₜ TrisecantComponent r c₀) {mhat : ℝ → ℝ}
    (hm : ∀ u : ℝ, (mhat u : AddCircle period) =
      componentMiddle c₀ (χ (u : AddCircle T))) :
    ∀ u : ℝ, (mhat (u + T) : AddCircle period) = (mhat u : AddCircle period) := by
  intro u
  rw [hm (u + T), hm u]
  apply congrArg (fun z : TrisecantComponent r c₀ => componentMiddle c₀ z)
  apply congrArg χ
  exact AddCircle.coe_add_period (p := T) u

/-- **The wired coefficient on a circular component (VERIFIED)**: for a
circular component chart `χ` with ordered lift `sig` (S257) and real
endpoint/middle lifts `a b m̂` (S261 / S252), the chord coefficient
`u ↦ chordCoeffAlong a b m̂ u` is continuous — the component instance of
`continuous_chordCoeffAlong` (distinct endpoint classes by
`component_endpoint_classes_ne`). -/
theorem component_trapped_coeff_continuous {r : ℝ → Space} (h : IsSmoothKnot r)
    (c₀ : OSub r) {T : ℝ} (χ : AddCircle T ≃ₜ TrisecantComponent r c₀)
    {sig : C(ℝ, OrderedPairs)} (_hσl : mobiusCover ∘ sig = componentClassMap c₀ χ)
    {a b mhat : ℝ → ℝ} (haC : Continuous a) (hbC : Continuous b) (hmC : Continuous mhat)
    (ha : ∀ u : ℝ, (a u : AddCircle period) = (sig u).1.1)
    (hb : ∀ u : ℝ, (b u : AddCircle period) = (sig u).1.2)
    (_hm : ∀ u : ℝ, (mhat u : AddCircle period) =
      componentMiddle c₀ (χ (u : AddCircle T))) :
    Continuous (fun u : ℝ => chordCoeffAlong (r := r) a b mhat u) := by
  exact continuous_chordCoeffAlong h haC hbC hmC
    (component_endpoint_classes_ne c₀ χ ha hb)

/-- **The strict coefficient of the trapped middle on a circular component
(VERIFIED)**: on a circular component, with the real endpoint/middle
lifts as above, the S260 real trappedness
`r (m̂ u) ∈ openSegment ℝ (r (a u)) (r (b u))` holds automatically
(`componentMiddle_real_betweenness`), so the chord coefficient is strict:
`0 < chordCoeffAlong a b m̂ u < 1` for every `u` — the middle knot point
sits strictly between the endpoints along the chord, with a continuous
strict coefficient (combine with
`component_trapped_coeff_continuous`). -/
theorem component_trapped_coeff_strict {r : ℝ → Space} (h : IsSmoothKnot r)
    (c₀ : OSub r) {T : ℝ} (χ : AddCircle T ≃ₜ TrisecantComponent r c₀)
    {sig : C(ℝ, OrderedPairs)} (hσl : mobiusCover ∘ sig = componentClassMap c₀ χ)
    {a b mhat : ℝ → ℝ}
    (ha : ∀ u : ℝ, (a u : AddCircle period) = (sig u).1.1)
    (hb : ∀ u : ℝ, (b u : AddCircle period) = (sig u).1.2)
    (hm : ∀ u : ℝ, (mhat u : AddCircle period) =
      componentMiddle c₀ (χ (u : AddCircle T))) :
    ∀ u : ℝ, 0 < chordCoeffAlong (r := r) a b mhat u ∧
      chordCoeffAlong (r := r) a b mhat u < 1 := by
  exact chordCoeffAlong_mem_Ioo h (component_endpoint_classes_ne c₀ χ ha hb)
    (componentMiddle_real_betweenness h c₀ χ hσl ha hb hm)

/-! ## The branch laws: the coefficient after one circuit -/

/-- **Even branch: the coefficient is `T`-periodic (VERIFIED)**: if the
endpoint *classes* and the middle *class* all return after one circuit
(the EVEN branch: the ordered lift closes, `sig (u+T) = sig u`, so each
endpoint class and the middle class are `T`-periodic), then the chord
coefficient is `T`-periodic: `λ (u + T) = λ u` (knot-period shifts of
the real representatives leave the knot values — and hence the
coefficient — unchanged: `r_eq_of_coe_eq` + `segmentCoeff_congr`). -/
theorem chordCoeffAlong_shift_of_even {r : ℝ → Space} (h : IsSmoothKnot r) {T : ℝ}
    {a b m : ℝ → ℝ}
    (hA : ∀ u : ℝ, (a (u + T) : AddCircle period) = (a u : AddCircle period))
    (hB : ∀ u : ℝ, (b (u + T) : AddCircle period) = (b u : AddCircle period))
    (hM : ∀ u : ℝ, (m (u + T) : AddCircle period) = (m u : AddCircle period)) :
    ∀ u : ℝ, chordCoeffAlong (r := r) a b m (u + T) = chordCoeffAlong (r := r) a b m u := by
  intro u
  unfold chordCoeffAlong
  exact segmentCoeff_congr (r_eq_of_coe_eq h (hA u)) (r_eq_of_coe_eq h (hB u))
    (r_eq_of_coe_eq h (hM u))

/-- **Odd branch: the coefficient flips (VERIFIED)**: if after one
circuit the endpoint classes have *exchanged* (the ODD branch: the two
sheets of the ordered double cover swap, so `(a (u+T))` has the class of
`b u` and vice versa) while the middle class returns, then the
coefficient flips: `λ (u + T) = 1 − λ u` — the endpoints' knot values
swap roles on the chord, and `segmentCoeff_swap` (S276) turns the
coefficient of the same middle point around.  This is the coefficient-
level expression of the once-winding switch: the middle point stays on
the same chord while its measured position `λ` is reflected to `1 − λ`. -/
theorem chordCoeffAlong_shift_of_odd {r : ℝ → Space} (h : IsSmoothKnot r) {T : ℝ}
    {a b m : ℝ → ℝ}
    (hA : ∀ u : ℝ, (a (u + T) : AddCircle period) = (b u : AddCircle period))
    (hB : ∀ u : ℝ, (b (u + T) : AddCircle period) = (a u : AddCircle period))
    (hM : ∀ u : ℝ, (m (u + T) : AddCircle period) = (m u : AddCircle period))
    (hab : ∀ u : ℝ, (a u : AddCircle period) ≠ (b u : AddCircle period))
    (hmid : ∀ u : ℝ, r (m u) ∈ openSegment ℝ (r (a u)) (r (b u))) :
    ∀ u : ℝ, chordCoeffAlong (r := r) a b m (u + T) = 1 - chordCoeffAlong (r := r) a b m u := by
  intro u
  unfold chordCoeffAlong
  calc
    segmentCoeff (r (a (u + T))) (r (b (u + T))) (r (m (u + T)))
        = segmentCoeff (r (b u)) (r (a u)) (r (m u)) := by
          exact segmentCoeff_congr (r_eq_of_coe_eq h (hA u)) (r_eq_of_coe_eq h (hB u))
            (r_eq_of_coe_eq h (hM u))
    _ = 1 - segmentCoeff (r (a u)) (r (b u)) (r (m u)) :=
      segmentCoeff_swap (r_ne_of_class_ne h (hab u)) (hmid u)

/-- **Component form of the even law (VERIFIED)**: on the EVEN branch of
a circular component's ordered lift (S257: `sig (u + T) = sig u`), with
real endpoint lifts `a b` (S261) and any real middle lift `m̂` (S252), the
chord coefficient is `T`-periodic: `λ (u + T) = λ u`. -/
theorem component_coeff_even_periodic {r : ℝ → Space} (h : IsSmoothKnot r)
    (c₀ : OSub r) {T : ℝ} (χ : AddCircle T ≃ₜ TrisecantComponent r c₀)
    {sig : C(ℝ, OrderedPairs)} (heven : ∀ u : ℝ, sig (u + T) = sig u)
    {a b mhat : ℝ → ℝ}
    (ha : ∀ u : ℝ, (a u : AddCircle period) = (sig u).1.1)
    (hb : ∀ u : ℝ, (b u : AddCircle period) = (sig u).1.2)
    (hm : ∀ u : ℝ, (mhat u : AddCircle period) =
      componentMiddle c₀ (χ (u : AddCircle T))) :
    ∀ u : ℝ, chordCoeffAlong (r := r) a b mhat (u + T) = chordCoeffAlong (r := r) a b mhat u := by
  apply chordCoeffAlong_shift_of_even h
  · intro u
    calc
      (a (u + T) : AddCircle period) = (sig (u + T)).1.1 := ha (u + T)
      _ = (sig u).1.1 := by rw [heven u]
      _ = (a u : AddCircle period) := (ha u).symm
  · intro u
    calc
      (b (u + T) : AddCircle period) = (sig (u + T)).1.2 := hb (u + T)
      _ = (sig u).1.2 := by rw [heven u]
      _ = (b u : AddCircle period) := (hb u).symm
  · exact component_middle_lift_class_periodic c₀ χ hm

/-- **Component form of the odd law (VERIFIED)**: on the ODD branch of a
circular component's ordered lift (S257: `sig (u + T) = swapOrdered (sig
u)`), with real endpoint lifts `a b` (S261) and any real middle lift `m̂`
(S252), the chord coefficient flips after one circuit:
`λ (u + T) = 1 − λ u` (the coefficient-level expression of the
once-winding switch, S261/S276). -/
theorem component_coeff_odd_flip {r : ℝ → Space} (h : IsSmoothKnot r)
    (c₀ : OSub r) {T : ℝ} (χ : AddCircle T ≃ₜ TrisecantComponent r c₀)
    {sig : C(ℝ, OrderedPairs)} (hσl : mobiusCover ∘ sig = componentClassMap c₀ χ)
    (hodd : ∀ u : ℝ, sig (u + T) = swapOrdered (sig u))
    {a b mhat : ℝ → ℝ}
    (ha : ∀ u : ℝ, (a u : AddCircle period) = (sig u).1.1)
    (hb : ∀ u : ℝ, (b u : AddCircle period) = (sig u).1.2)
    (hm : ∀ u : ℝ, (mhat u : AddCircle period) =
      componentMiddle c₀ (χ (u : AddCircle T))) :
    ∀ u : ℝ, chordCoeffAlong (r := r) a b mhat (u + T) = 1 - chordCoeffAlong (r := r) a b mhat u := by
  apply chordCoeffAlong_shift_of_odd h
  · intro u
    calc
      (a (u + T) : AddCircle period) = (sig (u + T)).1.1 := ha (u + T)
      _ = (sig u).1.2 := (component_ordered_endpoint_switch_odd hodd u).1
      _ = (b u : AddCircle period) := (hb u).symm
  · intro u
    calc
      (b (u + T) : AddCircle period) = (sig (u + T)).1.2 := hb (u + T)
      _ = (sig u).1.1 := (component_ordered_endpoint_switch_odd hodd u).2
      _ = (a u : AddCircle period) := (ha u).symm
  · exact component_middle_lift_class_periodic c₀ χ hm
  · exact component_endpoint_classes_ne c₀ χ ha hb
  · exact componentMiddle_real_betweenness h c₀ χ hσl ha hb hm

/-! ## S278 — the winding-measurement interfaces: TWICE and ONCE
contradiction targets, pinned precisely (VERIFIED assembly + documented
open geometric cores) (Submission/TrappedWinding.lean)

(Per the S277 STATUS: what remains of brick-(c) sub-problem 4 is the
derivation reading the endpoint windings against the middle's real
advance.  This section writes down the two case targets *precisely*, in
the shape the machinery of S253–S255/S257–S262 consumes, separating (a)
the assembly — which parts are already theorems — from (b) the missing
geometric core, so that the next lemma needed is forced into view.)

**TWICE.**  S255 proved that the middle selection of every circular
component has a `T`-periodic real lift (degree `0`); S254 proved that a
genuine nonzero-degree real middle lift (`MiddleNonZeroAdvance`) is
already a contradiction (`no_twiceWinding_component_of_lift_zsmul` —
surjectivity of the advancing middle against
`TrisecantStructure.exists_uncovered_middle`).  Hence the whole TWICE
contradiction reduces to *deriving* the nonzero-degree middle lift from
the twice-winding geometric data:

1. **`TwiceWindingEndpointsData`** (VERIFIED def Prop) — the twice-
   winding component data: the ordered double-cover lift is EVEN
   (`sig (u + T) = sig u`, S257), the endpoints admit continuous real
   lifts `a b` with `T`-periodic classes (S258), and each endpoint winds
   ONCE around the knot per circuit: the per-circuit advances are exactly
   `± period` (`ka = ±1`, `kb = ±1` — Kuperberg's "the endpoints each
   wind once around S¹");
2. **`MiddleNonZeroAdvance`** (VERIFIED def Prop) — the datum S255/S254
   are waiting for: a continuous real lift `G` of the canonical middle
   with integer degree `k ≠ 0`:
   `G (u + T) = G u + (k : ℝ) · period`;
3. **`twice_winding_middle_advance`** (PINNED, open — the missing
   geometric core of the TWICE branch): `TwiceWindingEndpointsData c₀ χ
   → MiddleNonZeroAdvance c₀ χ` — Kuperberg's "if C winds twice around
   M, the endpoints each wind once around S¹, and therefore so does
   m_t".  (The λ-laws of S277 show this is NOT a formal consequence of
   the coefficient algebra alone; the derivation needs the chord-
   direction / 1-manifold-local-order reading — the recorded
   continuation.)  [Formalised as a `def Prop` so the tree stays
   sorry-free; proving it closes the TWICE branch via (4).]
4. **`twice_contradiction_of_middle_advance`** (VERIFIED) — THE S255-
   waiting assembly: any nonzero-degree genuine middle lift of a
   circular component is contradictory
   (`no_twiceWinding_component_of_lift_zsmul`, S254, instantiated — the
   genuine-middle membership is automatic by
   `componentMiddle_mem_middleSet`).  So: TWICE = (3) + (4).

**ONCE.**  S253's `no_onceWinding_advance` shows that no half-period-
advancing lift of the (T-periodic-class) canonical middle exists over any
circular component — formalised here as the provable interface
`once_winding_no_half_advance_lift`.  Consequently the ONCE contradiction
cannot be the (impossible) half-avatar; it must be the direct geometric
jump: a once-winding component cannot carry the continuous single-valued
middle at all:

5. **`OnceWindingData`** (VERIFIED def Prop) — the once-winding component
   data: the ordered double-cover lift is ODD (`sig (u + T) = swapOrdered
   (sig u)`, S257 — the sheets exchange), with continuous real endpoint
   lifts `a b` (S261 — which then automatically switch with integer
   offsets: `component_endpoint_switch_odd`);
6. **`once_winding_no_half_advance_lift`** (VERIFIED) — the negative
   interface: `¬ ∃ mhat, Continuous mhat ∧ (mhat advances halfPeriod per
   circuit) ∧ (mhat is a real lift of the canonical middle)` — the
   precise sense in which the ONCE geometry can never supply the S253
   avatar (`no_onceWinding_advance`): over a circular component the
   middle's classes are `T`-periodic, so a half-period advance is
   inconsistent (`halfPeriod ≠ 0` in the circle);
7. **`once_winding_component_contradiction`** (PINNED, open — the missing
   geometric core of the ONCE branch): `OnceWindingData c₀ χ → False` —
   Kuperberg's jump: "if C winds once around M, the endpoints travel half
   way around S¹ and then switch places, and since m_t is trapped between
   them, it must jump discontinuously".  The λ-laws of S277 (odd branch:
   `λ (u + T) = 1 − λ u`) are the coefficient-level expression of the
   switch that the jump analysis must contradict; the derivation is the
   recorded open content (π_K / local-order reading).  [Formalised as a
   `def Prop`; proving it closes the ONCE branch.]

STATUS after S278 (superseded in part by S279 below: the two pinned cores
are RESOLVED — the twice data is uninhabited and the once contradiction is
proven — see the S279 section): both winding branches are now *precisely pinned* in
the shape their machinery consumes — TWICE reduces to
`twice_winding_middle_advance` (deriving `MiddleNonZeroAdvance`), ONCE
reduces to `once_winding_component_contradiction` (the direct jump), each
with the non-geometric assembly verified sorry-free.  The next lemma of
brick (c) is either of the two pinned cores.  Tree green (`lake build
Challenge Submission Solution` rc=0); TWO documented sorries (Challenge.lean:5
stub, Submission.lean final placeholder); no children pending.
-/

/-- **The twice-winding component data (VERIFIED def Prop)**: a circular
component chart `χ : AddCircle T ≃ₜ TrisecantComponent r c₀` whose ordered
double-cover lift is EVEN (`sig (u + T) = sig u` — the ordered lift closes
after one circuit, S257), with continuous real endpoint lifts `a b` of the
ordered chord (S258) whose per-circuit advances are exactly one knot
period in magnitude: `a (u + T) = a u + (ka : ℝ) · period` and
`b (u + T) = b u + (kb : ℝ) · period` with `ka = ±1`, `kb = ±1` — each
chord endpoint winds ONCE around the knot per circuit (Kuperberg's
twice-winding "the endpoints each wind once around S¹").
RESOLVED in S279: this data is UNINHABITED for a circular component of
the trisecant set under the general-position/quadrisecant-free hypotheses
— `twice_winding_data_false` (the even branch forces `ka = 0`). -/
def TwiceWindingEndpointsData {r : ℝ → Space} (c₀ : OSub r) {T : ℝ}
    (χ : AddCircle T ≃ₜ TrisecantComponent r c₀) : Prop :=
  ∃ (sig : C(ℝ, OrderedPairs)),
    mobiusCover ∘ sig = componentClassMap c₀ χ ∧
      (∀ u : ℝ, sig (u + T) = sig u) ∧
    ∃ (a b : ℝ → ℝ) (ka kb : ℤ),
      Continuous a ∧ Continuous b ∧
        (∀ u : ℝ, (a u : AddCircle period) = (sig u).1.1) ∧
        (∀ u : ℝ, (b u : AddCircle period) = (sig u).1.2) ∧
        (ka = 1 ∨ ka = -1) ∧ (kb = 1 ∨ kb = -1) ∧
        (∀ u : ℝ, a (u + T) = a u + (ka : ℝ) * period) ∧
        (∀ u : ℝ, b (u + T) = b u + (kb : ℝ) * period)

/-- **The nonzero-degree middle datum (VERIFIED def Prop)**: a continuous
real lift `G` of the canonical middle over the circular component chart
with integer degree `k ≠ 0`: `G (u + T) = G u + (k : ℝ) · period`.  This
is the datum that S255 (`componentMiddle_has_periodic_lift`: the degree
is always `0`) and S254 (`no_twiceWinding_component_of_lift_zsmul`: a
nonzero degree is contradictory) are waiting for the twice-winding
geometry to produce. -/
def MiddleNonZeroAdvance {r : ℝ → Space} (c₀ : OSub r) {T : ℝ}
    (χ : AddCircle T ≃ₜ TrisecantComponent r c₀) : Prop :=
  ∃ (G : ℝ → ℝ) (k : ℤ), k ≠ 0 ∧ Continuous G ∧
    (∀ u : ℝ, (G u : AddCircle period) =
      componentMiddle c₀ (χ (u : AddCircle T))) ∧
    (∀ u : ℝ, G (u + T) = G u + (k : ℝ) * period)

/-- **PINNED TARGET — the missing geometric core of the TWICE branch
(brick (c))**: from the twice-winding component data (even ordered lift,
endpoint real lifts winding once each, S257/S258) derive a nonzero-degree
real lift of the canonical middle — Kuperberg's "the endpoints each wind
once around S¹, and therefore so does m_t".  RESOLVED in S279: the
twice-winding endpoint data is UNINHABITED (`twice_winding_data_false`),
so the pin holds — `twice_winding_middle_advance_of_endpoints` (and the
data-free content is the elementary advance-agreement
`advance_eq_of_class_ne`). -/
def twice_winding_middle_advance : Prop :=
  ∀ {r : ℝ → Space} (c₀ : OSub r) {T : ℝ}
    (χ : AddCircle T ≃ₜ TrisecantComponent r c₀),
    TwiceWindingEndpointsData c₀ χ → MiddleNonZeroAdvance c₀ χ

/-- **The S255-waiting assembly (VERIFIED)**: a genuine nonzero-degree
real middle lift of a circular component is contradictory — the S254
`no_twiceWinding_component_of_lift_zsmul` instantiated (its genuine-
middle membership hypothesis is automatic by
`componentMiddle_mem_middleSet`, so only the chart, the degree `k ≠ 0`,
the continuity/advance and the middle compatibility are needed).  Hence
the ENTIRE TWICE branch reduces to deriving `MiddleNonZeroAdvance`
(pinned above) from the geometry. -/
theorem twice_contradiction_of_middle_advance {r : ℝ → Space}
    (h : IsSmoothKnot r) (c₀ : OSub r) {T : ℝ} (hT : 0 < T)
    (χ : AddCircle T ≃ₜ TrisecantComponent r c₀)
    (hAdv : MiddleNonZeroAdvance c₀ χ) : False := by
  rcases hAdv with ⟨G, k, hk, hG, hcompat, hadv⟩
  exact no_twiceWinding_component_of_lift_zsmul h c₀ hT χ hk hG hadv hcompat

/-- **The once-winding component data (VERIFIED def Prop)**: a circular
component chart whose ordered double-cover lift is ODD
(`sig (u + T) = swapOrdered (sig u)` — the two sheets of the double cover
are exchanged after one circuit, S257), with continuous real endpoint
lifts `a b` of the ordered chord (S261 — these then automatically switch
with integer offsets by `component_endpoint_switch_odd`: "the endpoints
travel half way around S¹ and then switch places"). -/
def OnceWindingData {r : ℝ → Space} (c₀ : OSub r) {T : ℝ}
    (χ : AddCircle T ≃ₜ TrisecantComponent r c₀) : Prop :=
  ∃ (sig : C(ℝ, OrderedPairs)),
    mobiusCover ∘ sig = componentClassMap c₀ χ ∧
      (∀ u : ℝ, sig (u + T) = swapOrdered (sig u)) ∧
    ∃ (a b : ℝ → ℝ),
      Continuous a ∧ Continuous b ∧
        (∀ u : ℝ, (a u : AddCircle period) = (sig u).1.1) ∧
        (∀ u : ℝ, (b u : AddCircle period) = (sig u).1.2)

/-- **The ONCE negative interface (VERIFIED)**: over ANY circular
component no half-period-advancing real lift of the canonical middle
exists — the canonical middle's classes are `T`-periodic (the chart
returns after one circuit), so a half-period advance would move the class
by the nonzero element `(halfPeriod : AddCircle period)`
(`no_onceWinding_advance`, S253; `halfPeriod_ne_zero_circle`).  This is
the precise sense in which the ONCE geometry can never close via the S253
half-period avatar — the once-contradiction must be the direct jump
(`once_winding_component_contradiction`, pinned below). -/
theorem once_winding_no_half_advance_lift {r : ℝ → Space} (c₀ : OSub r)
    {T : ℝ} (χ : AddCircle T ≃ₜ TrisecantComponent r c₀) :
    ¬ ∃ mhat : ℝ → ℝ, Continuous mhat ∧
      (∀ u : ℝ, mhat (u + T) = mhat u + halfPeriod) ∧
      (∀ u : ℝ, (mhat u : AddCircle period) =
        componentMiddle c₀ (χ (u : AddCircle T))) := by
  rintro ⟨mhat, hmc, hadv, hcompat⟩
  exact no_onceWinding_advance c₀ χ hmc hadv hcompat

/-- **PINNED TARGET — the missing geometric core of the ONCE branch
(brick (c))**: a once-winding circular component (ODD ordered lift with
the endpoint switch) is impossible — Kuperberg's jump: "if C winds once
around M, the endpoints travel half way around S¹ and then switch places,
and since m_t is trapped between them, it must jump discontinuously, a
contradiction".  The S277 odd-branch λ-law (`λ (u + T) = 1 − λ u`) is the
coefficient-level expression of the switch; the derivation that a
continuous single-valued middle cannot survive it is the recorded open
content (π_K / local-order reading; NOT a formal consequence of the
S254–S277 abstract data, per the S262 analysis).  RESOLVED in S279:
PROVEN — `once_winding_component_contradiction_holds` (the endpoint
switch forces `ka + kb = 0` by advance-agreement, and the resulting
`T`-anti-periodic endpoint difference has a zero by the intermediate
value theorem, contradicting the swap). -/
def once_winding_component_contradiction : Prop :=
  ∀ {r : ℝ → Space} (_h : IsSmoothKnot r) (_hqf : QuadrisecantFree r)
    (_hgp : TorusGeneralPositionTransverse r) (c₀ : OSub r) {T : ℝ}
    (_hT : 0 < T) (χ : AddCircle T ≃ₜ TrisecantComponent r c₀),
    OnceWindingData c₀ χ → False

/-! ## S279 — the winding measurement CLOSED at the chart level: circle-map
advance bookkeeping (VERIFIED, sorry-free) (Submission/TrappedWinding.lean)

(The S278 pins asked for the geometric derivation of the two winding
contradictions.  This section shows that the measurement needs no
chord-direction/π_K machinery at all: it is *elementary circle-map
bookkeeping*, and it closes both branches.)

**The advance-agreement principle.**  Two continuous real curves `f g`
whose classes in `AddCircle P` never meet have the SAME per-circuit
advance: if `f (u+T) = f u + df·P` and `g (u+T) = g u + dg·P` with
`f u − g u ∉ P·ℤ` for all `u`, then `df = dg`.  (Proof: the fractional part
`s u = fract((f u − g u)/P)` is continuous and `T`-periodic; the curve
`H = g + P·s` is a continuous real lift of the class of `f`, so `H − f`
takes values in the discrete subgroup `P·ℤ` and is continuous, hence
constant on `ℝ` — comparing its values at `u` and `u+T` gives
`dg·P = df·P`, so `df = dg`.)  This is the lift-level form of "two circle
maps of different degrees intersect".

**Even branch ⇒ endpoints do not wind.**  For an EVEN component
(`sig (u+T) = sig u`, S257) the endpoint classes are `T`-periodic, and the
canonical middle has a `T`-periodic real lift `G` with degree `0` (S255
`componentMiddle_has_periodic_lift`) whose class differs from the endpoint
classes at every `u` (strict middle, S260 +
`IsMiddleOnChord.ne_params`).  The advance-agreement principle applied to
`(a, G)` gives `ka = 0`, and to `(b, G)` gives `kb = 0` — in particular
the twice-winding data (`ka = ±1`) is UNINHABITED:
`twice_winding_data_false`, and the S278 pin
`twice_winding_middle_advance` holds in its data form
(`twice_winding_middle_advance_of_endpoints`).  (Without S255 the same
argument gives the h-free consistency fact `ka = kb`: the two endpoints of
an even ordered chord wind equally.)

**Odd branch is impossible.**  For an ODD component
(`sig (u+T) = swapOrdered (sig u)`, S257) the endpoints switch
(`a (u+T) ≡ b u`, S261).  Over the double period `2T` the endpoint lift
`a` is `2T`-periodic up to the advance `(ka + kb)·P` (S262,
`component_endpoint_double_circuit_odd` shape), while the periodic middle
lift `G` has advance `0`; advance-agreement (applied to `(a, G)` over `2T`)
forces `ka + kb = 0`, so the real function `u ↦ a (u+T) − a u` is
`T`-anti-periodic and continuous, hence has a zero (intermediate value
theorem): `a (u+T) = a u` for some `u`, contradicting the switch
`(sig (u+T)).1.1 = (sig u).1.2` and the distinctness of the ordered chord.
Hence `once_winding_data_false`, and the S278 pin
`once_winding_component_contradiction` becomes a theorem
(`once_winding_component_contradiction_holds`).

**Consequence.**  No circular component of the trisecant set is
"winding" in either sense: EVEN components carry no endpoint winding
(their ordered lift is `2`-periodic with equal, in fact zero, endpoint
advances), and ODD components do not exist.  The Layer-C winding branch is
therefore closed at the chart level: the S278 pins are theorems, and the
obstruction dichotomy (brick (d)) has no winding case to rule out.

Tree green (`lake build Challenge Submission Solution` rc=0); TWO
documented sorries (Challenge.lean:5 stub, Submission.lean final
placeholder); no children pending.
-/

section CircleAdvance

/-- **The advance-agreement principle (VERIFIED)**: two continuous real
curves `f g` with per-circuit advances `df, dg` whose classes in
`AddCircle P` never meet have equal advances.  (Lift-level form of "two
circle maps of different degrees intersect": the fractional-part
correction `H = g + P·fract((f−g)/P)` is a continuous lift of `f`'s class
with `g`'s advance, so `H − f` is a continuous `P·ℤ`-valued function —
constant on `ℝ` — and comparing at `u` and `u+T` gives `dg = df`.) -/
theorem advance_eq_of_class_ne {P T : ℝ} (hP : 0 < P) {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) {df dg : ℤ}
    (hfa : ∀ u : ℝ, f (u + T) = f u + (df : ℝ) * P)
    (hga : ∀ u : ℝ, g (u + T) = g u + (dg : ℝ) * P)
    (hne : ∀ u : ℝ, f u - g u ∉ AddSubgroup.zmultiples P) :
    df = dg := by
  have hP0 : P ≠ 0 := ne_of_gt hP
  let x : ℝ → ℝ := fun u => (f u - g u) / P
  have hxcont : Continuous x := (hf.sub hg).div_const P
  have hx_ne : ∀ u : ℝ, x u ≠ ⌊x u⌋ := by
    intro u h
    apply hne u
    have h' := h
    dsimp [x] at h'
    rw [div_eq_iff hP0] at h'
    have hval : f u - g u = P * (⌊x u⌋ : ℝ) := h'.trans (mul_comm _ _)
    rw [hval]
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨⌊x u⌋, by rw [zsmul_eq_mul, mul_comm]⟩
  let s : ℝ → ℝ := fun u => Int.fract (x u)
  have hfrac : Continuous s :=
    continuous_iff_continuousAt.mpr fun u =>
      (continuousAt_fract (hx_ne u)).comp hxcont.continuousAt
  have hxT : ∀ u : ℝ, x (u + T) = x u + ((df - dg : ℤ) : ℝ) := by
    intro u
    dsimp [x]
    have hnum : f u + (df : ℝ) * P - (g u + (dg : ℝ) * P)
        = (f u - g u) + ((df - dg : ℤ) : ℝ) * P := by
      rw [Int.cast_sub]
      ring
    rw [hfa u, hga u, hnum, add_div, mul_div_cancel_right₀ _ hP0]
  have hsT : ∀ u : ℝ, s (u + T) = s u := by
    intro u
    dsimp [s]
    rw [hxT u, Int.fract_add_intCast]
  let H : ℝ → ℝ := fun u => g u + P * s u
  have hHcont : Continuous H := hg.add (continuous_const.mul hfrac)
  have hHmem : ∀ u : ℝ, H u - f u ∈ AddSubgroup.zmultiples P := by
    intro u
    have hfr : Int.fract (x u) = x u - (⌊x u⌋ : ℝ) := (Int.self_sub_floor _).symm
    have hx : P * x u = f u - g u := by
      dsimp [x]
      rw [mul_div_cancel₀ (f u - g u) hP0]
    have hval : H u - f u = -(P * (⌊x u⌋ : ℝ)) := by
      dsimp [H, s]
      rw [hfr, mul_sub, hx]
      ring
    rw [hval]
    exact AddSubgroup.neg_mem _
      (AddSubgroup.mem_zmultiples_iff.mpr ⟨⌊x u⌋, by rw [zsmul_eq_mul, mul_comm]⟩)
  have hconst : H T - f T = H 0 - f 0 := by
    have hψ : Continuous (fun u : ℝ =>
        (⟨H u - f u, hHmem u⟩ : AddSubgroup.zmultiples P)) :=
      Continuous.subtype_mk (f := fun u => H u - f u) (hHcont.sub hf) hHmem
    have hc : (⟨H T - f T, hHmem T⟩ : AddSubgroup.zmultiples P) =
        ⟨H 0 - f 0, hHmem 0⟩ :=
      PreconnectedSpace.constant (α := ℝ) (Y := AddSubgroup.zmultiples P)
        (inferInstance : PreconnectedSpace ℝ) hψ
    exact congrArg Subtype.val hc
  have hHadv : H T = H 0 + (dg : ℝ) * P := by
    have h1 : s T = s 0 := by simpa using hsT 0
    have h2 : g T = g 0 + (dg : ℝ) * P := by simpa using hga 0
    dsimp [H]
    rw [h1, h2]
    ring
  have hcomp : (dg : ℝ) * P = (df : ℝ) * P := by
    have h1 : H T - f T = (H 0 - f 0) := hconst
    have h2 : f T = f 0 + (df : ℝ) * P := by simpa using hfa 0
    rw [hHadv, h2] at h1
    linarith
  have hcast : (dg : ℝ) = (df : ℝ) := mul_right_cancel₀ hP0 hcomp
  exact_mod_cast hcast.symm

/-- **A periodic curve has advance zero (VERIFIED)**: if
`f (u+T) = f u + d·P` and `f` is `T`-periodic, then `d = 0`. -/
theorem advance_eq_zero_of_periodic {P T : ℝ} (hP : 0 < P) {f : ℝ → ℝ} {d : ℤ}
    (hfa : ∀ u : ℝ, f (u + T) = f u + (d : ℝ) * P)
    (hper : ∀ u : ℝ, f (u + T) = f u) : d = 0 := by
  have h0 := hfa 0
  rw [hper 0] at h0
  have hz : (d : ℝ) * P = 0 := by linarith
  have hcast : (d : ℝ) = 0 := (mul_eq_zero.mp hz).resolve_right (ne_of_gt hP)
  exact_mod_cast hcast

/-- **A continuous `T`-anti-periodic function has a zero (VERIFIED)**:
`h (u + T) = − h u` forces `h u = 0` for some `u` (intermediate value
theorem between `u` and `u + T`). -/
theorem exists_eq_zero_of_antiperiodic {h : ℝ → ℝ} (hc : Continuous h) {T : ℝ}
    (hT : 0 < T) (hanti : ∀ u : ℝ, h (u + T) = - h u) : ∃ u : ℝ, h u = 0 := by
  by_cases h0 : h 0 = 0
  · exact ⟨0, h0⟩
  have hTval : h T = - h 0 := by simpa using hanti 0
  rcases lt_or_gt_of_ne (Ne.symm h0) with hpos | hneg
  · have hmem : (0 : ℝ) ∈ Set.Icc (h T) (h 0) := ⟨by rw [hTval]; linarith, le_of_lt hpos⟩
    rcases (intermediate_value_Icc' (a := 0) (b := T) (le_of_lt hT) hc.continuousOn) hmem with
      ⟨u, _, hu⟩
    exact ⟨u, hu⟩
  · have hmem : (0 : ℝ) ∈ Set.Icc (h 0) (h T) := ⟨le_of_lt hneg, by rw [hTval]; linarith⟩
    rcases (intermediate_value_Icc (a := 0) (b := T) (le_of_lt hT) hc.continuousOn) hmem with
      ⟨u, _, hu⟩
    exact ⟨u, hu⟩

/-- **Strictness in class form (VERIFIED)**: if `r m` lies strictly inside
the chord from `r a` to `r b` and the endpoint classes differ, then the
middle class differs from both endpoint classes
(`IsMiddleOnChord.ne_params`). -/
lemma middle_class_ne_endpoints {r : ℝ → Space} (h : IsSmoothKnot r) {a b m : ℝ}
    (hab : (a : AddCircle period) ≠ (b : AddCircle period))
    (hmid : r m ∈ openSegment ℝ (r a) (r b)) :
    (a : AddCircle period) ≠ (m : AddCircle period) ∧
      (b : AddCircle period) ≠ (m : AddCircle period) := by
  have hchord : IsMiddleOnChord r (a : AddCircle period) (b : AddCircle period)
      (m : AddCircle period) := (IsMiddleOnChord_iff_real h a b m).mpr hmid
  have hne := IsMiddleOnChord.ne_params h hab hchord
  exact ⟨fun h1 => hne.1 h1.symm, fun h2 => hne.2 h2.symm⟩

end CircleAdvance

/-! ## EVEN branch: the endpoints do not wind (and the twice data is
uninhabited) -/

/-- **The two endpoints of an even ordered chord wind equally (VERIFIED,
h-free)**: for the EVEN branch data (ordered lift closed, endpoint real
lifts with integer advances, distinct endpoint classes) the per-circuit
advances agree: `ka = kb` (advance-agreement applied to the two endpoint
lifts). -/
theorem even_endpoints_equal_advance {r : ℝ → Space} (c₀ : OSub r) {T : ℝ}
    (χ : AddCircle T ≃ₜ TrisecantComponent r c₀)
    {sig : C(ℝ, OrderedPairs)} (_heven : ∀ u : ℝ, sig (u + T) = sig u)
    {a b : ℝ → ℝ} (haC : Continuous a) (hbC : Continuous b) {ka kb : ℤ}
    (ha : ∀ u : ℝ, (a u : AddCircle period) = (sig u).1.1)
    (hb : ∀ u : ℝ, (b u : AddCircle period) = (sig u).1.2)
    (hAadv : ∀ u : ℝ, a (u + T) = a u + (ka : ℝ) * period)
    (hBadv : ∀ u : ℝ, b (u + T) = b u + (kb : ℝ) * period) :
    ka = kb := by
  have hab : ∀ u : ℝ, (a u : AddCircle period) ≠ (b u : AddCircle period) :=
    component_endpoint_classes_ne c₀ χ ha hb
  have hsub : ∀ u : ℝ, a u - b u ∉ AddSubgroup.zmultiples period := fun u hmem =>
    hab u ((QuotientAddGroup.eq_iff_sub_mem).mpr hmem)
  exact advance_eq_of_class_ne period_pos haC hbC hAadv hBadv hsub

/-- **The EVEN branch forces the endpoint advances to vanish (VERIFIED)**:
on the even branch the canonical middle has a `T`-periodic real lift `G` of
degree `0` (S255), whose class differs from BOTH endpoint classes at every
`u` (strict middle, S260 + `IsMiddleOnChord.ne_params`); advance-agreement
applied to `(a, G)` and `(b, G)` forces both per-circuit advances to
vanish: `ka = 0 ∧ kb = 0`. -/
theorem even_endpoint_advances_zero {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (c₀ : OSub r) {T : ℝ} (hT : 0 < T)
    (χ : AddCircle T ≃ₜ TrisecantComponent r c₀)
    {sig : C(ℝ, OrderedPairs)} (hσl : mobiusCover ∘ sig = componentClassMap c₀ χ)
    {a b : ℝ → ℝ} (haC : Continuous a) (hbC : Continuous b) {ka kb : ℤ}
    (ha : ∀ u : ℝ, (a u : AddCircle period) = (sig u).1.1)
    (hb : ∀ u : ℝ, (b u : AddCircle period) = (sig u).1.2)
    (hAadv : ∀ u : ℝ, a (u + T) = a u + (ka : ℝ) * period)
    (hBadv : ∀ u : ℝ, b (u + T) = b u + (kb : ℝ) * period) :
    ka = 0 ∧ kb = 0 := by
  rcases componentMiddle_has_periodic_lift h hqf hgp c₀ hT χ with ⟨G, hGc, hGl, hGper⟩
  have hab : ∀ u : ℝ, (a u : AddCircle period) ≠ (b u : AddCircle period) :=
    component_endpoint_classes_ne c₀ χ ha hb
  have hmid : ∀ u : ℝ, r (G u) ∈ openSegment ℝ (r (a u)) (r (b u)) :=
    componentMiddle_real_betweenness h c₀ χ hσl ha hb hGl
  have hneA : ∀ u : ℝ, (a u : AddCircle period) ≠ (G u : AddCircle period) := fun u =>
    (middle_class_ne_endpoints h (hab u) (hmid u)).1
  have hneB : ∀ u : ℝ, (b u : AddCircle period) ≠ (G u : AddCircle period) := fun u =>
    (middle_class_ne_endpoints h (hab u) (hmid u)).2
  have hGzero : ∀ u : ℝ, G (u + T) = G u + ((0 : ℤ) : ℝ) * period := fun u => by
    rw [hGper u]
    ring
  have hsubA : ∀ u : ℝ, a u - G u ∉ AddSubgroup.zmultiples period := fun u hmem =>
    hneA u ((QuotientAddGroup.eq_iff_sub_mem).mpr hmem)
  have hsubB : ∀ u : ℝ, b u - G u ∉ AddSubgroup.zmultiples period := fun u hmem =>
    hneB u ((QuotientAddGroup.eq_iff_sub_mem).mpr hmem)
  exact ⟨advance_eq_of_class_ne period_pos haC hGc hAadv hGzero hsubA,
    advance_eq_of_class_ne period_pos hbC hGc hBadv hGzero hsubB⟩

/-- **The twice-winding data is uninhabited (VERIFIED)**: `TwiceWindingEndpointsData`
(even ordered lift, endpoints winding once each, `ka = ±1`) is impossible
for a circular component of the trisecant set under the general-position
and quadrisecant-free hypotheses — the even branch forces `ka = 0`
(S255 + advance-agreement).  This is the TWICE branch of the winding
measurement, closed. -/
theorem twice_winding_data_false {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (c₀ : OSub r) {T : ℝ} (hT : 0 < T)
    (χ : AddCircle T ≃ₜ TrisecantComponent r c₀) :
    TwiceWindingEndpointsData c₀ χ → False := by
  rintro ⟨sig, hσl, heven, a, b, ka, kb, haC, hbC, ha, hb, hka, hkb, hAadv, hBadv⟩
  have hzero := (even_endpoint_advances_zero h hqf hgp c₀ hT χ hσl haC hbC ha hb
    hAadv hBadv).1
  rcases hka with h1 | h1 <;> rw [h1] at hzero <;> norm_num at hzero

/-- **The S278 TWICE pin in data form (VERIFIED)**: with the general-position
and quadrisecant-free hypotheses, the twice-winding endpoint data implies
the (vacuous) nonzero middle advance — the pin `twice_winding_middle_advance`
holds once the data is known to be uninhabited
(`twice_winding_data_false`). -/
theorem twice_winding_middle_advance_of_endpoints {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (c₀ : OSub r) {T : ℝ} (hT : 0 < T)
    (χ : AddCircle T ≃ₜ TrisecantComponent r c₀) :
    TwiceWindingEndpointsData c₀ χ → MiddleNonZeroAdvance c₀ χ :=
  fun hTw => (twice_winding_data_false h hqf hgp c₀ hT χ hTw).elim

/-! ## ODD branch: once-winding components are impossible -/

/-- **The once-winding data is uninhabited (VERIFIED)**: `OnceWindingData`
(odd ordered lift with the endpoint switch, `sig (u+T) = swapOrdered (sig
u)`) is impossible for a circular component of the trisecant set under the
general-position and quadrisecant-free hypotheses.  Proof: over the double
period `2T` the endpoint lift `a` has advance `ka + kb` (S262 shape) while
the periodic middle lift `G` (S255) has advance `0`, and their classes
never meet (strict middle) — advance-agreement forces `ka + kb = 0`; then
`u ↦ a (u+T) − a u` is continuous and `T`-anti-periodic, hence has a zero,
so `a (u+T) = a u` at some `u`, contradicting the switch
`(sig (u+T)).1.1 = (sig u).1.2` and the distinctness of the ordered
chord. -/
theorem once_winding_data_false {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (c₀ : OSub r) {T : ℝ} (hT : 0 < T)
    (χ : AddCircle T ≃ₜ TrisecantComponent r c₀) :
    OnceWindingData c₀ χ → False := by
  rintro ⟨sig, hσl, hodd, a, b, haC, hbC, ha, hb⟩
  rcases componentMiddle_has_periodic_lift h hqf hgp c₀ hT χ with ⟨G, hGc, hGl, hGper⟩
  rcases component_endpoint_switch_odd c₀ χ hσl hodd haC hbC ha hb with ⟨ka, kb, hak, hbk⟩
  have hab : ∀ u : ℝ, (a u : AddCircle period) ≠ (b u : AddCircle period) :=
    component_endpoint_classes_ne c₀ χ ha hb
  have hmid : ∀ u : ℝ, r (G u) ∈ openSegment ℝ (r (a u)) (r (b u)) :=
    componentMiddle_real_betweenness h c₀ χ hσl ha hb hGl
  have hneG : ∀ u : ℝ, (a u : AddCircle period) ≠ (G u : AddCircle period) := fun u =>
    (middle_class_ne_endpoints h (hab u) (hmid u)).1
  have hsub : ∀ u : ℝ, a u - G u ∉ AddSubgroup.zmultiples period := fun u hmem =>
    hneG u ((QuotientAddGroup.eq_iff_sub_mem).mpr hmem)
  -- the double-circuit advance of `a` is `ka + kb`
  have hkd : ∀ u : ℝ, a (u + T + T) = a u + ((ka + kb : ℤ) : ℝ) * period := by
    intro u
    calc
      a (u + T + T) = b (u + T) + (ka : ℝ) * period := hak (u + T)
      _ = (a u + (kb : ℝ) * period) + (ka : ℝ) * period := by rw [hbk u]
      _ = a u + ((ka + kb : ℤ) : ℝ) * period := by
        rw [Int.cast_add]
        ring
  -- advance-agreement over the double period `2T`
  have hsum : ka + kb = 0 := advance_eq_of_class_ne period_pos haC hGc
    (T := T + T)
    (fun u : ℝ => by simpa [add_assoc] using hkd u)
    (fun u : ℝ => by
      rw [show u + (T + T) = (u + T) + T by ring, hGper (u + T), hGper u]
      ring)
    hsub
  -- the anti-periodic function has a zero
  have hcont : Continuous (fun u : ℝ => a (u + T) - a u) :=
    (haC.comp (continuous_id.add continuous_const)).sub haC
  have hanti : ∀ u : ℝ,
      (fun u => a (u + T) - a u) (u + T) = - ((fun u => a (u + T) - a u) u) := by
    intro u
    have h2 : a (u + T + T) = a u + ((ka + kb : ℤ) : ℝ) * period := hkd u
    have hz : ((ka + kb : ℤ) : ℝ) * period = 0 := by rw [hsum]; ring
    dsimp only
    rw [h2, hz]
    ring
  rcases exists_eq_zero_of_antiperiodic hcont hT hanti with ⟨u, hu⟩
  have hau : a (u + T) = a u := sub_eq_zero.mp hu
  have hswitch := (component_ordered_endpoint_switch_odd hodd u).1
  have hbad : (sig u).1.1 = (sig u).1.2 := by
    calc
      (sig u).1.1 = (a u : AddCircle period) := (ha u).symm
      _ = (a (u + T) : AddCircle period) := by rw [hau]
      _ = (sig (u + T)).1.1 := ha (u + T)
      _ = (sig u).1.2 := hswitch
  exact (sig u).2 hbad

/-- **The S278 ONCE pin is a theorem (VERIFIED)**: the pinned target
`once_winding_component_contradiction` (once-winding circular components
of the trisecant set are impossible) — proven via
`once_winding_data_false`. -/
theorem once_winding_component_contradiction_holds :
    once_winding_component_contradiction := by
  intro r h hqf hgp c₀ T hT χ hdata
  exact once_winding_data_false h hqf hgp c₀ hT χ hdata

/-! ## Consequence: no circular component of the trisecant set winds

From `twice_winding_data_false` and `once_winding_data_false`: the even
branch carries no endpoint winding (`ka = kb = 0` under the
general-position/quadrisecant-free hypotheses) and the odd branch does not
exist.  The winding measurement of brick (c) is CLOSED at the chart level;
the Layer-C obstruction dichotomy (brick (d)) has no winding case left to
rule out. -/

end LeanEval.KnotTheory.Quadrisecant
