import Mathlib
import Submission.Work.SphereJordan.SpanHyp
import Submission.Work.SphereJordan.SpanSetup
import Submission.Work.SphereJordan.tgtUpPC_isSimple
import Submission.Work.Smooth.SphereJordan.windNumber_ne_zero_of_mem_V
import Submission.Work.Smooth.SphereJordan.thetaTwoHalvesSphereOfPlane

/-!
# The plan for `Work.SphereJordan.span_pairing`

This module contains no mathematical content; it records, for the colleagues working on the two
auxiliary lemmas `Work.SphereJordan.windNumber_pairing_identities` and
`Work.SphereJordan.odd_windNumber_of_mem_V`, the exact shape of the argument and the tools that
are already available.

## The target

`Work.SphereJordan.span_pairing` states, for the four curves
`T₁ := H.upPC true`, `T₂ := H.dnPC true`, `T₃ := H.upPC false`, `T₄ := H.dnPC false`
of the two-cuts configuration (`H : SpanHyp h hs hball S`, `S : PlaneSchoenflies γ`), and for any
Schoenflies data `STu, SDu, STf, SDf` of them:

`(S.V ⊆ STu.V ↔ S.V ⊆ SDu.V) ∧ (S.V ⊆ STu.V ↔ ¬ S.V ⊆ STf.V) ∧ (S.V ⊆ SDu.V ↔ ¬ S.V ⊆ SDf.V)`.

## The reduction

Write `D := S.V` (the bounded side of `γ`), and for `x : ℂ` let

`a := windNumber (H.upPC true).γ _ x`,  `b := windNumber (H.dnPC true).γ _ x`,
`c := windNumber (H.upPC false).γ _ x`, `d := windNumber (H.dnPC false).γ _ x`,
`e := windNumber γ.γ _ x`.

**The dictionary.**  For `x` off the trace of a simple closed curve `C` with Schoenflies datum `S_C`,

* `x ∈ S_C.V ↔ windNumber C.γ _ x ≠ 0`
  — the forward direction is `Work.Smooth.SphereJordan.windNumber_ne_zero_of_mem_V`, the backward
  direction is the contrapositive of `Work.Smooth.SphereJordan.windNumber_eq_zero_of_mem_U`
  (both proved, import them from
  `Submission/Work/Smooth/SphereJordan/windNumber_ne_zero_of_mem_V.lean` and
  `Submission/Work/Smooth/SphereJordan/thetaTwoHalvesSphereOfPlane.lean`).

Moreover `D` is preconnected and (once one knows that the four traces avoid `D`) lies entirely on
one side of each of the four curves; hence it suffices to prove the dictionary for a *single*
point `x ∈ S.V`, and the whole statement becomes the purely arithmetic claim

`(a ≠ 0 ↔ b ≠ 0) ∧ (a ≠ 0 ↔ c = 0) ∧ (b ≠ 0 ↔ d = 0)`.

**The arithmetic.**  Two ingredients give this.

* (`windNumber_pairing_identities`) the three identities

  `a + d = 1`,  `b + c = 1`,  `a + b = 1 + e`.

* (`odd_windNumber_of_mem_V`) for each of the *four* curves (and for `γ` itself, whose bounded side
  contains `x`): `windNumber ≠ 0 → Odd windNumber`.

Indeed, with `d = 1 - a`, `c = 1 - b` and `e = a + b - 1 ≠ 0` (the last from the oddness for `γ`):
if `a = 0` then `d = 1`, and `b ≠ 0` would force `b` odd hence `c = 1 - b` even hence `0`, so
`b = 1 = d`, contradicting `b ≠ d` (which is `e ≠ 0`); hence in that case
`(a,b,c,d) = (0,0,1,1)`.  If `a ≠ 0` then `a` is odd, `d = 1 - a` is even hence `0`, so `b ≠ 0`
(again `b ≠ d`), `b` odd, `c = 1 - b` even hence `0`.  In both cases the three equivalences hold.

## Hints for `windNumber_pairing_identities`

All three identities have the same shape: *two of the four four-arc curves together traverse the
unit circle (plus `γ`), with the shared arcs cancelling in opposite directions*.

Concretely, `tgtUpBun`/`tgtDnBun` split into four branches on the quarters
`[0,π/2]`, `[π/2,π]`, `[π,3π/2]`, `[3π/2,2π]` (`tgtUpB_eq`, `tgtDnB_eq`, and the quarter lemmas in
`Submission/Work/SphereJordan/annulusTargetCurves.lean` / `tgtUpPC_isSimple.lean`):

* `T₁ = O ⊕ C₂ ⊕ P₁ ⊕ C₁` where `O` is the upper outer semicircle `srcOuterUp` (from `u` to `-u`,
  `u = cutDir S`), `C₂ = tgtCut₂` (from `-u` to `a₂ = γ θ₂`), `P₁` is the `γ`-arc from `a₂` to `a₁`
  (`b = true` branch, parameter `θ₂ ↦ θ₁`), `C₁ = tgtCut₁` (from `a₁` to `u`);
* `T₂ = L ⊕ C₁⁻¹ ⊕ P₂ ⊕ C₂⁻¹` (the `γ`-arc from `a₁` to `a₂`, i.e. the complement arc);
* `T₃ = O ⊕ C₂ ⊕ P₂⁻¹ ⊕ C₁` (`b = false` for the upper curve: the complement arc traversed
  backwards);
* `T₄ = L ⊕ C₁⁻¹ ⊕ P₁⁻¹ ⊕ C₂⁻¹`.

Then `T₁ ⊕ T₄ = O ⊕ L ⊕ (C₂ ⊕ C₂⁻¹) ⊕ (P₁ ⊕ P₁⁻¹) ⊕ (C₁ ⊕ C₁⁻¹)`, and each "spike" `φ ⊕ φ⁻¹` is
null-homotopic *inside the image of `φ`*, so it can be cancelled without passing through `x ∈ S.V`
as soon as the image of `φ` avoids `S.V`: true for the cuts (`H.hseg₁`, `H.hseg₂` put their
interior in `ball ∖ S.V` and their endpoints on `γ.trace`/the circle) and for the arcs `P₁`, `P₂`
(they lie in `γ.trace = frontier S.V`).  What remains is `O ⊕ L`, the unit circle, whose winding
number about any point of `S.V` is `1` (it is `1` for the standard circle about `0`, and the
straight-line homotopy `t ↦ e^{2πit} - s·x` (`1 - ‖x‖ > 0`) compares the two).

A convenient way to organise this is to prove, once and for all, the *additivity of the winding
number over concatenation of loops* (e.g. via `Work.Smooth.SphereJordan.loopIndex_mul` applied to
the pointwise product, which is homotopic to the concatenation and has index the sum, together with
the general-`θ` witness machinery of `shiftWitness.lean` for the homotopies), and then to compute
the winding number of each four-arc curve as the sum of the increments of its four arcs
(the "argument-increment" bookkeeping: the increment of `φ⁻¹` is the negative of that of `φ`, and
the increments add over concatenation).


## A concrete recipe for the `increment` bookkeeping (for `windNumber_pairing_identities`)

`Work.Smooth.SphereJordan.argChangeLift` gives, for a continuous nowhere vanishing path
`c : C(unitInterval, ℂ)`, a continuous `Λ` with `Complex.exp (Λ t) = c t`, and shows that the
*increment* `Λ 1 - Λ 0` is independent of the choice of `Λ`.  Declare

  `noncomputable def increment (c : C(unitInterval, ℂ)) (hc : ∀ t, c t ≠ 0) : ℂ :=
     (Classical.choose (argChangeLift c hc)) 1 - (Classical.choose (argChangeLift c hc)) 0`

with the specification `increment_spec` (any lift gives the same increment) and the two facts

* `increment_eq_of_closed` — for a closed loop (`c 0 = c 1`):
  `increment c hc = (loopIndex c : ℂ) * (2 * π * I)`  (this is `loopIndex_spec`);
* `increment_concat` — for `c` split at `t₀` into `c₁ = c ∘ (t ↦ t₀ t)` and
  `c₂ = c ∘ (t ↦ t₀ + (1 - t₀) t)`: `increment c hc = increment c₁ _ + increment c₂ _`
  (the lift of `c` restricted to the two halves gives lifts of the halves, and the increment is
  additive for a concatenation of paths; conversely `increment` of a constant path is `0`);
* `increment_rev` — `increment (fun t ↦ c (1 - t)) _ = - increment c _`.

The three identities are then proved by writing each loop `τ ↦ (H.upPC b) (τ) - x` (and
`τ ↦ (H.dnPC b) τ - x`) as the concatenation of its four **quarter** pieces (the branch formulas of
`tgtUpBun`/`tgtDnBun` on `[0,π/2]`, `[π/2,π]`, `[π,3π/2]`, `[3π/2,2π]`; each quarter is the
reparametrisation `t ↦ σ₀ + t (σ₁ - σ₀)` of one of the four arcs), splitting twice with
`increment_concat`, and observing that

* `tgtCut₁ S t₁ s₁` (as a path from `u` to `a₁`) and its reverse appear in the two curves of each
  pair with opposite orientations, so their increments cancel by `increment_rev`;
* same for `tgtCut₂ S t₂ s₂` (a path from `-u` to `a₂`);
* the `γ`-arcs: for `b = true`, the third quarter of `upPC true` is the path
  `t ↦ γ (θ₂ + t (θ₁ - θ₂))` from `a₂` to `a₁`, while the third quarter of `dnPC false` is its
  reverse `t ↦ γ (θ₁ + t (θ₂ - θ₁))`; for the pair `(upPC false, dnPC true)` the same cancellation
  happens for the *complementary* arc `t ↦ γ (θ₁ - 2π + t (θ₂ - θ₁ + 2π))` and its reverse
  `t ↦ γ (θ₂ + t (θ₁ - θ₂ - 2π))`;
* what is left is `srcOuterUp` (from `u` to `-u`) followed by `srcOuterDn` (from `-u` to `u`),
  i.e. the counter-clockwise unit circle `τ ↦ cutDir S * Complex.exp (τ * I)`, whose increment about
  `x` with `‖x‖ < 1` is `2 * π * I` (compare with `x = 0` by the straight-line homotopy
  `τ ↦ cutDir S * exp (τ I) - s * x`, whose norm is at least `1 - ‖x‖ > 0`); note
  `‖x‖ < 1` for `x ∈ S.V` by `Work.Smooth.SphereJordan.planeSeparation_V_subset_closedBall`
  (`Submission/Work/Smooth/SphereJordan/BoundedSide.lean`) plus openness of `S.V`.

For the third identity the remaining piece is `P₁ ⊕ P₂`, i.e. `γ` itself (the `θ₂ ↦ θ₁` arc followed
by the `θ₁ ↦ θ₂ + 2π` arc), whose increment is the increment of the loop `τ ↦ γ.γ τ - x`, i.e.
`(windNumber γ.γ γ.cont x : ℂ) * (2 * π * I)`.

## Hints for `odd_windNumber_of_mem_V`

Given `C = γ` (a simple closed plane curve) with Schoenflies datum `S` and `z ∈ S.V`:

1. `z = S.e z₀` for a unique `z₀` with `‖z₀‖ < 1` (the argument of
   `windNumber_ne_zero_of_mem_V` already produces this).
2. Let `φ θ := normCircle (S.e (circlePoint θ) - z)` (`Work.CoreTopology.normCircle`), and let
   `Λ : ℝ → ℝ` be a continuous lift (`Circle.exp (Λ θ) = φ θ`,
   `Work.Smooth.SphereJordan.hlp_exists_continuous_lift`).
3. The loop `θ ↦ S.e (circlePoint θ) - z` has the same winding number as its normalisation `φ`
   (straight-line homotopy `w ↦ (1-s) w + s w/‖w‖ = w (1 - s + s/‖w‖)`, always non-zero).
   Via `loopIndex_spec` the winding number of `φ` (as a `ℂ`-valued loop) equals `Λ (2π) - Λ 0`
   (the `ℂ`-lift of `φ` is `2π I · Λ`).
4. `Work.Smooth.SphereJordan.hlp_lift_diff_eq_of_homotopy` compares `Λ` with the lift `Λ_δ` of the
   **odd loop** `δ θ := normCircle (S.e (circlePoint θ) - S.e (circlePoint (θ + π)))` along the
   explicit homotopy `B` of `Submission/Work/Smooth/SphereJordan/disc_openImage_subset_boundedSide.lean`.
5. For the odd loop, the proof of `hlp_lift_diff_ne_zero_of_odd` in the same file shows
   `Λ_δ (2π) - Λ_δ 0 = 2 ((1 + 2k) π)` for some `k : ℤ` — extract the *form* (not just the
   non-vanishing): `Λ_δ (2π) - Λ_δ 0 = 2π (2k+1)`, which is an odd multiple of `2π`.
6. Hence `windNumber γ.γ _ z = 2k + 1` is odd.
-/

namespace Work.SphereJordan

end Work.SphereJordan
