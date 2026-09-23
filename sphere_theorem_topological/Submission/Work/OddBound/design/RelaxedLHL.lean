import Mathlib

/-!
# Design notes: the long homotopy lemma with relaxed regularity

This module has no content; it exists so that the delegated statement below can `import` it and read
this design.

## Why

`Work.OddBound.longHomotopy.long_homotopy_lower_bound` (the *halved* form of Klingenberg's long
homotopy lemma) is proved here, under the hypothesis that the whole family
`(u : ℝ × ℝ) ↦ c u.1 u.2` is jointly `C^∞` on the **whole plane** (`SmoothBasedNullHomotopy`).
The value bound of the minimax, however, must be applied to a family that has been **reparametrised
proportionally to arclength**: such a family is jointly `C^∞` only where the slices have
non-vanishing speed, and is only *continuous* at the constant slice (the stall of a slice makes the
arclength reparametrisation of a family merely continuous there).  Hence the need for the following
relaxation: the family is jointly `C^∞` on `univ ×ˢ Ico 0 1` (i.e. in a neighbourhood of every
`(s,t)` with `t < 1`) and merely continuous on the whole rectangle.

## Proof design (it is the existing proof, with a limiting step)

The existing proof of `long_homotopy_lower_bound` is:

1. lift the two families `c₁ s t := c s t` and `c₂ s t := c (1 - s) t` under `GExp p` over the
   rectangle `[0,1/2] × [0,1]`, using `Work.OddBound.longHomotopy.lift_family_of_short`, obtaining
   jointly continuous `Wp, Wm` with `GExp p (Wp s t) = c s t`, `GExp p (Wm s t) = c (1-s) t`,
   `Wp 0 t = Wm 0 t = 0` and the norm bound `‖W s t‖ ≤ curveLength (c · t) 0 s < π/√K`;
2. the two curves `t ↦ Wp (1/2) t` and `t ↦ Wm (1/2) t` are two continuous lifts under `GExp p` of
   the *same* curve `t ↦ c (1/2) t`, both staying in the ball of radius `π/√K`, where `GExp p` is a
   local diffeomorphism; uniqueness of such lifts (`Work.OddBound.longHomotopy.eq_at_zero_of_continuous_lift_eq`,
   the clopen step) gives `Wp (1/2) t = Wm (1/2) t` for all `t`;
3. at `t = 1` (the constant slice) both lifts vanish, and at `t = 0` they are the two straight rays
   of the halves of `γ` (`lift_of_geodesic_ray`), so `γ'(0) = -γ'(0)`, contradicting
   `curveVelocity γ 0 ≠ 0`.

**The relaxation.**  For each `δ > 0` restrict the family to `u.2 ≤ 1 - δ`: there it is jointly
`C^∞` (after extending it off the rectangle, e.g. constantly in `t`), so steps 1–2 apply and give
`Wp^δ(1/2) t = Wm^δ(1/2) t` for `t ∈ [0, 1-δ]`.  The norm bound `‖W(s,t)‖ ≤ curveLength (c · t) 0 s`
makes the lifts *equicontinuous* in `t` up to `t = 1` (the lengths tend to `0` there, since the
slices converge uniformly to the constant slice and their lengths are bounded by the halved
condition), so a diagonal/limit argument over `δ ↓ 0` produces the identity
`Wp(1/2) t = Wm(1/2) t` on the whole of `[0,1]`, where `Wp, Wm` are now the lifts of the whole
family, continuous on the closed rectangle and smooth for `t < 1`.  Step 3 is then unchanged.

So the work is: (a) a version of `lift_family_of_short` for a family that is `C^∞` on
`univ ×ˢ Ico 0 1` and continuous, with joint continuity of the lift on the closed rectangle;
(b) the clopen step for it (the same argument, using `‖W‖ < π/√K`);
(c) steps 2–3 above.  All the analytic inputs (`InjBall`, `SegmentDomain`, `LiftLemma`,
`LiftUniform`, `GExpLocalInj`, `Gauss`, `ExpBound2`, `radial_estimate_of_lift`,
`norm_le_curveLength_of_lift`, `eq_at_zero_of_continuous_lift_eq`, `lift_of_geodesic_ray`) are in
`Submission/Work/OddBound/LiftKit.lean` and in `Submission/Work/OddBound/longHomotopy/`.
-/
