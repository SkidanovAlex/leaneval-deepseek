/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.SilvermanReduction
-/
import Mathlib
import Submission.Work.SilvermanReduction.Basic
import Submission.Work.SilvermanReduction.API
import Submission.Work.SilvermanReduction.not_isIntegralK_addX_neg
import Submission.Work.SilvermanReduction.redPoint_add_self_eq_zero
import Submission.Work.SilvermanReduction.exists_lift_slope

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Silverman, *AEC*, VII.2.1: additivity of the reduction map on integral points

The reduction map `redPoint R W : E(K) → Ẽ(k)` sends an integral point to the point of the special
fibre obtained by reducing its coordinates, and a point of negative valuation to `0`.  This file
proves that it is additive on *integral* points — Silverman, *AEC*, VII.2.1 in the chord–tangent
computation.

## Strategy

Write `P = (x,y)`, `Q = (u,v)` with integral coordinates, and let `r, s, r', s' ∈ R` be lifts of
`x, y, u, v`.  The reduction of an integral point is given coordinatewise by *any* lifts
(`redPoint_some_mk`), so

* `redPoint P = Point.some (residue r) (residue s) _` and `redPoint Q = Point.some (residue r')
  (residue s') _`, and
* `redPoint (P + Q)` is computed from the coordinates `W.addX x u λ`, `W.addY x u y λ` of the sum,
  where `λ = W.slope x u y v` is the slope of the chord (or the tangent).

The two cases are:

* `redPoint P = -redPoint Q` (the *degenerate* case).  Then `P + Q` is either `0` (when `P = -Q`),
  or `2P` (when `x = u` and `P = Q`, a doubling of a point with `2`-torsion reduction), or a point
  of negative valuation (when `x ≠ u`, by `not_isIntegralK_addX_neg`, the "difference of two points
  with the same reduction" case applied to `P` and `-Q`).  In each case both sides are `0`.
* otherwise (`exists_lift_slope`): the slope `λ` is integral and reduces to the slope of the chord
  through the reduced points, and the chord–tangent formulas `map_addX`, `map_addY` descend to the
  residue field, giving additivity.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open WeierstrassCurve WeierstrassCurve.Affine
open IsLocalRing (ResidueField residue)
open scoped WithZero

namespace Work.SilvermanReduction

noncomputable section

variable {K : Type*} [Field K] [DecidableEq K]
variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Algebra R K] [IsFractionRing R K] [DecidableEq (IsLocalRing.ResidueField R)]
variable {W : WeierstrassCurve.Affine K} [W.HasGoodReduction R]

/-- The `addX`-coordinate of a point of `W` is the image of the `addX`-coordinate of the
corresponding point of an integral model, when the slope is a lift. -/
lemma addX_eq_algebraMap (L : WeierstrassCurve.Affine R) (hL : L⁄K = W)
    {x u lam : K} {r r' ρ : R} (hr : algebraMap R K r = x) (hr' : algebraMap R K r' = u)
    (hρ : algebraMap R K ρ = lam) :
    W.addX x u lam = algebraMap R K (L.addX r r' ρ) := by
  have hm := WeierstrassCurve.Affine.map_addX (f := algebraMap R K) (W' := L) r r' ρ
  rw [hr, hr', hρ] at hm
  rw [← hL]
  exact hm

/-- The `addY`-coordinate of a point of `W` is the image of the `addY`-coordinate of the
corresponding point of an integral model, when the slope is a lift. -/
lemma addY_eq_algebraMap (L : WeierstrassCurve.Affine R) (hL : L⁄K = W)
    {x u y lam : K} {r r' s ρ : R} (hr : algebraMap R K r = x) (hr' : algebraMap R K r' = u)
    (hs : algebraMap R K s = y) (hρ : algebraMap R K ρ = lam) :
    W.addY x u y lam = algebraMap R K (L.addY r r' s ρ) := by
  have hm := WeierstrassCurve.Affine.map_addY (f := algebraMap R K) (W' := L) r s r' ρ
  rw [hr, hr', hs, hρ] at hm
  rw [← hL]
  exact hm

/-- The `y`-coordinate of the negative of an integral point lifts to the negation in the integral
model. -/
lemma negY_eq_algebraMap (L : WeierstrassCurve.Affine R) (hL : L⁄K = W)
    {u v : K} {r' s' : R} (hr' : algebraMap R K r' = u) (hs' : algebraMap R K s' = v) :
    algebraMap R K (WeierstrassCurve.Affine.negY L r' s') = W.negY u v := by
  have hm := WeierstrassCurve.Affine.map_negY (f := algebraMap R K) (W' := L) r' s'
  rw [hr', hs'] at hm
  rw [← hL]
  exact hm.symm

/-- **Silverman, AEC, VII.2.1 (the integral case).**  The reduction map on the points of a
Weierstrass curve with good reduction at a discrete valuation is additive on *integral* points:
if `(x, y)` and `(u, v)` are nonsingular points of `W` whose coordinates are integral at the place
(i.e. lift to the valuation ring `R`), then `redPoint (P + Q) = redPoint P + redPoint Q`.

Proof route (see `Submission/Work/SilvermanReduction/Basic.lean` for the API): write the lifts as
`r, s` and `r', s'`, use `redPoint_some_mk` on all three points, and compare coordinates in the
residue field.  The mathematical content is the chord–tangent computation: with `λ = W.slope`,
`x(P+Q) = W.addX x u λ` and `y(P+Q) = W.addY x u y λ`, so it suffices to know that `λ` is integral
and reduces to the slope of the reduced points; `WeierstrassCurve.Affine.map_slope`,
`WeierstrassCurve.Affine.map_addX`, `WeierstrassCurve.Affine.map_addY` transport these formulas.
The cases are (i) `x̄ ≠ ū`: `λ = (y-v)/(x-u)` with `x - u` a unit; (ii) `x = u` (doubling, `P = Q`):
the tangent slope, whose denominator `2y + a₁x + a₃` reduces to `∂F/∂y` at `red P` and is a unit
because `red P` is not `2`-torsion; (iii) `x ≠ u` but `x̄ = ū`: then `red P = red Q` (in the
non-degenerate case) and the identity `(y-v)·D = (x-u)·D'` with `D = y+v+a₁x+a₃`,
`D' = x²+xu+u²+a₂(x+u)+a₄-a₁v` computes `λ = D'/D`.  When `red P = -red Q` the sum is
non-integral and the reduction is `0`. -/
theorem redPoint_add_of_integral {K : Type*} [Field K] [DecidableEq K]
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R K] [IsFractionRing R K] [DecidableEq (IsLocalRing.ResidueField R)]
    {W : WeierstrassCurve.Affine K} [W.HasGoodReduction R]
    {x y u v : K} (h : WeierstrassCurve.Affine.Nonsingular W x y)
    (h' : WeierstrassCurve.Affine.Nonsingular W u v)
    (hx : ∃ r : R, algebraMap R K r = x) (hu : ∃ r : R, algebraMap R K r = u) :
    Work.SilvermanReduction.redPoint R W (WeierstrassCurve.Affine.Point.some x y h +
        WeierstrassCurve.Affine.Point.some u v h')
      = Work.SilvermanReduction.redPoint R W (WeierstrassCurve.Affine.Point.some x y h)
        + Work.SilvermanReduction.redPoint R W (WeierstrassCurve.Affine.Point.some u v h') := by
  classical
  obtain ⟨r, hr⟩ := hx
  obtain ⟨s, hs⟩ := exists_lift_of_y (W := W) h ⟨r, hr⟩
  obtain ⟨r', hr'⟩ := hu
  obtain ⟨s', hs'⟩ := exists_lift_of_y (W := W) h' ⟨r', hr'⟩
  have hs'' : algebraMap R K (WeierstrassCurve.Affine.negY (WeierstrassCurve.integralModel R W) r' s')
      = W.negY u v :=
    negY_eq_algebraMap R (WeierstrassCurve.integralModel R W)
      (WeierstrassCurve.baseChange_integralModel_eq R W) hr' hs'
  by_cases hbad : IsLocalRing.residue R r = IsLocalRing.residue R r' ∧
      IsLocalRing.residue R s = WeierstrassCurve.Affine.negY (W.reduction R)
        (IsLocalRing.residue R r') (IsLocalRing.residue R s')
  · -- degenerate case: `redPoint P = -redPoint Q`
    have hredneg : redPoint R W (WeierstrassCurve.Affine.Point.some x y h)
        = - redPoint R W (WeierstrassCurve.Affine.Point.some u v h') := by
      rw [redPoint_some_mk R h hr hs, redPoint_some_mk R h' hr' hs',
        WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.some.injEq]
      exact hbad
    by_cases hxu : x = u
    · rcases (WeierstrassCurve.Affine.Point.X_eq_iff (h₁ := h) (h₂ := h')).mp hxu with heq | hneg
      · -- `P = Q`: doubling
        rw [heq] at hredneg
        have h2 : redPoint R W (WeierstrassCurve.Affine.Point.some u v h')
            + redPoint R W (WeierstrassCurve.Affine.Point.some u v h') = 0 :=
          eq_neg_iff_add_eq_zero.mp hredneg
        rw [heq, redPoint_add_self_eq_zero h' ⟨r', hr'⟩ h2]
        exact h2.symm
      · -- `P = -Q`: the sum is zero
        have hsum0 : WeierstrassCurve.Affine.Point.some x y h
            + WeierstrassCurve.Affine.Point.some u v h' = (0 : WeierstrassCurve.Affine.Point W) := by
          rw [hneg, neg_add_cancel]
        rw [hsum0, redPoint_zero, hredneg, neg_add_cancel]
    · -- `x ≠ u`: the difference of two points with the same reduction
      have hneg2 : W.Nonsingular u (W.negY u v) :=
        (WeierstrassCurve.Affine.nonsingular_neg (W' := W) u v).mpr h'
      have hsv'' : IsLocalRing.residue R s
          = IsLocalRing.residue R
              (WeierstrassCurve.Affine.negY (WeierstrassCurve.integralModel R W) r' s') := by
        rw [← WeierstrassCurve.Affine.map_negY (f := IsLocalRing.residue R)
          (W' := WeierstrassCurve.integralModel R W) r' s']
        exact hbad.2
      have hnotInt := not_isIntegralK_addX_neg h hneg2 hr hs hr' hs'' hbad.1 hsv'' hxu
      rw [WeierstrassCurve.Affine.negY_negY] at hnotInt
      rw [WeierstrassCurve.Affine.Point.add_of_X_ne (h₁ := h) (h₂ := h') hxu,
        redPoint_some_eq_zero R (hx := fun hc => hnotInt ((IsIntegralK.iff_exists _).mpr hc)),
        hredneg, neg_add_cancel]
  · -- non-degenerate case: the slope is integral and reduces correctly
    have hredneg : ¬ (redPoint R W (WeierstrassCurve.Affine.Point.some x y h)
        = - redPoint R W (WeierstrassCurve.Affine.Point.some u v h')) := by
      intro hc
      exact hbad (by
        rw [redPoint_some_mk R h hr hs, redPoint_some_mk R h' hr' hs',
          WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.some.injEq] at hc
        exact hc)
    obtain ⟨ρ, hρ, hρres⟩ := exists_lift_slope h h' hr hs hr' hs' hredneg
    have hxy' : ¬ (x = u ∧ y = W.negY u v) := by
      rintro ⟨hx_eq, hy_eq⟩
      apply hbad
      refine ⟨?_, ?_⟩
      · exact congrArg (IsLocalRing.residue R)
          (algebraMap_injective (by rw [hr, hx_eq, ← hr']))
      · have hs_eq : s
            = WeierstrassCurve.Affine.negY (WeierstrassCurve.integralModel R W) r' s' :=
          algebraMap_injective (by rw [hs, hy_eq, ← hs''])
        rw [hs_eq, ← WeierstrassCurve.Affine.map_negY (f := IsLocalRing.residue R)
          (W' := WeierstrassCurve.integralModel R W) r' s']
        rfl
    rw [WeierstrassCurve.Affine.Point.add_some (h₁ := h) (h₂ := h') hxy',
      redPoint_some_mk R _
        (addX_eq_algebraMap R (WeierstrassCurve.integralModel R W)
          (WeierstrassCurve.baseChange_integralModel_eq R W) hr hr' hρ).symm
        (addY_eq_algebraMap R (WeierstrassCurve.integralModel R W)
          (WeierstrassCurve.baseChange_integralModel_eq R W) hr hr' hs hρ).symm,
      redPoint_some_mk R h hr hs, redPoint_some_mk R h' hr' hs',
      WeierstrassCurve.Affine.Point.add_some hbad, WeierstrassCurve.Affine.Point.some.injEq]
    constructor
    · rw [← WeierstrassCurve.Affine.map_addX (f := IsLocalRing.residue R)
        (W' := WeierstrassCurve.integralModel R W) r r' ρ, hρres]
      rfl
    · rw [← WeierstrassCurve.Affine.map_addY (f := IsLocalRing.residue R)
        (W' := WeierstrassCurve.integralModel R W) r s r' ρ, hρres]
      rfl

end

end Work.SilvermanReduction
