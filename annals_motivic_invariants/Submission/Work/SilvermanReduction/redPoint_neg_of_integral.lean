/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.SilvermanReduction
-/
import Mathlib
import Submission.Work.SilvermanReduction.Basic

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Silverman, *AEC*, VII.2.1: the reduction map commutes with negation on integral points

The reduction map `redPoint R W : E(K) → Ẽ(k)` of a Weierstrass curve with good reduction at a
discrete valuation sends an integral point — one whose coordinates lift to the valuation ring `R` —
to the point of the special fibre obtained by reducing its coordinates, and a point of negative
valuation to `0`.  Here we prove that it is compatible with negation on integral points:

  `redPoint (-P) = - redPoint P`  for `P = (x, y)` with `x` integral.

This is a direct coordinate computation, independent of the chord–tangent additivity theorem
(`redPoint_add`).  Write `x = r`, `y = s` with `r, s ∈ R`.  The negative of `(x,y)` is
`(x, W.negY x y)`, and `W.negY x y` lifts to `negY L r s` for the integral model `L` of `W`
(`redPoint_neg_of_integral_negY_eq`); reducing this lift gives exactly the `negY` of the reductions
(`redPoint_neg_of_integral_residue_negY`), which is the `y`-coordinate of `-redPoint P`.

## Main result

* `redPoint_neg_of_integral` — the reduction map is compatible with the group inverse on integral
  points.
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

variable {K : Type*} [Field K]
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Algebra R K] [IsFractionRing R K]

/-- The `y`-coordinate of the negative of an integral point lifts to the negation in the integral
model: if `r, s ∈ R` lift `x, y`, then `negY L r s` lifts `W.negY x y`, where `L` is the integral
model of `W`. -/
lemma redPoint_neg_of_integral_negY_eq {W : WeierstrassCurve.Affine K} [W.IsIntegral R]
    {x y : K} {r s : R} (hr : algebraMap R K r = x) (hs : algebraMap R K s = y) :
    algebraMap R K
        (WeierstrassCurve.Affine.negY (WeierstrassCurve.integralModel R W) r s) =
      W.negY x y := by
  have hm := WeierstrassCurve.Affine.map_negY (f := algebraMap R K)
    (W' := WeierstrassCurve.integralModel R W) r s
  rw [hr, hs] at hm
  have hbc : WeierstrassCurve.Affine.map (WeierstrassCurve.integralModel R W) (algebraMap R K) =
      W :=
    WeierstrassCurve.baseChange_integralModel_eq R W
  rw [hbc] at hm
  exact hm.symm

/-- Reducing a lift of the `y`-coordinate of the negative of an integral point gives the `negY` of
the reduced coordinates in the special fibre. -/
lemma redPoint_neg_of_integral_residue_negY {W : WeierstrassCurve.Affine K} [W.IsMinimal R]
    {r s : R} :
    residue R (WeierstrassCurve.Affine.negY (WeierstrassCurve.integralModel R W) r s) =
      WeierstrassCurve.Affine.negY (W.reduction R) (residue R r) (residue R s) := by
  rw [show W.reduction R =
        WeierstrassCurve.Affine.map (WeierstrassCurve.integralModel R W) (residue R) from rfl,
    WeierstrassCurve.Affine.map_negY]

/-- **Silverman, *AEC*, VII.2.1 (negation).**  The reduction map on the points of a Weierstrass
curve with good reduction at a discrete valuation commutes with the group inverse on *integral*
points: if `x` lifts to the valuation ring, then `redPoint (-P) = -redPoint P`. -/
theorem redPoint_neg_of_integral {K : Type*} [Field K] [DecidableEq K]
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R K] [IsFractionRing R K] [DecidableEq (IsLocalRing.ResidueField R)]
    {W : WeierstrassCurve.Affine K} [W.HasGoodReduction R] {x y : K}
    (h : WeierstrassCurve.Affine.Nonsingular W x y) (hx : ∃ r : R, algebraMap R K r = x) :
    Work.SilvermanReduction.redPoint R W
        (-(WeierstrassCurve.Affine.Point.some x y h)) =
      - Work.SilvermanReduction.redPoint R W (WeierstrassCurve.Affine.Point.some x y h) := by
  classical
  obtain ⟨r, hr⟩ := hx
  obtain ⟨s, hs⟩ := exists_lift_of_y (W := W) h ⟨r, hr⟩
  have hneg : WeierstrassCurve.Affine.Nonsingular W x (W.negY x y) :=
    (WeierstrassCurve.Affine.nonsingular_neg x y).mpr h
  rw [WeierstrassCurve.Affine.Point.neg_some h]
  rw [redPoint_some_mk R hneg hr (redPoint_neg_of_integral_negY_eq hr hs)]
  rw [redPoint_some_mk R h hr hs]
  rw [WeierstrassCurve.Affine.Point.neg_some]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨rfl, redPoint_neg_of_integral_residue_negY⟩

end

end Work.SilvermanReduction
