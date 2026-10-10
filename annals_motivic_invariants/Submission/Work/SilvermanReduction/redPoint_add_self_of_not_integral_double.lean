import Mathlib
import Submission.Work.SilvermanReduction.Basic
import Submission.Work.SilvermanReduction.Helpers
import Submission.Work.SilvermanReduction.API
import Submission.Work.SilvermanReduction.isIntegralK_addX_self_of_val_sub_negY_eq_one
import Submission.Work.SilvermanReduction.negY_reduction_eq_of_residue_doublingDenom_eq_zero
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The doubling case of Silverman VII.2.1 when `2P` has negative valuation

Let `R` be a discrete valuation ring with fraction field `K`, and `W/K` a Weierstrass curve with
**good reduction** at `R`.  For a nonsingular point `P = (x, y)` of `W` with integral
`x`-coordinate, if the double `2P` has **negative valuation** (its `x`-coordinate does not lift to
`R`, so that `redPoint R W (2P) = 0`), then

  `redPoint R W (2P) = redPoint R W P + redPoint R W P`.

This is one of the cases of the additivity of the reduction map (Silverman, *AEC*, VII.2.1): the
hypothesis says that `redPoint R W P` is a `2`-torsion point of the special fibre, and the two
possibilities for the doubling denominator prove it.

Write `A = WeierstrassCurve.integralModel R W` for the integral model of `W`, choose lifts
`r, s : R` of `x, y` (`x` is integral by hypothesis, and then so is `y`, by
`isIntegralK_of_equation`), and let

  `d = 2s + A.a₁ r + A.a₃ ∈ R`

be the lift of the doubling denominator `D = y - W.negY x y = 2y + a₁x + a₃` (`doublingDenom_lift`).
There are two cases.

* `residue R d = 0` (the reduced tangent at `redPoint P` is vertical).  Then the reduced point
  `redPoint R W P = (residue r, residue s)` is its own negative, i.e. it is a `2`-torsion point of
  the special fibre: this is `negY_reduction_eq_of_residue_doublingDenom_eq_zero`.  Hence
  `redPoint R W P + redPoint R W P = 0` by `Point.add_self_of_Y_eq`, while
  `redPoint R W (2P) = 0` because `2P` has negative valuation (`redPoint_eq_zero_iff`).
* `residue R d ≠ 0` (the doubling denominator is a unit: `val D = 1`).  Then the tangent slope
  `λ = N/D`, with `N = 3x² + 2a₂x + a₄ - a₁y` integral, is integral, and so is
  `addX x x λ = λ² + a₁λ - a₂ - 2x`: this is `isIntegralK_addX_self_of_val_sub_negY_eq_one`.  Since
  `2P = Point.some (addX x x λ) (addY x x y λ)`, the point `2P` has an integral `x`-coordinate, i.e.
  it does *not* have negative valuation — contradicting the hypothesis.

## Main results

* `redPoint_add_self_of_not_integral_double` — the requested statement.
* `doublingDenom_lift` — the lift of the doubling denominator in the integral model.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open WeierstrassCurve WeierstrassCurve.Affine
open IsLocalRing (ResidueField residue)
open scoped WithZero

namespace Work.SilvermanReduction

noncomputable section

/-- **The lift of the doubling denominator.**  If `r` lifts `x` and `s` lifts `y`, then the
element `2s + A.a₁ r + A.a₃` of the integral model `A = WeierstrassCurve.integralModel R W` lifts
the doubling denominator `y - W.negY x y = 2y + a₁x + a₃`. -/
lemma doublingDenom_lift {K : Type*} [Field K] {R : Type*} [CommRing R] [Algebra R K]
    {W : WeierstrassCurve.Affine K} [W.IsIntegral R] {x y : K} {r s : R}
    (hr : algebraMap R K r = x) (hs : algebraMap R K s = y) :
    algebraMap R K (2 * s + (WeierstrassCurve.integralModel R W).a₁ * r
        + (WeierstrassCurve.integralModel R W).a₃) = y - W.negY x y := by
  rw [map_add, map_add, map_mul, map_mul, map_ofNat,
    WeierstrassCurve.integralModel_a₁_eq R W, WeierstrassCurve.integralModel_a₃_eq R W,
    hr, hs, WeierstrassCurve.Affine.negY]
  first | refl_ring1 | ring

theorem redPoint_add_self_of_not_integral_double {K : Type*} [Field K] [DecidableEq K]
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R K] [IsFractionRing R K] [DecidableEq (IsLocalRing.ResidueField R)]
    {W : WeierstrassCurve.Affine K} [W.HasGoodReduction R] {x y : K}
    (h : WeierstrassCurve.Affine.Nonsingular W x y) (hx : ∃ r : R, algebraMap R K r = x)
    (h2 : Work.SilvermanReduction.HasNegativeValuation R
      (WeierstrassCurve.Affine.Point.some x y h + WeierstrassCurve.Affine.Point.some x y h)) :
    Work.SilvermanReduction.redPoint R W
        (WeierstrassCurve.Affine.Point.some x y h + WeierstrassCurve.Affine.Point.some x y h) =
      Work.SilvermanReduction.redPoint R W (WeierstrassCurve.Affine.Point.some x y h) +
        Work.SilvermanReduction.redPoint R W (WeierstrassCurve.Affine.Point.some x y h) := by
  classical
  obtain ⟨r, hr⟩ := hx
  obtain ⟨s, hs⟩ := exists_lift_of_y (W := W) h ⟨r, hr⟩
  -- the two points reduce coordinatewise through the lifts `r`, `s`
  have hP : redPoint R W (Point.some x y h)
      = Point.some (residue R r) (residue R s)
        (nonsingular_reduction (W := W) (equation_integralModel (W := W) h.1 hr hs)) :=
    redPoint_some_mk R h hr hs
  -- `2P` has negative valuation, so it reduces to `0`
  have hzero : redPoint R W (Point.some x y h + Point.some x y h) = 0 :=
    (redPoint_eq_zero_iff R _).mpr (Or.inr h2)
  rw [hzero, hP]
  by_cases hd : residue R (2 * s + (WeierstrassCurve.integralModel R W).a₁ * r
      + (WeierstrassCurve.integralModel R W).a₃) = 0
  · -- the reduced tangent at `redPoint P` is vertical: `redPoint P` is `2`-torsion
    rw [Point.add_self_of_Y_eq
      (negY_reduction_eq_of_residue_doublingDenom_eq_zero (W := W) hd)]
  · -- the doubling denominator is a unit, so `2P` is integral: contradiction
    exfalso
    have hDval : val R K (y - W.negY x y) = 1 := by
      rw [← doublingDenom_lift (W := W) hr hs]
      exact (val_algebraMap_eq_one_iff_residue_ne_zero _).mpr hd
    have hyne : y ≠ W.negY x y := by
      intro hyy
      rw [sub_eq_zero.mpr hyy] at hDval
      simp at hDval
    obtain ⟨x', y', h', hPeq, hx'⟩ := h2
    rw [Point.add_self_of_Y_ne hyne, Point.some.injEq] at hPeq
    refine hx' ?_
    rw [← hPeq.1]
    exact (IsIntegralK.iff_exists (W.addX x x (W.slope x x y y))).mp
      (isIntegralK_addX_self_of_val_sub_negY_eq_one (R := R) h ⟨r, hr⟩ hDval)

end

end Work.SilvermanReduction
