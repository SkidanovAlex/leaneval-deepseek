import Mathlib
import Submission.Work.SilvermanReduction.Basic

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The doubling of an integral point whose `∂F/∂Y` is a unit is integral

Silverman, *AEC*, VII.2.1, the case of the tangent line at an integral point `P = (x, y)` at which
the tangent is **not** vertical: if the `x`-coordinate of `P` is integral and

  `val R K (y - negY W x y) = 1`,

i.e. the `Y`-derivative `2y + a₁x + a₃ = ∂F/∂Y(P)` is a *unit* of the valuation ring, then the
`x`-coordinate of `2P`,

  `addX W x x (slope W x x y y)`,

is integral.

Indeed the tangent slope is

  `λ = (3x² + 2a₂x + a₄ - a₁y) / (y - negY W x y)`,

a quotient of two integral quantities whose denominator is a unit; hence `λ` is integral, and so is
`addX W x x λ = λ² + a₁λ - a₂ - 2x`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open WeierstrassCurve WeierstrassCurve.Affine
open scoped WithZero

namespace Work.SilvermanReduction

noncomputable section

theorem isIntegralK_addX_self_of_val_sub_negY_eq_one {K : Type*} [Field K] [DecidableEq K]
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R K] [IsFractionRing R K]
    {W : WeierstrassCurve.Affine K} [W.HasGoodReduction R] {x y : K}
    (h : WeierstrassCurve.Affine.Nonsingular W x y)
    (hx : ∃ r : R, algebraMap R K r = x)
    (hD : Work.SilvermanReduction.val R K (y - WeierstrassCurve.Affine.negY W x y) = 1) :
    Work.SilvermanReduction.IsIntegralK R K
      (WeierstrassCurve.Affine.addX W x x (WeierstrassCurve.Affine.slope W x x y y)) := by
  -- integrality of the two coordinates
  have hxI : IsIntegralK R K x := (IsIntegralK.iff_exists x).mpr hx
  have hyI : IsIntegralK R K y := isIntegralK_of_equation h.1 hxI
  -- the denominator `D = y - negY W x y = ∂F/∂Y(P)` is a unit
  set D : K := y - W.negY x y with hDdef
  have hDval : val R K D = 1 := by rw [hDdef]; exact hD
  have hDne : D ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hDval
    exact zero_ne_one hDval
  have hyne : y ≠ W.negY x y := fun h0 => hDne (by rw [hDdef]; exact sub_eq_zero.mpr h0)
  -- the numerator of the tangent slope
  set N : K := 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y with hNdef
  have h3 : IsIntegralK R K (3 : K) := by
    simpa only [map_ofNat] using (IsIntegralK.of_algebraMap (R := R) (K := K) (3 : R))
  have h2 : IsIntegralK R K (2 : K) := by
    simpa only [map_ofNat] using (IsIntegralK.of_algebraMap (R := R) (K := K) (2 : R))
  have hNle : IsIntegralK R K N := by
    rw [hNdef]
    exact (((h3.mul (hxI.pow 2)).add ((h2.mul isIntegralK_a₂).mul hxI)).add
      isIntegralK_a₄).sub (isIntegralK_a₁.mul hyI)
  -- the tangent slope is the quotient `N / D`
  have hslope : W.slope x x y y = N / D := by
    rw [hNdef, hDdef]
    exact slope_of_Y_ne rfl hyne
  have hmul : W.slope x x y y * D = N := by
    rw [hslope]
    exact div_mul_cancel₀ N hDne
  -- `val` of the slope is `val` of the numerator
  have hvalL : val R K (W.slope x x y y) = val R K N := by
    have h1 : val R K (W.slope x x y y) * val R K D = val R K N := by
      rw [← map_mul, hmul]
    rw [hDval, mul_one] at h1
    exact h1
  have hLI : IsIntegralK R K (W.slope x x y y) := by
    show val R K (W.slope x x y y) ≤ 1
    rw [hvalL]
    exact hNle
  -- `addX W x x λ = λ² + a₁λ - a₂ - 2x` is integral
  show IsIntegralK R K (W.addX x x (W.slope x x y y))
  rw [WeierstrassCurve.Affine.addX]
  exact ((((hLI.pow 2).add (isIntegralK_a₁.mul hLI)).sub isIntegralK_a₂).sub hxI).sub hxI

end

end Work.SilvermanReduction
