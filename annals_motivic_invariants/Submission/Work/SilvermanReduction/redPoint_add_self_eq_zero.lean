import Mathlib
import Submission.Work.SilvermanReduction.Basic
import Submission.Work.SilvermanReduction.API
import Submission.Work.SilvermanReduction.Helpers
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `redPoint (P + P) = 0` when `redPoint P` is `2`-torsion

Let `R` be a discrete valuation ring with fraction field `K`, and `W/K` a Weierstrass curve with
**good reduction** at `R`.  Let `P = (x, y)` be a nonsingular point of `W` with *integral*
`x`-coordinate.  If the reduction `redPoint R W P` of `P` is `2`-torsion in the special fibre,

  `redPoint R W P + redPoint R W P = 0`,

then `P + P` reduces to `0`:

  `redPoint R W (P + P) = 0`.

This is a `2`-torsion special case of Silverman, *AEC*, VII.2.1 (the additivity of the reduction
map), obtained directly from the tangent-slope formula rather than from the general additivity
theorem: the hypothesis says that the reduced point has a **vertical tangent**, i.e. that the
doubling denominator

  `D = 2y + a₁x + a₃ = y - W.negY x y`

lies in the maximal ideal of `R` (`val D < 1`), while the doubling numerator

  `N = 3x² + 2a₂x + a₄ - a₁y`

is a **unit** (its residue is the `X`-partial of the Weierstrass polynomial at the nonsingular
reduced point, and the `Y`-partial vanishes there).  The tangent slope `λ = N/D` then has
`val λ = 1/val D > 1`, whence `x(2P) = λ² + a₁λ - a₂ - 2x` is dominated by `λ²` and has
`val (x(2P)) = (1/val D)² > 1`: the point `2P` has negative valuation and reduces to `0`.

## Main results

* `redPoint_add_self_eq_zero` — the requested statement.
* `val_sub_negY_lt_one_and_val_num_eq_one` — `val (y - W.negY x y) < 1` together with
  `val (3x² + 2a₂x + a₄ - a₁y) = 1` (the "vertical tangent, unit numerator" input).
* `one_lt_val_addX_self` — the valuation computation for the doubling step,
  `1 < val (W.addX x x (W.slope x x y y))`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open WeierstrassCurve WeierstrassCurve.Affine
open IsLocalRing (ResidueField residue)
open scoped WithZero

namespace Work.SilvermanReduction

noncomputable section

variable {K : Type*} [Field K] [DecidableEq K] {R : Type*} [CommRing R]
  [IsDomain R] [IsDiscreteValuationRing R] [Algebra R K] [IsFractionRing R K]

/-! ## 1. The "vertical tangent" input -/

/-- **A reduced `2`-torsion point has a vertical tangent and a unit numerator.**

If the integral point `(x, y)` of `W` has `redPoint P + redPoint P = 0` in the special fibre, then

* the doubling denominator `D = y - W.negY x y = 2y + a₁x + a₃` has valuation `< 1` (it lies in the
  maximal ideal: the reduced tangent is vertical), and
* the doubling numerator `N = 3x² + 2a₂x + a₄ - a₁y` has valuation `1` (it is a unit: it is the
  `X`-partial of the Weierstrass polynomial at a nonsingular reduced point whose `Y`-partial
  vanishes). -/
lemma val_sub_negY_lt_one_and_val_num_eq_one [DecidableEq (ResidueField R)]
    {W : WeierstrassCurve.Affine K} [W.HasGoodReduction R] {x y : K}
    (h : WeierstrassCurve.Affine.Nonsingular W x y)
    (hx : ∃ r : R, algebraMap R K r = x)
    (h2 : redPoint R W (WeierstrassCurve.Affine.Point.some x y h)
        + redPoint R W (WeierstrassCurve.Affine.Point.some x y h) = 0) :
    val R K (y - W.negY x y) < 1 ∧
      val R K (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) = 1 := by
  classical
  obtain ⟨r, hr⟩ := hx
  obtain ⟨s, hs⟩ := exists_lift_of_y (W := W) h ⟨r, hr⟩
  -- the reduction of `P`, with explicit lifts of its coordinates
  have h2' : WeierstrassCurve.Affine.Point.some (residue R r) (residue R s)
        (nonsingular_reduction (W := W) (equation_integralModel (W := W) h.1 hr hs))
      + WeierstrassCurve.Affine.Point.some (residue R r) (residue R s)
        (nonsingular_reduction (W := W) (equation_integralModel (W := W) h.1 hr hs)) = 0 := by
    rw [redPoint_some_mk R h hr hs] at h2
    exact h2
  -- the reduced point is its own negative: its `Y`-partial vanishes
  have hb : residue R s = WeierstrassCurve.Affine.negY (W.reduction R) (residue R r) (residue R s) := by
    by_contra hne
    rw [Point.add_self_of_Y_ne hne] at h2'
    exact Point.some_ne_zero _ h2'
  have hb1 : residue R s = - residue R s - (W.reduction R).a₁ * residue R r
      - (W.reduction R).a₃ := by
    simpa only [WeierstrassCurve.Affine.negY] using hb
  have hky : 2 * residue R s + (W.reduction R).a₁ * residue R r + (W.reduction R).a₃ = 0 := by
    linear_combination (norm := first | refl_ring1 | ring1) hb1
  -- the denominator is lifted by `2s + (integralModel).a₁ * r + (integralModel).a₃`
  have hresD : residue R (2 * s + (WeierstrassCurve.integralModel R W).a₁ * r
      + (WeierstrassCurve.integralModel R W).a₃) = 0 := by
    rw [map_add, map_add, map_mul, map_mul, map_ofNat]
    have e1 : (W.reduction R).a₁ = residue R (WeierstrassCurve.integralModel R W).a₁ :=
      WeierstrassCurve.map_a₁ (W := WeierstrassCurve.integralModel R W) (f := residue R)
    have e3 : (W.reduction R).a₃ = residue R (WeierstrassCurve.integralModel R W).a₃ :=
      WeierstrassCurve.map_a₃ (W := WeierstrassCurve.integralModel R W) (f := residue R)
    rw [e1, e3] at hky
    exact hky
  have hDlift : algebraMap R K (2 * s + (WeierstrassCurve.integralModel R W).a₁ * r
      + (WeierstrassCurve.integralModel R W).a₃) = y - W.negY x y := by
    rw [map_add, map_add, map_mul, map_mul, map_ofNat,
      WeierstrassCurve.integralModel_a₁_eq R W, WeierstrassCurve.integralModel_a₃_eq R W,
      hr, hs, WeierstrassCurve.Affine.negY]
    first | refl_ring1 | ring
  refine ⟨by rw [← hDlift]; exact (val_algebraMap_lt_one_iff_residue_eq_zero _).mpr hresD, ?_⟩
  -- the numerator is lifted by `3r² + 2(integralModel).a₂ r + (integralModel).a₄
  -- - (integralModel).a₁ s`, and its residue is the `X`-partial at the nonsingular reduced point
  have hresN : residue R (3 * r ^ 2 + 2 * (WeierstrassCurve.integralModel R W).a₂ * r
      + (WeierstrassCurve.integralModel R W).a₄ - (WeierstrassCurve.integralModel R W).a₁ * s) ≠ 0 := by
    have hns := (nonsingular_reduction (W := W) (equation_integralModel (W := W) h.1 hr hs))
    rw [nonsingular_iff'] at hns
    rcases hns with ⟨-, hX | hY⟩
    · intro hc
      apply hX
      simp only [map_add, map_sub, map_mul, map_pow, map_ofNat] at hc
      have e1 : (W.reduction R).a₁ = residue R (WeierstrassCurve.integralModel R W).a₁ :=
        WeierstrassCurve.map_a₁ (W := WeierstrassCurve.integralModel R W) (f := residue R)
      have e2 : (W.reduction R).a₂ = residue R (WeierstrassCurve.integralModel R W).a₂ :=
        WeierstrassCurve.map_a₂ (W := WeierstrassCurve.integralModel R W) (f := residue R)
      have e4 : (W.reduction R).a₄ = residue R (WeierstrassCurve.integralModel R W).a₄ :=
        WeierstrassCurve.map_a₄ (W := WeierstrassCurve.integralModel R W) (f := residue R)
      rw [e1, e2, e4]
      linear_combination (norm := first | refl_ring1 | ring1) -hc
    · exact absurd hky hY
  have hNlift : algebraMap R K (3 * r ^ 2 + 2 * (WeierstrassCurve.integralModel R W).a₂ * r
      + (WeierstrassCurve.integralModel R W).a₄ - (WeierstrassCurve.integralModel R W).a₁ * s)
      = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat,
      WeierstrassCurve.integralModel_a₁_eq R W, WeierstrassCurve.integralModel_a₂_eq R W,
      WeierstrassCurve.integralModel_a₄_eq R W, hr, hs]
  rw [← hNlift]
  exact (val_algebraMap_eq_one_iff_residue_ne_zero _).mpr hresN

/-! ## 2. The doubling valuation -/

/-- **The `X`-coordinate of `2P` has negative valuation.**

If the doubling denominator `D = y - W.negY x y` has `val D < 1` (vertical reduced tangent) and is
nonzero, and the doubling numerator `N = 3x² + 2a₂x + a₄ - a₁y` has `val N = 1`, then the tangent
slope `λ = W.slope x x y y = N/D` satisfies `val λ = 1/val D > 1`, and
`W.addX x x λ = λ² + a₁λ - a₂ - 2x` is dominated by `λ²`, so
`val (W.addX x x λ) = (val λ)² > 1`. -/
lemma one_lt_val_addX_self {W : WeierstrassCurve.Affine K} [W.HasGoodReduction R] {x y : K}
    (hxI : IsIntegralK R K x)
    (hDlt : val R K (y - W.negY x y) < 1) (hDne : y ≠ W.negY x y)
    (hN : val R K (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) = 1) :
    1 < val R K (W.addX x x (W.slope x x y y)) := by
  have hsl : W.slope x x y y
      = (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) / (y - W.negY x y) :=
    slope_of_Y_ne rfl hDne
  have hD0 : y - W.negY x y ≠ 0 := sub_ne_zero.mpr hDne
  have hdpos : 0 < val R K (y - W.negY x y) :=
    WithZero.pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff (val R K)).mpr hD0)
  have hvalslope : val R K (W.slope x x y y) = (val R K (y - W.negY x y))⁻¹ := by
    rw [hsl, Valuation.map_div, hN, one_div]
  have hgt1 : 1 < val R K (W.slope x x y y) := by
    rw [hvalslope]
    exact (one_lt_inv₀ hdpos).mpr hDlt
  have hposslope : 0 < val R K (W.slope x x y y) := lt_trans zero_lt_one hgt1
  have hsq_gt : 1 < val R K (W.slope x x y y ^ 2) := by
    rw [map_pow, pow_two]
    exact one_lt_mul_self hgt1
  have hsq_gt' : val R K (W.slope x x y y) < val R K (W.slope x x y y ^ 2) := by
    rw [map_pow, pow_two]
    simpa using mul_lt_mul_of_pos_left hgt1 hposslope
  have hw1 : val R K (W.a₁ * W.slope x x y y) ≤ val R K (W.slope x x y y) := by
    rw [map_mul]
    calc val R K W.a₁ * val R K (W.slope x x y y) ≤ 1 * val R K (W.slope x x y y) :=
          mul_le_mul_left (isIntegralK_a₁ (W := W)) _
      _ = val R K (W.slope x x y y) := one_mul _
  have h2xI : IsIntegralK R K (2 * x) := by
    rw [two_mul]; exact hxI.add hxI
  have hw2 : val R K (W.a₂ + 2 * x) ≤ 1 :=
    (isIntegralK_a₂ (W := W)).add h2xI
  have hv_w : val R K (W.a₁ * W.slope x x y y - (W.a₂ + 2 * x))
      < val R K (W.slope x x y y ^ 2) := by
    have hle : val R K (W.a₁ * W.slope x x y y - (W.a₂ + 2 * x))
        ≤ max (val R K (W.slope x x y y)) 1 := by
      refine le_trans (Valuation.map_sub (val R K) _ _) ?_
      exact max_le_max hw1 hw2
    rw [max_eq_left hgt1.le] at hle
    exact lt_of_le_of_lt hle hsq_gt'
  have haddX : W.addX x x (W.slope x x y y)
      = W.slope x x y y ^ 2 + (W.a₁ * W.slope x x y y - (W.a₂ + 2 * x)) := by
    simp only [addX]; ring
  rw [haddX, Valuation.map_add_eq_of_lt_left (v := val R K) hv_w]
  exact hsq_gt

/-! ## 3. The requested statement -/

theorem redPoint_add_self_eq_zero {K : Type*} [Field K] [DecidableEq K] {R : Type*} [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] [Algebra R K] [IsFractionRing R K]
    [DecidableEq (IsLocalRing.ResidueField R)]
    {W : WeierstrassCurve.Affine K} [W.HasGoodReduction R] {x y : K}
    (h : WeierstrassCurve.Affine.Nonsingular W x y)
    (hx : ∃ r : R, algebraMap R K r = x)
    (h2 : Work.SilvermanReduction.redPoint R W (WeierstrassCurve.Affine.Point.some x y h) + Work.SilvermanReduction.redPoint R W (WeierstrassCurve.Affine.Point.some x y h) = 0) :
    Work.SilvermanReduction.redPoint R W (WeierstrassCurve.Affine.Point.some x y h + WeierstrassCurve.Affine.Point.some x y h) = 0 := by
  classical
  by_cases hy : y = W.negY x y
  · -- `P` is `2`-torsion over `K`: `P + P = 0`
    rw [Point.add_self_of_Y_eq hy, redPoint_zero]
  · -- the reduced tangent at `P` is vertical: `2P` has negative valuation
    obtain ⟨hDlt, hN⟩ := val_sub_negY_lt_one_and_val_num_eq_one (R := R) (W := W) h hx h2
    have hxI : IsIntegralK R K x := (IsIntegralK.iff_exists x).mpr hx
    have hbig : 1 < val R K (W.addX x x (W.slope x x y y)) :=
      one_lt_val_addX_self (R := R) (W := W) hxI hDlt hy hN
    rw [Point.add_self_of_Y_ne hy]
    refine redPoint_some_eq_zero R _ ?_
    intro hcon
    exact absurd ((IsIntegralK.iff_exists _).mpr hcon) (not_le.mpr hbig)

end

end Work.SilvermanReduction
