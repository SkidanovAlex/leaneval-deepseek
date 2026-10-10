import Mathlib
import Submission.Work.SilvermanReduction.Basic
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
# Silverman, *AEC*, VII.2.1: the case where the sum of two integral points is non-integral

If `(x, y)` and `(u, v)` are nonsingular points of a Weierstrass curve with good reduction at a
discrete valuation, both of them integral at the place, `x ≠ u`, and their **sum** has negative
valuation, then the reduction of the sum is the sum of the reductions.

This is the sub-case of Silverman VII.2.1 in which the reduced points are opposite: the sum of two
integral points is non-integral exactly when the two reduced points add up to `0` in the special
fibre.  The proof is a valuation computation with the chord and slope identities of `Helpers`:
`x ≠ u` and the sum non-integral force the reduced `x`-coordinates to coincide, and the non-integrality
of the sum then forces the reduced points to be negatives of each other.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

open WeierstrassCurve WeierstrassCurve.Affine
open IsLocalRing (ResidueField residue)
open scoped WithZero

namespace Work.SilvermanReduction

noncomputable section

/-! ## Integrality of the polynomial combinations appearing in the chord and slope identities -/

section Integrality

variable {K : Type*} [Field K] {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Algebra R K] [IsFractionRing R K]
variable {W : Affine K} [W.IsIntegral R]

private lemma isIntegralK_two : IsIntegralK R K (2 : K) := by
  rw [← map_ofNat (algebraMap R K) 2]
  exact IsIntegralK.of_algebraMap (2 : R)

/-- The numerator `N` of the chord identity `(x-u)^2 * addX = N` is integral. -/
private lemma isIntegralK_chord_N {x y u v : K} (hx : IsIntegralK R K x) (hy : IsIntegralK R K y)
    (hu : IsIntegralK R K u) (hv : IsIntegralK R K v) :
    IsIntegralK R K (x ^ 2 * u + x * u ^ 2 + 2 * W.a₂ * x * u + W.a₄ * (x + u) + 2 * W.a₆
      - W.a₁ * (x * v + u * y) - W.a₃ * (y + v) - 2 * y * v) := by
  have h2 : IsIntegralK R K (2 : K) := isIntegralK_two
  have hT1 : IsIntegralK R K (x ^ 2 * u) := (hx.pow 2).mul hu
  have hT2 : IsIntegralK R K (x * u ^ 2) := hx.mul (hu.pow 2)
  have hT3 : IsIntegralK R K (2 * W.a₂ * x * u) := ((h2.mul isIntegralK_a₂).mul hx).mul hu
  have hT4 : IsIntegralK R K (W.a₄ * (x + u)) := isIntegralK_a₄.mul (hx.add hu)
  have hT5 : IsIntegralK R K (2 * W.a₆) := h2.mul isIntegralK_a₆
  have hT6 : IsIntegralK R K (W.a₁ * (x * v + u * y)) :=
    isIntegralK_a₁.mul ((hx.mul hv).add (hu.mul hy))
  have hT7 : IsIntegralK R K (W.a₃ * (y + v)) := isIntegralK_a₃.mul (hy.add hv)
  have hT8 : IsIntegralK R K (2 * y * v) := (h2.mul hy).mul hv
  have hcomb := ((((((hT1.add hT2).add hT3).add hT4).add hT5).sub hT6).sub hT7).sub hT8
  convert hcomb using 1 <;> ring

/-- The factor `B = x² + xu + u² + a₂(x+u) + a₄ - a₁v` of the slope identity is integral. -/
private lemma isIntegralK_slope_B {x u v : K} (hx : IsIntegralK R K x) (hu : IsIntegralK R K u)
    (hv : IsIntegralK R K v) :
    IsIntegralK R K (x ^ 2 + x * u + u ^ 2 + W.a₂ * (x + u) + W.a₄ - W.a₁ * v) := by
  have hT1 : IsIntegralK R K (x ^ 2) := hx.pow 2
  have hT2 : IsIntegralK R K (x * u) := hx.mul hu
  have hT3 : IsIntegralK R K (u ^ 2) := hu.pow 2
  have hT4 : IsIntegralK R K (W.a₂ * (x + u)) := isIntegralK_a₂.mul (hx.add hu)
  have hT5 : IsIntegralK R K (W.a₄) := isIntegralK_a₄
  have hT6 : IsIntegralK R K (W.a₁ * v) := isIntegralK_a₁.mul hv
  have hcomb := ((((hT1.add hT2).add hT3).add hT4).add hT5).sub hT6
  convert hcomb using 1 <;> ring

end Integrality

/-! ## The two valuation computations -/

section Valuation

variable {K : Type*} [Field K] [DecidableEq K] {R : Type*} [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R] [Algebra R K] [IsFractionRing R K]
variable {W : Affine K} [W.IsIntegral R]

/-- If two lifts of `x` and `u` have different residues, then `x - u` is a unit at the place. -/
private lemma val_sub_eq_one_of_residue_ne {x u : K} {r r' : R} (hr : algebraMap R K r = x)
    (hr' : algebraMap R K r' = u) (h : residue R r ≠ residue R r') : val R K (x - u) = 1 := by
  have hxr : x - u = algebraMap R K (r - r') := by rw [map_sub, hr, hr']
  rw [hxr, val_algebraMap_eq_one_iff]
  intro hmem
  apply h
  have : residue R (r - r') = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hmem
  rw [map_sub, sub_eq_zero] at this
  exact this

/-- **The sum of two integral points with distinct reductions of the `x`-coordinates is
integral.**  This is the chord identity `(x-u)² · addX = N` with `x - u` a unit and `N` integral. -/
private lemma isIntegralK_addX_of_residue_ne {x y u v : K} {r s r' s' : R}
    (h : W.Equation x y) (h' : W.Equation u v)
    (hr : algebraMap R K r = x) (hs : algebraMap R K s = y) (hr' : algebraMap R K r' = u)
    (hs' : algebraMap R K s' = v) (hne : x ≠ u) (hres : residue R r ≠ residue R r') :
    IsIntegralK R K (W.addX x u (W.slope x u y v)) := by
  have hx : IsIntegralK R K x := (IsIntegralK.iff_exists x).mpr ⟨r, hr⟩
  have hu : IsIntegralK R K u := (IsIntegralK.iff_exists u).mpr ⟨r', hr'⟩
  have hy : IsIntegralK R K y := isIntegralK_of_equation h hx
  have hv : IsIntegralK R K v := isIntegralK_of_equation h' hu
  have hN : IsIntegralK R K (x ^ 2 * u + x * u ^ 2 + 2 * W.a₂ * x * u + W.a₄ * (x + u) + 2 * W.a₆
      - W.a₁ * (x * v + u * y) - W.a₃ * (y + v) - 2 * y * v) :=
    isIntegralK_chord_N hx hy hu hv
  have hval : val R K (x - u) = 1 := val_sub_eq_one_of_residue_ne hr hr' hres
  show val R K (W.addX x u (W.slope x u y v)) ≤ 1
  have h1 : val R K ((x - u) ^ 2 * W.addX x u (W.slope x u y v)) ≤ 1 := by
    rw [addX_mul_sq hne h h']
    exact hN
  rw [Valuation.map_mul, Valuation.map_pow, hval] at h1
  simpa using h1

/-- If `D = y + v + a₁x + a₃` is a unit at the place, then the slope `(y-v)/(x-u)` is integral.
This is the slope identity `(y-v)·D = (x-u)·B` with `B` integral. -/
private lemma isIntegralK_slope_of_val_D_eq_one {x y u v : K}
    (h : W.Equation x y) (h' : W.Equation u v)
    (hx : IsIntegralK R K x) (hu : IsIntegralK R K u) (hne : x ≠ u)
    (hD : val R K (y + v + W.a₁ * x + W.a₃) = 1) :
    IsIntegralK R K (W.slope x u y v) := by
  have hy : IsIntegralK R K y := isIntegralK_of_equation h hx
  have hv : IsIntegralK R K v := isIntegralK_of_equation h' hu
  have hB : IsIntegralK R K (x ^ 2 + x * u + u ^ 2 + W.a₂ * (x + u) + W.a₄ - W.a₁ * v) :=
    isIntegralK_slope_B hx hu hv
  have hkey : val R K (y - v)
      = val R K (x - u)
        * val R K (x ^ 2 + x * u + u ^ 2 + W.a₂ * (x + u) + W.a₄ - W.a₁ * v) := by
    have h1 := congrArg (val R K) (slope_mul_eq h h')
    rw [Valuation.map_mul, Valuation.map_mul, hD, mul_one] at h1
    exact h1
  have hxu : val R K (x - u) ≠ 0 := by
    intro h0
    exact hne (sub_eq_zero.mp ((Valuation.zero_iff (val R K)).mp h0))
  show val R K (W.slope x u y v) ≤ 1
  rw [slope_of_X_ne hne, Valuation.map_div, hkey]
  rw [mul_div_cancel_left₀
    (val R K (x ^ 2 + x * u + u ^ 2 + W.a₂ * (x + u) + W.a₄ - W.a₁ * v)) hxu]
  exact hB

/-- `addX x u ℓ = ℓ² + a₁ℓ - a₂ - x - u` is integral as soon as `ℓ`, `x`, `u` are. -/
private lemma isIntegralK_addX_of_slope {x y u v : K} (hx : IsIntegralK R K x) (hu : IsIntegralK R K u)
    (hℓ : IsIntegralK R K (W.slope x u y v)) :
    IsIntegralK R K (W.addX x u (W.slope x u y v)) := by
  have h1 : IsIntegralK R K (W.slope x u y v ^ 2) := hℓ.pow 2
  have h2 : IsIntegralK R K (W.a₁ * W.slope x u y v) := isIntegralK_a₁.mul hℓ
  have h3 : IsIntegralK R K (W.a₂) := isIntegralK_a₂
  have hcomb := (((h1.add h2).sub h3).sub hx).sub hu
  simpa only [WeierstrassCurve.Affine.addX] using hcomb

end Valuation

/-! ## The coefficients of the reduced curve -/

section ReducedCoeff

variable {K : Type*} [Field K] {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Algebra R K] [IsFractionRing R K]
variable {W : Affine K} [W.HasGoodReduction R]

private lemma reduction_a₁_eq :
    (W.reduction R).a₁ = residue R (WeierstrassCurve.integralModel R W).a₁ := by
  rw [WeierstrassCurve.reduction, WeierstrassCurve.map_a₁]

private lemma reduction_a₃_eq :
    (W.reduction R).a₃ = residue R (WeierstrassCurve.integralModel R W).a₃ := by
  rw [WeierstrassCurve.reduction, WeierstrassCurve.map_a₃]

end ReducedCoeff

/-! ## The main theorem -/

theorem redPoint_add_of_not_integral_sum {K : Type*} [Field K] [DecidableEq K]
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R K] [IsFractionRing R K] [DecidableEq (IsLocalRing.ResidueField R)]
    {W : WeierstrassCurve.Affine K} [W.HasGoodReduction R] {x y u v : K}
    (h : WeierstrassCurve.Affine.Nonsingular W x y)
    (h' : WeierstrassCurve.Affine.Nonsingular W u v)
    (hx : ∃ r : R, algebraMap R K r = x) (hu : ∃ r : R, algebraMap R K r = u) (hne : x ≠ u)
    (hS : Work.SilvermanReduction.HasNegativeValuation R
      (WeierstrassCurve.Affine.Point.some x y h +
        WeierstrassCurve.Affine.Point.some u v h')) :
    Work.SilvermanReduction.redPoint R W
        (WeierstrassCurve.Affine.Point.some x y h +
          WeierstrassCurve.Affine.Point.some u v h') =
      Work.SilvermanReduction.redPoint R W (WeierstrassCurve.Affine.Point.some x y h) +
        Work.SilvermanReduction.redPoint R W (WeierstrassCurve.Affine.Point.some u v h') := by
  classical
  obtain ⟨r, hr⟩ := hx
  obtain ⟨r', hr'⟩ := hu
  obtain ⟨s, hs⟩ : ∃ s : R, algebraMap R K s = y := exists_lift_of_y (W := W) h ⟨r, hr⟩
  obtain ⟨s', hs'⟩ : ∃ s' : R, algebraMap R K s' = v := exists_lift_of_y (W := W) h' ⟨r', hr'⟩
  -- the sum reduces to `0`
  have hpq_zero : redPoint R W (Point.some x y h + Point.some u v h') = 0 :=
    (redPoint_eq_zero_iff R _).mpr (Or.inr hS)
  rw [hpq_zero]
  -- set up the sum coordinates
  have hadd : Point.some x y h + Point.some u v h' =
      Point.some (W.addX x u (W.slope x u y v)) (W.addY x u y (W.slope x u y v))
        (nonsingular_add h h' (fun hxy => hne hxy.1)) :=
    Point.add_some (fun hxy => hne hxy.1)
  -- the `x`-coordinate of the sum is not integral
  have hX3 : 1 < val R K (W.addX x u (W.slope x u y v)) := by
    have hS' : HasNegativeValuation R (Point.some (W.addX x u (W.slope x u y v))
        (W.addY x u y (W.slope x u y v)) (nonsingular_add h h' (fun hxy => hne hxy.1))) := by
      rw [← hadd]; exact hS
    exact (hasNegativeValuation_some_iff R _).mp hS'
  have hxI : IsIntegralK R K x := (IsIntegralK.iff_exists x).mpr ⟨r, hr⟩
  have huI : IsIntegralK R K u := (IsIntegralK.iff_exists u).mpr ⟨r', hr'⟩
  -- the sum of the two reduced points is `0`
  have hsum0 : redPoint R W (Point.some x y h) + redPoint R W (Point.some u v h') = 0 := by
    rw [redPoint_some_mk (R := R) h hr hs, redPoint_some_mk (R := R) h' hr' hs']
    by_cases hrr' : residue R r = residue R r'
    · have hsy : residue R s =
          WeierstrassCurve.Affine.negY (W.reduction R) (residue R r') (residue R s') := by
        set ρ : R := s + s' + (WeierstrassCurve.integralModel R W).a₁ * r
          + (WeierstrassCurve.integralModel R W).a₃ with hρdef
        have hρzero : residue R ρ = 0 := by
          by_contra hρ
          have hDval : val R K (y + v + W.a₁ * x + W.a₃) = 1 := by
            have hDlift : y + v + W.a₁ * x + W.a₃ = algebraMap R K ρ := by
              simp only [hρdef, map_add, map_mul, WeierstrassCurve.integralModel_a₁_eq R W,
                WeierstrassCurve.integralModel_a₃_eq R W, hr, hs, hs', hr']
            rw [hDlift, val_algebraMap_eq_one_iff]
            exact fun hmem => hρ ((IsLocalRing.residue_eq_zero_iff ρ).mpr hmem)
          have hslope : IsIntegralK R K (W.slope x u y v) :=
            isIntegralK_slope_of_val_D_eq_one h.1 h'.1 hxI huI hne hDval
          exact (not_le.mpr hX3) (isIntegralK_addX_of_slope hxI huI hslope)
        have hDsum : residue R s + residue R s' + (W.reduction R).a₁ * residue R r
            + (W.reduction R).a₃ = 0 := by
          rw [reduction_a₁_eq (R := R) (W := W), reduction_a₃_eq (R := R) (W := W)]
          have hh := hρzero
          rw [hρdef] at hh
          simp only [map_add, map_mul] at hh
          exact hh
        have hDsum' : residue R s + residue R s' + (W.reduction R).a₁ * residue R r'
            + (W.reduction R).a₃ = 0 := by
          rw [← hrr']; exact hDsum
        rw [WeierstrassCurve.Affine.negY]
        linear_combination (norm := first | refl_ring1 | ring1) hDsum'
      exact Point.add_of_Y_eq hrr' hsy
    · exfalso
      exact (not_le.mpr hX3) (isIntegralK_addX_of_residue_ne h.1 h'.1 hr hs hr' hs' hne hrr')
  exact hsum0.symm

end

end Work.SilvermanReduction
