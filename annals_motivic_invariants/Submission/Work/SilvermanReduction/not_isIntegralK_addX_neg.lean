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
# The difference of two integral points with the same reduction has negative valuation

If `P = (x,y)` and `Q = (u,v)` are two nonsingular points of a Weierstrass curve `W/K` with good
reduction at a discrete valuation ring `R ⊆ K`, whose coordinates are integral (`x, y, u, v` lift
to `R`) and whose reductions in the special fibre coincide, and if `x ≠ u`, then `P - Q` is a point
of negative valuation: the `x`-coordinate of `P - Q`, computed by the chord–tangent formula, has
value `> 1`.

Concretely, the `x`-coordinate of `P - Q = P + (u, -v)` is
`addX W x u (slope W x u y (negY W u v))`, and the statement is that it is *not* integral.

## Proof outline

Write `D = x - u`, `E = y - v`, `Y = y + v + a₁u + a₃` (the numerator of the slope of the chord
through `P` and `-Q`) and `C = u² + ux + x² + a₂(u+x) + a₄ - a₁y`.  The chord identity gives
`E * Y = D * C`.  Both `D` and `E` lie in the maximal ideal (the reductions of the coordinates
coincide), and `Y`, `C` are integral; because the reduction of `(r,s)` is a nonsingular point of the
special fibre, `Y` and `C` cannot both be non-units.  Hence, splitting on whether `Y` is a unit,

* if `Y` is a unit then `val (Y/D) = 1/val D > 1`;
* otherwise `C` is a unit and `E * Y = D * C` gives `val (Y/D) = 1/val E > 1`.

In both cases the slope `λ = Y/D` has value `> 1`, so `λ²` dominates `a₁λ` and `a₂ + x + u` in
`addX W x u λ = λ² + a₁λ - a₂ - x - u`, and that `x`-coordinate has value `val λ * val λ > 1`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open WeierstrassCurve WeierstrassCurve.Affine
open IsLocalRing (ResidueField residue)
open scoped WithZero

namespace Work.SilvermanReduction

noncomputable section

section Helpers

variable {K : Type*} [Field K] {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Algebra R K] [IsFractionRing R K]

/-- The lift `s + s' + a₁ r' + a₃` of the chord numerator `y + v + a₁u + a₃` reduces to `∂F/∂Y` at
the reduction of `(r, s)`. -/
private lemma residue_chordY {W : WeierstrassCurve.Affine K} [W.HasGoodReduction R]
    (r r' s s' : R) (hru : residue R r = residue R r') (hsv : residue R s = residue R s') :
    residue R (s + s' + (WeierstrassCurve.integralModel R W).a₁ * r'
        + (WeierstrassCurve.integralModel R W).a₃)
      = 2 * residue R s + (W.reduction R).a₁ * residue R r + (W.reduction R).a₃ := by
  rw [WeierstrassCurve.reduction, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]
  simp only [map_add, map_mul]
  rw [← hru, ← hsv]
  first | refl_ring1 | ring

/-- The lift `r'² + r'r + r² + a₂(r'+r) + a₄ - a₁s` of the chord denominator
`u² + ux + x² + a₂(u+x) + a₄ - a₁y` reduces to `-∂F/∂X` at the reduction of `(r, s)`. -/
private lemma residue_chordX {W : WeierstrassCurve.Affine K} [W.HasGoodReduction R]
    (r r' s : R) (hru : residue R r = residue R r') :
    residue R (r' ^ 2 + r' * r + r ^ 2 + (WeierstrassCurve.integralModel R W).a₂ * (r' + r)
        + (WeierstrassCurve.integralModel R W).a₄ - (WeierstrassCurve.integralModel R W).a₁ * s)
      = - ((W.reduction R).a₁ * residue R s
          - (3 * (residue R r) ^ 2 + 2 * (W.reduction R).a₂ * residue R r
              + (W.reduction R).a₄)) := by
  rw [WeierstrassCurve.reduction, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₄]
  simp only [map_add, map_sub, map_mul, map_pow]
  rw [← hru]
  first | refl_ring1 | ring

end Helpers

theorem not_isIntegralK_addX_neg {K : Type*} [Field K] [DecidableEq K] {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Algebra R K] [IsFractionRing R K]
    {W : WeierstrassCurve.Affine K} [W.HasGoodReduction R] {x y u v : K}
    (h : WeierstrassCurve.Affine.Nonsingular W x y)
    (h' : WeierstrassCurve.Affine.Nonsingular W u v)
    {r s r' s' : R} (hr : algebraMap R K r = x) (hs : algebraMap R K s = y)
    (hr' : algebraMap R K r' = u) (hs' : algebraMap R K s' = v)
    (hru : IsLocalRing.residue R r = IsLocalRing.residue R r')
    (hsv : IsLocalRing.residue R s = IsLocalRing.residue R s') (hxu : x ≠ u) :
    ¬ Work.SilvermanReduction.IsIntegralK R K (WeierstrassCurve.Affine.addX W x u (WeierstrassCurve.Affine.slope W x u y (WeierstrassCurve.Affine.negY W u v))) := by
  classical
  set D : K := x - u with hD
  set E : K := y - v with hE
  set Y : K := y + v + W.a₁ * u + W.a₃ with hY
  set C : K := u ^ 2 + u * x + x ^ 2 + W.a₂ * (u + x) + W.a₄ - W.a₁ * y with hC
  -- ### the chord identity
  have hchord : E * Y = D * C := by
    rw [hE, hD, hY, hC]
    exact chord_identity' (W' := W) h.1 h'.1
  -- ### integrality of the four coordinates
  have hxI : IsIntegralK R K x := by rw [← hr]; exact IsIntegralK.of_algebraMap r
  have hyI : IsIntegralK R K y := by rw [← hs]; exact IsIntegralK.of_algebraMap s
  have huI : IsIntegralK R K u := by rw [← hr']; exact IsIntegralK.of_algebraMap r'
  have hvI : IsIntegralK R K v := by rw [← hs']; exact IsIntegralK.of_algebraMap s'
  have hYle : val R K Y ≤ 1 := by
    rw [hY]
    exact (((hyI.add hvI)).add (isIntegralK_a₁.mul huI)).add isIntegralK_a₃
  have hCle : val R K C ≤ 1 := by
    rw [hC]
    exact (((((huI.pow 2).add (huI.mul hxI)).add (hxI.pow 2)).add
      (isIntegralK_a₂.mul (huI.add hxI))).add isIntegralK_a₄).sub (isIntegralK_a₁.mul hyI)
  -- ### the chord numerator/denominator as lifts
  have hYeq : algebraMap R K (s + s' + (WeierstrassCurve.integralModel R W).a₁ * r'
      + (WeierstrassCurve.integralModel R W).a₃) = Y := by
    rw [hY]
    simp only [map_add, map_mul, hr', hs, hs',
      WeierstrassCurve.integralModel_a₁_eq, WeierstrassCurve.integralModel_a₃_eq]
  have hCeq : algebraMap R K (r' ^ 2 + r' * r + r ^ 2
      + (WeierstrassCurve.integralModel R W).a₂ * (r' + r)
      + (WeierstrassCurve.integralModel R W).a₄
      - (WeierstrassCurve.integralModel R W).a₁ * s) = C := by
    rw [hC]
    simp only [map_add, map_sub, map_mul, map_pow, hr, hr', hs,
      WeierstrassCurve.integralModel_a₁_eq, WeierstrassCurve.integralModel_a₂_eq,
      WeierstrassCurve.integralModel_a₄_eq]
  -- ### `Y` and `C` cannot both be non-units
  have hYlt_iff : val R K Y < 1 ↔
      2 * residue R s + (W.reduction R).a₁ * residue R r + (W.reduction R).a₃ = 0 := by
    rw [← hYeq, val_algebraMap_lt_one_iff_residue_eq_zero,
      residue_chordY r r' s s' hru hsv]
  have hClt_iff : val R K C < 1 ↔
      (W.reduction R).a₁ * residue R s
        - (3 * (residue R r) ^ 2 + 2 * (W.reduction R).a₂ * residue R r
            + (W.reduction R).a₄) = 0 := by
    rw [← hCeq, val_algebraMap_lt_one_iff_residue_eq_zero, residue_chordX r r' s hru,
      neg_eq_zero]
  have hnotboth : ¬ (val R K Y < 1 ∧ val R K C < 1) := by
    rintro ⟨hYl, hCl⟩
    have hns := (WeierstrassCurve.Affine.nonsingular_iff'
        (W := W.reduction R) (residue R r) (residue R s)).mp
      (nonsingular_reduction (W := W) (equation_integralModel (W := W) h.1 hr hs))
    rcases hns.2 with hpx | hpy
    · exact hpx (hClt_iff.mp hCl)
    · exact hpy (hYlt_iff.mp hYl)
  have hdisj : val R K Y = 1 ∨ val R K C = 1 := by
    by_cases hYl : val R K Y < 1
    · exact Or.inr (le_antisymm hCle (not_lt.mp fun hCl => hnotboth ⟨hYl, hCl⟩))
    · exact Or.inl (le_antisymm hYle (not_lt.mp hYl))
  -- ### `D = x - u` and `E = y - v` lie in the maximal ideal
  have hDne : D ≠ 0 := by rw [hD, sub_ne_zero]; exact hxu
  have hDmem : r - r' ∈ IsLocalRing.maximalIdeal R := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hru, sub_self]
  have hDlt : val R K D < 1 := by
    have hDalg : D = algebraMap R K (r - r') := by rw [hD, map_sub, hr, hr']
    rw [hDalg]
    exact val_algebraMap_lt_one_iff.mpr hDmem
  have hDpos : 0 < val R K D := (Valuation.pos_iff (val R K)).mpr hDne
  have hEmem : s - s' ∈ IsLocalRing.maximalIdeal R := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hsv, sub_self]
  have hElt : val R K E < 1 := by
    have hEalg : E = algebraMap R K (s - s') := by rw [hE, map_sub, hs, hs']
    rw [hEalg]
    exact val_algebraMap_lt_one_iff.mpr hEmem
  -- ### the main valuation estimate `val D < val Y`
  have hDY : val R K D < val R K Y := by
    by_cases hY1 : val R K Y = 1
    · rw [hY1]; exact hDlt
    · have hC1 : val R K C = 1 := hdisj.resolve_left hY1
      have hval : val R K D = val R K E * val R K Y := by
        have hh := congrArg (val R K) hchord
        rw [map_mul, map_mul, hC1, mul_one] at hh
        exact hh.symm
      have hYne : val R K Y ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hval
        exact hDne ((Valuation.zero_iff (val R K)).mp hval)
      have hYpos : 0 < val R K Y := zero_lt_iff.mpr hYne
      calc val R K D = val R K E * val R K Y := hval
        _ < 1 * val R K Y := mul_lt_mul_of_pos_right hElt hYpos
        _ = val R K Y := one_mul _
  -- ### the slope has value `> 1`
  have hnum : y - W.negY u v = Y := by
    rw [hY, WeierstrassCurve.Affine.negY]; ring
  set L : K := W.slope x u y (W.negY u v) with hL
  have hslope : L = Y / D := by
    rw [hL, slope_of_X_ne hxu, hnum, hD]
  have hLval : 1 < val R K L := by
    rw [hslope, Valuation.map_div]
    exact (one_lt_div₀ hDpos).mpr hDY
  -- ### the `x`-coordinate of the sum is dominated by `λ²`
  have hLsq : val R K (L ^ 2) = val R K L * val R K L := by rw [map_pow, pow_two]
  have hLpos : 0 < val R K L := lt_trans zero_lt_one hLval
  have hLlt : val R K L < val R K (L ^ 2) := by
    rw [hLsq]
    simpa using mul_lt_mul_of_pos_left hLval hLpos
  have hB1 : val R K (W.a₁ * L) < val R K (L ^ 2) := by
    calc val R K (W.a₁ * L) = val R K W.a₁ * val R K L := by rw [map_mul]
      _ ≤ 1 * val R K L :=
          mul_le_mul_of_nonneg_right (show val R K W.a₁ ≤ 1 from isIntegralK_a₁) zero_le
      _ = val R K L := one_mul _
      _ < val R K (L ^ 2) := hLlt
  have hB2 : val R K (-(W.a₂ + x + u)) < val R K (L ^ 2) := by
    rw [Valuation.map_neg]
    exact lt_of_le_of_lt (show val R K (W.a₂ + x + u) ≤ 1 from
      (isIntegralK_a₂.add hxI).add huI) (by rw [hLsq]; exact one_lt_mul_self hLval)
  have hB : val R K (W.a₁ * L - W.a₂ - x - u) < val R K (L ^ 2) := by
    rw [show W.a₁ * L - W.a₂ - x - u = W.a₁ * L + (-(W.a₂ + x + u)) by ring]
    exact Valuation.map_add_lt (val R K) hB1 hB2
  have hx3val : val R K (W.addX x u L) = val R K (L ^ 2) := by
    rw [WeierstrassCurve.Affine.addX,
      show L ^ 2 + W.a₁ * L - W.a₂ - x - u = (W.a₁ * L - W.a₂ - x - u) + L ^ 2 by ring]
    exact Valuation.map_add_eq_of_lt_right (val R K) hB
  have hfinal : 1 < val R K (W.addX x u L) := by
    rw [hx3val, hLsq]
    exact one_lt_mul_self hLval
  intro hx3
  exact absurd hx3 (not_le.mpr hfinal)

end

end Work.SilvermanReduction
