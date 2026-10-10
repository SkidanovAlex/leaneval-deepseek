import Mathlib
import Submission.Work.SilvermanReduction.Basic
import Submission.Work.SilvermanReduction.API
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.SilvermanReduction

/-- **The chord case on the special fibre.**  Let `R` be a discrete valuation ring with fraction
field `K`, `W/K` a Weierstrass curve with good reduction, and `r, s, r', s' ∈ R` lifts whose
residues satisfy `res r = res r'` (`hξ`) and `res s' = res s` (`hη`).  Assume the reduced point
`(res r, res s)` is not `2`-torsion: `res s ≠ negY (res r') (res s')` (`hnt`).

Write `A := WeierstrassCurve.integralModel R W`,
`d := s + s' + A.a₁ * r + A.a₃` and
`n := r² + r*r' + r'² + A.a₂*(r + r') + A.a₄ - A.a₁*s'`.

Then `d` is a unit of `R`, and the slope of the reduced points
`(res r, res s)`, `(res r', res s')` — whose `x`-coordinates coincide by `hξ`, so that it is the
*tangent* slope at the common reduced point — is the quotient `res n / res d` of the residues. -/
theorem residue_chord_ne_x {K : Type*} [Field K] {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Algebra R K] [IsFractionRing R K]
    [DecidableEq (IsLocalRing.ResidueField R)]
    {W : WeierstrassCurve.Affine K} [W.HasGoodReduction R] {r s r' s' : R}
    (hξ : IsLocalRing.residue R r = IsLocalRing.residue R r')
    (hη : IsLocalRing.residue R s' = IsLocalRing.residue R s)
    (hnt : IsLocalRing.residue R s ≠
      WeierstrassCurve.Affine.negY (W.reduction R) (IsLocalRing.residue R r')
        (IsLocalRing.residue R s')) :
    IsUnit (s + s' + (WeierstrassCurve.integralModel R W).a₁ * r
        + (WeierstrassCurve.integralModel R W).a₃) ∧
      WeierstrassCurve.Affine.slope (W.reduction R) (IsLocalRing.residue R r)
          (IsLocalRing.residue R r') (IsLocalRing.residue R s) (IsLocalRing.residue R s')
        = IsLocalRing.residue R
            (r ^ 2 + r * r' + r' ^ 2 + (WeierstrassCurve.integralModel R W).a₂ * (r + r')
              + (WeierstrassCurve.integralModel R W).a₄
              - (WeierstrassCurve.integralModel R W).a₁ * s')
          / IsLocalRing.residue R
            (s + s' + (WeierstrassCurve.integralModel R W).a₁ * r
              + (WeierstrassCurve.integralModel R W).a₃) := by
  -- the coefficients of the special fibre are the residues of the coefficients of the integral
  -- model of `W`
  have hA1 : (W.reduction R).a₁ = IsLocalRing.residue R (WeierstrassCurve.integralModel R W).a₁ :=
    WeierstrassCurve.map_a₁ (WeierstrassCurve.integralModel R W) (IsLocalRing.residue R)
  have hA2 : (W.reduction R).a₂ = IsLocalRing.residue R (WeierstrassCurve.integralModel R W).a₂ :=
    WeierstrassCurve.map_a₂ (WeierstrassCurve.integralModel R W) (IsLocalRing.residue R)
  have hA3 : (W.reduction R).a₃ = IsLocalRing.residue R (WeierstrassCurve.integralModel R W).a₃ :=
    WeierstrassCurve.map_a₃ (WeierstrassCurve.integralModel R W) (IsLocalRing.residue R)
  have hA4 : (W.reduction R).a₄ = IsLocalRing.residue R (WeierstrassCurve.integralModel R W).a₄ :=
    WeierstrassCurve.map_a₄ (WeierstrassCurve.integralModel R W) (IsLocalRing.residue R)
  -- the two points of the special fibre have the same `x`-coordinate, hence opposite
  -- `y`-coordinates agree
  have hnegY : WeierstrassCurve.Affine.negY (W.reduction R) (IsLocalRing.residue R r)
        (IsLocalRing.residue R s)
      = WeierstrassCurve.Affine.negY (W.reduction R) (IsLocalRing.residue R r')
        (IsLocalRing.residue R s') := by
    simp only [WeierstrassCurve.Affine.negY, hξ, hη]
  -- **the residue of the denominator** `d = s + s' + A.a₁ * r + A.a₃` is
  -- `η - negY ξ η' = η + η' + Ã₁ ξ + Ã₃`; by `hη` and `hξ` this is the *same* at the two points
  have hdres : IsLocalRing.residue R (s + s' + (WeierstrassCurve.integralModel R W).a₁ * r
        + (WeierstrassCurve.integralModel R W).a₃)
      = IsLocalRing.residue R s
        - WeierstrassCurve.Affine.negY (W.reduction R) (IsLocalRing.residue R r')
            (IsLocalRing.residue R s') := by
    simp only [map_add, map_mul, ← hA1, ← hA3, WeierstrassCurve.Affine.negY]
    rw [hξ, hη]
    first | refl_ring1 | ring
  -- **the residue of the numerator** `n` is the numerator of the *tangent* slope at the common
  -- reduced point, because `ξ = ξ'` and `η = η'`
  have hnres : IsLocalRing.residue R
        (r ^ 2 + r * r' + r' ^ 2 + (WeierstrassCurve.integralModel R W).a₂ * (r + r')
          + (WeierstrassCurve.integralModel R W).a₄
          - (WeierstrassCurve.integralModel R W).a₁ * s')
      = 3 * (IsLocalRing.residue R r) ^ 2 + 2 * (W.reduction R).a₂ * (IsLocalRing.residue R r)
          + (W.reduction R).a₄ - (W.reduction R).a₁ * (IsLocalRing.residue R s) := by
    simp only [map_add, map_sub, map_mul, map_pow, ← hA1, ← hA2, ← hA4]
    rw [hξ, hη]
    first | refl_ring1 | ring
  have hdunit : IsUnit (s + s' + (WeierstrassCurve.integralModel R W).a₁ * r
      + (WeierstrassCurve.integralModel R W).a₃) := by
    rw [Work.SilvermanReduction.isUnit_iff_residue_ne_zero', hdres]
    exact fun h => hnt (sub_eq_zero.mp h)
  refine ⟨hdunit, ?_⟩
  -- the slope of the reduced points, with equal `x`-coordinates and non-vanishing tangent
  -- denominator `η - negY ξ' η' ≠ 0`, is the tangent slope; its numerator and denominator are the
  -- residues computed above
  rw [WeierstrassCurve.Affine.slope_of_Y_ne hξ hnt, hnres, hdres, hnegY]

end Work.SilvermanReduction
