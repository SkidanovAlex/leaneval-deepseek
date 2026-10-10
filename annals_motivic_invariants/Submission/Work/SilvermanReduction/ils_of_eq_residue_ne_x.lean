import Mathlib
import Submission.Work.SilvermanReduction.Basic
import Submission.Work.SilvermanReduction.API
import Submission.Work.SilvermanReduction.Helpers
import Submission.Work.SilvermanReduction.slope_eq_div_of_chord
import Submission.Work.SilvermanReduction.residue_chord_ne_x

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.SilvermanReduction

/-- **The chord-identity case of the reduction of the slope.**  Let `R` be a discrete valuation
ring with fraction field `K`, `W/K` a Weierstrass curve with good reduction at `R`, and `(x,y)`,
`(u,v)` nonsingular points of `W` whose coordinates lift to `r,s,r',s' ∈ R`.  Assume the lifts have
the same residue in `x` (`hξ`) but are different (`hrr : r ≠ r'`), so that `x ≠ u` in `K` while the
reduced points have the same `x`-coordinate; assume moreover that the reduced point
`(residue r, residue s)` is not `2`-torsion (`hnt`, using `hη`).

Then the slope `W.slope x u y v` (a chord slope) is the image of an element `ρ ∈ R`, and the
reduction of `ρ` equals the slope of the reduced points.

Proof route: since `r ≠ r'`, `x ≠ u`, so `W.slope x u y v = (y-v)/(x-u)`; the chord identity
`slope_mul_eq` (`Submission.Work.SilvermanReduction.Helpers`) gives
`(y-v)(y+v+a₁x+a₃) = (x-u)(x²+xu+u²+a₂(x+u)+a₄-a₁v)`.  The element
`d := s + s' + A.a₁*r + A.a₃` of `R` (`A = WeierstrassCurve.integralModel R W`) maps to
`y + v + a₁x + a₃` and has residue `η + η' + Ã₁ξ + Ã₃ = 2η + Ã₁ξ + Ã₃ = η - negY ξ η ≠ 0` by `hnt`
and `hη`, hence is a unit; so `W.slope x u y v = (algebraMap R K n)/(algebraMap R K d)` with
`n := r² + r*r' + r'² + A.a₂*(r+r') + A.a₄ - A.a₁*s'` (the numerator of the right side of the chord
identity).  On the reduced side the `x`-coordinates coincide, so the slope is the *tangent* slope
`(3ξ² + 2Ã₂ξ + Ã₄ - Ã₁η)/(η - negY ξ η)`, whose numerator and denominator are the residues of `n`
and of `d`.  `exists_lift_div` (`Submission.Work.SilvermanReduction.API`) then gives `ρ`. -/
theorem ils_of_eq_residue_ne_x {K : Type*} [Field K] [DecidableEq K] {R : Type*} [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] [Algebra R K] [IsFractionRing R K]
    [DecidableEq (IsLocalRing.ResidueField R)]
    {W : WeierstrassCurve.Affine K} [W.HasGoodReduction R] {x y u v : K}
    (h : WeierstrassCurve.Affine.Nonsingular W x y)
    (h' : WeierstrassCurve.Affine.Nonsingular W u v)
    {r s r' s' : R} (hr : algebraMap R K r = x) (hs : algebraMap R K s = y)
    (hr' : algebraMap R K r' = u) (hs' : algebraMap R K s' = v)
    (hξ : IsLocalRing.residue R r = IsLocalRing.residue R r') (hrr : r ≠ r')
    (hη : IsLocalRing.residue R s' = IsLocalRing.residue R s)
    (hnt : IsLocalRing.residue R s ≠
      WeierstrassCurve.Affine.negY (W.reduction R) (IsLocalRing.residue R r')
        (IsLocalRing.residue R s')) :
    ∃ ρ : R, algebraMap R K ρ = WeierstrassCurve.Affine.slope W x u y v ∧
      IsLocalRing.residue R ρ = WeierstrassCurve.Affine.slope (W.reduction R)
        (IsLocalRing.residue R r) (IsLocalRing.residue R r') (IsLocalRing.residue R s)
        (IsLocalRing.residue R s') := by
  classical
  -- `r ≠ r'` forces `x ≠ u`, since `algebraMap R K` is injective.
  have hxu : x ≠ u := by
    intro hx
    apply hrr
    have : algebraMap R K r = algebraMap R K r' := by rw [hr, hx, ← hr']
    exact algebraMap_injective this
  -- The numerator and denominator of the right side of the chord identity, in `R`.
  let A := WeierstrassCurve.integralModel R W
  let n : R := r ^ 2 + r * r' + r' ^ 2 + A.a₂ * (r + r') + A.a₄ - A.a₁ * s'
  let d : R := s + s' + A.a₁ * r + A.a₃
  -- `d` is a unit, and the reduced slope is `residue n / residue d`.
  have hdunit : IsUnit d := (residue_chord_ne_x (K := K) (W := W) hξ hη hnt).1
  have hDeq : algebraMap R K d = y + v + W.a₁ * x + W.a₃ := by
    simp only [d, A, map_add, map_mul, hr, hs, hs',
      WeierstrassCurve.integralModel_a₁_eq, WeierstrassCurve.integralModel_a₃_eq]
  have hNeq : algebraMap R K n = x ^ 2 + x * u + u ^ 2 + W.a₂ * (x + u) + W.a₄ - W.a₁ * v := by
    simp only [n, A, map_add, map_mul, map_sub, map_pow, hr, hr', hs',
      WeierstrassCurve.integralModel_a₁_eq, WeierstrassCurve.integralModel_a₂_eq,
      WeierstrassCurve.integralModel_a₄_eq]
  have hDne : y + v + W.a₁ * x + W.a₃ ≠ 0 := by
    rw [← hDeq]
    exact (IsUnit.map (algebraMap R K) hdunit).ne_zero
  -- The chord identity computes the slope over `K`.
  have hslope : WeierstrassCurve.Affine.slope W x u y v = algebraMap R K n / algebraMap R K d := by
    have h0 := slope_eq_div_of_chord (W := W) h.1 h'.1 hxu hDne
    rw [← hNeq, ← hDeq] at h0
    exact h0
  obtain ⟨ρ, hρ, hρres⟩ := exists_lift_div (K := K) (n := n) (d := d) hdunit
  refine ⟨ρ, ?_, ?_⟩
  · rw [hρ, hslope]
  · rw [hρres]
    exact ((residue_chord_ne_x (K := K) (W := W) hξ hη hnt).2).symm

end Work.SilvermanReduction
