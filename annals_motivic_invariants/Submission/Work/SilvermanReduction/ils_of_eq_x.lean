import Mathlib
import Submission.Work.SilvermanReduction.Basic
import Submission.Work.SilvermanReduction.API

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open WeierstrassCurve WeierstrassCurve.Affine
open IsLocalRing (ResidueField residue)
open scoped WithZero

namespace Work.SilvermanReduction

noncomputable section

/-- **The tangent case of the reduction of the slope.**  Let `R` be a discrete valuation ring with
fraction field `K`, `W/K` a Weierstrass curve with good reduction at `R`, and `(x,y)`, `(u,v)`
nonsingular points of `W` whose coordinates lift to `r,s,r',s' ∈ R`.  Assume `r = r'` (so the two
points have the same `x`-coordinate in `K`) and that the `y`-coordinate of the reduction of `(x,y)`
is not the `y`-coordinate of its own negative, i.e. the reduced point `(residue r, residue s)` is
not `2`-torsion.

Then the slope `W.slope x u y v` (a tangent slope) is the image of an element `ρ ∈ R`, and the
reduction of `ρ` is the slope of the reduced points `(residue r, residue s)`,
`(residue r', residue s')`.

Proof route: `r = r'` gives `x = u`, so `W.slope x u y v` is the tangent slope
`(3x² + 2a₂x + a₄ - a₁y)/(y - W.negY x y)` provided `y ≠ W.negY x y`; the latter follows from the
non-`2`-torsion hypothesis (`y = W.negY x y` would force `residue s = negY (residue r) (residue s)`
once one knows that `negY` commutes with `algebraMap R K` and with `residue R`, and that `hη`
identifies the two `y`-coordinates).  Then `y - W.negY x y` is the image of the element
`2s + A.a₁*r + A.a₃` of `R` (where `A = WeierstrassCurve.integralModel R W`), whose residue
`2η + Ã₁ξ + Ã₃` is nonzero, hence a unit; `exists_lift_div` (in
`Submission.Work.SilvermanReduction.API`) applied to `n = 3r² + 2A.a₂r + A.a₄ - A.a₁s` and
`d = 2s + A.a₁r + A.a₃` produces `ρ`, and `map_add`, `map_mul` and
`WeierstrassCurve.integralModel_aᵢ_eq` identify the two sides.  On the reduced side the
`x`-coordinates coincide (`hξ`), so `slope_of_Y_ne` again gives the tangent slope, whose numerator
and denominator are the residues of `n` and `d`. -/
theorem ils_of_eq_x {K : Type*} [Field K] [DecidableEq K] {R : Type*} [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] [Algebra R K] [IsFractionRing R K]
    [DecidableEq (IsLocalRing.ResidueField R)]
    {W : WeierstrassCurve.Affine K} [W.HasGoodReduction R] {x y u v : K}
    {r s r' s' : R} (hr : algebraMap R K r = x) (hs : algebraMap R K s = y)
    (hr' : algebraMap R K r' = u) (hs' : algebraMap R K s' = v)
    (hξ : IsLocalRing.residue R r = IsLocalRing.residue R r') (hrr : r = r')
    (hη : IsLocalRing.residue R s' = IsLocalRing.residue R s)
    (hnt : IsLocalRing.residue R s ≠
      WeierstrassCurve.Affine.negY (W.reduction R) (IsLocalRing.residue R r')
        (IsLocalRing.residue R s')) :
    ∃ ρ : R, algebraMap R K ρ = WeierstrassCurve.Affine.slope W x u y v ∧
      IsLocalRing.residue R ρ = WeierstrassCurve.Affine.slope (W.reduction R)
        (IsLocalRing.residue R r) (IsLocalRing.residue R r') (IsLocalRing.residue R s)
        (IsLocalRing.residue R s') := by
  classical
  -- `r = r'` gives `x = u`
  have hxu : x = u := by rw [← hr, hrr, hr']
  -- `negY` commutes with `algebraMap`
  have hnegY_lift : ∀ a b : R,
      algebraMap R K (WeierstrassCurve.Affine.negY (WeierstrassCurve.integralModel R W) a b)
        = WeierstrassCurve.Affine.negY W (algebraMap R K a) (algebraMap R K b) := by
    intro a b
    simp only [WeierstrassCurve.Affine.negY, map_sub, map_neg, map_mul,
      WeierstrassCurve.integralModel_a₁_eq R W, WeierstrassCurve.integralModel_a₃_eq R W]
  -- `negY` commutes with `residue`
  have hnegY_res : ∀ a b : R,
      IsLocalRing.residue R (WeierstrassCurve.Affine.negY (WeierstrassCurve.integralModel R W) a b)
        = WeierstrassCurve.Affine.negY (W.reduction R) (IsLocalRing.residue R a)
            (IsLocalRing.residue R b) := by
    intro a b
    have hA1 : (W.reduction R).a₁ =
        IsLocalRing.residue R (WeierstrassCurve.integralModel R W).a₁ :=
      WeierstrassCurve.map_a₁ (WeierstrassCurve.integralModel R W) (IsLocalRing.residue R)
    have hA3 : (W.reduction R).a₃ =
        IsLocalRing.residue R (WeierstrassCurve.integralModel R W).a₃ :=
      WeierstrassCurve.map_a₃ (WeierstrassCurve.integralModel R W) (IsLocalRing.residue R)
    simp only [WeierstrassCurve.Affine.negY, map_sub, map_neg, map_mul, hA1, hA3]
  -- the non-`2`-torsion hypothesis, transported to the lifts `r`, `s`
  have hnt' : IsLocalRing.residue R s ≠
      WeierstrassCurve.Affine.negY (W.reduction R) (IsLocalRing.residue R r)
        (IsLocalRing.residue R s) := by
    have h1 : WeierstrassCurve.Affine.negY (W.reduction R) (IsLocalRing.residue R r')
          (IsLocalRing.residue R s')
        = WeierstrassCurve.Affine.negY (W.reduction R) (IsLocalRing.residue R r)
            (IsLocalRing.residue R s) := by
      rw [← hξ, hη]
    rwa [h1] at hnt
  -- hence `y ≠ W.negY u v`
  have hyne : y ≠ WeierstrassCurve.Affine.negY W u v := by
    intro hy
    have hseq : s = WeierstrassCurve.Affine.negY (WeierstrassCurve.integralModel R W) r' s' := by
      apply algebraMap_injective (R := R) (K := K)
      rw [hnegY_lift r' s', hs, hy, ← hr', ← hs']
    have h1 : IsLocalRing.residue R s
        = IsLocalRing.residue R
            (WeierstrassCurve.Affine.negY (WeierstrassCurve.integralModel R W) r' s') :=
      congrArg (IsLocalRing.residue R) hseq
    have h2 : IsLocalRing.residue R
          (WeierstrassCurve.Affine.negY (WeierstrassCurve.integralModel R W) r' s')
        = WeierstrassCurve.Affine.negY (W.reduction R) (IsLocalRing.residue R r)
            (IsLocalRing.residue R s) := by
      rw [hnegY_res r' s', ← hξ, hη]
    exact hnt' (h1.trans h2)
  -- the two tangent slope formulae
  have hslope : WeierstrassCurve.Affine.slope W x u y v
      = (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y)
        / (y - WeierstrassCurve.Affine.negY W x y) :=
    WeierstrassCurve.Affine.slope_of_Y_ne hxu hyne
  have hslope' : WeierstrassCurve.Affine.slope (W.reduction R)
        (IsLocalRing.residue R r) (IsLocalRing.residue R r')
        (IsLocalRing.residue R s) (IsLocalRing.residue R s')
      = (3 * (IsLocalRing.residue R r) ^ 2 + 2 * (W.reduction R).a₂ * (IsLocalRing.residue R r)
          + (W.reduction R).a₄ - (W.reduction R).a₁ * (IsLocalRing.residue R s))
        / (IsLocalRing.residue R s
          - WeierstrassCurve.Affine.negY (W.reduction R) (IsLocalRing.residue R r)
              (IsLocalRing.residue R s)) :=
    WeierstrassCurve.Affine.slope_of_Y_ne hξ hnt
  -- the numerator `n` and the denominator `d` of the tangent slope
  have hnlig : algebraMap R K (3 * r ^ 2 + 2 * (WeierstrassCurve.integralModel R W).a₂ * r
        + (WeierstrassCurve.integralModel R W).a₄
        - (WeierstrassCurve.integralModel R W).a₁ * s)
      = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat,
      WeierstrassCurve.integralModel_a₁_eq R W, WeierstrassCurve.integralModel_a₂_eq R W,
      WeierstrassCurve.integralModel_a₄_eq R W, hr, hs]
  have hdlig : algebraMap R K
        (s - WeierstrassCurve.Affine.negY (WeierstrassCurve.integralModel R W) r s)
      = y - WeierstrassCurve.Affine.negY W x y := by
    rw [map_sub, hs, hnegY_lift r s, hr, hs]
  have hdres : IsLocalRing.residue R
        (s - WeierstrassCurve.Affine.negY (WeierstrassCurve.integralModel R W) r s)
      = IsLocalRing.residue R s
        - WeierstrassCurve.Affine.negY (W.reduction R) (IsLocalRing.residue R r)
            (IsLocalRing.residue R s) := by
    rw [map_sub, hnegY_res r s]
  have hnres : IsLocalRing.residue R (3 * r ^ 2 + 2 * (WeierstrassCurve.integralModel R W).a₂ * r
        + (WeierstrassCurve.integralModel R W).a₄
        - (WeierstrassCurve.integralModel R W).a₁ * s)
      = 3 * (IsLocalRing.residue R r) ^ 2 + 2 * (W.reduction R).a₂ * (IsLocalRing.residue R r)
        + (W.reduction R).a₄ - (W.reduction R).a₁ * (IsLocalRing.residue R s) := by
    have hA1 : (W.reduction R).a₁ = IsLocalRing.residue R (WeierstrassCurve.integralModel R W).a₁ :=
      WeierstrassCurve.map_a₁ (WeierstrassCurve.integralModel R W) (IsLocalRing.residue R)
    have hA2 : (W.reduction R).a₂ = IsLocalRing.residue R (WeierstrassCurve.integralModel R W).a₂ :=
      WeierstrassCurve.map_a₂ (WeierstrassCurve.integralModel R W) (IsLocalRing.residue R)
    have hA4 : (W.reduction R).a₄ = IsLocalRing.residue R (WeierstrassCurve.integralModel R W).a₄ :=
      WeierstrassCurve.map_a₄ (WeierstrassCurve.integralModel R W) (IsLocalRing.residue R)
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, ← hA1, ← hA2, ← hA4]
  -- the denominator is a unit
  have hdunit : IsUnit
      (s - WeierstrassCurve.Affine.negY (WeierstrassCurve.integralModel R W) r s) := by
    rw [isUnit_iff_residue_ne_zero'
      (r := s - WeierstrassCurve.Affine.negY (WeierstrassCurve.integralModel R W) r s), hdres]
    intro hz
    exact hnt' (sub_eq_zero.mp hz)
  obtain ⟨ρ, hρ, hρres⟩ := exists_lift_div (K := K) (R := R)
    (n := 3 * r ^ 2 + 2 * (WeierstrassCurve.integralModel R W).a₂ * r
      + (WeierstrassCurve.integralModel R W).a₄ - (WeierstrassCurve.integralModel R W).a₁ * s)
    (d := s - WeierstrassCurve.Affine.negY (WeierstrassCurve.integralModel R W) r s) hdunit
  refine ⟨ρ, ?_, ?_⟩
  · rw [hρ, hnlig, hdlig]
    exact hslope.symm
  · rw [hρres, hnres, hdres]
    exact hslope'.symm

end

end Work.SilvermanReduction
