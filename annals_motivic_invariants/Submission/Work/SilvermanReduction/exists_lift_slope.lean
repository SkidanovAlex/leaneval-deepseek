/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.SilvermanReduction
-/
import Mathlib
import Submission.Work.SilvermanReduction.Basic
import Submission.Work.SilvermanReduction.API
import Submission.Work.SilvermanReduction.Helpers
import Submission.Work.SilvermanReduction.ils_some_ne_neg_some
import Submission.Work.SilvermanReduction.ils_of_eq_x
import Submission.Work.SilvermanReduction.ils_of_eq_residue_ne_x

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Lifting the slope of the chord through two integral points

Silverman, *AEC*, VII.2.1, the computational core: let `R` be a discrete valuation ring with
fraction field `K`, `W/K` a Weierstrass curve with good reduction at `R`, and let `(x,y)`, `(u,v)`
be two nonsingular points of `W` whose coordinates lift to `r, s, r', s' ∈ R` (so both points are
integral at the place).  If the two points do **not** reduce to opposite points of the special
fibre, then the slope of the chord through them is itself integral, and it reduces to the slope of
the chord through the reduced points.

The two degenerate configurations are exactly the ones excluded by `hbad`:

* the reduced points could have the same `x`-coordinate and be opposite (`redPoint P = -redPoint Q`):
  then `y + v + a₁x + a₃` lies in the maximal ideal and the slope need not be integral;
* the reduced points could be `2`-torsion (`redPoint P = redPoint Q = -redPoint Q`), equally
  excluded.

The proof splits on `residue R r = residue R r'`:

* `residue R r ≠ residue R r'`: the difference `r - r'` is a unit of `R`, hence
  `slope W x u y v = (y-v)/(x-u)` is the quotient of the image of `s - s'` by the image of the unit
  `r - r'`; `exists_lift_div` lifts it, and the reduced slope is the same quotient in the residue
  field (both have `x₁ ≠ x₂`).
* `residue R r = residue R r'`: `hbad`, transported to the special fibre, says that the reduced
  points are equal (`residue R s' = residue R s`) and not `2`-torsion
  (`residue R s ≠ negY (W.reduction R) (residue R r') (residue R s')`); the two remaining cases
  `r = r'` and `r ≠ r'` are handled by the lemmas `ils_of_eq_x` (both slopes are tangent slopes)
  and `ils_of_eq_residue_ne_x` (the slope over `K` is a chord slope, the one over the residue field
  a tangent slope, and the chord identity `slope_mul_eq` transfers the one to the other).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open WeierstrassCurve WeierstrassCurve.Affine
open IsLocalRing (ResidueField residue)

namespace Work.SilvermanReduction

noncomputable section

theorem exists_lift_slope {K : Type*} [Field K] [DecidableEq K] {R : Type*} [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] [Algebra R K] [IsFractionRing R K]
    [DecidableEq (IsLocalRing.ResidueField R)]
    {W : WeierstrassCurve.Affine K} [W.HasGoodReduction R] {x y u v : K}
    (h : WeierstrassCurve.Affine.Nonsingular W x y)
    (h' : WeierstrassCurve.Affine.Nonsingular W u v)
    {r s r' s' : R} (hr : algebraMap R K r = x) (hs : algebraMap R K s = y)
    (hr' : algebraMap R K r' = u) (hs' : algebraMap R K s' = v)
    (hbad : ¬ (Work.SilvermanReduction.redPoint R W (WeierstrassCurve.Affine.Point.some x y h) = - Work.SilvermanReduction.redPoint R W (WeierstrassCurve.Affine.Point.some u v h'))) :
    ∃ ρ : R, algebraMap R K ρ = WeierstrassCurve.Affine.slope W x u y v ∧ IsLocalRing.residue R ρ = WeierstrassCurve.Affine.slope (W.reduction R) (IsLocalRing.residue R r) (IsLocalRing.residue R r') (IsLocalRing.residue R s) (IsLocalRing.residue R s') := by
  classical
  by_cases hξ : IsLocalRing.residue R r = IsLocalRing.residue R r'
  · -- the reduced points have the same `x`-coordinate
    have hP : WeierstrassCurve.Affine.Nonsingular (W.reduction R) (IsLocalRing.residue R r)
        (IsLocalRing.residue R s) :=
      nonsingular_reduction (W := W) (equation_integralModel (W := W) h.1 hr hs)
    have hQ : WeierstrassCurve.Affine.Nonsingular (W.reduction R) (IsLocalRing.residue R r')
        (IsLocalRing.residue R s') :=
      nonsingular_reduction (W := W) (equation_integralModel (W := W) h'.1 hr' hs')
    have hbad' : (WeierstrassCurve.Affine.Point.some (IsLocalRing.residue R r)
          (IsLocalRing.residue R s) hP ≠
        - WeierstrassCurve.Affine.Point.some (IsLocalRing.residue R r')
          (IsLocalRing.residue R s') hQ) := by
      intro hc
      apply hbad
      simpa only [redPoint_some_mk R h hr hs, redPoint_some_mk R h' hr' hs'] using hc
    obtain ⟨hnt, hη⟩ := (ils_some_ne_neg_some hP hQ hξ).mp hbad'
    by_cases hrr : r = r'
    · exact ils_of_eq_x hr hs hr' hs' hξ hrr hη hnt
    · exact ils_of_eq_residue_ne_x h h' hr hs hr' hs' hξ hrr hη hnt
  · -- the reduced points have different `x`-coordinates: both slopes are chord slopes
    have hrr' : r ≠ r' := fun hh => hξ (by rw [hh])
    have hxu : x ≠ u := by
      intro hh
      exact hrr' (algebraMap_injective (by rw [hr, hh, ← hr']))
    have hd : IsUnit (r - r') := by
      rw [isUnit_iff_residue_ne_zero', map_sub]
      exact sub_ne_zero.mpr hξ
    obtain ⟨ρ, hρ1, hρ2⟩ := exists_lift_div (K := K) (n := s - s') hd
    refine ⟨ρ, ?_, ?_⟩
    · rw [hρ1, map_sub, map_sub, hs, hs', hr, hr',
        WeierstrassCurve.Affine.slope_of_X_ne hxu]
    · rw [hρ2]
      simp only [map_sub]
      rw [WeierstrassCurve.Affine.slope_of_X_ne hξ]

end

end Work.SilvermanReduction
