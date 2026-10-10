import Mathlib
import Submission.Work.SilvermanReduction.Basic
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.SilvermanReduction

open WeierstrassCurve WeierstrassCurve.Affine
open IsLocalRing (residue)

/-- If the residue of the doubling denominator `2s + a₁r + a₃` of the integral model vanishes, then
the residue of `s` is the negative `Y`-coordinate of the residue of `r` on the reduced curve. -/
lemma negY_reduction_eq_of_residue_doublingDenom_eq_zero {K : Type*} [Field K]
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R K] [IsFractionRing R K]
    {W : WeierstrassCurve.Affine K} [W.HasGoodReduction R] {r s : R}
    (hd : IsLocalRing.residue R
      (2 * s + (WeierstrassCurve.integralModel R W).a₁ * r
        + (WeierstrassCurve.integralModel R W).a₃) = 0) :
    IsLocalRing.residue R s =
      WeierstrassCurve.Affine.negY (W.reduction R) (IsLocalRing.residue R r)
        (IsLocalRing.residue R s) := by
  rw [WeierstrassCurve.Affine.negY]
  simp only [WeierstrassCurve.reduction, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]
  have h := hd
  simp only [map_add, map_mul, map_ofNat] at h
  linear_combination (norm := first | refl_ring1 | ring1) h

end Work.SilvermanReduction
