/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.SilvermanReduction
-/
import Submission.Work.SilvermanReduction.Basic
import Submission.Work.SilvermanReduction.redPoint_add_of_integral
import Submission.Work.SilvermanReduction.redPoint_add_of_not_integral_left

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Silverman, *AEC*, VII.2.1: the reduction map on points is a group homomorphism

This file assembles the two halves of the chord–tangent computation

* `redPoint_add_of_integral` — the reduction of a *sum of two integral points*,
* `redPoint_add_of_not_integral_left` — the case where the first point has negative valuation,

into the theorem `redPoint_add` and the group homomorphism `redPointAddMonoidHom`.

## Main results

* `redPoint_add` — **Silverman VII.2.1**: `redPoint R W (P + Q) = redPoint R W P + redPoint R W Q`.
* `redPointAddMonoidHom` — the reduction map as an additive homomorphism `E(K) →+ Ẽ(k)`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open WeierstrassCurve WeierstrassCurve.Affine
open IsLocalRing (ResidueField residue)
open scoped WithZero

namespace Work.SilvermanReduction

noncomputable section

variable {K : Type*} [Field K] [DecidableEq K]
variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Algebra R K] [IsFractionRing R K] [DecidableEq (ResidueField R)]

/-- **Silverman, *AEC*, VII.2.1: the reduction map on the points of a Weierstrass curve with good
reduction at a discrete valuation is additive.** -/
theorem redPoint_add {W : Affine K} [W.HasGoodReduction R]
    (P Q : WeierstrassCurve.Affine.Point W) :
    redPoint R W (P + Q) = redPoint R W P + redPoint R W Q := by
  classical
  rcases P with _ | ⟨x, y, h⟩
  · rw [← WeierstrassCurve.Affine.Point.zero_def, zero_add, redPoint_zero, zero_add]
  rcases Q with _ | ⟨u, v, h'⟩
  · rw [← WeierstrassCurve.Affine.Point.zero_def, add_zero, redPoint_zero, add_zero]
  by_cases hx : ∃ r : R, algebraMap R K r = x
  · by_cases hu : ∃ r : R, algebraMap R K r = u
    · exact redPoint_add_of_integral R h h' hx hu
    · rw [add_comm (WeierstrassCurve.Affine.Point.some x y h)
        (WeierstrassCurve.Affine.Point.some u v h')]
      rw [redPoint_add_of_not_integral_left R h' h hu, add_comm]
  · exact redPoint_add_of_not_integral_left R h h' hx

/-- **The reduction map as a homomorphism of abelian groups `E(K) →+ Ẽ(k)`.**
This is the map whose kernel is `E₁(K)` and whose image is the special fibre. -/
def redPointAddMonoidHom {W : Affine K} [W.HasGoodReduction R] :
    WeierstrassCurve.Affine.Point W →+ WeierstrassCurve.Affine.Point (W.reduction R) where
  toFun := redPoint R W
  map_zero' := redPoint_zero R
  map_add' P Q := redPoint_add R P Q

@[simp]
theorem redPointAddMonoidHom_apply {W : Affine K} [W.HasGoodReduction R]
    (P : WeierstrassCurve.Affine.Point W) :
    redPointAddMonoidHom R P = redPoint R W P := rfl

/-- The reduction commutes with negation. -/
theorem redPoint_neg {W : Affine K} [W.HasGoodReduction R]
    (P : WeierstrassCurve.Affine.Point W) : redPoint R W (-P) = -redPoint R W P := by
  rw [← redPointAddMonoidHom_apply R (W := W), map_neg, redPointAddMonoidHom_apply]

/-- The reduction commutes with the multiplication by an integer. -/
theorem redPoint_nsmul {W : Affine K} [W.HasGoodReduction R] (n : ℕ)
    (P : WeierstrassCurve.Affine.Point W) :
    redPoint R W (n • P) = n • redPoint R W P := by
  rw [← redPointAddMonoidHom_apply R (W := W), map_nsmul, redPointAddMonoidHom_apply]

end

end Work.SilvermanReduction
