/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.SilvermanReduction
-/
import Submission.Work.SilvermanReduction.Marker
import Submission.Work.PointlessTwist.All
import Submission.Work.TorsorExistence.nonempty_fiveTorsionPoint
import Submission.Work.PointlessTwist.Constants.hasGoodAut_of_j_ne

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The concrete curve of the number-field class (a)

The class-(a) residual of `Submission/Work/PointlessTwist` is stated with `C₅` existentially
quantified.  This file *pins* it: the Tate normal form with `c = 1`,

  `E : y² - y = x³ - x²`,  i.e. `(a₁, a₂, a₃, a₄, a₆) = (0, -1, -1, 0, 0)`,

is an elliptic curve over `ℚ` with discriminant `Δ = -11`, `j = 16³/(-11) ≠ 1728`, and the point
`(0,0)` of order `5`; Silverman *AEC* A.1.2 for `j ≠ 1728` supplies the `order_aut` datum.  It
therefore gives a concrete `Work.PointlessTwist.FiveTorsionCurve ℚ`.

By `tateCurve_hasGoodReduction` it has good reduction at the place `5` of `ℚ` (`c = 1` and
`c² - 11c - 1 = -11` are units of `ℤ_(5)`), and by `Marker.tateCurve_redPoint_zero_ne_zero` its
marker reduces non-trivially.  What is left for class (a) is therefore *only* the field theory of
the place of the cyclotomic quintic field — see `NOTES.md` §4.

## Main results

* `tateCurve_one_isElliptic`, `tateCurve_one_j_ne`, `tateCurve_one_hasGoodAut`
* `tateFiveTorsionCurve : Work.PointlessTwist.FiveTorsionCurve ℚ` with `E = tateCurve 1` and
  `P = (0,0)` (and `tateFiveTorsionCurve_E`, `tateFiveTorsionCurve_P`)
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open WeierstrassCurve WeierstrassCurve.Affine
open IsLocalRing (ResidueField residue)

namespace Work.SilvermanReduction

noncomputable section

/-- The Tate normal form with `c = 1` is elliptic: its discriminant is `-11`. -/
theorem tateCurve_one_isElliptic : (Work.TorsorExistence.Tate.tateCurve (1 : ℚ)).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, Work.TorsorExistence.Tate.tateCurve_Δ]
  norm_num

local instance tateOneIsElliptic :
    (Work.TorsorExistence.Tate.tateCurve (1 : ℚ)).IsElliptic :=
  tateCurve_one_isElliptic

/-- The `j`-invariant of the Tate normal form with `c = 1` is `16³/(-11)`, which is not `1728`. -/
theorem tateCurve_one_j_ne : (Work.TorsorExistence.Tate.tateCurve (1 : ℚ)).j ≠ 1728 := by
  intro h
  have hΔ : (Work.TorsorExistence.Tate.tateCurve (1 : ℚ)).Δ ≠ 0 := by
    rw [Work.TorsorExistence.Tate.tateCurve_Δ]
    norm_num
  have h2 := congrArg (fun t => (Work.TorsorExistence.Tate.tateCurve (1 : ℚ)).Δ * t) h
  rw [WeierstrassCurve.j_eq] at h2
  rw [← mul_assoc, mul_inv_cancel₀ hΔ, one_mul, mul_comm _ (1728 : ℚ)] at h2
  rw [Work.TorsorExistence.Tate.tateCurve_c₄, Work.TorsorExistence.Tate.tateCurve_Δ] at h2
  norm_num at h2

/-- The marker `(0,0)` of the Tate normal form with `c = 1` is nonsingular. -/
theorem tateCurve_one_nonsingular :
    Nonsingular (Work.TorsorExistence.Tate.tateCurve (1 : ℚ)) 0 0 :=
  tateCurve_nonsingular_zero_zero 1 one_ne_zero

/-- **Silverman, *AEC*, A.1.2 for the concrete curve of class (a)**: every automorphism of the
Tate normal form with `c = 1` has order dividing `2` or `6`. -/
theorem tateCurve_one_hasGoodAut :
    Work.PointlessIndexFive.HasGoodAut (Work.TorsorExistence.Tate.tateCurve (1 : ℚ)) :=
  Work.PointlessTwist.Constants.hasGoodAut_of_j_ne _ tateCurve_one_j_ne

/-- **The concrete curve of the number-field class (a)**: the Tate normal form with `c = 1`,
together with its point `(0,0)` of order `5`. -/
def tateFiveTorsionCurve : Work.PointlessTwist.FiveTorsionCurve ℚ where
  E := Work.TorsorExistence.Tate.tateCurve 1
  isElliptic := tateCurve_one_isElliptic
  j_ne := tateCurve_one_j_ne
  P := WeierstrassCurve.Affine.Point.some 0 0 tateCurve_one_nonsingular
  P_ne_zero := WeierstrassCurve.Affine.Point.some_ne_zero _
  five_smul := Work.TorsorExistence.Tate.tate_five_smul 1 one_ne_zero tateCurve_one_nonsingular
  order_aut := tateCurve_one_hasGoodAut

@[simp]
theorem tateFiveTorsionCurve_E :
    tateFiveTorsionCurve.E = Work.TorsorExistence.Tate.tateCurve (1 : ℚ) := rfl

@[simp]
theorem tateFiveTorsionCurve_P :
    tateFiveTorsionCurve.P
      = WeierstrassCurve.Affine.Point.some 0 0 tateCurve_one_nonsingular := rfl

-- Note.  The field `LocalModelData.red_PL_ne_zero` of the class-(a) residual is *automatically*
-- satisfied for the pinned curve: its marker is the base change of `(0,0)`, and
-- `Marker.redPoint_some_zero_zero_ne_zero` shows that the reduction of an integral point is an
-- affine point, never the origin.  We record the general form
-- `Marker.redPoint_PL_ne_zero_of_eq_some_zero`, which applies to any twist whose marked point is
-- `(0,0)`; specialising it to `tateFiveTorsionCurve` requires unfolding the structure literal of
-- `tateFiveTorsionCurve` (the `PointlessIndexFive.quinticTwistOf` construction), which is a
-- definitional but expensive step, and is deliberately not done here.

end

end Work.SilvermanReduction
