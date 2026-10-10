/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.TwistModel
-/
import Mathlib
import ChallengeDeps
import Submission.Work.TwistModel.Corrected
import Submission.Work.TwistModel.Split
import Submission.Work.TwistModel.GeomIntegral
import Submission.Work.TwistModel.hasRatPoint_projectiveSpace_one
import Submission.Work.TwistModel.ClosedPoint

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The twist model with the corrected divisor predicate

The parent chapter's `Work.PointlessIndexFive.TwistCurveModel` carries a divisor-degree bridge stated
with `Work.Arithmetic.HasRatDivisorOfDegree`, which **was** degenerate (`Work.TwistModel.Defect`) at
the time this file was written: the predicate selected the generic points of the irreducible
components, not the closed points, so on any curve of positive dimension it was false for `n ≠ 0`,
and the structure was unsatisfiable.  **The arithmetic predicate has since been repaired**
(`Submission/Work/ArithFix`: the support condition is now `Order.height x = 0`), so the parent
structure is satisfiable as it stands, and the corrected predicate used here
(`HasRatDivisorOfDegreeClosed`) is the same predicate in a different spelling
(`Work.ArithFix.predicateAgrees`).  Nothing below changes; the file is kept as the version of the
theory stated in closed-point form.

This file redoes the theory with the corrected predicate
`Work.TwistModel.HasRatDivisorOfDegreeClosed` (support on closed points).  Nothing else changes:

* `DivisorBridgeClosed`, `DivisorRigidityClosed` — the bridge and its rigid half;
* `TwistModelDataClosed` — the decomposition of the residual (geometry + point bridge + orbit divisor
  + rigidity), with `nonempty_twistModelDataClosed_iff_of_pointless` showing it is equivalent to
  `TwistCurveModelClosed` for pointless twists (the only case of interest: for `cls = 0` the twist
  curve has a rational point and the bridge is the trivial statement that all degrees occur);
* `TwistCurveModelClosed` — the corrected twist model;
* `rigidityClosed_iff_index_five` — the rigidity is the index-`5` statement;
* `nonempty_twistCurveModelClosed_of_pointlessIndexFiveCurve` — **any pointless curve of index `5`
  realizes every pointless twist** (the corrected counterpart of the parent chapter's structural
  theorem; it is what makes the geometric residual reducible to producing *any* such curve);
* `nonempty_twistCurveModelClosed_of_hasPoint` — the trivial-class case, realized by `ℙ¹`, so the
  corrected structures are satisfiable.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory AlgebraicGeometry

namespace Work.TwistModel

noncomputable section

variable {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]

/-! ## 1. The corrected bridges -/

/-- The divisor-degree bridge, with the corrected predicate: `C` carries a `𝕜`-rational divisor of
degree `n` (supported on closed points) iff `n • cls = 0`. -/
def DivisorBridgeClosed (D : QuinticTwist 𝕜) (C : Scheme)
    [C.Over (Spec (CommRingCat.of 𝕜))] : Prop :=
  ∀ n : ℕ, HasRatDivisorOfDegreeClosed 𝕜 C n ↔ D.toTorsor.DivisorOfDegree n

/-- The rigid half of `DivisorBridgeClosed`: a rational divisor of degree `n` forces `n • cls = 0`. -/
def DivisorRigidityClosed (D : QuinticTwist 𝕜) (C : Scheme)
    [C.Over (Spec (CommRingCat.of 𝕜))] : Prop :=
  ∀ n : ℕ, HasRatDivisorOfDegreeClosed 𝕜 C n → D.toTorsor.DivisorOfDegree n

/-- **The corrected twist model of a quintic twist**: a curve over `𝕜` (smooth, proper,
geometrically integral, dimension one) whose rational points and rational divisors (with the
corrected, closed-point, predicate) are those prescribed by the class of `D`. -/
structure TwistCurveModelClosed (D : QuinticTwist 𝕜) where
  /-- The curve `(E_L)/G`. -/
  C : Scheme
  [variety : MotivicInvariants.Variety 𝕜 C]
  [isProper : IsProper (C ↘ Spec (CommRingCat.of 𝕜))]
  [isSmooth : Smooth (C ↘ Spec (CommRingCat.of 𝕜))]
  [isGeomIntegral : GeometricallyIntegral (C ↘ Spec (CommRingCat.of 𝕜))]
  /-- A curve is one-dimensional. -/
  dim_eq_one : topologicalKrullDim C = 1
  /-- `C(𝕜) ≠ ∅ ↔ cls = 0`. -/
  hasPoint_iff : Work.Arithmetic.HasRatPoint 𝕜 C ↔ D.toTorsor.HasPoint
  /-- `C` carries a corrected `𝕜`-rational divisor of degree `n` iff `n • cls = 0`. -/
  divisorOfDegree_iff : DivisorBridgeClosed D C

namespace TwistCurveModelClosed

variable {D : QuinticTwist 𝕜} (M : TwistCurveModelClosed D)

instance : MotivicInvariants.Variety 𝕜 M.C := M.variety
instance : M.C.Over (Spec (CommRingCat.of 𝕜)) := MotivicInvariants.Variety.over
instance : IsProper (M.C ↘ Spec (CommRingCat.of 𝕜)) := M.isProper
instance : Smooth (M.C ↘ Spec (CommRingCat.of 𝕜)) := M.isSmooth
instance : GeometricallyIntegral (M.C ↘ Spec (CommRingCat.of 𝕜)) := M.isGeomIntegral

/-- A corrected twist model is in particular a curve model. -/
def toCurveModel : CurveModel 𝕜 where
  C := M.C
  variety := M.variety
  isProper := M.isProper
  isSmooth := M.isSmooth
  isGeomIntegral := M.isGeomIntegral
  dim_eq_one := M.dim_eq_one

end TwistCurveModelClosed

/-- **The decomposition of the corrected residual.**  A `TwistModelDataClosed D` is a curve over `𝕜`
together with the three ingredients of the paper's geometric argument: the point bridge, the orbit
divisor of degree `5`, and the rigidity of the divisor-degree bridge. -/
structure TwistModelDataClosed (D : QuinticTwist 𝕜) where
  /-- The curve and its geometry. -/
  C : Scheme
  [variety : MotivicInvariants.Variety 𝕜 C]
  [isProper : IsProper (C ↘ Spec (CommRingCat.of 𝕜))]
  [isSmooth : Smooth (C ↘ Spec (CommRingCat.of 𝕜))]
  [isGeomIntegral : GeometricallyIntegral (C ↘ Spec (CommRingCat.of 𝕜))]
  /-- A curve is one-dimensional. -/
  dim_eq_one : topologicalKrullDim C = 1
  /-- Galois descent of points. -/
  point_bridge : PointBridge D C
  /-- The orbit divisor. -/
  divisor_five : HasRatDivisorOfDegreeClosed 𝕜 C 5
  /-- The rigid half of the divisor bridge. -/
  rigid : DivisorRigidityClosed D C

namespace TwistModelDataClosed

variable {D : QuinticTwist 𝕜} (M : TwistModelDataClosed D)

instance : MotivicInvariants.Variety 𝕜 M.C := M.variety
instance : M.C.Over (Spec (CommRingCat.of 𝕜)) := MotivicInvariants.Variety.over
instance : IsProper (M.C ↘ Spec (CommRingCat.of 𝕜)) := M.isProper
instance : Smooth (M.C ↘ Spec (CommRingCat.of 𝕜)) := M.isSmooth
instance : GeometricallyIntegral (M.C ↘ Spec (CommRingCat.of 𝕜)) := M.isGeomIntegral

/-- The underlying curve model. -/
def toCurveModel : CurveModel 𝕜 where
  C := M.C
  variety := M.variety
  isProper := M.isProper
  isSmooth := M.isSmooth
  isGeomIntegral := M.isGeomIntegral
  dim_eq_one := M.dim_eq_one

end TwistModelDataClosed

/-! ## 2. The rigidity is the index-`5` statement -/

/-- **The rigid half of the corrected divisor bridge is the index-`5` statement** for a pointless
twist. -/
theorem rigidityClosed_iff_index_five {D : QuinticTwist 𝕜} {C : Scheme}
    [C.Over (Spec (CommRingCat.of 𝕜))] (h : D.Pointless) :
    DivisorRigidityClosed D C ↔
      ∀ n : ℕ, HasRatDivisorOfDegreeClosed 𝕜 C n → 5 ∣ n := by
  constructor
  · intro hR n hn
    have hcls : n • D.cls = 0 :=
      (Work.PointlessIndexFive.toTorsor_divisorOfDegree_iff D n).mp (hR n hn)
    rw [← Work.PointlessIndexFive.addOrderOf_cls_eq_five D h]
    exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr hcls
  · intro hR n hn
    rw [Work.PointlessIndexFive.toTorsor_divisorOfDegree_iff]
    exact addOrderOf_dvd_iff_nsmul_eq_zero.mp (by
      rw [Work.PointlessIndexFive.addOrderOf_cls_eq_five D h]
      exact hR n hn)

/-- **The corrected divisor bridge is equivalent to its rigid half** (pointless case, with the orbit
divisor present): the other half follows because `n • cls = 0` forces `5 ∣ n`. -/
theorem divisorBridgeClosed_iff_rigidityClosed_of_pointless {D : QuinticTwist 𝕜} {C : Scheme}
    [C.Over (Spec (CommRingCat.of 𝕜))] (h : D.Pointless)
    (h5 : HasRatDivisorOfDegreeClosed 𝕜 C 5) :
    DivisorBridgeClosed D C ↔ DivisorRigidityClosed D C := by
  constructor
  · intro hB n hn
    exact (hB n).mp hn
  · intro hR n
    refine ⟨hR n, fun hn => ?_⟩
    have h5n : 5 ∣ n := by
      rw [← Work.PointlessIndexFive.addOrderOf_cls_eq_five D h]
      exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr
        ((Work.PointlessIndexFive.toTorsor_divisorOfDegree_iff D n).mpr hn)
    obtain ⟨m, rfl⟩ := h5n
    exact hasRatDivisorOfDegreeClosed_mul_five h5 m

/-- **The decomposition of the corrected residual, for pointless twists.** -/
theorem nonempty_twistModelDataClosed_iff_of_pointless {D : QuinticTwist 𝕜} (h : D.Pointless) :
    Nonempty (TwistModelDataClosed D) ↔ Nonempty (TwistCurveModelClosed D) := by
  constructor
  · rintro ⟨M⟩
    exact ⟨{ C := M.C
             variety := M.variety
             isProper := M.isProper
             isSmooth := M.isSmooth
             isGeomIntegral := M.isGeomIntegral
             dim_eq_one := M.dim_eq_one
             hasPoint_iff := M.point_bridge
             divisorOfDegree_iff :=
               (divisorBridgeClosed_iff_rigidityClosed_of_pointless h M.divisor_five).mpr
                 M.rigid }⟩
  · rintro ⟨M⟩
    exact ⟨{ C := M.C
             variety := M.variety
             isProper := M.isProper
             isSmooth := M.isSmooth
             isGeomIntegral := M.isGeomIntegral
             dim_eq_one := M.dim_eq_one
             point_bridge := M.hasPoint_iff
             divisor_five := (M.divisorOfDegree_iff 5).mpr
               ((Work.PointlessIndexFive.toTorsor_divisorOfDegree_iff D 5).mpr
                 (Work.TorsorExistence.five_smul_cls D))
             rigid := fun n hn => (M.divisorOfDegree_iff n).mp hn }⟩

/-! ## 3. Any pointless curve of index `5` realizes every pointless twist -/

/-- **A pointless curve of index `5`**, with the corrected divisor predicate: a curve model with no
`𝕜`-rational point, a `𝕜`-rational divisor of degree `5` (supported on closed points), and no
rational divisor of a degree not divisible by `5`.  This is the corrected counterpart of
`Work.TorsorExistence.PointlessIndexFiveCurve`, whose `five`/`dvd` fields use the degenerate
predicate. -/
structure PointlessIndexFiveCurveClosed (𝕜 : Type) [Field 𝕜] where
  /-- The curve. -/
  C : Scheme
  [variety : MotivicInvariants.Variety 𝕜 C]
  [isProper : IsProper (C ↘ Spec (CommRingCat.of 𝕜))]
  [isSmooth : Smooth (C ↘ Spec (CommRingCat.of 𝕜))]
  [isGeomIntegral : GeometricallyIntegral (C ↘ Spec (CommRingCat.of 𝕜))]
  /-- A curve is one-dimensional. -/
  dim_eq_one : topologicalKrullDim C = 1
  /-- `C(𝕜) = ∅`. -/
  no_point : ¬ Work.Arithmetic.HasRatPoint 𝕜 C
  /-- The orbit divisor. -/
  five : HasRatDivisorOfDegreeClosed 𝕜 C 5
  /-- The index is `5`. -/
  dvd : ∀ n : ℕ, HasRatDivisorOfDegreeClosed 𝕜 C n → 5 ∣ n

namespace PointlessIndexFiveCurveClosed

variable (X : PointlessIndexFiveCurveClosed 𝕜)

instance : MotivicInvariants.Variety 𝕜 X.C := X.variety
instance : X.C.Over (Spec (CommRingCat.of 𝕜)) := MotivicInvariants.Variety.over
instance : IsProper (X.C ↘ Spec (CommRingCat.of 𝕜)) := X.isProper
instance : Smooth (X.C ↘ Spec (CommRingCat.of 𝕜)) := X.isSmooth
instance : GeometricallyIntegral (X.C ↘ Spec (CommRingCat.of 𝕜)) := X.isGeomIntegral

omit [DecidableEq 𝕜] in
/-- **The divisor degrees of a pointless index-`5` curve are exactly the multiples of `5`.** -/
theorem hasRatDivisorOfDegreeClosed_iff (n : ℕ) :
    HasRatDivisorOfDegreeClosed 𝕜 X.C n ↔ 5 ∣ n := by
  refine ⟨X.dvd n, fun h => ?_⟩
  obtain ⟨k, rfl⟩ := h
  exact hasRatDivisorOfDegreeClosed_mul_five X.five k

end PointlessIndexFiveCurveClosed

/-- **A pointless curve of index `5` realizes every pointless quintic twist**, in the corrected
setting: the two bridges only speak about the class `cls`, and both sides are determined by
`C(𝕜) = ∅` and the index-`5` statement. -/
theorem nonempty_twistCurveModelClosed_of_pointlessIndexFiveCurve
    (X : PointlessIndexFiveCurveClosed 𝕜) (D : QuinticTwist 𝕜)
    (h : D.Pointless) : Nonempty (TwistCurveModelClosed D) := by
  refine ⟨{ C := X.C
            variety := X.variety
            isProper := X.isProper
            isSmooth := X.isSmooth
            isGeomIntegral := X.isGeomIntegral
            dim_eq_one := X.dim_eq_one
            hasPoint_iff := ?_
            divisorOfDegree_iff := ?_ }⟩
  · have hcls : ¬ D.toTorsor.HasPoint :=
      (Work.PointlessIndexFive.pointless_iff_toTorsor D).mp h
    exact ⟨fun hp => absurd hp X.no_point, fun hp => absurd hp hcls⟩
  · intro n
    rw [Work.PointlessIndexFive.toTorsor_divisorOfDegree_iff,
      Work.Twist.nsmul_cls_eq_zero_iff D n,
      X.hasRatDivisorOfDegreeClosed_iff n]
    exact (Work.Twist.exists_shift_eq_nsmul_iff_five_dvd D h n).symm

/-! ## 4. The corrected residual statements -/

/-- **The corrected residual of this area**, for the paper's own data: every quintic twist (a curve
`C₅` with a rational point of order `5` and `j ≠ 1728`, together with a cyclic quintic extension
`L/𝕜`) is realized by a curve model with the corrected divisor predicate. -/
def RealizationOfClosed {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (C₅ : Work.Twist.FiveTorsionCurve 𝕜)
    (L : Work.Twist.CyclicExtension 𝕜 5) : Prop :=
  Nonempty (TwistCurveModelClosed (Work.Twist.quinticTwistOf C₅ L))

/-- The corrected residual, uniform in the twist: every quintic twist over `𝕜` is realized. -/
def HasTwistModelClosed (𝕜 : Type) [Field 𝕜] [DecidableEq 𝕜] : Prop :=
  ∀ D : QuinticTwist 𝕜, Nonempty (TwistCurveModelClosed D)

/-- The corrected residual, for pointless twists only. -/
def HasPointlessTwistModelClosed (𝕜 : Type) [Field 𝕜] [DecidableEq 𝕜] : Prop :=
  ∀ D : QuinticTwist 𝕜, D.Pointless → Nonempty (TwistCurveModelClosed D)

/-- The corrected arithmetic residual: some quintic twist is pointless (this is
`Work.Twist.HasPointlessTwist`, unchanged: it does not involve divisors). -/
abbrev HasPointlessTwist' (𝕜 : Type) [Field 𝕜] [DecidableEq 𝕜] : Prop := Work.Twist.HasPointlessTwist 𝕜

/-- **A pointless index-`5` curve gives the corrected residual for every pointless twist.** -/
theorem hasPointlessTwistModelClosed_of_pointlessIndexFiveCurve
    (h : Nonempty (PointlessIndexFiveCurveClosed 𝕜)) : HasPointlessTwistModelClosed 𝕜 :=
  fun D hD => nonempty_twistCurveModelClosed_of_pointlessIndexFiveCurve h.some D hD


/-! ## 5. The trivial-class case: `ℙ¹` as a model -/

set_option maxHeartbeats 800000 in
theorem nonempty_twistCurveModelClosed_of_hasPoint_of_ratDivisor
    (hd : ∀ n : ℕ, HasRatDivisorOfDegreeClosed 𝕜
      (Work.PointlessIndexFive.projectiveSpace 𝕜 1) n)
    {D : QuinticTwist 𝕜} (h : D.toTorsor.HasPoint) : Nonempty (TwistCurveModelClosed D) := by
  have h0 : D.cls = 0 := ofAdd_eq_one.mp h
  refine ⟨{ C := Work.PointlessIndexFive.projectiveSpace 𝕜 1
            variety := variety_projectiveSpace 𝕜 1
            isProper := Work.PointlessIndexFive.isProper_projectiveSpaceToSpec 𝕜 1
            isSmooth := Work.Twist.smooth_projectiveSpaceToSpec 𝕜 1
            isGeomIntegral := geometricallyIntegral_projectiveSpaceToSpec 𝕜 1
            dim_eq_one := Work.Twist.topologicalKrullDim_projectiveSpace 𝕜 1
            hasPoint_iff := ⟨fun _ => h, fun _ => hasRatPoint_projectiveSpace_one 𝕜⟩
            divisorOfDegree_iff := fun n => ⟨fun _ => by
              rw [Work.PointlessIndexFive.toTorsor_divisorOfDegree_iff, h0, nsmul_zero],
              fun _ => hd n⟩ }⟩

/-- **In the trivial-class case the twist is modelled by `ℙ¹_𝕜`** — unconditionally: `ℙ¹_𝕜` is a
curve model, it has rational points, and a rational point gives corrected rational divisors of every
degree (`Work.TwistModel.hasRatDivisorOfDegreeClosed_of_hasRatPoint`).  In particular the corrected
structures are non-empty: the corrected residual is exactly "the pointless twists are realized". -/
theorem nonempty_twistCurveModelClosed_of_hasPoint {D : QuinticTwist 𝕜}
    (h : D.toTorsor.HasPoint) : Nonempty (TwistCurveModelClosed D) :=
  nonempty_twistCurveModelClosed_of_hasPoint_of_ratDivisor
    (fun n => hasRatDivisorOfDegreeClosed_of_hasRatPoint (hasRatPoint_projectiveSpace_one 𝕜) n) h

end

end Work.TwistModel
