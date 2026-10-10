/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.TwistModel
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Twist.All

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.TwistModel` — the twist model: decomposition of `RealizationOf`

This is the interface of the area `Submission/Work/TwistModel`, which continues
`Submission/Work/Twist` (read its `NOTES.md` first).  Its deliverable is the **second named
residual** of the `Twist` area:

  `RealizationOf C₅ L` (`Work.Twist`), i.e. `Nonempty (TwistCurveModel (quinticTwistOf C₅ L))`

for every quintic twist datum (a curve `C₅` with a rational point of order `5` and `j ≠ 1728`,
and a cyclic quintic extension `L/𝕜`).

Recall (`Work.PointlessIndexFive.Defs`): a `TwistCurveModel D` for `D : QuinticTwist 𝕜` is

* a scheme `C` over `𝕜` with `Variety 𝕜 C`, `IsProper`, `Smooth`, `GeometricallyIntegral` and
  `topologicalKrullDim C = 1` (a *curve*);
* together with the two **Galois-descent bridges** `C(𝕜) ≠ ∅ ↔ cls = 0` and
  `(∃ a 𝕜-rational divisor of degree n) ↔ n • cls = 0`.

## What this file provides

The point of this area is to **decompose** that structure into the pieces the geometric argument
of the paper actually produces, and to prove that everything else follows:

1. `PointBridge D C` — the point bridge `C(𝕜) ≠ ∅ ↔ D.toTorsor.HasPoint`, which is Galois descent
   for the twisted action `g ⋆ Q = gQ + P` (a `𝕜`-point of `C` is a point `R` with `σR = R + P`);
2. `Work.Arithmetic.HasRatDivisorOfDegree 𝕜 C 5` — the *orbit divisor*: the twist carries a
   `𝕜`-rational divisor of degree `5` (the orbit of a point of `E(L)` under `G = ℤ/5`);
3. `DivisorRigidity D C` — the **hard half** of the divisor bridge: a `𝕜`-rational divisor of
   degree `n` on `C` forces `n • cls = 0` (equivalently, for pointless `D`, that `5 ∣ n`: the
   index of `C` is `5`).  This is the geometric statement "`C` is the twist of `E` by `cls`",
   i.e. `Jac^n C ≅ E` (Riemann–Roch for the twist), and it is what Mathlib has no theory for.

`TwistModelData D` bundles a curve with these three pieces, and the sibling modules prove

* `nonempty_twistModelData_iff` — `Nonempty (TwistModelData D) ↔ Nonempty (TwistCurveModel D)`;
  the *only* direction that is not formal is the derivation of `n • cls = 0 → ∃ a divisor of
  degree n` from the orbit divisor of degree `5`, the point bridge and the element-level
  dictionary of `Work.Twist` (the class of the twist has exact order `5`);
* `rigidity_iff_index_five` — for `D.Pointless`, `DivisorRigidity D C` is *exactly* the index-`5`
  statement `∀ n, HasRatDivisorOfDegree 𝕜 C n → 5 ∣ n`; so the residual is the parent chapter's
  `PointlessIndexFiveCurve` datum, tied to `D` by the point bridge alone;
* `realizationOf_iff` — `RealizationOf C₅ L ↔ Nonempty (TwistModelData (quinticTwistOf C₅ L))`;
* `twistRealization_iff_hasPointlessIndexFiveCurve` — the **structural theorem** of this area: a
  curve model of *some* pointless quintic twist exists iff `HasPointlessIndexFiveCurve 𝕜`, i.e.
  `HasPointlessIndexFiveCurve 𝕜 ↔ TwistRealization 𝕜 ∧ HasPointlessTwist 𝕜` (the parent chapter
  had only `←`); consequently the geometric residual may be discharged by producing **any**
  pointless curve of index `5` over `𝕜`.

The geometric construction of an explicit model (the Pfaffian elliptic quintic in `ℙ⁴`) is
prepared in `Pfaffian.lean`, and the projective model layer it rests on is completed in
`Projective.lean`; see `NOTES.md` for the roadmap.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory AlgebraicGeometry

namespace Work.TwistModel

noncomputable section

/-! ## 0. Short names of the parent interface -/

/-- The quintic twist data of the paper's construction. -/
abbrev QuinticTwist (𝕜 : Type) [Field 𝕜] [DecidableEq 𝕜] := Work.Twist.QuinticTwist 𝕜

/-- A curve model over `𝕜` (smooth, proper, geometrically integral, one-dimensional). -/
abbrev CurveModel (𝕜 : Type) [Field 𝕜] := Work.Twist.CurveModel 𝕜

/-- The twist model of a quintic twist: a curve plus the two descent bridges. -/
abbrev TwistCurveModel {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (D : QuinticTwist 𝕜) :=
  Work.Twist.TwistCurveModel D

/-- The geometric residual for the paper's own data. -/
abbrev RealizationOf {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (C₅ : Work.Twist.FiveTorsionCurve 𝕜)
    (L : Work.Twist.CyclicExtension 𝕜 5) : Prop := Work.Twist.RealizationOf C₅ L

/-! ## 1. The three pieces of a twist model -/

/-- **The point bridge** of the twist model: `C` has a `𝕜`-rational point iff the class of the
twist is trivial.  Mathematically this is Galois descent for the twisted action `g ⋆ Q = gQ + P`
on `E(L)`: a `𝕜`-point of `C = (E_L)/G` is a `G`-fixed `L`-point, i.e. a point `R ∈ E(L)` with
`σR = R + P` (`Work.TorsorExistence.cls_eq_zero_iff`). -/
def PointBridge {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (D : QuinticTwist 𝕜) (C : Scheme)
    [C.Over (Spec (CommRingCat.of 𝕜))] : Prop :=
  Work.Arithmetic.HasRatPoint 𝕜 C ↔ D.toTorsor.HasPoint

/-- **The divisor-degree bridge** of the twist model: the `𝕜`-rational divisor degrees of `C` are
exactly the multiples of the period `5`, i.e. `n • cls = 0` (the classical `Jac^n C ≅ E`). -/
def DivisorBridge {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (D : QuinticTwist 𝕜) (C : Scheme)
    [C.Over (Spec (CommRingCat.of 𝕜))] : Prop :=
  ∀ n : ℕ, Work.Arithmetic.HasRatDivisorOfDegree 𝕜 C n ↔ D.toTorsor.DivisorOfDegree n

/-- **The rigidity of the divisor-degree bridge** — the half of `DivisorBridge` that is *not*
formal: a `𝕜`-rational divisor of degree `n` on the twist forces `n • cls = 0`.

Geometrically this is the statement that `C` is the twist of `E` by the class `cls`, so that its
`n`-th symmetric power maps onto `E` by the Abel–Jacobi map, i.e. `Jac^n C ≅ E`; the pinned
Mathlib has no `Pic`, no `Jac` and no Riemann–Roch, so this is the geometric residual.  For
pointless `D` it is *equivalent* to the index-`5` statement
`∀ n, HasRatDivisorOfDegree 𝕜 C n → 5 ∣ n` (`rigidity_iff_index_five`). -/
def DivisorRigidity {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (D : QuinticTwist 𝕜) (C : Scheme)
    [C.Over (Spec (CommRingCat.of 𝕜))] : Prop :=
  ∀ n : ℕ, Work.Arithmetic.HasRatDivisorOfDegree 𝕜 C n → D.toTorsor.DivisorOfDegree n

/-- **The decomposition of the twist-model residual.**  A `TwistModelData D` is a curve over `𝕜`
together with the three ingredients the paper's geometric argument produces: the point bridge, the
orbit divisor of degree `5`, and the rigidity of the divisor-degree bridge.

`nonempty_twistModelData_iff` (`Model.lean`) shows that this is *equivalent* to
`Nonempty (TwistCurveModel D)`: the two remaining halves of the divisor bridge
(`n • cls = 0 → ∃ a rational divisor of degree n`) follow from these and the element-level
dictionary of `Work.Twist`. -/
structure TwistModelData {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (D : QuinticTwist 𝕜) where
  /-- The curve `(E_L)/G`. -/
  C : Scheme
  [variety : MotivicInvariants.Variety 𝕜 C]
  [isProper : IsProper (C ↘ Spec (CommRingCat.of 𝕜))]
  [isSmooth : Smooth (C ↘ Spec (CommRingCat.of 𝕜))]
  [isGeomIntegral : GeometricallyIntegral (C ↘ Spec (CommRingCat.of 𝕜))]
  /-- A curve is one-dimensional. -/
  dim_eq_one : topologicalKrullDim C = 1
  /-- Galois descent of points: `C(𝕜) ≠ ∅ ↔ cls = 0`. -/
  point_bridge : PointBridge D C
  /-- The orbit divisor: `C` carries a `𝕜`-rational divisor of degree `5`. -/
  divisor_five : Work.Arithmetic.HasRatDivisorOfDegree 𝕜 C 5
  /-- Every degree of a `𝕜`-rational divisor is a period of the class; for pointless `D` this is
  the index-`5` statement. -/
  rigid : DivisorRigidity D C

namespace TwistModelData

variable {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] {D : QuinticTwist 𝕜}

instance (M : TwistModelData D) : MotivicInvariants.Variety 𝕜 M.C := M.variety
instance (M : TwistModelData D) : M.C.Over (Spec (CommRingCat.of 𝕜)) :=
  MotivicInvariants.Variety.over
instance (M : TwistModelData D) : IsProper (M.C ↘ Spec (CommRingCat.of 𝕜)) := M.isProper
instance (M : TwistModelData D) : Smooth (M.C ↘ Spec (CommRingCat.of 𝕜)) := M.isSmooth
instance (M : TwistModelData D) :
    GeometricallyIntegral (M.C ↘ Spec (CommRingCat.of 𝕜)) := M.isGeomIntegral

/-- The underlying curve model (the geometric half, no arithmetic). -/
def toCurveModel (M : TwistModelData D) : CurveModel 𝕜 where
  C := M.C
  variety := M.variety
  isProper := M.isProper
  isSmooth := M.isSmooth
  isGeomIntegral := M.isGeomIntegral
  dim_eq_one := M.dim_eq_one

end TwistModelData

/-! ## 2. The residual statements -/

/-- **The residual of this area, for one twist.**  A twist model of `D` exists, presented through
the decomposition `TwistModelData`; this is `Work.Twist.RealizationAt D` by
`nonempty_twistModelData_iff`. -/
def RealizationData {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (D : QuinticTwist 𝕜) : Prop :=
  Nonempty (TwistModelData D)

/-- **The residual of this area, on the paper's own data**: step (B) curve and step (A) extension
give a twist model.  This is `Work.Twist.RealizationOf C₅ L` (`realizationOf_iff`). -/
def RealizationOfData {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (C₅ : Work.Twist.FiveTorsionCurve 𝕜)
    (L : Work.Twist.CyclicExtension 𝕜 5) : Prop :=
  RealizationData (Work.Twist.quinticTwistOf C₅ L)

/-- **The residual of this area, uniform in the field**: every quintic twist over `𝕜` has a twist
model.  This is `Work.Twist.TwistRealization 𝕜` (`twistRealization_iff_data`). -/
def HasTwistModel (𝕜 : Type) [Field 𝕜] [DecidableEq 𝕜] : Prop :=
  ∀ D : QuinticTwist 𝕜, RealizationData D

end

end Work.TwistModel
