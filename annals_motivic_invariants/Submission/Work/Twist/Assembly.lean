/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.Twist
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Twist.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.Twist` — assembly of the two residuals

This file proves everything that follows *formally* from the definitions of `Defs.lean`:

* the residual `PointlessTwistData 𝕜` of this area (the paper's own data: a curve with a rational
  point of order `5` and `j ≠ 1728`, a cyclic quintic extension, pointlessness, and a curve model)
  is exactly the parent chapter's sharp residual `TwistResidualSharp 𝕜` / witness form
  `HasPointlessIndexFiveCurveOfTwist 𝕜`;
* from it, `HasPointlessIndexFiveCurve 𝕜`, the paper's Lemma `lem:torsors`
  (`Work.Arithmetic.HasLLinkCurve 𝕜`) and `Work.Arithmetic.ClarkLacyFive 𝕜`;
* the *local-obstruction form* of the arithmetic residual is equivalent to the residual itself
  (`hasLocalObstruction_iff_pointless`), so the paper's way of deciding `cls ≠ 0` loses nothing;
* the assembly of a `TwistCurveModel` from a `CurveModel` plus the descent bridges
  (`twistCurveModelOf`), which is the interface that the geometric half must target;
* the four field classes, stated directly from `PointlessTwistData`.

Nothing here is deep: the mathematics of the two residuals lives in the sibling files of this
directory and in `Submission/Work/PointlessIndexFive`; see `NOTES.md`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry
open Work.Twist

namespace Work.Twist

noncomputable section

/-! ## 1. The twist built from a twist datum is its own datum -/

/-- The twist data extracted from a `QuinticTwist` (`toFiveTorsionCurve` and `ext`) rebuilds it:
`quinticTwistOf D.toFiveTorsionCurve D.ext = D`.  This makes the data-level residual of this area
(`PointlessOf`, `RealizationOf`, `PointlessTwistData`) equivalent to the parent chapter's
`TwistResidualSharp`. -/
theorem quinticTwistOf_toFiveTorsionCurve {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (D : Work.TorsorExistence.QuinticTwist 𝕜) :
    quinticTwistOf (Work.TorsorExistence.QuinticTwist.toFiveTorsionCurve D) D.ext = D := by
  cases D with
  | mk c5 ext =>
    show Work.PointlessIndexFive.quinticTwistOf c5 ext = _
    simp only [Work.PointlessIndexFive.quinticTwistOf]
    congr 1

/-! ## 2. The residual in data form and the parent chapter's residual -/

/-- `PointlessTwistData 𝕜` is the parent chapter's witness form of the residual
(`HasPointlessIndexFiveCurveOfTwist 𝕜`): the two are the same statement, one written on the
paper's own data (step (B) curve + step (A) extension) and one on a `QuinticTwist`. -/
theorem pointlessTwistData_iff {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] :
    PointlessTwistData 𝕜 ↔ Work.PointlessIndexFive.HasPointlessIndexFiveCurveOfTwist 𝕜 := by
  constructor
  · rintro ⟨C₅, L, hP, hR⟩
    exact ⟨quinticTwistOf C₅ L, hP, hR⟩
  · rintro ⟨D, hP, hM⟩
    refine ⟨Work.TorsorExistence.QuinticTwist.toFiveTorsionCurve D, D.ext, ?_, ?_⟩
    · show Work.TorsorExistence.QuinticTwist.Pointless
        (quinticTwistOf (Work.TorsorExistence.QuinticTwist.toFiveTorsionCurve D) D.ext)
      rw [quinticTwistOf_toFiveTorsionCurve D]
      exact hP
    · show Nonempty (TwistCurveModel
        (quinticTwistOf (Work.TorsorExistence.QuinticTwist.toFiveTorsionCurve D) D.ext))
      rw [quinticTwistOf_toFiveTorsionCurve D]
      exact hM

/-- The `DecidableEq`-free form of the residual in data form. -/
noncomputable def PointlessTwistDataAny (𝕜 : Type) [Field 𝕜] : Prop :=
  ∃ d : DecidableEq 𝕜, @PointlessTwistData 𝕜 _ d

/-- The `DecidableEq`-free equivalence with the parent chapter's sharp residual. -/
theorem pointlessTwistDataAny_iff_residualSharp {𝕜 : Type} [Field 𝕜] :
    PointlessTwistDataAny 𝕜 ↔ Work.PointlessIndexFive.TwistResidualSharp 𝕜 := by
  constructor
  · rintro ⟨d, hd⟩
    letI : DecidableEq 𝕜 := d
    have h := (pointlessTwistData_iff (𝕜 := 𝕜)).mp hd
    exact ⟨d, h⟩
  · rintro ⟨d, hd⟩
    letI : DecidableEq 𝕜 := d
    exact ⟨d, (pointlessTwistData_iff (𝕜 := 𝕜)).mpr hd⟩

/-- **The paper's Lemma `lem:torsors` from the residual in data form.** -/
theorem hasLLinkCurve_of_pointlessTwistDataAny {𝕜 : Type} [Field 𝕜]
    (h : PointlessTwistDataAny 𝕜) : Work.Arithmetic.HasLLinkCurve 𝕜 :=
  Work.PointlessIndexFive.hasLLinkCurve_of_residualSharp
    (pointlessTwistDataAny_iff_residualSharp.mp h)

/-! ## 3. The two halves of the residual in data form -/

/-- The arithmetic half in data form gives the parent chapter's arithmetic residual. -/
theorem hasPointlessTwist_of_pointlessData {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    {C₅ : FiveTorsionCurve 𝕜} {L : CyclicExtension 𝕜 5} (h : PointlessOf C₅ L) :
    HasPointlessTwist 𝕜 :=
  Work.PointlessIndexFive.hasPointlessTwist_of_pointless_data C₅ L h

/-- **The composition: the data-level residual gives `HasPointlessIndexFiveCurve 𝕜`.**  Given the
paper's data (step (B) curve `C₅`, step (A) extension `L`), pointlessness of the twist and a curve
model realizing it, we obtain a smooth proper geometrically integral curve of dimension one over
`𝕜`, with no `𝕜`-point, carrying a `𝕜`-rational divisor of degree `5` and with all rational
divisor degrees divisible by `5` — the input of `Work.Arithmetic.HasLLinkCurve`. -/
theorem hasPointlessIndexFiveCurve_of_pointlessData {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    {C₅ : FiveTorsionCurve 𝕜} {L : CyclicExtension 𝕜 5} (hP : PointlessOf C₅ L)
    (M : TwistCurveModel (quinticTwistOf C₅ L)) : HasPointlessIndexFiveCurve 𝕜 :=
  Work.PointlessIndexFive.hasPointlessIndexFiveCurve_of_twistModel _ M hP

/-- The same from the existential form. -/
theorem hasPointlessIndexFiveCurve_of_pointlessTwistData {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (h : PointlessTwistData 𝕜) : HasPointlessIndexFiveCurve 𝕜 := by
  obtain ⟨C₅, L, hP, M⟩ := h
  exact hasPointlessIndexFiveCurve_of_pointlessData hP M.some

/-- Everything at once, from the residual in data form. -/
theorem conclusions_of_pointlessTwistData {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (h : PointlessTwistData 𝕜) :
    HasPointlessIndexFiveCurve 𝕜 ∧ Work.Arithmetic.HasLLinkCurve 𝕜 ∧
      Work.Arithmetic.ClarkLacyFive 𝕜 :=
  Work.PointlessIndexFive.conclusions_of_residualSharp
    ⟨(inferInstance : DecidableEq 𝕜), (pointlessTwistData_iff (𝕜 := 𝕜)).mp h⟩

/-- **The uniform geometric residual, in the paper's own data.**  `TwistRealization 𝕜` (every
quintic twist is realized) is equivalent to the same statement for every curve with a rational point
of order `5` and `j ≠ 1728` and every cyclic quintic extension, i.e. to `RealizationOf` for all
data.  So the geometric half may be attacked on the concrete data of the paper's steps (A) and (B).

(Uses `quinticTwistOf_toFiveTorsionCurve` in the non-trivial direction.) -/
theorem twistRealization_iff {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] :
    TwistRealization 𝕜 ↔
      ∀ (C₅ : FiveTorsionCurve 𝕜) (L : CyclicExtension 𝕜 5), RealizationOf C₅ L := by
  constructor
  · intro h C₅ L
    exact h (quinticTwistOf C₅ L)
  · intro h D
    have hD := h (Work.TorsorExistence.QuinticTwist.toFiveTorsionCurve D) D.ext
    rwa [RealizationOf, RealizationAt, quinticTwistOf_toFiveTorsionCurve D] at hD

/-! ## 4. Assembling a twist model from a curve model -/

/-- **A `TwistCurveModel` from a `CurveModel` and the two descent bridges.**  This is the target
of the *geometric* residual: `CurveModel 𝕜` is the scheme-theoretic statement (smooth, proper,
geometrically integral, dimension one over `𝕜`), and the two hypotheses are the Galois-descent
bridges identifying the rational points and rational divisors of the curve with the class of `D`
in `H¹(ℤ/5, E(L)) = ker N/(σ - 1)E(L)`. -/
def twistCurveModelOf {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (D : Work.TorsorExistence.QuinticTwist 𝕜) (M : CurveModel 𝕜)
    (h₁ : Work.Arithmetic.HasRatPoint 𝕜 M.C ↔ D.toTorsor.HasPoint)
    (h₂ : ∀ n : ℕ, Work.Arithmetic.HasRatDivisorOfDegree 𝕜 M.C n ↔
      D.toTorsor.DivisorOfDegree n) : TwistCurveModel D :=
  { C := M.C, variety := M.variety, isProper := M.isProper, isSmooth := M.isSmooth,
    isGeomIntegral := M.isGeomIntegral, dim_eq_one := M.dim_eq_one,
    hasPoint_iff := h₁, divisorOfDegree_iff := h₂ }

/-! ## 5. The local obstruction -/

/-- **The local-obstruction criterion.**  A local obstruction (`LocalObstruction D`,
`Defs.lean`) forces the twist to be pointless: if `P = σ R - R` and `φ` is additive with
`φ (σ R - R) = 0` but `φ P ≠ 0`, contradiction.  This is
`Work.PointlessIndexFive.pointless_of_shift_mem_ker` in the bundled form, and it is the paper's
reduction-modulo-a-place argument. -/
theorem localObstruction_pointless {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (D : Work.TorsorExistence.QuinticTwist 𝕜) (h : HasLocalObstruction D) : D.Pointless := by
  obtain ⟨obs⟩ := h
  rw [Work.PointlessIndexFive.pointless_iff_not_exists_shift]
  rintro ⟨R, hR⟩
  have h0 : obs.toFun D.PL = obs.toFun (D.galMap R - R) := congrArg obs.toFun hR.symm
  exact obs.map_PL (h0.trans (obs.map_shift R))

/-- **The arithmetic residual in local-obstruction form implies the arithmetic residual.** -/
theorem hasPointlessTwist_of_obstruction {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (h : HasPointlessTwistByObstruction 𝕜) : HasPointlessTwist 𝕜 := by
  obtain ⟨D, hD⟩ := h
  exact ⟨D, localObstruction_pointless D hD⟩

/-! ## 6. The four field classes, from the residual in data form

The field-class hypotheses (`NumberField`, `Finite`, `IsAlgClosed`) enter only through the
*existence* of the twist data (steps (A) and (B)), which is where the Clark--Lacy / Lang--Tate
arithmetic lives; the residual `PointlessTwistDataAny 𝕜` already contains the chosen data, its
pointlessness and its realization.  The `DecidableEq 𝕜` instance carried by `QuinticTwist` is
quantified in `PointlessTwistDataAny`, so these four theorems have no decidability hypothesis. -/

/-- **Class (a)**, number fields. -/
theorem hasLLinkCurve_pointlessTwistDataAny_numberField {𝕜 : Type} [Field 𝕜] [NumberField 𝕜]
    (h : PointlessTwistDataAny 𝕜) : Work.Arithmetic.HasLLinkCurve 𝕜 :=
  hasLLinkCurve_of_pointlessTwistDataAny h

/-- **Class (b)**, function fields over number fields. -/
theorem hasLLinkCurve_pointlessTwistDataAny_functionField_numberField (𝔽 : Type) [Field 𝔽]
    [NumberField 𝔽] (X : Scheme) [MotivicInvariants.Variety 𝔽 X]
    (_hX : 0 < topologicalKrullDim X) (h : PointlessTwistDataAny X.functionField) :
    Work.Arithmetic.HasLLinkCurve X.functionField :=
  hasLLinkCurve_of_pointlessTwistDataAny h

/-- **Class (c)**, function fields over finite fields. -/
theorem hasLLinkCurve_pointlessTwistDataAny_functionField_finite (𝔽 : Type) [Field 𝔽] [Finite 𝔽]
    (X : Scheme) [MotivicInvariants.Variety 𝔽 X]
    (_hX : 0 < topologicalKrullDim X) (h : PointlessTwistDataAny X.functionField) :
    Work.Arithmetic.HasLLinkCurve X.functionField :=
  hasLLinkCurve_of_pointlessTwistDataAny h

/-- **Class (d)**, function fields over algebraically closed fields. -/
theorem hasLLinkCurve_pointlessTwistDataAny_functionField_algClosed (𝔽 : Type) [Field 𝔽]
    [IsAlgClosed 𝔽] (X : Scheme) [MotivicInvariants.Variety 𝔽 X]
    (_hX : 0 < topologicalKrullDim X) (h : PointlessTwistDataAny X.functionField) :
    Work.Arithmetic.HasLLinkCurve X.functionField :=
  hasLLinkCurve_of_pointlessTwistDataAny h

end

end Work.Twist
