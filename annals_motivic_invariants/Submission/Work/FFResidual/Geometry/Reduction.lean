/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: Work.FFResidual
-/
import Submission.Work.FFResidual.Main
import Submission.Work.FFResidual.Geometry.OverAlgebraDefs
import Submission.Work.FFResidual.Geometry.hasFunctionFieldPlace_of_coheight_one_stalk
import Submission.Work.FFResidual.Geometry.isScalarTower_overStalkAlgebra_overFunctionFieldAlgebra

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The function-field residual from a codimension-one point of integrally closed local ring

The chapter `Submission/Work/FFResidual` proves the residual `FunctionFieldResidual 𝔽 𝕜` from a
*place* `FunctionFieldPlace 𝔽 𝕜` of the function field over its constants.  This file supplies the
missing geometric input in its sharpest algebraic form: **a point `z` of codimension one whose local
ring `𝒪_{X,z}` is integrally closed** (a *normal* point), together with the two `𝔽`-algebra
structures compatible with the structure morphism `X ↘ Spec 𝔽` (`overStalkAlgebra`,
`overFunctionFieldAlgebra`, whose compatibility is `isScalarTower_overStalkAlgebra`).

The reduction is
`𝔽 → 𝒪_{X,z} → X.functionField` with `𝒪_{X,z}` a discrete valuation ring (a Noetherian local domain
of Krull dimension `1` that is integrally closed: `isDiscreteValuationRing_of_isIntegrallyClosed_of_krullDimLE_one`),
which is exactly a place of `X.functionField` over `𝔽`; the residual then follows from the chapter's
Kummer / Artin–Schreier analysis at that place.

The **only** remaining geometric input is therefore the existence of such a point `z` of `X` itself
(a normal model of `X` at a codimension-one point): see `NOTES.md` §3.1 and
`HasIntegrallyClosedCodimOnePoint`.

## Main results

* `Work.FFResidual.HasIntegrallyClosedCodimOnePoint` — the geometric sub-residual.
* `Work.FFResidual.nonempty_functionFieldResidual_of_coheight_one_stalk` — the residual at `X.functionField`
  from a point of codimension one with integrally closed local ring, in the Kummer case.
* `Work.FFResidual.nonempty_hasPointlessTwist_of_coheight_one_stalk` — the same, in the
  `DecidableEq`-free form consumed by the class theorems.
* the characteristic-`5` (Artin–Schreier) analogues, and the `Variety`-level versions
  `nonempty_functionFieldResidual_of_hasIntegrallyClosedCodimOnePoint`,
  `hasPointlessTwist_functionField_of_hasIntegrallyClosedCodimOnePoint{,_charP}`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory

namespace Work.FFResidual

noncomputable section

/-- **The geometric sub-residual of the function-field classes**: the scheme `X` has a point `z` of
codimension one whose local ring `𝒪_{X,z}` is integrally closed in its fraction field, i.e. a
*normal* point of codimension one (such a point is a discrete valuation ring).

For `X` a variety this holds — one takes a normal (or regular) model of `X` and a codimension-one
point of its smooth locus — but the existence of the normal model and of a codimension-one point of
it are not in Mathlib (`NOTES.md` §3.1).  Everything else of the function-field classes is proved. -/
def HasIntegrallyClosedCodimOnePoint (X : Scheme) : Prop :=
  ∃ z : X, Order.coheight z = 1 ∧ IsIntegrallyClosed (X.presheaf.stalk z)

/-- **A variety is locally Noetherian** (it is locally of finite type over the spectrum of a field).
Mathlib's `LocallyOfFiniteType.isLocallyNoetherian` is not found by type class search because the
structure morphism `X ↘ Spec 𝔽` cannot be guessed from the goal, and the instance field
`Variety.locallyOfFiniteType` is not found either; both are applied explicitly here, so that the
class statements below need only the `Variety` hypothesis. -/
theorem isLocallyNoetherian_of_variety (𝔽 : Type) [Field 𝔽] (X : Scheme)
    [MotivicInvariants.Variety 𝔽 X] : IsLocallyNoetherian X :=
  @LocallyOfFiniteType.isLocallyNoetherian X (Spec (CommRingCat.of 𝔽))
    (X ↘ Spec (CommRingCat.of 𝔽)) MotivicInvariants.Variety.locallyOfFiniteType _

/-- **The function-field residual (Kummer case) from a codimension-one point of integrally closed
local ring.** -/
theorem nonempty_functionFieldResidual_of_coheight_one_stalk
    (𝔽 : Type) [Field 𝔽] [DecidableEq 𝔽] {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {z : X} [Algebra 𝔽 X.functionField] [Algebra 𝔽 (X.presheaf.stalk z)]
    [IsScalarTower 𝔽 (X.presheaf.stalk z) X.functionField]
    (hz : Order.coheight z = 1) (hint : IsIntegrallyClosed (X.presheaf.stalk z))
    (ζ : 𝔽) (hζ : IsPrimitiveRoot ζ 5) (c : 𝔽)
    (hΔ : (Work.TorsorExistence.Tate.tateCurve c).Δ ≠ 0)
    (hj : (Work.TorsorExistence.Tate.tateCurve c).c₄ ^ 3
      ≠ 1728 * (Work.TorsorExistence.Tate.tateCurve c).Δ) :
    Nonempty (Work.ClassBCD.FunctionFieldResidual 𝔽 X.functionField) :=
  ((Geometry.hasFunctionFieldPlace_of_coheight_one_stalk hz hint).some).nonempty_functionFieldResidual
    ζ hζ c hΔ hj

/-- **The arithmetic half of the classes (b), (c), (d), from a codimension-one point of integrally
closed local ring** (Kummer case), in the `DecidableEq`-free form consumed by the class theorems. -/
theorem nonempty_hasPointlessTwist_of_coheight_one_stalk
    (𝔽 : Type) [Field 𝔽] [DecidableEq 𝔽] {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {z : X} [Algebra 𝔽 X.functionField] [Algebra 𝔽 (X.presheaf.stalk z)]
    [IsScalarTower 𝔽 (X.presheaf.stalk z) X.functionField]
    (hz : Order.coheight z = 1) (hint : IsIntegrallyClosed (X.presheaf.stalk z))
    (ζ : 𝔽) (hζ : IsPrimitiveRoot ζ 5) (c : 𝔽)
    (hΔ : (Work.TorsorExistence.Tate.tateCurve c).Δ ≠ 0)
    (hj : (Work.TorsorExistence.Tate.tateCurve c).c₄ ^ 3
      ≠ 1728 * (Work.TorsorExistence.Tate.tateCurve c).Δ) :
    ∃ dec : DecidableEq X.functionField,
      @Work.PointlessTwist.HasPointlessTwist X.functionField _ dec :=
  ((Geometry.hasFunctionFieldPlace_of_coheight_one_stalk hz hint).some).nonempty_hasPointlessTwist_of_place
    ζ hζ c hΔ hj

/-- **The function-field residual (characteristic five) from a codimension-one point of integrally
closed local ring.** -/
theorem nonempty_functionFieldResidual_of_coheight_one_stalk_charP
    (𝔽 : Type) [Field 𝔽] [DecidableEq 𝔽] [CharP 𝔽 5]
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {z : X} [Algebra 𝔽 X.functionField] [Algebra 𝔽 (X.presheaf.stalk z)]
    [IsScalarTower 𝔽 (X.presheaf.stalk z) X.functionField]
    (hz : Order.coheight z = 1) (hint : IsIntegrallyClosed (X.presheaf.stalk z))
    (c : 𝔽)
    (hΔ : (Work.TorsorExistence.Tate.tateCurve c).Δ ≠ 0)
    (hj : (Work.TorsorExistence.Tate.tateCurve c).c₄ ^ 3
      ≠ 1728 * (Work.TorsorExistence.Tate.tateCurve c).Δ) :
    Nonempty (Work.ClassBCD.FunctionFieldResidual 𝔽 X.functionField) := by
  haveI : CharP X.functionField 5 :=
    charP_of_injective_algebraMap (algebraMap 𝔽 X.functionField).injective 5
  exact ((Geometry.hasFunctionFieldPlace_of_coheight_one_stalk hz hint).some)
    |>.nonempty_functionFieldResidual_charP c hΔ hj

/-- **The arithmetic half in characteristic five**, from a codimension-one point of integrally closed
local ring. -/
theorem nonempty_hasPointlessTwist_of_coheight_one_stalk_charP
    (𝔽 : Type) [Field 𝔽] [DecidableEq 𝔽] [CharP 𝔽 5]
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {z : X} [Algebra 𝔽 X.functionField] [Algebra 𝔽 (X.presheaf.stalk z)]
    [IsScalarTower 𝔽 (X.presheaf.stalk z) X.functionField]
    (hz : Order.coheight z = 1) (hint : IsIntegrallyClosed (X.presheaf.stalk z))
    (c : 𝔽)
    (hΔ : (Work.TorsorExistence.Tate.tateCurve c).Δ ≠ 0)
    (hj : (Work.TorsorExistence.Tate.tateCurve c).c₄ ^ 3
      ≠ 1728 * (Work.TorsorExistence.Tate.tateCurve c).Δ) :
    ∃ dec : DecidableEq X.functionField,
      @Work.PointlessTwist.HasPointlessTwist X.functionField _ dec := by
  haveI : CharP X.functionField 5 :=
    charP_of_injective_algebraMap (algebraMap 𝔽 X.functionField).injective 5
  exact ((Geometry.hasFunctionFieldPlace_of_coheight_one_stalk hz hint).some)
    |>.nonempty_hasPointlessTwist_of_place_charP c hΔ hj

/-! ## The class statements at `𝕜 = X.functionField`, modulo the geometric sub-residual -/

/-- **The residual at `𝕜 = X.functionField` from the geometric sub-residual** (Kummer case).  The
`𝔽`-algebra structure on `X.functionField` is the explicit one `overFunctionFieldAlgebra`. -/
theorem nonempty_functionFieldResidual_of_hasIntegrallyClosedCodimOnePoint
    (𝔽 : Type) [Field 𝔽] [DecidableEq 𝔽] (X : Scheme) [MotivicInvariants.Variety 𝔽 X]
    (h : HasIntegrallyClosedCodimOnePoint X) (ζ : 𝔽) (hζ : IsPrimitiveRoot ζ 5) (c : 𝔽)
    (hΔ : (Work.TorsorExistence.Tate.tateCurve c).Δ ≠ 0)
    (hj : (Work.TorsorExistence.Tate.tateCurve c).c₄ ^ 3
      ≠ 1728 * (Work.TorsorExistence.Tate.tateCurve c).Δ) :
    letI := overFunctionFieldAlgebra 𝔽 X
    Nonempty (Work.ClassBCD.FunctionFieldResidual 𝔽 X.functionField) := by
  haveI := isLocallyNoetherian_of_variety 𝔽 X
  letI := overFunctionFieldAlgebra 𝔽 X
  obtain ⟨z, hz, hint⟩ := h
  letI := overStalkAlgebra 𝔽 X z
  haveI := Geometry.isScalarTower_overStalkAlgebra_overFunctionFieldAlgebra 𝔽 X z
  exact nonempty_functionFieldResidual_of_coheight_one_stalk 𝔽 hz hint ζ hζ c hΔ hj

/-- **Class (b)/(c) at `𝕜 = X.functionField`, modulo the geometric sub-residual** (Kummer case):
the arithmetic half of Theorem 1.2 (1) for every `𝔽` containing a primitive fifth root of unity. -/
theorem hasPointlessTwist_functionField_of_hasIntegrallyClosedCodimOnePoint
    (𝔽 : Type) [Field 𝔽] [DecidableEq 𝔽] (X : Scheme) [MotivicInvariants.Variety 𝔽 X]
    (h : HasIntegrallyClosedCodimOnePoint X) (ζ : 𝔽) (hζ : IsPrimitiveRoot ζ 5) (c : 𝔽)
    (hΔ : (Work.TorsorExistence.Tate.tateCurve c).Δ ≠ 0)
    (hj : (Work.TorsorExistence.Tate.tateCurve c).c₄ ^ 3
      ≠ 1728 * (Work.TorsorExistence.Tate.tateCurve c).Δ) :
    ∃ dec : DecidableEq X.functionField,
      @Work.PointlessTwist.HasPointlessTwist X.functionField _ dec := by
  haveI := isLocallyNoetherian_of_variety 𝔽 X
  letI := overFunctionFieldAlgebra 𝔽 X
  obtain ⟨z, hz, hint⟩ := h
  letI := overStalkAlgebra 𝔽 X z
  haveI := Geometry.isScalarTower_overStalkAlgebra_overFunctionFieldAlgebra 𝔽 X z
  exact nonempty_hasPointlessTwist_of_coheight_one_stalk 𝔽 hz hint ζ hζ c hΔ hj

/-- **Class (c)/(d) at `𝕜 = X.functionField` in characteristic five**, modulo the geometric
sub-residual (Artin–Schreier case). -/
theorem hasPointlessTwist_functionField_of_hasIntegrallyClosedCodimOnePoint_charP
    (𝔽 : Type) [Field 𝔽] [DecidableEq 𝔽] [CharP 𝔽 5] (X : Scheme) [MotivicInvariants.Variety 𝔽 X]
    (h : HasIntegrallyClosedCodimOnePoint X) (c : 𝔽)
    (hΔ : (Work.TorsorExistence.Tate.tateCurve c).Δ ≠ 0)
    (hj : (Work.TorsorExistence.Tate.tateCurve c).c₄ ^ 3
      ≠ 1728 * (Work.TorsorExistence.Tate.tateCurve c).Δ) :
    ∃ dec : DecidableEq X.functionField,
      @Work.PointlessTwist.HasPointlessTwist X.functionField _ dec := by
  haveI := isLocallyNoetherian_of_variety 𝔽 X
  letI := overFunctionFieldAlgebra 𝔽 X
  obtain ⟨z, hz, hint⟩ := h
  letI := overStalkAlgebra 𝔽 X z
  haveI := Geometry.isScalarTower_overStalkAlgebra_overFunctionFieldAlgebra 𝔽 X z
  exact nonempty_hasPointlessTwist_of_coheight_one_stalk_charP 𝔽 hz hint c hΔ hj

end

end Work.FFResidual
