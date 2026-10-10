/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: Work.FFResidual
-/
import Submission.Work.FFResidual.Kummer.Residual
import Submission.Work.FFResidual.CharP.Residual
import Submission.Work.ClassBCD.instAlgebraFunctionField
import Submission.Work.ClassBCD.exists_isPrimitiveRoot_five_of_isAlgClosed
import Submission.Work.ClassBCD.Wiring
import Submission.Work.FFResidual.exists_isPrimitiveRoot_five_of_finite

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The function-field residual at `𝕜 = X.functionField`: the class statements

This file states the function-field classes (b), (c), (d) of Lin–Shinder, *Motivic invariants of
birational maps*, Annals of Math. **199** (1), 2024, Theorem 1.2 (1), at the **general function
field** `𝕜 = X.functionField` of a positive-dimensional `𝔽`-variety `X`, *modulo the existence of a
place of `𝕜` over its constants* (`FunctionFieldPlace 𝔽 𝕜`) and a primitive fifth root of unity in
the constants.

The remaining input — the place of the function field of a variety — is the geometric part of the
paper's route (ii)/(iii): it is produced by a point of codimension one of a normal model of `X`,
whose local ring is a discrete valuation ring with fraction field `X.functionField`; Mathlib has
neither the codimension-one point theory of the function field of a variety nor the extension
theory of a valuation to a finite extension, which is what a future stretch has to build (see
`Submission/Work/FFResidual/NOTES.md`).

## Main results

* `nonempty_functionFieldResidual_of_place` — `Nonempty (FunctionFieldResidual 𝔽 X.functionField)`
  from a place of `X.functionField` and `ζ₅ ∈ 𝔽`.
* `hasPointlessTwist_functionField_of_place` — the arithmetic half at `X.functionField` from the
  same data, hence the class theorem for each class in which `𝔽` contains `ζ₅` (class (d) in
  characteristic `≠ 5` via `exists_isPrimitiveRoot_five_of_isAlgClosed`, class (c) when
  `5 ∣ #𝔽 - 1`, class (b) when `ζ₅ ∈ 𝔽`).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

universe u

open AlgebraicGeometry MotivicInvariants

namespace Work.FFResidual

noncomputable section

/-- **The function-field residual at a place of a function field.**  Let `X` be a
positive-dimensional `𝔽`-variety whose function field carries a place `P` over the constants, let
`ζ₅ ∈ 𝔽` and let `c ∈ 𝔽` be a good Tate parameter.  Then the residual
`Work.ClassBCD.FunctionFieldResidual 𝔽 X.functionField` holds. -/
theorem nonempty_functionFieldResidual_of_place (𝔽 : Type) [Field 𝔽] [DecidableEq 𝔽]
    (X : Scheme) [Variety 𝔽 X] (hX : 0 < topologicalKrullDim X)
    (P : FunctionFieldPlace 𝔽 X.functionField) (ζ : 𝔽) (hζ : IsPrimitiveRoot ζ 5)
    (c : 𝔽)
    (hΔ : (Work.TorsorExistence.Tate.tateCurve c).Δ ≠ 0)
    (hj : (Work.TorsorExistence.Tate.tateCurve c).c₄ ^ 3
      ≠ 1728 * (Work.TorsorExistence.Tate.tateCurve c).Δ) :
    Nonempty (Work.ClassBCD.FunctionFieldResidual 𝔽 X.functionField) :=
  P.nonempty_functionFieldResidual ζ hζ c hΔ hj

/-- **The arithmetic half of the classes (b), (c), (d) at the function field of a variety, from a
place of the function field**: the class theorem of Theorem 1.2 (1) modulo the place. -/
theorem hasPointlessTwist_functionField_of_place (𝔽 : Type) [Field 𝔽] [DecidableEq 𝔽]
    (X : Scheme) [Variety 𝔽 X] (hX : 0 < topologicalKrullDim X)
    (P : FunctionFieldPlace 𝔽 X.functionField) (ζ : 𝔽) (hζ : IsPrimitiveRoot ζ 5)
    (c : 𝔽)
    (hΔ : (Work.TorsorExistence.Tate.tateCurve c).Δ ≠ 0)
    (hj : (Work.TorsorExistence.Tate.tateCurve c).c₄ ^ 3
      ≠ 1728 * (Work.TorsorExistence.Tate.tateCurve c).Δ) :
    ∃ dec : DecidableEq X.functionField,
      @Work.PointlessTwist.HasPointlessTwist X.functionField _ dec :=
  P.nonempty_hasPointlessTwist_of_place ζ hζ c hΔ hj

/-- **Class (d) at a place**: for an algebraically closed field `𝔽` of characteristic `≠ 5`, the
primitive fifth root of unity exists, so the class theorem holds at `X.functionField` for a
positive-dimensional `X` as soon as its function field carries a place over the constants. -/
theorem hasPointlessTwist_functionField_algClosed_of_place (𝔽 : Type) [Field 𝔽] [DecidableEq 𝔽]
    [IsAlgClosed 𝔽] (h5 : (5 : 𝔽) ≠ 0) (X : Scheme) [Variety 𝔽 X]
    (hX : 0 < topologicalKrullDim X) (P : FunctionFieldPlace 𝔽 X.functionField) (c : 𝔽)
    (hΔ : (Work.TorsorExistence.Tate.tateCurve c).Δ ≠ 0)
    (hj : (Work.TorsorExistence.Tate.tateCurve c).c₄ ^ 3
      ≠ 1728 * (Work.TorsorExistence.Tate.tateCurve c).Δ) :
    ∃ dec : DecidableEq X.functionField,
      @Work.PointlessTwist.HasPointlessTwist X.functionField _ dec := by
  obtain ⟨ζ, hζ⟩ := Work.ClassBCD.exists_isPrimitiveRoot_five_of_isAlgClosed 𝔽 h5
  exact P.nonempty_hasPointlessTwist_of_place ζ hζ c hΔ hj


/-! ## 2. The characteristic-five classes (Artin–Schreier)

At `char 𝔽 = 5` there is no primitive fifth root of unity; the cyclic quintic extension of the
classes is the Artin–Schreier extension of the place at infinity
(`FunctionFieldPlace.asCyclicExtension`), and the residual is
`FunctionFieldPlace.nonempty_functionFieldResidual_charP`.  This covers class (c) for finite fields
of characteristic `5` (e.g. `𝔽₅`) and class (d) for algebraically closed fields of characteristic
`5` — the two cases in which the Kummer route of §1 is unavailable.
-/

/-- **The function-field residual at a place in characteristic five**, at `𝕜 = X.functionField`. -/
theorem nonempty_functionFieldResidual_charP_of_place (𝔽 : Type) [Field 𝔽] [DecidableEq 𝔽]
    [CharP 𝔽 5] (X : Scheme) [Variety 𝔽 X] (hX : 0 < topologicalKrullDim X)
    (P : FunctionFieldPlace 𝔽 X.functionField) (c : 𝔽)
    (hΔ : (Work.TorsorExistence.Tate.tateCurve c).Δ ≠ 0)
    (hj : (Work.TorsorExistence.Tate.tateCurve c).c₄ ^ 3
      ≠ 1728 * (Work.TorsorExistence.Tate.tateCurve c).Δ) :
    Nonempty (Work.ClassBCD.FunctionFieldResidual 𝔽 X.functionField) := by
  haveI : CharP X.functionField 5 :=
    charP_of_injective_algebraMap (algebraMap 𝔽 X.functionField).injective 5
  exact P.nonempty_functionFieldResidual_charP c hΔ hj

/-- **The arithmetic half of the classes in characteristic five, at `𝕜 = X.functionField`**, from a
place of the function field: this is the class statement of Theorem 1.2 (1) (c) for finite fields
of characteristic `5` and (d) for algebraically closed fields of characteristic `5`, modulo the
existence of the place. -/
theorem hasPointlessTwist_functionField_charP_of_place (𝔽 : Type) [Field 𝔽] [DecidableEq 𝔽]
    [CharP 𝔽 5] (X : Scheme) [Variety 𝔽 X] (hX : 0 < topologicalKrullDim X)
    (P : FunctionFieldPlace 𝔽 X.functionField) (c : 𝔽)
    (hΔ : (Work.TorsorExistence.Tate.tateCurve c).Δ ≠ 0)
    (hj : (Work.TorsorExistence.Tate.tateCurve c).c₄ ^ 3
      ≠ 1728 * (Work.TorsorExistence.Tate.tateCurve c).Δ) :
    ∃ dec : DecidableEq X.functionField,
      @Work.PointlessTwist.HasPointlessTwist X.functionField _ dec := by
  haveI : CharP X.functionField 5 :=
    charP_of_injective_algebraMap (algebraMap 𝔽 X.functionField).injective 5
  exact P.nonempty_hasPointlessTwist_of_place_charP c hΔ hj


/-! ## 3. Two concrete instances

The general statements above are instantiated at the two finite fields of class (c) in which the
constants are small: `𝔽₁₁` (Kummer route, `3` is a primitive fifth root of unity) and `𝔽₅`
(characteristic `5`, Artin–Schreier route).
-/

section ConcreteFields

local instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- **Class (c) at `𝔽₁₁`**, modulo the place of the function field. -/
theorem hasPointlessTwist_functionField_finite11_of_place (X : Scheme) [Variety (ZMod 11) X]
    (hX : 0 < topologicalKrullDim X)
    (P : FunctionFieldPlace (ZMod 11) X.functionField) :
    ∃ dec : DecidableEq X.functionField,
      @Work.PointlessTwist.HasPointlessTwist X.functionField _ dec := by
  have hζ : IsPrimitiveRoot (3 : ZMod 11) 5 := by
    rw [IsPrimitiveRoot.iff_orderOf]
    exact orderOf_eq_prime (by decide) (by decide)
  have hΔ : (Work.TorsorExistence.Tate.tateCurve (2 : ZMod 11)).Δ ≠ 0 := by
    rw [Work.TorsorExistence.Tate.tateCurve_Δ]; decide
  have hj : (Work.TorsorExistence.Tate.tateCurve (2 : ZMod 11)).c₄ ^ 3
      ≠ 1728 * (Work.TorsorExistence.Tate.tateCurve (2 : ZMod 11)).Δ := by
    rw [Work.TorsorExistence.Tate.tateCurve_Δ, Work.TorsorExistence.Tate.tateCurve_c₄]; decide
  exact hasPointlessTwist_functionField_of_place (ZMod 11) X hX P 3 hζ 2 hΔ hj

/-- **Class (c) at `𝔽₅`** (characteristic `5`, Artin–Schreier route), modulo the place. -/
theorem hasPointlessTwist_functionField_five_of_place (X : Scheme) [Variety (ZMod 5) X]
    (hX : 0 < topologicalKrullDim X)
    (P : FunctionFieldPlace (ZMod 5) X.functionField) :
    ∃ dec : DecidableEq X.functionField,
      @Work.PointlessTwist.HasPointlessTwist X.functionField _ dec := by
  have hΔ : (Work.TorsorExistence.Tate.tateCurve (1 : ZMod 5)).Δ ≠ 0 := by
    rw [Work.TorsorExistence.Tate.tateCurve_Δ]; decide
  have hj : (Work.TorsorExistence.Tate.tateCurve (1 : ZMod 5)).c₄ ^ 3
      ≠ 1728 * (Work.TorsorExistence.Tate.tateCurve (1 : ZMod 5)).Δ := by
    rw [Work.TorsorExistence.Tate.tateCurve_Δ, Work.TorsorExistence.Tate.tateCurve_c₄]; decide
  exact hasPointlessTwist_functionField_charP_of_place (ZMod 5) X hX P 1 hΔ hj

end ConcreteFields


/-! ## 4. Class (c): general finite fields with `5 ∣ #𝔽 - 1`

For a finite field `𝔽` whose cardinality satisfies `5 ∣ #𝔽 - 1`, the fifth root of unity exists
(`exists_isPrimitiveRoot_five_of_finite`), so the Kummer route applies and the class theorem of
Theorem 1.2 (1) (c) holds at `X.functionField` modulo the place.
-/

/-- **Class (c), general finite field, modulo the place.** -/
theorem hasPointlessTwist_functionField_finite_of_place (𝔽 : Type) [Field 𝔽] [Finite 𝔽]
    (h5 : 5 ∣ Nat.card 𝔽 - 1) (X : Scheme) [Variety 𝔽 X] (hX : 0 < topologicalKrullDim X)
    (P : FunctionFieldPlace 𝔽 X.functionField) (c : 𝔽)
    (hΔ : (Work.TorsorExistence.Tate.tateCurve c).Δ ≠ 0)
    (hj : (Work.TorsorExistence.Tate.tateCurve c).c₄ ^ 3
      ≠ 1728 * (Work.TorsorExistence.Tate.tateCurve c).Δ) :
    ∃ dec : DecidableEq X.functionField,
      @Work.PointlessTwist.HasPointlessTwist X.functionField _ dec := by
  classical
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_five_of_finite 𝔽 h5
  exact hasPointlessTwist_functionField_of_place 𝔽 X hX P ζ hζ c hΔ hj

end

end Work.FFResidual
