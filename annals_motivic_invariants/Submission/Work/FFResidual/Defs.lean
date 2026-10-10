/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: Work.FFResidual
-/
import Mathlib
import Submission.Work.ClassBCD.Defs
import Submission.Work.ClassA.Model

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FFResidual` — the function-field residual of the classes (b), (c), (d)

This area proves the *function-field residual* `Work.ClassBCD.FunctionFieldResidual 𝔽 𝕜` for the
general function field `𝕜 = X.functionField` of a positive-dimensional `𝔽`-variety, i.e. the place
obstruction of the function-field classes of Lin–Shinder, *Motivic invariants of birational maps*,
Annals of Math. **199** (1), 2024, Theorem 1.2 (1) (b)–(d), *at the top field of a place of* `𝕜`.

## The shape of the argument

At `𝕜 = 𝔽(t)` the residual is proved (`Work.ClassBCD.RatFunc`) through the classical
`E(𝔽(s)) = E(𝔽)` at the rational function field.  At a general function field `𝕜` that route is
unavailable (a positive-dimensional `X` may map non-constantly to the constant curve `E`); the
honest input is a **place** of `𝕜` over the constants,

  `FunctionFieldPlace 𝔽 𝕜` — a discrete valuation ring `R ⊆ 𝕜` with `IsFractionRing R 𝕜`,
  containing the constants (`IsScalarTower 𝔽 R 𝕜`), together with a chosen uniformizer `π`.

The chapter `Submission/Work/FFResidual` proves, from such a place and a cyclic quintic extension
of the function field built out of the *uniformizer* `π` (Kummer when `ζ₅ ∈ 𝔽` and characteristic
`≠ 5`, Artin–Schreier in characteristic `5`), that the residual holds:

* `FunctionFieldResidual 𝔽 𝕜` from `HasFunctionFieldPlace 𝔽 𝕜` together with `ζ₅ ∈ 𝔽`
  (`nonempty_functionFieldResidual_of_hasFunctionFieldPlace`), and the characteristic-`5`
  analogue;
* consequently the three class theorems at `X.functionField` *modulo the place*:
  `hasPointlessTwist_functionField_numberField_of_place` etc.

## Main definitions

* `Work.FFResidual.FunctionFieldPlace 𝔽 𝕜` — the place of the function field over the constants.
* `Work.FFResidual.HasFunctionFieldPlace 𝔽 𝕜` — the residual input in `Prop` form.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false


namespace Work.FFResidual

noncomputable section

/-! ## 1. Places of a function field over its field of constants -/

/-- **A place of the function field `𝕜` over the constants `𝔽`.**

A discrete valuation ring `R` whose fraction field is `𝕜`, along the structure map `𝔽 → 𝕜` (so
that the constants are integral at the place: `𝔽 ⊆ R` through `IsScalarTower 𝔽 R 𝕜`), together
with a chosen uniformizer `π` generating the maximal ideal.

For `𝕜 = X.functionField` of a positive-dimensional variety `X` such a place is produced by a
point of codimension `1` of a normal model of `X` (the local ring of the point, which is a discrete
valuation ring with fraction field `X.functionField`); this chapter does not construct it — the
geometry of `X` is the *only* remaining input of the function-field classes. -/
structure FunctionFieldPlace (𝔽 : Type) [Field 𝔽] (𝕜 : Type) [Field 𝕜] [Algebra 𝔽 𝕜] where
  /-- The valuation ring of the place. -/
  R : Type
  [commRing : CommRing R]
  [isDomain : IsDomain R]
  [isDiscreteValuationRing : IsDiscreteValuationRing R]
  /-- The constants are integral at the place. -/
  [algebraF : Algebra 𝔽 R]
  /-- The place is a place of `𝕜` over `𝔽`. -/
  [algebraR : Algebra R 𝕜]
  [tower : IsScalarTower 𝔽 R 𝕜]
  [isFractionRing : IsFractionRing R 𝕜]
  /-- A uniformizer of the place. -/
  π : R
  /-- `π` generates the maximal ideal. -/
  isUniformizer : IsLocalRing.maximalIdeal R = Ideal.span {π}

attribute [instance] FunctionFieldPlace.commRing FunctionFieldPlace.isDomain
  FunctionFieldPlace.isDiscreteValuationRing FunctionFieldPlace.algebraF FunctionFieldPlace.algebraR
  FunctionFieldPlace.tower FunctionFieldPlace.isFractionRing

/-- **The place of a function field over its constants**, in `Prop` form: the residual input of the
function-field classes (b), (c), (d) at a general function field. -/
def HasFunctionFieldPlace (𝔽 : Type) [Field 𝔽] (𝕜 : Type) [Field 𝕜] [Algebra 𝔽 𝕜] : Prop :=
  Nonempty (FunctionFieldPlace 𝔽 𝕜)

namespace FunctionFieldPlace

variable {𝔽 : Type} [Field 𝔽] {𝕜 : Type} [Field 𝕜] [Algebra 𝔽 𝕜]
  (P : FunctionFieldPlace 𝔽 𝕜)

/-- The constants are units at the place: a nonzero constant is a unit of the valuation ring. -/
theorem isUnit_algebraMap (x : 𝔽) (hx : x ≠ 0) : IsUnit (algebraMap 𝔽 P.R x) := by
  refine ⟨⟨algebraMap 𝔽 P.R x, algebraMap 𝔽 P.R x⁻¹, ?_, ?_⟩, rfl⟩ <;>
    simp [← map_mul, hx]

/-- The uniformizer is nonzero. -/
theorem pi_ne_zero : P.π ≠ 0 := by
  intro h
  have h1 : IsLocalRing.maximalIdeal P.R = ⊥ := by rw [P.isUniformizer, h, Ideal.span_singleton_eq_bot]
  exact (IsDiscreteValuationRing.not_a_field P.R) h1

end FunctionFieldPlace

end

end Work.FFResidual
