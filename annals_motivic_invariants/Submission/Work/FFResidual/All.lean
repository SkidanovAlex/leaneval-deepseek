/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: Work.FFResidual
-/
import Submission.Work.FFResidual.Kummer.Basic
import Submission.Work.FFResidual.Kummer.Model
import Submission.Work.FFResidual.Kummer.Residual
import Submission.Work.FFResidual.Main
import Submission.Work.FFResidual.CharP.Residual
import Submission.Work.FFResidual.RatFunc
import Submission.Work.FFResidual.Geometry.OverAlgebraDefs
import Submission.Work.FFResidual.Geometry.isDiscreteValuationRing_of_isIntegrallyClosed_of_krullDimLE_one
import Submission.Work.FFResidual.Geometry.hasFunctionFieldPlace_of_coheight_one_stalk
import Submission.Work.FFResidual.Geometry.isScalarTower_overStalkAlgebra_overFunctionFieldAlgebra
import Submission.Work.FFResidual.Geometry.Reduction
import Submission.Work.FFResidual.Geometry.isDiscreteValuationRing_localization_AtPrime_of_span_singleton
import Submission.Work.FFResidual.Geometry.hasFunctionFieldPlace_of_algEquiv
import Submission.Work.FFResidual.Geometry.height_span_mvPolynomial_X
import Submission.Work.FFResidual.Geometry.hasIntegrallyClosedCodimOnePoint_spec_mvPolynomial
import Submission.Work.FFResidual.Geometry.hasFunctionFieldPlace_fractionRing_mvPolynomial
import Submission.Work.FFResidual.Geometry.MvPolynomialClasses
import Submission.Work.FFResidual.Geometry.SpecMvPolynomialClasses

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FFResidual`: the function-field residual of the classes (b), (c), (d) at a place

Entry point of the area; see `Submission/Work/FFResidual/NOTES.md` for the mathematical content and
the precise remaining sub-residuals.

* `Work.FFResidual.FunctionFieldPlace 𝔽 𝕜` — a place of the function field `𝕜` over its constants
  `𝔽` (a discrete valuation ring `R ⊆ 𝕜` with `IsFractionRing R 𝕜`, uniformizer `π`).
* `Work.FFResidual.FunctionFieldPlace.nonempty_functionFieldResidual` — the residual
  `Work.ClassBCD.FunctionFieldResidual 𝔽 𝕜` from a place, `ζ₅ ∈ 𝔽` and a good Tate parameter.
* `Work.FFResidual.nonempty_functionFieldResidual_of_place`,
  `Work.FFResidual.hasPointlessTwist_functionField_of_place` — the same at `𝕜 = X.functionField`.
* `Work.FFResidual.HasIntegrallyClosedCodimOnePoint X` — **the sharpened geometric sub-residual**:
  a point of codimension one whose local ring is integrally closed (a normal point of codimension
  one; its local ring is a discrete valuation ring, hence a place of `X.functionField`).
* `Work.FFResidual.nonempty_functionFieldResidual_of_coheight_one_stalk`,
  `Work.FFResidual.hasPointlessTwist_functionField_of_hasIntegrallyClosedCodimOnePoint` — the residual
  and the arithmetic half at `𝕜 = X.functionField` from that geometric input.
-/
