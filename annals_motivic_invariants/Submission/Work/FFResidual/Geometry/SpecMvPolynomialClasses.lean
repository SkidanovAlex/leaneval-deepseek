/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: Work.FFResidual
-/
import Submission.Work.FFResidual.Geometry.Reduction
import Submission.Work.FFResidual.Geometry.hasIntegrallyClosedCodimOnePoint_spec_mvPolynomial

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The function-field classes at the function field of affine space, as a variety

`Spec (MvPolynomial (Fin (n+1)) 𝔽)` is a positive-dimensional `𝔽`-variety (its function field is the
rational function field `𝔽(x₁,…,x_{n+1})`), and it *satisfies the geometric sub-residual*
`Work.FFResidual.HasIntegrallyClosedCodimOnePoint` (`hasIntegrallyClosedCodimOnePoint_spec_mvPolynomial`).
Hence the class theorems hold **at `X.functionField` for this `X`**, in the exact shape of the
challenge statement `¬ GenByPseudoRegularizable X.functionField 3`'s input:

  `hasPointlessTwist_functionField_specMvPolynomial_cyclotomic (n)` — class (b) over `ℚ(ζ₅)`;
  `hasPointlessTwist_functionField_specMvPolynomial_five (n)` — class (c)/(d) in characteristic `5`;
  `hasPointlessTwist_functionField_specMvPolynomial_of_zeta5` — the general Kummer form.

This validates the `Variety`-level chain `HasIntegrallyClosedCodimOnePoint X ⟹ HasPointlessTwist X.functionField`
end to end, at a variety of dimension `n + 1 ≥ 1` (for `n ≥ 1` this is a function field of
transcendence degree `≥ 2`, out of reach of the `ConstantsOnly` route).

## Main results

* `Work.FFResidual.specMvPolynomialVariety` — the `Variety` instance.
* `Work.FFResidual.nonempty_functionFieldResidual_specMvPolynomial`,
  `Work.FFResidual.hasPointlessTwist_functionField_specMvPolynomial_of_zeta5{,_cyclotomic,_five}`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory

namespace Work.FFResidual

noncomputable section

/-- **Affine `(n+1)`-space is a variety over `𝔽`**: `Spec (MvPolynomial (Fin (n+1)) 𝔽)` is integral,
separated, locally of finite type and quasicompact over `Spec 𝔽`. -/
instance specMvPolynomialVariety (𝔽 : Type) [Field 𝔽] (n : ℕ) :
    MotivicInvariants.Variety 𝔽 (Spec (CommRingCat.of (MvPolynomial (Fin (n+1)) 𝔽))) where

/-- **The residual at the function field of affine `(n+1)`-space** (Kummer case), in the exact shape
of the deliverable.  The `𝔽`-algebra structure used is the explicit `overFunctionFieldAlgebra`. -/
theorem nonempty_functionFieldResidual_specMvPolynomial_of_zeta5
    (𝔽 : Type) [Field 𝔽] [DecidableEq 𝔽] (n : ℕ) (ζ : 𝔽) (hζ : IsPrimitiveRoot ζ 5) (c : 𝔽)
    (hΔ : (Work.TorsorExistence.Tate.tateCurve c).Δ ≠ 0)
    (hj : (Work.TorsorExistence.Tate.tateCurve c).c₄ ^ 3
      ≠ 1728 * (Work.TorsorExistence.Tate.tateCurve c).Δ) :
    letI := overFunctionFieldAlgebra 𝔽 (Spec (CommRingCat.of (MvPolynomial (Fin (n+1)) 𝔽)))
    Nonempty (Work.ClassBCD.FunctionFieldResidual 𝔽
      (Spec (CommRingCat.of (MvPolynomial (Fin (n+1)) 𝔽))).functionField) :=
  nonempty_functionFieldResidual_of_hasIntegrallyClosedCodimOnePoint 𝔽 _ 
    (Geometry.hasIntegrallyClosedCodimOnePoint_spec_mvPolynomial 𝔽 n) ζ hζ c hΔ hj

/-- **The classes at the function field of affine `(n+1)`-space over an infinite field containing
`ζ₅`** (Kummer case). -/
theorem hasPointlessTwist_functionField_specMvPolynomial_of_zeta5
    (𝔽 : Type) [Field 𝔽] [DecidableEq 𝔽] [Infinite 𝔽] (n : ℕ) (ζ : 𝔽)
    (hζ : IsPrimitiveRoot ζ 5) :
    ∃ dec : DecidableEq (Spec (CommRingCat.of (MvPolynomial (Fin (n+1)) 𝔽))).functionField,
      @Work.PointlessTwist.HasPointlessTwist
        (Spec (CommRingCat.of (MvPolynomial (Fin (n+1)) 𝔽))).functionField _ dec := by
  classical
  obtain ⟨c, hcΔ, hcj⟩ := Work.TorsorExistence.Tate.exists_tate_param (𝕜 := 𝔽)
  have hΔ : (Work.TorsorExistence.Tate.tateCurve c).Δ ≠ 0 := by
    rwa [Work.TorsorExistence.Tate.tateCurve_Δ]
  have hj : (Work.TorsorExistence.Tate.tateCurve c).c₄ ^ 3
      ≠ 1728 * (Work.TorsorExistence.Tate.tateCurve c).Δ := by
    rwa [Work.TorsorExistence.Tate.tateCurve_Δ, Work.TorsorExistence.Tate.tateCurve_c₄]
  exact hasPointlessTwist_functionField_of_hasIntegrallyClosedCodimOnePoint 𝔽 _ 
    (Geometry.hasIntegrallyClosedCodimOnePoint_spec_mvPolynomial 𝔽 n) ζ hζ c hΔ hj

/-- **Class (b) at the function field of affine `(n+1)`-space over `ℚ(ζ₅)`**, unconditionally. -/
theorem hasPointlessTwist_functionField_specMvPolynomial_cyclotomic (n : ℕ) :
    ∃ dec : DecidableEq
        (Spec (CommRingCat.of (MvPolynomial (Fin (n+1)) (CyclotomicField 5 ℚ)))).functionField,
      @Work.PointlessTwist.HasPointlessTwist
        (Spec (CommRingCat.of (MvPolynomial (Fin (n+1)) (CyclotomicField 5 ℚ)))).functionField _ dec := by
  classical
  haveI : IsCyclotomicExtension {5} ℚ (CyclotomicField 5 ℚ) :=
    CyclotomicField.isCyclotomicExtension 5 ℚ
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot (S := {5}) ℚ
    (CyclotomicField 5 ℚ) rfl (by norm_num : (5 : ℕ) ≠ 0)
  exact hasPointlessTwist_functionField_specMvPolynomial_of_zeta5 (CyclotomicField 5 ℚ) n ζ hζ

section CharFive

local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- **Class (c)/(d) at the function field of affine `(n+1)`-space over `𝔽₅`** (characteristic `5`,
Artin–Schreier route), unconditionally. -/
theorem hasPointlessTwist_functionField_specMvPolynomial_five (n : ℕ) :
    ∃ dec : DecidableEq (Spec (CommRingCat.of (MvPolynomial (Fin (n+1)) (ZMod 5)))).functionField,
      @Work.PointlessTwist.HasPointlessTwist
        (Spec (CommRingCat.of (MvPolynomial (Fin (n+1)) (ZMod 5)))).functionField _ dec := by
  have hΔ : (Work.TorsorExistence.Tate.tateCurve (1 : ZMod 5)).Δ ≠ 0 := by
    rw [Work.TorsorExistence.Tate.tateCurve_Δ]; decide
  have hj : (Work.TorsorExistence.Tate.tateCurve (1 : ZMod 5)).c₄ ^ 3
      ≠ 1728 * (Work.TorsorExistence.Tate.tateCurve (1 : ZMod 5)).Δ := by
    rw [Work.TorsorExistence.Tate.tateCurve_Δ, Work.TorsorExistence.Tate.tateCurve_c₄]; decide
  exact hasPointlessTwist_functionField_of_hasIntegrallyClosedCodimOnePoint_charP (ZMod 5) _ 
    (Geometry.hasIntegrallyClosedCodimOnePoint_spec_mvPolynomial (ZMod 5) n) 1 hΔ hj

end CharFive

end

end Work.FFResidual
