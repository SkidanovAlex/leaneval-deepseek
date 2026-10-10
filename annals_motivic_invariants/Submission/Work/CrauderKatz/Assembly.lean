/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.CrauderKatz
-/
import Mathlib
import Submission.Work.CrauderKatz.Defs
import Submission.Work.LLink.Classes

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.CrauderKatz.Assembly` — from the decomposed residual to `CrauderKatzExists`

This file assembles the decomposition of `Work.CrauderKatz.Defs`:

```
CrauderKatzLinkExists 𝕜 + FunctionFieldInput 𝕜
      ⟹  Work.LLink.CrauderKatzExists 𝕜
      ⟹  Work.LLink.not_gen_of_quadroCubic_*   (four field classes)
```

where

* `CrauderKatzLinkExists 𝕜` is the *geometric* residual: for every genus-one curve `X` of index
  `5` with `X.NotIsoJacSq` there is a `CrauderKatzLink 𝕜 X`, i.e. (GEO) + (F1) + (TRA) of
  `Defs.lean` — the Crauder–Katz quadro-cubic transformation, its two exceptional divisors with
  their function fields, and the transports to affine space;
* `FunctionFieldInput 𝕜` is the *field-theoretic* residual: (F2) one-variable function-field
  stability and (F3) curve rigidity + Shinder–Zhang.

The whole of the paper's argument *downstream* of those two inputs is proved here, sorry-free:
in particular the paper's `¬ ResEquiv 𝕜 y x` (i.e. `κ(C)(t) ≇_𝕜 κ(C')(t)`, `C` not stably
birational to `Jac²C`) is *derived*, and the base point and the model of `C × ℙ¹` which
`Work.LLink.QuadroCubicLink` carries are eliminated (the base point is the exceptional divisor
`y` itself).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MotivicInvariants Order
open Work.Arithmetic (GenOneCurve)

namespace Work.CrauderKatz

noncomputable section

variable {𝕜 : Type} [Field 𝕜]

/-! ## The geometric residual, in existence form -/

/-- **The geometric residual of the Crauder–Katz link**, in the form in which the four field
classes consume it: for every genus-one curve `X` over `𝕜` of index `5` which is not isomorphic
to `Jac²X`, the quadro-cubic construction produces a `CrauderKatzLink 𝕜 X`.

This is `Work.LLink.CrauderKatzExists` with the field-theoretic content (F2)+(F3) removed, the
base point `z₀` removed, and the redundant model `Z` of `C × ℙ¹` removed; see
`Submission/Work/CrauderKatz/NOTES.md` for the field-by-field comparison. -/
def CrauderKatzLinkExists (𝕜 : Type) [Field 𝕜] : Prop :=
  ∀ X : GenOneCurve 𝕜, X.index = 5 → X.NotIsoJacSq → Nonempty (CrauderKatzLink 𝕜 X)

/-! ## From the decomposed residual to `QuadroCubicLink` -/

variable {X : GenOneCurve 𝕜}

/-- **Every `CrauderKatzLink` gives a `Work.LLink.QuadroCubicLink`**, provided the caller
supplies the arithmetic hypothesis `X.NotIsoJacSq` and the function-field input (F2)+(F3).

The base point `z₀` of the link is taken to be the exceptional divisor `y` itself, with `Z := P`;
`resEquiv_y` is then reflexive (`κ(y) ≅ κ(y)`, and the paper's value `c(φ) = 1` is computed at the
same class by `Work.LLink.QuadroCubicLink.invAtY`), and `not_resEquiv_yx` is derived in
`Work.CrauderKatz.CrauderKatzLink.not_resEquiv_yx` from (F2), (F3) and `X.NotIsoJacSq`. -/
noncomputable def toQuadroCubicLink (L : CrauderKatzLink 𝕜 X) (hni : X.NotIsoJacSq)
    (hF : FunctionFieldInput 𝕜) : Work.LLink.QuadroCubicLink 𝕜 X :=
  letI : Variety 𝕜 L.Q := L.varietyQ
  letI : Variety 𝕜 L.P := L.varietyP
  letI : (L.ψ).IsOver (Spec (.of 𝕜)) := L.isOverψ
  letI : (L.ε).IsOver (Spec (.of 𝕜)) := L.isOverε
  letI : (L.δ).IsOver (Spec (.of 𝕜)) := L.isOverδ
  { notIsoJacSq := hni
    Z := L.P
    z₀ := L.y
    Q := L.Q
    P := L.P
    ψ := L.ψ
    x := L.x
    y := L.y
    exDiv_ψ := L.exDiv_ψ
    exDiv_ψ_symm := L.exDiv_ψ_symm
    ε := L.ε
    δ := L.δ
    resEquiv_y := Work.Motivic.ResEquiv.refl 𝕜 L.y
    not_resEquiv_yx := L.not_resEquiv_yx hF hni
    cInv_ε := L.cInv_ε
    cInv_δ := L.cInv_δ }

/-- **The residual of the Crauder–Katz link, bundled.**  This is the single `Prop` that a caller
has to discharge in order to feed `Work.LLink.CrauderKatzExists 𝕜`: the geometry of
`prop:elliptic` with its two exceptional divisors and the transports (`CrauderKatzLinkExists`),
plus the two field-theoretic inputs (F2) and (F3) (`FunctionFieldInput`).  Every ingredient is
separately attackable; see `Submission/Work/CrauderKatz/NOTES.md`. -/
def Residual (𝕜 : Type) [Field 𝕜] : Prop :=
  CrauderKatzLinkExists 𝕜 ∧ FunctionFieldInput 𝕜

/-- **The assembly theorem.**  The geometric residual `CrauderKatzLinkExists` together with the
function-field input `FunctionFieldInput` implies the geometric residual
`Work.LLink.CrauderKatzExists 𝕜` of the sibling area. -/
theorem crauderKatzExists_of_linkExists (h : CrauderKatzLinkExists 𝕜)
    (hF : FunctionFieldInput 𝕜) : Work.LLink.CrauderKatzExists 𝕜 :=
  fun X hindex hni =>
    (h X hindex hni).map (toQuadroCubicLink · hni hF)

/-- The bundled form of the assembly theorem. -/
theorem crauderKatzExists_of_residual (h : Residual 𝕜) : Work.LLink.CrauderKatzExists 𝕜 :=
  crauderKatzExists_of_linkExists h.1 h.2

/-- The same at the level of the existential consumed by `Work.Motivic.not_gen_of_cInv_ne_zero`,
from the period-`5` form of the arithmetic input. -/
theorem exists_cInv_ne_zero_of_genOneCurveFive (h : Work.Arithmetic.GenOneCurveFive 𝕜)
    (hg : CrauderKatzLinkExists 𝕜) (hF : FunctionFieldInput 𝕜) :
    ∃ (Z : Scheme.{0}) (_ : Z.Over (Spec (.of 𝕜))) (z₀ : Z) (φ : Cr 𝕜 3),
      cInv 𝕜 z₀ (φ : (Work.LLink.Affine3 𝕜).BirationalMap
        (Work.LLink.Affine3 𝕜)) ≠ 0 := by
  obtain ⟨X, -, -, -, hindex, hni⟩ := Work.Arithmetic.GenOneCurve.exists_tors_of_period_five h
  exact Work.LLink.QuadroCubicLink.exists_cInv_ne_zero
    ⟨toQuadroCubicLink (hg X hindex hni).some hni hF⟩

/-- The same, from the paper's `lem:torsors` input `Work.Arithmetic.HasLLinkCurve`. -/
theorem exists_cInv_ne_zero_of_hasLLinkCurve (h : Work.Arithmetic.HasLLinkCurve 𝕜)
    (hg : CrauderKatzLinkExists 𝕜) (hF : FunctionFieldInput 𝕜) :
    ∃ (Z : Scheme.{0}) (_ : Z.Over (Spec (.of 𝕜))) (z₀ : Z) (φ : Cr 𝕜 3),
      cInv 𝕜 z₀ (φ : (Work.LLink.Affine3 𝕜).BirationalMap
        (Work.LLink.Affine3 𝕜)) ≠ 0 :=
  exists_cInv_ne_zero_of_genOneCurveFive
    (Work.Arithmetic.genOneCurveFive_of_hasLLinkCurve h) hg hF

/-! ## The four field classes of Theorem 1.2 (1) -/

/-- **(a) Number fields.** -/
theorem exists_cInv_ne_zero_numberField [NumberField 𝕜] (h : Work.Arithmetic.HasLLinkCurve 𝕜)
    (hg : CrauderKatzLinkExists 𝕜) (hF : FunctionFieldInput 𝕜) :
    ∃ (Z : Scheme.{0}) (_ : Z.Over (Spec (.of 𝕜))) (z₀ : Z) (φ : Cr 𝕜 3),
      cInv 𝕜 z₀ (φ : (Work.LLink.Affine3 𝕜).BirationalMap
        (Work.LLink.Affine3 𝕜)) ≠ 0 := by
  obtain ⟨X, -, -, -, hindex, hni⟩ := Work.Arithmetic.llink_tors_numberField h
  exact Work.LLink.QuadroCubicLink.exists_cInv_ne_zero
    ⟨toQuadroCubicLink (hg X hindex hni).some hni hF⟩

/-- **(a) Number fields**, wired straight to Theorem 1.2 (1) (a). -/
theorem not_gen_numberField [NumberField 𝕜] (h : Work.Arithmetic.HasLLinkCurve 𝕜)
    (hg : CrauderKatzLinkExists 𝕜) (hF : FunctionFieldInput 𝕜) :
    ¬ GenByPseudoRegularizable 𝕜 3 :=
  Work.Motivic.not_gen_of_cInv_ne_zero 𝕜 3 (exists_cInv_ne_zero_numberField h hg hF)

/-- **(a) Number fields**, from the bundled residual. -/
theorem not_gen_of_residual_numberField [NumberField 𝕜] (h : Work.Arithmetic.HasLLinkCurve 𝕜)
    (hg : Residual 𝕜) : ¬ GenByPseudoRegularizable 𝕜 3 :=
  not_gen_numberField h hg.1 hg.2

/-- **(b) Function fields over number fields.** -/
theorem exists_cInv_ne_zero_functionField_numberField (𝔽 : Type) [Field 𝔽] [NumberField 𝔽]
    (X : Scheme.{0}) [Variety 𝔽 X] (hX : 0 < topologicalKrullDim X)
    (h : Work.Arithmetic.HasLLinkCurve X.functionField)
    (hg : CrauderKatzLinkExists X.functionField) (hF : FunctionFieldInput X.functionField) :
    ∃ (Z : Scheme.{0}) (_ : Z.Over (Spec (.of X.functionField))) (z₀ : Z)
      (φ : Cr X.functionField 3),
      cInv X.functionField z₀
        (φ : (Work.LLink.Affine3 X.functionField).BirationalMap
          (Work.LLink.Affine3 X.functionField)) ≠ 0 := by
  obtain ⟨Y, -, -, -, hindex, hni⟩ := Work.Arithmetic.llink_tors_functionField_numberField 𝔽 X hX h
  exact Work.LLink.QuadroCubicLink.exists_cInv_ne_zero
    ⟨toQuadroCubicLink (hg Y hindex hni).some hni hF⟩

/-- **(b) Function fields over number fields**, wired to Theorem 1.2 (1) (b). -/
theorem not_gen_functionField_numberField (𝔽 : Type) [Field 𝔽] [NumberField 𝔽]
    (X : Scheme.{0}) [Variety 𝔽 X] (hX : 0 < topologicalKrullDim X)
    (h : Work.Arithmetic.HasLLinkCurve X.functionField)
    (hg : CrauderKatzLinkExists X.functionField) (hF : FunctionFieldInput X.functionField) :
    ¬ GenByPseudoRegularizable X.functionField 3 :=
  Work.Motivic.not_gen_of_cInv_ne_zero X.functionField 3
    (exists_cInv_ne_zero_functionField_numberField 𝔽 X hX h hg hF)

/-- **(c) Function fields over finite fields.** -/
theorem exists_cInv_ne_zero_functionField_finiteField (𝔽 : Type) [Field 𝔽] [Finite 𝔽]
    (X : Scheme.{0}) [Variety 𝔽 X] (hX : 0 < topologicalKrullDim X)
    (h : Work.Arithmetic.HasLLinkCurve X.functionField)
    (hg : CrauderKatzLinkExists X.functionField) (hF : FunctionFieldInput X.functionField) :
    ∃ (Z : Scheme.{0}) (_ : Z.Over (Spec (.of X.functionField))) (z₀ : Z)
      (φ : Cr X.functionField 3),
      cInv X.functionField z₀
        (φ : (Work.LLink.Affine3 X.functionField).BirationalMap
          (Work.LLink.Affine3 X.functionField)) ≠ 0 := by
  obtain ⟨Y, -, -, -, hindex, hni⟩ := Work.Arithmetic.llink_tors_functionField_finite 𝔽 X hX h
  exact Work.LLink.QuadroCubicLink.exists_cInv_ne_zero
    ⟨toQuadroCubicLink (hg Y hindex hni).some hni hF⟩

/-- **(c) Function fields over finite fields**, wired to Theorem 1.2 (1) (c). -/
theorem not_gen_functionField_finiteField (𝔽 : Type) [Field 𝔽] [Finite 𝔽]
    (X : Scheme.{0}) [Variety 𝔽 X] (hX : 0 < topologicalKrullDim X)
    (h : Work.Arithmetic.HasLLinkCurve X.functionField)
    (hg : CrauderKatzLinkExists X.functionField) (hF : FunctionFieldInput X.functionField) :
    ¬ GenByPseudoRegularizable X.functionField 3 :=
  Work.Motivic.not_gen_of_cInv_ne_zero X.functionField 3
    (exists_cInv_ne_zero_functionField_finiteField 𝔽 X hX h hg hF)

/-- **(d) Function fields over algebraically closed fields.** -/
theorem exists_cInv_ne_zero_functionField_algClosed (𝔽 : Type) [Field 𝔽] [IsAlgClosed 𝔽]
    (X : Scheme.{0}) [Variety 𝔽 X] (hX : 0 < topologicalKrullDim X)
    (h : Work.Arithmetic.HasLLinkCurve X.functionField)
    (hg : CrauderKatzLinkExists X.functionField) (hF : FunctionFieldInput X.functionField) :
    ∃ (Z : Scheme.{0}) (_ : Z.Over (Spec (.of X.functionField))) (z₀ : Z)
      (φ : Cr X.functionField 3),
      cInv X.functionField z₀
        (φ : (Work.LLink.Affine3 X.functionField).BirationalMap
          (Work.LLink.Affine3 X.functionField)) ≠ 0 := by
  obtain ⟨Y, -, -, -, hindex, hni⟩ := Work.Arithmetic.llink_tors_functionField_algClosed 𝔽 X hX h
  exact Work.LLink.QuadroCubicLink.exists_cInv_ne_zero
    ⟨toQuadroCubicLink (hg Y hindex hni).some hni hF⟩

/-- **(d) Function fields over algebraically closed fields**, wired to Theorem 1.2 (1) (d). -/
theorem not_gen_functionField_algClosed (𝔽 : Type) [Field 𝔽] [IsAlgClosed 𝔽]
    (X : Scheme.{0}) [Variety 𝔽 X] (hX : 0 < topologicalKrullDim X)
    (h : Work.Arithmetic.HasLLinkCurve X.functionField)
    (hg : CrauderKatzLinkExists X.functionField) (hF : FunctionFieldInput X.functionField) :
    ¬ GenByPseudoRegularizable X.functionField 3 :=
  Work.Motivic.not_gen_of_cInv_ne_zero X.functionField 3
    (exists_cInv_ne_zero_functionField_algClosed 𝔽 X hX h hg hF)

end

end Work.CrauderKatz

/-! ## Closing the lead's `not_gen_of_quadroCubic_*` chains as far as the residual allows -/

namespace Work.CrauderKatz

variable {𝕜 : Type} [Field 𝕜]

/-- **(a) Number fields**: the sibling area's `Work.LLink.not_gen_of_quadroCubic_numberField` with
the geometric residual `Work.LLink.CrauderKatzExists 𝕜` supplied from this area's decomposition
`Residual 𝕜`.  This is the chain that Theorem 1.2 (1) (a) needs, closed as far as the arithmetic
input `HasLLinkCurve 𝕜` and the Crauder–Katz residual allow. -/
theorem not_gen_of_quadroCubic_of_residual_numberField [NumberField 𝕜]
    (h : Work.Arithmetic.HasLLinkCurve 𝕜) (hg : Residual 𝕜) :
    ¬ GenByPseudoRegularizable 𝕜 3 :=
  Work.LLink.not_gen_of_quadroCubic_numberField h (crauderKatzExists_of_residual hg)

/-- **(b) Function fields over number fields.** -/
theorem not_gen_of_quadroCubic_of_residual_functionField_numberField (𝔽 : Type) [Field 𝔽]
    [NumberField 𝔽] (X : Scheme.{0}) [Variety 𝔽 X] (hX : 0 < topologicalKrullDim X)
    (h : Work.Arithmetic.HasLLinkCurve X.functionField) (hg : Residual X.functionField) :
    ¬ GenByPseudoRegularizable X.functionField 3 :=
  Work.LLink.not_gen_of_quadroCubic_functionField_numberField 𝔽 X hX h
    (crauderKatzExists_of_residual hg)

/-- **(c) Function fields over finite fields.** -/
theorem not_gen_of_quadroCubic_of_residual_functionField_finiteField (𝔽 : Type) [Field 𝔽]
    [Finite 𝔽] (X : Scheme.{0}) [Variety 𝔽 X] (hX : 0 < topologicalKrullDim X)
    (h : Work.Arithmetic.HasLLinkCurve X.functionField) (hg : Residual X.functionField) :
    ¬ GenByPseudoRegularizable X.functionField 3 :=
  Work.LLink.not_gen_of_quadroCubic_functionField_finiteField 𝔽 X hX h
    (crauderKatzExists_of_residual hg)

/-- **(d) Function fields over algebraically closed fields.** -/
theorem not_gen_of_quadroCubic_of_residual_functionField_algClosed (𝔽 : Type) [Field 𝔽]
    [IsAlgClosed 𝔽] (X : Scheme.{0}) [Variety 𝔽 X] (hX : 0 < topologicalKrullDim X)
    (h : Work.Arithmetic.HasLLinkCurve X.functionField) (hg : Residual X.functionField) :
    ¬ GenByPseudoRegularizable X.functionField 3 :=
  Work.LLink.not_gen_of_quadroCubic_functionField_algClosed 𝔽 X hX h
    (crauderKatzExists_of_residual hg)

end Work.CrauderKatz
