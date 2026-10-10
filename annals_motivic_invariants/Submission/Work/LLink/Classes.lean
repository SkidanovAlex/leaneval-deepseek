import Mathlib
import Submission.Work.LLink.QuadroCubic
import Submission.Work.Motivic.not_gen_of_cInv_ne_zero

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.LLink.Classes` — non-vanishing of the invariant, per field class

The four field classes of Theorem 1.2 (1) of Lin–Shinder,
`Motivic invariants of birational maps` (Annals 199 (1), 2024):

* a number field `𝕜`;
* a function field `𝕜 = X.functionField` of a positive-dimensional variety `X` over a number
  field `𝔽`;
* the same over a finite field `𝔽`;
* the same over an algebraically closed field `𝔽`.

Each theorem takes **two** hypotheses:

1. the *named arithmetic input* `Work.Arithmetic.HasLLinkCurve 𝕜` — the paper's Lemma
   `lem:torsors` in geometric form (a genus-one curve `C/𝕜` with a `𝕜`-rational divisor of
   degree `5`, with `C(𝕜) = ∅` and `j(Jac⁰C) ≠ 1728`).  It is consumed through the Arithmetic
   area's `Work.Arithmetic.llink_tors_*`, which additionally produce the curve `X`, its index
   `5` and `X.NotIsoJacSq` (Shinder–Zhang Lemma 2.7);
2. the *single geometric residual* `Work.LLink.CrauderKatzExists 𝕜` of
   `Work.LLink/QuadroCubic.lean`, i.e. Proposition `prop:elliptic` for every curve of index `5`
   with `C ≇ Jac²C`.

From those, the theorem produces a Cremona transformation of `𝔸³` over `𝕜` with a non-vanishing
coefficient, in exactly the shape consumed by `Work.Motivic.not_gen_of_cInv_ne_zero`; the
`..._not_gen_*` statements do that final one-line application.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MotivicInvariants Order
open Work.Arithmetic (GenOneCurveFive HasLLinkCurve)

namespace Work.LLink

variable {𝕜 : Type} [Field 𝕜]

/-! ## From the arithmetic input to the non-vanishing element -/

/-- **The L-link non-vanishing, from the period-`5` formulation of the arithmetic input.**
`GenOneCurveFive 𝕜` is `∃ X : GenOneCurve 𝕜, X.period = 5`. -/
theorem exists_cInv_ne_zero_of_genOneCurveFive (h : GenOneCurveFive 𝕜)
    (hg : CrauderKatzExists 𝕜) :
    ∃ (Z : Scheme.{0}) (_ : Z.Over (Spec (.of 𝕜))) (z₀ : Z) (φ : Cr 𝕜 3),
      cInv 𝕜 z₀ (φ : (Affine3 𝕜).BirationalMap (Affine3 𝕜)) ≠ 0 := by
  obtain ⟨X, -, -, -, hindex, hni⟩ := Work.Arithmetic.GenOneCurve.exists_tors_of_period_five h
  exact QuadroCubicLink.exists_cInv_ne_zero (hg X hindex hni)

/-- **The L-link non-vanishing, from the paper's Lemma `lem:torsors`.** -/
theorem exists_cInv_ne_zero_of_hasLLinkCurve (h : HasLLinkCurve 𝕜)
    (hg : CrauderKatzExists 𝕜) :
    ∃ (Z : Scheme.{0}) (_ : Z.Over (Spec (.of 𝕜))) (z₀ : Z) (φ : Cr 𝕜 3),
      cInv 𝕜 z₀ (φ : (Affine3 𝕜).BirationalMap (Affine3 𝕜)) ≠ 0 :=
  exists_cInv_ne_zero_of_genOneCurveFive
    (Work.Arithmetic.genOneCurveFive_of_hasLLinkCurve h) hg

/-! ## The four field classes -/

/-- **(a) Number fields.**  From Clark–Lacy Theorem 1.10 (`Work.Arithmetic.llink_tors_numberField`)
and the geometric residual. -/
theorem exists_cInv_ne_zero_numberField [NumberField 𝕜] (h : HasLLinkCurve 𝕜)
    (hg : CrauderKatzExists 𝕜) :
    ∃ (Z : Scheme.{0}) (_ : Z.Over (Spec (.of 𝕜))) (z₀ : Z) (φ : Cr 𝕜 3),
      cInv 𝕜 z₀ (φ : (Affine3 𝕜).BirationalMap (Affine3 𝕜)) ≠ 0 := by
  obtain ⟨X, -, -, -, hindex, hni⟩ := Work.Arithmetic.llink_tors_numberField h
  exact QuadroCubicLink.exists_cInv_ne_zero (hg X hindex hni)

/-- **(b) Function fields over a number field.** -/
theorem exists_cInv_ne_zero_functionField_numberField (𝔽 : Type) [Field 𝔽] [NumberField 𝔽]
    (X : Scheme.{0}) [Variety 𝔽 X] (hX : 0 < topologicalKrullDim X)
    (h : HasLLinkCurve X.functionField) (hg : CrauderKatzExists X.functionField) :
    ∃ (Z : Scheme.{0}) (_ : Z.Over (Spec (.of X.functionField))) (z₀ : Z)
      (φ : Cr X.functionField 3),
      cInv X.functionField z₀
        (φ : (Affine3 X.functionField).BirationalMap (Affine3 X.functionField)) ≠ 0 := by
  obtain ⟨Y, -, -, -, hindex, hni⟩ :=
    Work.Arithmetic.llink_tors_functionField_numberField 𝔽 X hX h
  exact QuadroCubicLink.exists_cInv_ne_zero (hg Y hindex hni)

/-- **(c) Function fields over a finite field.** -/
theorem exists_cInv_ne_zero_functionField_finiteField (𝔽 : Type) [Field 𝔽] [Finite 𝔽]
    (X : Scheme.{0}) [Variety 𝔽 X] (hX : 0 < topologicalKrullDim X)
    (h : HasLLinkCurve X.functionField) (hg : CrauderKatzExists X.functionField) :
    ∃ (Z : Scheme.{0}) (_ : Z.Over (Spec (.of X.functionField))) (z₀ : Z)
      (φ : Cr X.functionField 3),
      cInv X.functionField z₀
        (φ : (Affine3 X.functionField).BirationalMap (Affine3 X.functionField)) ≠ 0 := by
  obtain ⟨Y, -, -, -, hindex, hni⟩ :=
    Work.Arithmetic.llink_tors_functionField_finite 𝔽 X hX h
  exact QuadroCubicLink.exists_cInv_ne_zero (hg Y hindex hni)

/-- **(d) Function fields over an algebraically closed field.** -/
theorem exists_cInv_ne_zero_functionField_algClosed (𝔽 : Type) [Field 𝔽] [IsAlgClosed 𝔽]
    (X : Scheme.{0}) [Variety 𝔽 X] (hX : 0 < topologicalKrullDim X)
    (h : HasLLinkCurve X.functionField) (hg : CrauderKatzExists X.functionField) :
    ∃ (Z : Scheme.{0}) (_ : Z.Over (Spec (.of X.functionField))) (z₀ : Z)
      (φ : Cr X.functionField 3),
      cInv X.functionField z₀
        (φ : (Affine3 X.functionField).BirationalMap (Affine3 X.functionField)) ≠ 0 := by
  obtain ⟨Y, -, -, -, hindex, hni⟩ :=
    Work.Arithmetic.llink_tors_functionField_algClosed 𝔽 X hX h
  exact QuadroCubicLink.exists_cInv_ne_zero (hg Y hindex hni)

/-! ## Direct wiring to Theorem 1.2 (1) of the challenge -/

/-- Theorem 1.2 (1) (a), from the arithmetic input and the geometric residual. -/
theorem not_gen_of_quadroCubic_numberField [NumberField 𝕜] (h : HasLLinkCurve 𝕜)
    (hg : CrauderKatzExists 𝕜) : ¬ GenByPseudoRegularizable 𝕜 3 :=
  Work.Motivic.not_gen_of_cInv_ne_zero 𝕜 3 (exists_cInv_ne_zero_numberField h hg)

/-- Theorem 1.2 (1) (b). -/
theorem not_gen_of_quadroCubic_functionField_numberField (𝔽 : Type) [Field 𝔽] [NumberField 𝔽]
    (X : Scheme.{0}) [Variety 𝔽 X] (hX : 0 < topologicalKrullDim X)
    (h : HasLLinkCurve X.functionField) (hg : CrauderKatzExists X.functionField) :
    ¬ GenByPseudoRegularizable X.functionField 3 :=
  Work.Motivic.not_gen_of_cInv_ne_zero X.functionField 3
    (exists_cInv_ne_zero_functionField_numberField 𝔽 X hX h hg)

/-- Theorem 1.2 (1) (c). -/
theorem not_gen_of_quadroCubic_functionField_finiteField (𝔽 : Type) [Field 𝔽] [Finite 𝔽]
    (X : Scheme.{0}) [Variety 𝔽 X] (hX : 0 < topologicalKrullDim X)
    (h : HasLLinkCurve X.functionField) (hg : CrauderKatzExists X.functionField) :
    ¬ GenByPseudoRegularizable X.functionField 3 :=
  Work.Motivic.not_gen_of_cInv_ne_zero X.functionField 3
    (exists_cInv_ne_zero_functionField_finiteField 𝔽 X hX h hg)

/-- Theorem 1.2 (1) (d). -/
theorem not_gen_of_quadroCubic_functionField_algClosed (𝔽 : Type) [Field 𝔽] [IsAlgClosed 𝔽]
    (X : Scheme.{0}) [Variety 𝔽 X] (hX : 0 < topologicalKrullDim X)
    (h : HasLLinkCurve X.functionField) (hg : CrauderKatzExists X.functionField) :
    ¬ GenByPseudoRegularizable X.functionField 3 :=
  Work.Motivic.not_gen_of_cInv_ne_zero X.functionField 3
    (exists_cInv_ne_zero_functionField_algClosed 𝔽 X hX h hg)

end Work.LLink
