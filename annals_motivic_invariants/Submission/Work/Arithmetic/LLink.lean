/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.Arithmetic
-/
import Submission.Work.Arithmetic.PeriodFive

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The L-link input, in the paper's own terms

Lin–Shinder's Lemma `lem:torsors` produces, for each of the four field classes of Theorem
`thm:ell-curves`, a genus-one curve without rational points carrying a divisor of degree `5`
and with `j(Jac⁰C) ≠ 1728`.  That is the input of the L-link construction of Proposition
`prop:elliptic`.  This file names that input as `HasLLinkCurve`, states it in terms of the
scheme `C` (no abstract class data visible), and proves it *equivalent* to the period-`5`
formulation `GenOneCurveFive` used elsewhere in this area:

> `Work.Arithmetic.hasLLinkCurve_iff : HasLLinkCurve 𝕜 ↔ GenOneCurveFive 𝕜`

So the residual of the four class theorems can be supplied either as "period `5`"
(`GenOneCurveFive`) or as "the paper's Lemma `lem:torsors`" (`HasLLinkCurve`).

Note: `HasLLinkCurve` is not weaker than `GenOneCurveFive` in the direction that matters —
the bridge field `divisorOfDegree_iff` of `GenOneCurve` identifies `5 · [C] = 0` with the
existence of a degree-`5` rational divisor, and `cls_eq_one_iff` identifies `[C] ≠ 0` with
`C(𝕜) = ∅`; hence a degree-`5` divisor plus pointlessness forces period and index `5`.
-/

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Order

namespace Work.Arithmetic

noncomputable section

variable {𝕜 : Type} [Field 𝕜]

/-- The paper's Lemma `lem:torsors` in the geometric form that the L-link construction
consumes: there is a genus-one curve `C/𝕜` (smooth, proper, geometrically integral,
one-dimensional) carrying a `𝕜`-rational divisor of degree `5`, with `C(𝕜) = ∅` and
`j(Jac⁰C) ≠ 1728`. -/
def HasLLinkCurve (𝕜 : Type) [Field 𝕜] : Prop :=
  ∃ X : GenOneCurve 𝕜, HasRatDivisorOfDegree 𝕜 X.C 5 ∧ ¬ HasRatPoint 𝕜 X.C ∧ X.j ≠ 1728

/-- A degree-`5` divisor plus pointlessness forces period `5`: `5 · [C] = 0` gives
`period ∣ 5`, and `[C] ≠ 0` gives `period ≠ 1`. -/
theorem genOneCurveFive_of_hasLLinkCurve (h : HasLLinkCurve 𝕜) : GenOneCurveFive 𝕜 := by
  obtain ⟨X, hdiv, hpt, _hj⟩ := h
  refine ⟨X, ?_⟩
  have hd5 : X.torsor.DivisorOfDegree 5 := (X.divisorOfDegree_iff 5).mp hdiv
  have hdvd : X.period ∣ 5 := (Torsor.divisorOfDegree_iff_dvd X.torsor 5).mp hd5
  have hne1 : X.torsor.cls ≠ 1 := fun hc => hpt (X.cls_eq_one_iff.mp hc)
  have hne : X.period ≠ 1 := by
    intro h1
    have h2 : orderOf X.torsor.cls = 1 := by
      simpa [GenOneCurve.period, Torsor.period] using h1
    exact hne1 (orderOf_eq_one_iff.mp h2)
  rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_five X.period hdvd with h1 | h5
  · exact absurd h1 hne
  · exact h5

/-- Conversely, a curve of period `5` satisfies the paper's Lemma `lem:torsors`. -/
theorem hasLLinkCurve_of_genOneCurveFive (h : GenOneCurveFive 𝕜) : HasLLinkCurve 𝕜 := by
  obtain ⟨X, hper⟩ := h
  exact ⟨X, X.hasRatDivisorOfDegree_five hper, X.not_hasRatPoint hper, X.j_ne_1728⟩

/-- The paper's `lem:torsors` and the period-`5` formulation are equivalent. -/
theorem hasLLinkCurve_iff : HasLLinkCurve 𝕜 ↔ GenOneCurveFive 𝕜 :=
  ⟨genOneCurveFive_of_hasLLinkCurve, hasLLinkCurve_of_genOneCurveFive⟩

/-! ## (TORS) for the four field classes, with the paper's Lemma as the residual -/

/-- **(TORS)**, class (a): number fields, with the residual stated as the paper's
`lem:torsors` (Clark–Lacy, Theorem 1.10). -/
theorem llink_tors_numberField [NumberField 𝕜] (h : HasLLinkCurve 𝕜) :
    ∃ X : GenOneCurve 𝕜, HasRatDivisorOfDegree 𝕜 X.C 5 ∧ ¬ HasRatPoint 𝕜 X.C ∧
      X.j ≠ 1728 ∧ X.index = 5 ∧ X.NotIsoJacSq :=
  GenOneCurve.exists_tors_of_period_five (genOneCurveFive_of_hasLLinkCurve h)

/-- **(TORS)**, class (b): function fields over number fields, with the residual stated as the
paper's `lem:torsors` (Clark–Lacy, Theorem 1.10). -/
theorem llink_tors_functionField_numberField (𝔽 : Type) [Field 𝔽] [NumberField 𝔽]
    (_X : Scheme) [MotivicInvariants.Variety 𝔽 _X] (_hX : 0 < topologicalKrullDim _X)
    (h : HasLLinkCurve _X.functionField) :
    ∃ Y : GenOneCurve _X.functionField, HasRatDivisorOfDegree _X.functionField Y.C 5 ∧
      ¬ HasRatPoint _X.functionField Y.C ∧ Y.j ≠ 1728 ∧ Y.index = 5 ∧ Y.NotIsoJacSq :=
  GenOneCurve.exists_tors_of_period_five (genOneCurveFive_of_hasLLinkCurve h)

/-- **(TORS)**, class (c): function fields over finite fields, with the residual stated as the
paper's `lem:torsors` (Clark–Lacy, Theorem 1.10, including characteristic `5`). -/
theorem llink_tors_functionField_finite (𝔽 : Type) [Field 𝔽] [Finite 𝔽]
    (_X : Scheme) [MotivicInvariants.Variety 𝔽 _X] (_hX : 0 < topologicalKrullDim _X)
    (h : HasLLinkCurve _X.functionField) :
    ∃ Y : GenOneCurve _X.functionField, HasRatDivisorOfDegree _X.functionField Y.C 5 ∧
      ¬ HasRatPoint _X.functionField Y.C ∧ Y.j ≠ 1728 ∧ Y.index = 5 ∧ Y.NotIsoJacSq :=
  GenOneCurve.exists_tors_of_period_five (genOneCurveFive_of_hasLLinkCurve h)

/-- **(TORS)**, class (d): function fields over algebraically closed fields, with the residual
stated as the paper's `lem:torsors` (Lang–Tate, Theorem 7). -/
theorem llink_tors_functionField_algClosed (𝔽 : Type) [Field 𝔽] [IsAlgClosed 𝔽]
    (_X : Scheme) [MotivicInvariants.Variety 𝔽 _X] (_hX : 0 < topologicalKrullDim _X)
    (h : HasLLinkCurve _X.functionField) :
    ∃ Y : GenOneCurve _X.functionField, HasRatDivisorOfDegree _X.functionField Y.C 5 ∧
      ¬ HasRatPoint _X.functionField Y.C ∧ Y.j ≠ 1728 ∧ Y.index = 5 ∧ Y.NotIsoJacSq :=
  GenOneCurve.exists_tors_of_period_five (genOneCurveFive_of_hasLLinkCurve h)

end

end Work.Arithmetic
