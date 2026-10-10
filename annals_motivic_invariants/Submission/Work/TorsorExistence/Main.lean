/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.TorsorExistence
-/
import Submission.Work.Arithmetic.LLink
import Submission.Work.TorsorExistence.Defs
import Submission.Work.TorsorExistence.existsCyclicExtension_of_zeta5
import Submission.Work.TorsorExistence.existsCyclicExtension_of_charP_five
import Submission.Work.TorsorExistence.existsCyclicExtension_numberField
import Submission.Work.TorsorExistence.nonempty_fiveTorsionPoint
import Submission.Work.TorsorExistence.nonempty_orderAutCurve_of_two_three_invertible
import Submission.Work.TorsorExistence.nonempty_orderAutCurve_char_two
import Submission.Work.TorsorExistence.nonempty_orderAutCurve_char_three

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The geometric residual, and (TORS) for the four field classes

This file reduces the paper's Lemma `lem:torsors` — `Work.Arithmetic.HasLLinkCurve 𝕜` — to the
single geometric statement `HasPointlessIndexFiveCurve 𝕜` (a smooth, proper, geometrically
integral curve of dimension one over `𝕜` with no `𝕜`-point, carrying a rational divisor of
degree `5`, and with all rational divisor degrees divisible by `5`), and states the result for
the four field classes of Lin–Shinder, Theorem 1.2 (1).

## What is proved here

* `nonempty_orderAutCurve` — every field has an elliptic curve with `j ≠ 1728` and Silverman
  A.1.2's automorphism bound (assembled from the three characteristic cases proved by the fleet).
* `hasLLinkCurve_of_indexFive` — the main reduction: from the geometric residual and such an
  elliptic curve, build a `Work.Arithmetic.GenOneCurve` of period `5` and hence
  `HasLLinkCurve 𝕜`.
* `hasLLinkCurve_of_hasPointlessIndexFiveCurve` — the same, with the elliptic curve supplied by
  `nonempty_orderAutCurve`.
* `hasLLinkCurve_numberField`, `hasLLinkCurve_functionField_numberField`,
  `hasLLinkCurve_functionField_finite`, `hasLLinkCurve_functionField_algClosed` — the four field
  classes, each reducing `HasLLinkCurve 𝕜` to `HasPointlessIndexFiveCurve 𝕜`.

The `Torsor` of the `GenOneCurve` is built with `W := Multiplicative (ZMod 5)` and
`cls := ofAdd 1`; the bridge field `divisorOfDegree_iff` is then exactly
`PointlessIndexFiveCurve.hasRatDivisorOfDegree_iff` (a rational divisor of degree `n` exists iff
`5 ∣ n`), and `cls_eq_one_iff` is `PointlessIndexFiveCurve.no_point`.  All the content of the
residual is therefore used, and nothing is smuggled: see `NOTES.md` for why the residual cannot
be discharged with the current Mathlib (there is no smooth proper curve over a field in Mathlib).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry

namespace Work.TorsorExistence

noncomputable section

/-! ## The elliptic curve needed by `Work.Arithmetic.Torsor` -/

/-- **Every field has an elliptic curve with `j ≠ 1728` and with every automorphism of order
dividing `2` or `6`** (Silverman, *AEC*, Proposition A.1.2): split on the characteristic and use
the three cases proved by the fleet. -/
theorem nonempty_orderAutCurve (𝕜 : Type) [Field 𝕜] : Nonempty (OrderAutCurve 𝕜) := by
  by_cases h2 : (2 : 𝕜) = 0
  · haveI : CharP 𝕜 2 := (CharP.charP_iff_prime_eq_zero (by norm_num)).mpr h2
    exact nonempty_orderAutCurve_char_two
  · by_cases h3 : (3 : 𝕜) = 0
    · haveI : CharP 𝕜 3 := (CharP.charP_iff_prime_eq_zero (by norm_num)).mpr h3
      exact nonempty_orderAutCurve_char_three
    · exact nonempty_orderAutCurve_of_two_three_invertible h2 h3

/-! ## The main reduction -/

/-- The `Work.Arithmetic.Torsor` used in the reduction: the Weil–Châtelet group is
`W := Multiplicative (ZMod 5)` and the class is `ofAdd 1` (of order `5`), with the trivial
`Aut(E)`-action. -/
noncomputable def torsorOfIndexFive {𝕜 : Type} [Field 𝕜] (D : OrderAutCurve 𝕜) :
    Work.Arithmetic.Torsor 𝕜 where
  E := D.E
  isElliptic := D.isElliptic
  j_ne := D.j_ne
  W := Multiplicative (ZMod 5)
  commGroup := inferInstance
  act :=
    { toFun := fun _ => 1
      map_one' := rfl
      map_mul' := fun _ _ => (one_mul 1).symm }
  cls := Multiplicative.ofAdd (1 : ZMod 5)
  order_aut := D.order_aut

/-- `ofAdd 1 ≠ 1` in `Multiplicative (ZMod 5)`. -/
theorem ofAdd_one_ne_one_zmod_five : Multiplicative.ofAdd (1 : ZMod 5) ≠ 1 := by
  rw [Ne, ofAdd_eq_one]
  decide

/-- `(ofAdd 1) ^ n = 1` in `Multiplicative (ZMod 5)` iff `5 ∣ n`. -/
theorem ofAdd_one_pow_eq_one_iff {n : ℕ} :
    (Multiplicative.ofAdd (1 : ZMod 5)) ^ n = 1 ↔ 5 ∣ n := by
  rw [← ofAdd_nsmul, ofAdd_eq_one, Nat.smul_one_eq_cast, ZMod.natCast_eq_zero_iff]

/-- The divisor-degree bookkeeping of `torsorOfIndexFive`: a `𝕜`-rational divisor of degree `n`
exists iff `5 ∣ n`. -/
theorem divisorOfDegree_torsorOfIndexFive {𝕜 : Type} [Field 𝕜] (D : OrderAutCurve 𝕜) (n : ℕ) :
    (torsorOfIndexFive D).DivisorOfDegree n ↔ 5 ∣ n := by
  change (Multiplicative.ofAdd (1 : ZMod 5)) ^ n = 1 ↔ 5 ∣ n
  exact ofAdd_one_pow_eq_one_iff

/-- **The main reduction.**  A smooth proper geometrically integral curve of index `5` over `𝕜`
with no `𝕜`-point, together with an elliptic curve over `𝕜` with `j ≠ 1728` (Silverman A.1.2 as
data), yields the paper's Lemma `lem:torsors` in the form `HasLLinkCurve 𝕜`. -/
theorem hasLLinkCurve_of_indexFive {𝕜 : Type} [Field 𝕜] (D : OrderAutCurve 𝕜)
    (X : PointlessIndexFiveCurve 𝕜) : Work.Arithmetic.HasLLinkCurve 𝕜 := by
  refine ⟨{ C := X.C
            isVariety := X.variety
            isProper := X.isProper
            isSmooth := X.isSmooth
            isGeomIntegral := X.isGeomIntegral
            dim_eq_one := X.dim_eq_one
            torsor := torsorOfIndexFive D
            cls_eq_one_iff := ?_
            divisorOfDegree_iff := ?_ }, X.five, X.no_point, D.j_ne⟩
  · have hcl : (torsorOfIndexFive D).cls ≠ 1 := ofAdd_one_ne_one_zmod_five
    exact ⟨fun h => absurd h hcl, fun h => absurd h X.no_point⟩
  · intro n
    exact (X.hasRatDivisorOfDegree_iff n).trans
      (divisorOfDegree_torsorOfIndexFive D n).symm

/-- **The paper's Lemma `lem:torsors`, reduced to the geometric residual.** -/
theorem hasLLinkCurve_of_hasPointlessIndexFiveCurve {𝕜 : Type} [Field 𝕜]
    (h : HasPointlessIndexFiveCurve 𝕜) : Work.Arithmetic.HasLLinkCurve 𝕜 := by
  obtain ⟨D⟩ := nonempty_orderAutCurve 𝕜
  obtain ⟨X⟩ := h
  exact hasLLinkCurve_of_indexFive D X

/-- Conversely, a `Work.Arithmetic.GenOneCurve` of period `5` (the Arithmetic area's residual
`Work.Arithmetic.GenOneCurveFive`) satisfies the geometric residual, so the two residuals are
inter-derivable and `HasLLinkCurve 𝕜` is *equivalent* to `HasPointlessIndexFiveCurve 𝕜`. -/
theorem hasPointlessIndexFiveCurve_of_period_five {𝕜 : Type} [Field 𝕜]
    (X : Work.Arithmetic.GenOneCurve 𝕜) (h : X.period = 5) : HasPointlessIndexFiveCurve 𝕜 := by
  refine ⟨{ C := X.C
            variety := X.isVariety
            isProper := X.isProper
            isSmooth := X.isSmooth
            isGeomIntegral := X.isGeomIntegral
            dim_eq_one := X.dim_eq_one
            no_point := ?_
            five := ?_
            dvd := ?_ }⟩
  · rw [← X.cls_eq_one_iff]
    exact X.torsor.pointless_of_period_five h
  · exact X.hasRatDivisorOfDegree_five h
  · intro n hn
    have hn' : X.torsor.period ∣ n :=
      (Work.Arithmetic.Torsor.divisorOfDegree_iff_dvd X.torsor n).mp ((X.divisorOfDegree_iff n).mp hn)
    rwa [show X.torsor.period = 5 from h] at hn'

/-! ## The four field classes -/

/-- **(TORS), class (a)**: number fields.  Reduces `HasLLinkCurve 𝕜` to the geometric residual
`HasPointlessIndexFiveCurve 𝕜`. -/
theorem hasLLinkCurve_numberField {𝕜 : Type} [Field 𝕜] [NumberField 𝕜]
    (h : HasPointlessIndexFiveCurve 𝕜) : Work.Arithmetic.HasLLinkCurve 𝕜 :=
  hasLLinkCurve_of_hasPointlessIndexFiveCurve h

/-- **(TORS), class (b)**: function fields of positive-dimensional varieties over a number
field. -/
theorem hasLLinkCurve_functionField_numberField (𝔽 : Type) [Field 𝔽] [NumberField 𝔽]
    (X : Scheme) [MotivicInvariants.Variety 𝔽 X] (_hX : 0 < topologicalKrullDim X)
    (h : HasPointlessIndexFiveCurve X.functionField) :
    Work.Arithmetic.HasLLinkCurve X.functionField :=
  hasLLinkCurve_of_hasPointlessIndexFiveCurve h

/-- **(TORS), class (c)**: function fields of positive-dimensional varieties over a finite
field. -/
theorem hasLLinkCurve_functionField_finite (𝔽 : Type) [Field 𝔽] [Finite 𝔽]
    (X : Scheme) [MotivicInvariants.Variety 𝔽 X] (_hX : 0 < topologicalKrullDim X)
    (h : HasPointlessIndexFiveCurve X.functionField) :
    Work.Arithmetic.HasLLinkCurve X.functionField :=
  hasLLinkCurve_of_hasPointlessIndexFiveCurve h

/-- **(TORS), class (d)**: function fields of positive-dimensional varieties over an
algebraically closed field. -/
theorem hasLLinkCurve_functionField_algClosed (𝔽 : Type) [Field 𝔽] [IsAlgClosed 𝔽]
    (X : Scheme) [MotivicInvariants.Variety 𝔽 X] (_hX : 0 < topologicalKrullDim X)
    (h : HasPointlessIndexFiveCurve X.functionField) :
    Work.Arithmetic.HasLLinkCurve X.functionField :=
  hasLLinkCurve_of_hasPointlessIndexFiveCurve h

end

end Work.TorsorExistence
