/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.PointlessIndexFive
-/
import Submission.Work.PointlessIndexFive.Defs
import Submission.Work.PointlessIndexFive.hasPointlessIndexFiveCurve_of_twistModel
import Submission.Work.PointlessIndexFive.hasPointlessTwist_clarkLacyFive
import Submission.Work.TorsorExistence.Main

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The residual, and the four field classes

This file assembles the residual `Work.TorsorExistence.HasPointlessIndexFiveCurve 𝕜` from the two
halves named in `Defs.lean`,

* `TwistRealization 𝕜` — the *geometric* half: the quintic twist `(E_L)/G` exists as a curve over
  `𝕜` with the Galois-descent bridges (`TwistCurveModel`), and
* `HasPointlessTwist 𝕜` — the *arithmetic* half: some quintic twist has non-vanishing class
  (Clark–Lacy Theorem 1.10 for the classes (a)–(c), Lang–Tate Theorem 7 for class (d)),

and derives, for the four field classes of Lin–Shinder Theorem 1.2 (1) (a)–(d), both
`HasPointlessIndexFiveCurve 𝕜` and the end product of the parent chapter,
`Work.Arithmetic.HasLLinkCurve 𝕜` (the paper's Lemma `lem:torsors`).

## The reduction

  `hasPointlessIndexFiveCurve_of_twistModel`  (`hasPointlessIndexFiveCurve_of_twistModel.lean`)
  `hasPointlessIndexFiveCurve_of_twistRealization`
  `hasPointlessIndexFiveCurve_of_twistResidual`

`HasPointlessIndexFiveCurve 𝕜` is *equivalent in content* to
`TwistRealization 𝕜 ∧ HasPointlessTwist 𝕜`: the backward direction is the theorem above, and the
forward direction is the paper's own construction (a pointless index-`5` curve has period `5`, and
its class in `H¹(𝕜,E)` of order `5` is the twist class by the Kummer exact sequence
`H¹(𝕜,μ₅) → H¹(𝕜,E[5]) → H¹(𝕜,E)` with `P ∈ E[5](𝕜)`; the *realization* half is automatic since
the class comes from a curve).  The decomposition is nevertheless the useful one, because the
geometric half is a single statement uniform in `𝕜` and the arithmetic half is what Clark–Lacy and
Lang–Tate actually supply.

## Field classes

| theorem | field class | arithmetic half supplied by |
|---|---|---|
| `hasPointlessIndexFiveCurve_numberField` | number field | Clark–Lacy Thm 1.10 (`ClarkLacyPointless`) |
| `hasPointlessIndexFiveCurve_functionField_numberField` | function field over a number field | Clark–Lacy Thm 1.10 |
| `hasPointlessIndexFiveCurve_functionField_finite` | function field over a finite field | Clark–Lacy Thm 1.10 |
| `hasPointlessIndexFiveCurve_functionField_algClosed` | function field over an algebraically closed field | Lang–Tate Thm 7 (`LangTatePointless`) |

and the four `hasLLinkCurve_*` for the same classes, which run
`Work.TorsorExistence.hasLLinkCurve_of_hasPointlessIndexFiveCurve`.

The `[DecidableEq 𝕜]` hypothesis is a Mathlib artefact of
`WeierstrassCurve.Affine.Point.instAddCommGroup` (exactly as in the parent chapter); it is
dischargeable by `Classical.decEq` and does *not* occur in `HasPointlessIndexFiveCurve` or in
`Work.Arithmetic.HasLLinkCurve`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry

namespace Work.PointlessIndexFive

noncomputable section

/-! ## 1. The two halves, bundled -/

/-- The residual of the paper's Lemma `lem:torsors` in *witness* form: a quintic twist over `𝕜`
which is pointless and which is realized by a curve model.

This is `TwistRealization 𝕜 ∧ HasPointlessTwist 𝕜` with the two halves sharing their witness `D`;
it is the form in which the per-class construction naturally produces the answer. -/
def HasPointlessIndexFiveCurveOfTwist (𝕜 : Type) [Field 𝕜] [DecidableEq 𝕜] : Prop :=
  ∃ D : QuinticTwist 𝕜, D.Pointless ∧ Nonempty (TwistCurveModel D)

/-- Every curve model realizing a pointless quintic twist is a `PointlessIndexFiveCurve`; in
particular the witness form of the residual suffices. -/
theorem hasPointlessIndexFiveCurve_of_twistResidual {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (h : HasPointlessIndexFiveCurveOfTwist 𝕜) : HasPointlessIndexFiveCurve 𝕜 := by
  obtain ⟨D, hD, M⟩ := h
  exact hasPointlessIndexFiveCurve_of_twistModel D M.some hD

/-- **The main reduction.**  `HasPointlessIndexFiveCurve 𝕜` follows from the geometric half
(`TwistRealization 𝕜`, a single statement uniform in the field class) and the arithmetic half
(`HasPointlessTwist 𝕜`). -/
theorem hasPointlessIndexFiveCurve_of_twistRealization {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (hR : TwistRealization 𝕜) (hA : HasPointlessTwist 𝕜) : HasPointlessIndexFiveCurve 𝕜 := by
  obtain ⟨D, hD⟩ := hA
  exact hasPointlessIndexFiveCurve_of_twistModel D (hR D).some hD

/-- The witness form follows from the two separate halves. -/
theorem hasPointlessIndexFiveCurveOfTwist_of {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (hR : TwistRealization 𝕜) (hA : HasPointlessTwist 𝕜) :
    HasPointlessIndexFiveCurveOfTwist 𝕜 := by
  obtain ⟨D, hD⟩ := hA
  exact ⟨D, hD, hR D⟩

/-- **The parent chapter's residual, split geometrically and arithmetically.**  A
`PointlessIndexFiveCurve 𝕜` is exactly a *curve model* together with the three arithmetic
conditions: no rational point, a rational divisor of degree `5`, and all rational divisor degrees
divisible by `5`.

This is the form in which the two halves can be attacked independently: `CurveModel` is field
theory and projective/scheme geometry, the three conditions are the arithmetic of the relevant
genus-one curve (Clark–Lacy Theorem 1.10 / Lang–Tate Theorem 7). -/
theorem hasPointlessIndexFiveCurve_iff_curveModel (𝕜 : Type) [Field 𝕜] :
    HasPointlessIndexFiveCurve 𝕜 ↔
      ∃ M : CurveModel 𝕜, ¬ Work.Arithmetic.HasRatPoint 𝕜 M.C ∧
        Work.Arithmetic.HasRatDivisorOfDegree 𝕜 M.C 5 ∧
        (∀ n : ℕ, Work.Arithmetic.HasRatDivisorOfDegree 𝕜 M.C n → 5 ∣ n) := by
  constructor
  · rintro ⟨X⟩
    exact ⟨{ C := X.C
             variety := X.variety
             isProper := X.isProper
             isSmooth := X.isSmooth
             isGeomIntegral := X.isGeomIntegral
             dim_eq_one := X.dim_eq_one }, X.no_point, X.five, X.dvd⟩
  · rintro ⟨M, hnp, h5, hdvd⟩
    exact ⟨{ C := M.C
             variety := M.variety
             isProper := M.isProper
             isSmooth := M.isSmooth
             isGeomIntegral := M.isGeomIntegral
             dim_eq_one := M.dim_eq_one
             no_point := hnp
             five := h5
             dvd := hdvd }⟩

/-! ## 2. The end product of the parent chapter

`Work.Arithmetic.HasLLinkCurve 𝕜` is the paper's Lemma `lem:torsors` in the geometric form that the
L-link construction consumes; `Work.TorsorExistence` proves it from
`HasPointlessIndexFiveCurve 𝕜`.  We expose the composition so that a caller of this area gets the
paper's statement directly. -/

/-- `Work.Arithmetic.HasLLinkCurve 𝕜` from the two halves of the residual. -/
theorem hasLLinkCurve_of_twistRealization {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (hR : TwistRealization 𝕜) (hA : HasPointlessTwist 𝕜) : Work.Arithmetic.HasLLinkCurve 𝕜 :=
  Work.TorsorExistence.hasLLinkCurve_of_hasPointlessIndexFiveCurve
    (hasPointlessIndexFiveCurve_of_twistRealization hR hA)

/-- `Work.Arithmetic.HasLLinkCurve 𝕜` from the witness form of the residual. -/
theorem hasLLinkCurve_of_twistResidual {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (h : HasPointlessIndexFiveCurveOfTwist 𝕜) : Work.Arithmetic.HasLLinkCurve 𝕜 :=
  Work.TorsorExistence.hasLLinkCurve_of_hasPointlessIndexFiveCurve
    (hasPointlessIndexFiveCurve_of_twistResidual h)

/-! ## 3. The four field classes -/

/-- **(TORS), class (a)**: number fields.  The arithmetic half is Clark–Lacy, Theorem 1.10. -/
theorem hasPointlessIndexFiveCurve_numberField {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    [NumberField 𝕜] (hR : TwistRealization 𝕜) (hA : ClarkLacyPointless 𝕜) :
    HasPointlessIndexFiveCurve 𝕜 :=
  hasPointlessIndexFiveCurve_of_twistRealization hR hA

/-- **(TORS), class (b)**: function fields of positive-dimensional varieties over a number
field.  The arithmetic half is Clark–Lacy, Theorem 1.10. -/
theorem hasPointlessIndexFiveCurve_functionField_numberField (𝔽 : Type) [Field 𝔽] [NumberField 𝔽]
    (X : Scheme) [MotivicInvariants.Variety 𝔽 X] (_hX : 0 < topologicalKrullDim X)
    [DecidableEq X.functionField] (hR : TwistRealization X.functionField)
    (hA : ClarkLacyPointless X.functionField) : HasPointlessIndexFiveCurve X.functionField :=
  hasPointlessIndexFiveCurve_of_twistRealization hR hA

/-- **(TORS), class (c)**: function fields of positive-dimensional varieties over a finite
field.  The arithmetic half is Clark–Lacy, Theorem 1.10 (which covers characteristic `5` too, via
the Artin–Schreier route `existsCyclicExtension_of_charP_five`). -/
theorem hasPointlessIndexFiveCurve_functionField_finite (𝔽 : Type) [Field 𝔽] [Finite 𝔽]
    (X : Scheme) [MotivicInvariants.Variety 𝔽 X] (_hX : 0 < topologicalKrullDim X)
    [DecidableEq X.functionField] (hR : TwistRealization X.functionField)
    (hA : ClarkLacyPointless X.functionField) : HasPointlessIndexFiveCurve X.functionField :=
  hasPointlessIndexFiveCurve_of_twistRealization hR hA

/-- **(TORS), class (d)**: function fields of positive-dimensional varieties over an algebraically
closed field.  The arithmetic half is Lang–Tate, Theorem 7. -/
theorem hasPointlessIndexFiveCurve_functionField_algClosed (𝔽 : Type) [Field 𝔽] [IsAlgClosed 𝔽]
    (X : Scheme) [MotivicInvariants.Variety 𝔽 X] (_hX : 0 < topologicalKrullDim X)
    [DecidableEq X.functionField] (hR : TwistRealization X.functionField)
    (hA : LangTatePointless X.functionField) : HasPointlessIndexFiveCurve X.functionField :=
  hasPointlessIndexFiveCurve_of_twistRealization hR hA

/-! ### The end product for the four classes -/

/-- **(TORS), class (a)**, in the form consumed by the L-link construction. -/
theorem hasLLinkCurve_numberField {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] [NumberField 𝕜]
    (hR : TwistRealization 𝕜) (hA : ClarkLacyPointless 𝕜) : Work.Arithmetic.HasLLinkCurve 𝕜 :=
  hasLLinkCurve_of_twistRealization hR hA

/-- **(TORS), class (b)**, in the form consumed by the L-link construction. -/
theorem hasLLinkCurve_functionField_numberField (𝔽 : Type) [Field 𝔽] [NumberField 𝔽]
    (X : Scheme) [MotivicInvariants.Variety 𝔽 X] (_hX : 0 < topologicalKrullDim X)
    [DecidableEq X.functionField] (hR : TwistRealization X.functionField)
    (hA : ClarkLacyPointless X.functionField) :
    Work.Arithmetic.HasLLinkCurve X.functionField :=
  hasLLinkCurve_of_twistRealization hR hA

/-- **(TORS), class (c)**, in the form consumed by the L-link construction. -/
theorem hasLLinkCurve_functionField_finite (𝔽 : Type) [Field 𝔽] [Finite 𝔽]
    (X : Scheme) [MotivicInvariants.Variety 𝔽 X] (_hX : 0 < topologicalKrullDim X)
    [DecidableEq X.functionField] (hR : TwistRealization X.functionField)
    (hA : ClarkLacyPointless X.functionField) :
    Work.Arithmetic.HasLLinkCurve X.functionField :=
  hasLLinkCurve_of_twistRealization hR hA

/-- **(TORS), class (d)**, in the form consumed by the L-link construction. -/
theorem hasLLinkCurve_functionField_algClosed (𝔽 : Type) [Field 𝔽] [IsAlgClosed 𝔽]
    (X : Scheme) [MotivicInvariants.Variety 𝔽 X] (_hX : 0 < topologicalKrullDim X)
    [DecidableEq X.functionField] (hR : TwistRealization X.functionField)
    (hA : LangTatePointless X.functionField) :
    Work.Arithmetic.HasLLinkCurve X.functionField :=
  hasLLinkCurve_of_twistRealization hR hA

/-! ## 4. The `DecidableEq`-free interface

`QuinticTwist 𝕜` carries a `DecidableEq 𝕜` argument, an artefact of Mathlib's group law on affine
points of a Weierstrass curve.  `TwistResidual 𝕜` (in `Defs.lean`) hides it by existentially
quantifying the instance — legitimate because `DecidableEq` is a subsingleton — so the following
theorems ask for no decidability hypothesis at all, matching the parent chapter's convention that
the artefact "does not appear in the residual or in `HasLLinkCurve`". -/

/-- **The sharp residual, `DecidableEq`-free.**  This is the *weakest* form of the residual: one
quintic twist which is pointless and which *is* realized by a curve model.  Nothing is asked of the
other quintic twists, so this is exactly what the paper's Lemma `lem:torsors` constructs.  It is
strictly weaker than `TwistResidual` (which asks for a realization of *every* quintic twist), via
`twistResidualSharp_of_twistResidual`. -/
noncomputable def TwistResidualSharp (𝕜 : Type) [Field 𝕜] : Prop :=
  ∃ d : DecidableEq 𝕜, @HasPointlessIndexFiveCurveOfTwist 𝕜 _ d

/-- `TwistResidual` implies the sharp form: a realization of every quintic twist certainly gives
one for the pointless twist. -/
theorem twistResidualSharp_of_twistResidual {𝕜 : Type} [Field 𝕜] (h : TwistResidual 𝕜) :
    TwistResidualSharp 𝕜 := by
  obtain ⟨d, hA, hR⟩ := h
  exact ⟨d, hasPointlessIndexFiveCurveOfTwist_of hR hA⟩

/-- **The main reduction, `DecidableEq`-free.** -/
theorem hasPointlessIndexFiveCurve_of_residual {𝕜 : Type} [Field 𝕜] (h : TwistResidual 𝕜) :
    HasPointlessIndexFiveCurve 𝕜 := by
  obtain ⟨d, hA, hR⟩ := h
  letI : DecidableEq 𝕜 := d
  exact hasPointlessIndexFiveCurve_of_twistRealization hR hA

/-- **The main reduction from the sharp residual.** -/
theorem hasPointlessIndexFiveCurve_of_residualSharp {𝕜 : Type} [Field 𝕜]
    (h : TwistResidualSharp 𝕜) : HasPointlessIndexFiveCurve 𝕜 := by
  obtain ⟨d, hD⟩ := h
  letI : DecidableEq 𝕜 := d
  exact hasPointlessIndexFiveCurve_of_twistResidual hD

/-- The paper's Lemma `lem:torsors` from the sharp residual, `DecidableEq`-free. -/
theorem hasLLinkCurve_of_residualSharp {𝕜 : Type} [Field 𝕜] (h : TwistResidualSharp 𝕜) :
    Work.Arithmetic.HasLLinkCurve 𝕜 :=
  Work.TorsorExistence.hasLLinkCurve_of_hasPointlessIndexFiveCurve
    (hasPointlessIndexFiveCurve_of_residualSharp h)

/-- The Arithmetic area's named input `ClarkLacyFive 𝕜` from the sharp residual. -/
theorem clarkLacyFive_of_residualSharp {𝕜 : Type} [Field 𝕜] (h : TwistResidualSharp 𝕜) :
    Work.Arithmetic.ClarkLacyFive 𝕜 := by
  obtain ⟨d, hD⟩ := h
  letI : DecidableEq 𝕜 := d
  obtain ⟨D, hP, _⟩ := hD
  exact hasPointlessTwist_clarkLacyFive ⟨D, hP⟩

/-- Everything the parent chapter can ask for at once, from the sharp residual. -/
theorem conclusions_of_residualSharp {𝕜 : Type} [Field 𝕜] (h : TwistResidualSharp 𝕜) :
    HasPointlessIndexFiveCurve 𝕜 ∧ Work.Arithmetic.HasLLinkCurve 𝕜 ∧
      Work.Arithmetic.ClarkLacyFive 𝕜 :=
  ⟨hasPointlessIndexFiveCurve_of_residualSharp h, hasLLinkCurve_of_residualSharp h,
    clarkLacyFive_of_residualSharp h⟩

/-- The paper's Lemma `lem:torsors` from the residual, `DecidableEq`-free. -/
theorem hasLLinkCurve_of_residual {𝕜 : Type} [Field 𝕜] (h : TwistResidual 𝕜) :
    Work.Arithmetic.HasLLinkCurve 𝕜 :=
  Work.TorsorExistence.hasLLinkCurve_of_hasPointlessIndexFiveCurve
    (hasPointlessIndexFiveCurve_of_residual h)

/-- The residual gives the Arithmetic area's named input `ClarkLacyFive 𝕜`. -/
theorem clarkLacyFive_of_residual {𝕜 : Type} [Field 𝕜] (h : TwistResidual 𝕜) :
    Work.Arithmetic.ClarkLacyFive 𝕜 := by
  obtain ⟨d, hA, _⟩ := h
  letI : DecidableEq 𝕜 := d
  exact hasPointlessTwist_clarkLacyFive hA

/-- Everything the parent chapter can ask for at once, from the residual. -/
theorem conclusions_of_residual {𝕜 : Type} [Field 𝕜] (h : TwistResidual 𝕜) :
    HasPointlessIndexFiveCurve 𝕜 ∧ Work.Arithmetic.HasLLinkCurve 𝕜 ∧
      Work.Arithmetic.ClarkLacyFive 𝕜 :=
  ⟨hasPointlessIndexFiveCurve_of_residual h, hasLLinkCurve_of_residual h,
    clarkLacyFive_of_residual h⟩

/-- **(TORS), class (a)**, `DecidableEq`-free: number fields. -/
theorem hasPointlessIndexFiveCurve_residual_numberField {𝕜 : Type} [Field 𝕜] [NumberField 𝕜]
    (h : TwistResidual 𝕜) : HasPointlessIndexFiveCurve 𝕜 :=
  hasPointlessIndexFiveCurve_of_residual h

/-- **(TORS), class (a)**, `DecidableEq`-free, in the form consumed by the L-link construction. -/
theorem hasLLinkCurve_residual_numberField {𝕜 : Type} [Field 𝕜] [NumberField 𝕜]
    (h : TwistResidualSharp 𝕜) : Work.Arithmetic.HasLLinkCurve 𝕜 :=
  hasLLinkCurve_of_residualSharp h

/-- **(TORS), class (b)**, `DecidableEq`-free: function fields over number fields. -/
theorem hasLLinkCurve_residual_functionField_numberField (𝔽 : Type) [Field 𝔽] [NumberField 𝔽]
    (X : Scheme) [MotivicInvariants.Variety 𝔽 X] (_hX : 0 < topologicalKrullDim X)
    (h : TwistResidualSharp X.functionField) : Work.Arithmetic.HasLLinkCurve X.functionField :=
  hasLLinkCurve_of_residualSharp h

/-- **(TORS), class (c)**, `DecidableEq`-free: function fields over finite fields. -/
theorem hasLLinkCurve_residual_functionField_finite (𝔽 : Type) [Field 𝔽] [Finite 𝔽]
    (X : Scheme) [MotivicInvariants.Variety 𝔽 X] (_hX : 0 < topologicalKrullDim X)
    (h : TwistResidualSharp X.functionField) : Work.Arithmetic.HasLLinkCurve X.functionField :=
  hasLLinkCurve_of_residualSharp h

/-- **(TORS), class (d)**, `DecidableEq`-free: function fields over algebraically closed fields. -/
theorem hasLLinkCurve_residual_functionField_algClosed (𝔽 : Type) [Field 𝔽] [IsAlgClosed 𝔽]
    (X : Scheme) [MotivicInvariants.Variety 𝔽 X] (_hX : 0 < topologicalKrullDim X)
    (h : TwistResidualSharp X.functionField) : Work.Arithmetic.HasLLinkCurve X.functionField :=
  hasLLinkCurve_of_residualSharp h

end

end Work.PointlessIndexFive
