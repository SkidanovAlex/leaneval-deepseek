/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.PointlessIndexFive
-/
import Mathlib
import ChallengeDeps
import Submission.Work.TorsorExistence.All

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.PointlessIndexFive` — the interface

Area target (as handed to me by the lead): **discharge the geometric residual
`Work.TorsorExistence.HasPointlessIndexFiveCurve 𝕜` for the four field classes of Lin–Shinder,
*Motivic invariants of birational maps*, Annals of Math. **199** (1), 2024, Theorem 1.2 (1)
(a)–(d)** — the named residual of the `TorsorExistence` chapter.

`Work.TorsorExistence.PointlessIndexFiveCurve 𝕜` asks for a *scheme* `C` over `𝕜` that is a
smooth, proper, geometrically integral curve of dimension one, has no `𝕜`-point, carries a
`𝕜`-rational divisor of degree `5`, and has all its rational divisor degrees divisible by `5`.
The `TorsorExistence` chapter proved (i) the arithmetic steps (A), (B) of the paper's proof of
Lemma `lem:torsors` (cyclic quintic extensions; a curve with a rational point of order `5` and
`j ≠ 1728`), (ii) the quintic twist (C) as the concrete Galois cohomology group
`H¹(ℤ/5, E(L)) = ker N / (σ - 1)E(L)` with its class `cls`, (iii) the orbit-divisor/period facts
(D) (`five_smul_cls`, `cls_eq_zero_iff`, `period_toTorsor_eq_five_iff`), and (iv) the reduction
`Work.Arithmetic.HasLLinkCurve 𝕜 ← HasPointlessIndexFiveCurve 𝕜`.  What it left open is exactly
the *scheme-theoretic* statement, together with the *arithmetic* statement `cls ≠ 0`.

This file names those two open statements **separately**, so that the geometry and the arithmetic
can be attacked independently, and fixes the conventions that the rest of the area uses.

## Conventions

* `CurveModel 𝕜`: a scheme `C` over `𝕜` with `Variety 𝕜 C` (`𝕜`-scheme of finite type,
  separated, integral), `IsProper`, `Smooth` and `GeometricallyIntegral` over `Spec 𝕜`, and
  `topologicalKrullDim C = 1`.  This is the *geometric* half of `PointlessIndexFiveCurve`, with
  no arithmetic content at all.
* `TwistCurveModel 𝕜 D`, for `D : QuinticTwist 𝕜`: a `CurveModel` whose rational points and
  rational divisors are exactly those prescribed by the class of `D`:
  `C(𝕜) ≠ ∅ ↔ (D.cls = 0)` and `(∃ D', deg D' = n) ↔ (n • D.cls = 0)`.  Geometrically `C` is the
  quotient `(E_L)/G` of the twist construction — the scheme that Mathlib cannot build (see
  `NOTES.md` §3).
* `TwistRealization 𝕜`: *every* quintic twist over `𝕜` is realized by a curve model.  This is a
  single geometric statement, uniform in the field class.
* `HasPointlessTwist 𝕜`: *some* quintic twist over `𝕜` has non-vanishing class — the sharp
  arithmetic form of the paper's Lemma `lem:torsors` (Clark–Lacy Theorem 1.10 for the classes
  (a)–(c), Lang–Tate Theorem 7 for class (d)).

## The reduction (proved in `Main.lean`)

  `Work.PointlessIndexFive.hasPointlessIndexFiveCurve_of`
    : `TwistRealization 𝕜 → HasPointlessTwist 𝕜 → HasPointlessIndexFiveCurve 𝕜`

so that `HasPointlessIndexFiveCurve 𝕜` is `TwistRealization 𝕜 ∧ HasPointlessTwist 𝕜`, with the
two halves named, and the four field-class theorems
`hasPointlessIndexFiveCurve_numberField`, `hasPointlessIndexFiveCurve_functionField_numberField`,
`hasPointlessIndexFiveCurve_functionField_finite`,
`hasPointlessIndexFiveCurve_functionField_algClosed` erase the field-class data once the two
halves are supplied.  The arithmetic half implies the Arithmetic area's own named input
`Work.Arithmetic.ClarkLacyFive 𝕜` (`hasPointlessTwist_clarkLacyFive`), and the geometric half
only has to be supplied once for all four classes.

## Honest status

Neither half is provable in the pinned Mathlib:

* `TwistRealization` needs the quotient of a variety by a finite group action (the twist
  `(E_L)/G`), which Mathlib does not have; `NOTES.md` §3 records the construction and the exact
  missing pieces, together with the fact — verified in `Model.lean` — that *properness* of such
  models **is** available (`AlgebraicGeometry.Proj.toSpecZero` is proper), so the gap is smaller
  than `Submission/Work/TorsorExistence/NOTES.md` §2 suggests;
* `HasPointlessTwist` needs weak Mordell–Weil (`E(𝕜)/5E(𝕜)` finite, Clark–Lacy) or the local
  obstruction at a place of `𝕜`; its *criterion* form is proved here
  (`pointless_of_shift_mem_ker`, `Twist/Criterion.lean`), which is exactly the local
  computation the paper performs.

See `NOTES.md` for the full account.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory AlgebraicGeometry

namespace Work.PointlessIndexFive

noncomputable section

/-! ## Re-exported names of the parent chapter

The residual of `Submission/Work/TorsorExistence` and the twist data of its `Twist.lean` are the
starting point of this area; we re-export them under short names so that callers of
`Work.PointlessIndexFive` need only one import. -/

/-- The residual of `Submission/Work/TorsorExistence`: a smooth proper geometrically integral
curve of dimension one over `𝕜` with no `𝕜`-point, a `𝕜`-rational divisor of degree `5` and all
rational divisor degrees divisible by `5`. -/
abbrev PointlessIndexFiveCurve (𝕜 : Type) [Field 𝕜] :=
  Work.TorsorExistence.PointlessIndexFiveCurve 𝕜

/-- `Nonempty (PointlessIndexFiveCurve 𝕜)`. -/
abbrev HasPointlessIndexFiveCurve (𝕜 : Type) [Field 𝕜] : Prop :=
  Work.TorsorExistence.HasPointlessIndexFiveCurve 𝕜

/-- The quintic twist data of the paper's construction: an elliptic curve `E/𝕜` with a rational
point of exact order `5` and `j ≠ 1728`, together with a cyclic quintic extension `L/𝕜`. -/
abbrev QuinticTwist (𝕜 : Type) [Field 𝕜] [DecidableEq 𝕜] :=
  Work.TorsorExistence.QuinticTwist 𝕜

/-! ## 1. The geometric half: curve models -/

/-- A *curve over `𝕜`*: a scheme with `Variety 𝕜 C` (finite type, separated and integral over
`Spec 𝕜`), proper, smooth and geometrically integral over `Spec 𝕜`, of topological Krull
dimension one.

This is the geometric content of `PointlessIndexFiveCurve`, isolated from the arithmetic
content (`C(𝕜) = ∅`, the degree-`5` divisor, the divisibility of all degrees). -/
structure CurveModel (𝕜 : Type) [Field 𝕜] where
  /-- The curve. -/
  C : Scheme
  [variety : MotivicInvariants.Variety 𝕜 C]
  [isProper : IsProper (C ↘ Spec (CommRingCat.of 𝕜))]
  [isSmooth : Smooth (C ↘ Spec (CommRingCat.of 𝕜))]
  [isGeomIntegral : GeometricallyIntegral (C ↘ Spec (CommRingCat.of 𝕜))]
  /-- A curve is one-dimensional. -/
  dim_eq_one : topologicalKrullDim C = 1

namespace CurveModel

variable {𝕜 : Type} [Field 𝕜]

instance (X : CurveModel 𝕜) : MotivicInvariants.Variety 𝕜 X.C := X.variety
instance (X : CurveModel 𝕜) : X.C.Over (Spec (CommRingCat.of 𝕜)) :=
  MotivicInvariants.Variety.over
instance (X : CurveModel 𝕜) : IsProper (X.C ↘ Spec (CommRingCat.of 𝕜)) := X.isProper
instance (X : CurveModel 𝕜) : Smooth (X.C ↘ Spec (CommRingCat.of 𝕜)) := X.isSmooth
instance (X : CurveModel 𝕜) : GeometricallyIntegral (X.C ↘ Spec (CommRingCat.of 𝕜)) :=
  X.isGeomIntegral

end CurveModel

/-! ## 2. The geometric half: realizing a quintic twist by a curve -/

/-- **The geometric realization of a quintic twist.**  For `D : QuinticTwist 𝕜` — an elliptic
curve with a rational point `P` of order `5` and a cyclic quintic extension `L/𝕜` — this structure
records the quotient `C := (E_L)/G` of the twist construction as a curve over `𝕜`, together with
the two Galois-descent bridges that identify its rational points and rational divisors with the
class of `D` in `H¹(ℤ/5, E(L)) = ker N / (σ - 1)E(L)`:

* `C(𝕜) ≠ ∅` iff the class of the cocycle `σ ↦ P` is trivial (`= D.toTorsor.HasPoint`, i.e.
  `cls = 0`);
* `C` carries a `𝕜`-rational divisor of degree `n` iff `cls ^ n = 1`
  (`= D.toTorsor.DivisorOfDegree n`).

This is the *scheme* produced by the paper's proof of Lemma `lem:torsors`; it is not
constructible in the pinned Mathlib (no quotient of a variety by a group action, see `NOTES.md`
§3). -/
structure TwistCurveModel {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (D : QuinticTwist 𝕜) where
  /-- The curve `(E_L)/G`. -/
  C : Scheme
  [variety : MotivicInvariants.Variety 𝕜 C]
  [isProper : IsProper (C ↘ Spec (CommRingCat.of 𝕜))]
  [isSmooth : Smooth (C ↘ Spec (CommRingCat.of 𝕜))]
  [isGeomIntegral : GeometricallyIntegral (C ↘ Spec (CommRingCat.of 𝕜))]
  /-- A curve is one-dimensional. -/
  dim_eq_one : topologicalKrullDim C = 1
  /-- The class of the twist is trivial iff the twist has a rational point. -/
  hasPoint_iff : Work.Arithmetic.HasRatPoint 𝕜 C ↔ D.toTorsor.HasPoint
  /-- The twist carries a rational divisor of degree `n` iff `n` is a multiple of the period,
  i.e. iff the class satisfies `cls ^ n = 1`. -/
  divisorOfDegree_iff :
    ∀ n : ℕ, Work.Arithmetic.HasRatDivisorOfDegree 𝕜 C n ↔ D.toTorsor.DivisorOfDegree n

namespace TwistCurveModel

variable {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] {D : QuinticTwist 𝕜} (M : TwistCurveModel D)

instance : MotivicInvariants.Variety 𝕜 M.C := M.variety
instance : M.C.Over (Spec (CommRingCat.of 𝕜)) := MotivicInvariants.Variety.over
instance : IsProper (M.C ↘ Spec (CommRingCat.of 𝕜)) := M.isProper
instance : Smooth (M.C ↘ Spec (CommRingCat.of 𝕜)) := M.isSmooth
instance : GeometricallyIntegral (M.C ↘ Spec (CommRingCat.of 𝕜)) := M.isGeomIntegral

/-- A `TwistCurveModel` is in particular a curve model. -/
def toCurveModel : CurveModel 𝕜 where
  C := M.C
  variety := M.variety
  isProper := M.isProper
  isSmooth := M.isSmooth
  isGeomIntegral := M.isGeomIntegral
  dim_eq_one := M.dim_eq_one

end TwistCurveModel

/-- **The geometric residual, uniform in the field.**  Every quintic twist over `𝕜` is realized
by a curve model: the quotient `(E_L)/G` exists as a smooth proper geometrically integral curve
over `𝕜` and the Galois-descent bridges hold.

This is a single statement, independent of the field class of Theorem 1.2 (1), and it is exactly
the *scheme-theoretic* content of the paper's Lemma `lem:torsors` (the twist construction) that
`Mathlib` cannot express (no quotient by a group action). -/
def TwistRealization (𝕜 : Type) [Field 𝕜] [DecidableEq 𝕜] : Prop :=
  ∀ D : QuinticTwist 𝕜, Nonempty (TwistCurveModel D)

/-! ## 3. The arithmetic half: a pointless quintic twist -/

/-- **The arithmetic residual, sharp form.**  There is a quintic twist `D` over `𝕜` whose class
in `H¹(ℤ/5, E(L))` is non-zero, i.e. `P ∉ (σ - 1)E(L)`: the twist `C = (E_L)/G` has no rational
point.

This is the arithmetic content of the paper's Lemma `lem:torsors` — Clark–Lacy, *Period-index
problems for WC-groups*, Theorem 1.10 for the classes (a)–(c) and Lang–Tate, Theorem 7 for class
(d) (see `ClarkLacyPointless` and `LangTatePointless` below for the class-specific names). -/
def HasPointlessTwist (𝕜 : Type) [Field 𝕜] [DecidableEq 𝕜] : Prop :=
  ∃ D : QuinticTwist 𝕜, D.Pointless

/-- **Clark–Lacy, Theorem 1.10** (J. reine angew. Math. **749** (2019) 1–34), in the sharp form
used by the paper: over a number field or an infinite finitely generated field, the twist
construction produces a quintic twist whose class is non-zero (`j ≠ 1728` is part of the
`QuinticTwist` data, and Clark–Lacy §4) supplies it).  This is `HasPointlessTwist 𝕜`. -/
abbrev ClarkLacyPointless (𝕜 : Type) [Field 𝕜] [DecidableEq 𝕜] : Prop := HasPointlessTwist 𝕜

/-- **Lang–Tate, Theorem 7** (Amer. J. Math. **80** (1958)), in the same form: over a function
field `𝕜` of a positive-dimensional variety over an algebraically closed field, Hilbertianity
(`𝕜` has infinitely many linearly disjoint cyclic quintic extensions) together with the
finiteness of `E(𝕜)/5E(𝕜)` and a rational `5`-torsion point of a constant ordinary curve produces
a quintic twist with non-zero class.  This is `HasPointlessTwist 𝕜`. -/
abbrev LangTatePointless (𝕜 : Type) [Field 𝕜] [DecidableEq 𝕜] : Prop := HasPointlessTwist 𝕜

/-- Both halves of the residual, as a single `Prop`, with the `DecidableEq 𝕜` artefact hidden.

`QuinticTwist 𝕜` (inherited from the parent chapter) carries a `DecidableEq 𝕜` argument, purely
because Mathlib's group law on affine points of a Weierstrass curve,
`WeierstrassCurve.Affine.Point.instAddCommGroup`, requires it.  Since `DecidableEq 𝕜` is a
subsingleton (it is a function into the subsingleton-valued `Decidable`), existentially quantifying
the instance does not change the mathematics, and it makes the interface of this area free of the
artefact: this is the single hypothesis under which the four field-class theorems of `Main.lean`
produce `HasPointlessIndexFiveCurve 𝕜` and `Work.Arithmetic.HasLLinkCurve 𝕜`. -/
noncomputable def TwistResidual (𝕜 : Type) [Field 𝕜] : Prop :=
  ∃ d : DecidableEq 𝕜, @HasPointlessTwist 𝕜 _ d ∧ @TwistRealization 𝕜 _ d

/-- The witness form of the residual, with the `DecidableEq 𝕜` artefact hidden.  (This is
`HasPointlessIndexFiveCurveOfTwist`, see `Main.lean`, with the instance quantified.) -/
noncomputable def HasPointlessTwistAny (𝕜 : Type) [Field 𝕜] : Prop :=
  ∃ d : DecidableEq 𝕜, @HasPointlessTwist 𝕜 _ d

/-- The arithmetic half of `TwistResidual`. -/
theorem hasPointlessTwistAny_of_residual {𝕜 : Type} [Field 𝕜] (h : TwistResidual 𝕜) :
    HasPointlessTwistAny 𝕜 := by
  obtain ⟨d, hA, _⟩ := h
  exact ⟨d, hA⟩

/-- `ClarkLacyPointless 𝕜` is `HasPointlessTwist 𝕜` by definition; recorded for rewriting. -/
theorem clarkLacyPointless_iff {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] :
    ClarkLacyPointless 𝕜 ↔ HasPointlessTwist 𝕜 := Iff.rfl

/-- `LangTatePointless 𝕜` is `HasPointlessTwist 𝕜` by definition; recorded for rewriting. -/
theorem langTatePointless_iff {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] :
    LangTatePointless 𝕜 ↔ HasPointlessTwist 𝕜 := Iff.rfl

end

end Work.PointlessIndexFive
