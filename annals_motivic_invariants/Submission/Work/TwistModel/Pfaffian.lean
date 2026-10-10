/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.TwistModel
-/
import Mathlib
import ChallengeDeps
import Submission.Work.TwistModel.Defs
import Submission.Work.TwistModel.ClosedModel
import Submission.Work.Twist.away_chart_mvPolynomial_X

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The explicit model of the twist: the Pfaffian elliptic quintic in `ℙ⁴`

This file sets up the *explicit* projective model of the twist, following the paper's
`§Elliptic curves` and Shinder–Zhang, *L-equivalence for degree five elliptic curves*, Lemma 2.1
(`lem:deg-5`): a genus-one curve of degree `5` in `ℙ⁴` is, after [SZ] Theorem 1, cut out by the five
`4 × 4` Pfaffians of a `5 × 5` skew-symmetric matrix of linear forms (equivalently it is
`Gr(2,5) ∩ ℙ³` for a hyperplane `ℙ³ ⊂ ℙ⁴`), i.e. by five quadrics; the "good model locus" is the
open condition that they cut out a smooth, geometrically integral curve.

Everything here is the *algebraic* half of that model, which is what Mathlib lacks (there is no
`Matrix.pfaffian` at all in the pinned Mathlib):

* `Matrix.pfaffian4` and `Matrix.skewPfaffian5` — the `4 × 4` Pfaffian and the five Pfaffians of a
  `5 × 5` matrix;
* `IsAlternatingFamily`, `linFormMatrix`, `pfaffianForm` — the five Pfaffian *quadrics* of a family
  of alternating matrices of linear forms; `pfaffianIdeal` is the ideal they generate in
  `𝕜[X₀,…,X₄]`;
* `dehomogenisedIdeal` (using the chart dehomogenisation `Work.Twist.chartDhomX`) and
  `chartModel` — the affine chart model cut out by the dehomogenised quadrics, as a closed
  subscheme of `𝔸⁴ = Spec 𝕜[y₁,…,y₄]`;
* `IsGoodModel` — the **good-model locus**: the discriminant non-vanishing conditions the paper
  imposes on the twist parameters (the five quadrics generate a prime ideal of height `3`, and stay
  prime after every base change of the coefficient field);
* `IsPfaffianCutOutBy`, `PfaffianTwistModel` — the explicit form of the residual: a curve in `ℙ⁴`
  cut out by the five Pfaffians which is a twist model.

The classical identities used throughout ([SZ] §2, Buchsbaum–Eisenbud) are
`Matrix.det_eq_pfaffian4_sq` (the determinant of a `4 × 4` skew matrix is the square of its
Pfaffian) and `Matrix.adjugate_eq_skewPfaffian5` (the adjugate of a `5 × 5` skew matrix is
`(-1)^{i+j} pᵢ pⱼ`); both are proved in the sibling modules of this directory.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory AlgebraicGeometry

namespace Work.TwistModel

noncomputable section

/-! ## 1. Pfaffians -/

namespace Matrix

/-- The **Pfaffian** of a `4 × 4` matrix, `a₀₁a₂₃ - a₀₂a₁₃ + a₀₃a₁₂`.  For skew-symmetric `A` its
square is `det A` (`Matrix.det_eq_pfaffian4_sq`). -/
def pfaffian4 {R : Type*} [CommRing R] (A : Matrix (Fin 4) (Fin 4) R) : R :=
  A 0 1 * A 2 3 - A 0 2 * A 1 3 + A 0 3 * A 1 2

/-- The five **`4 × 4` Pfaffians** of a `5 × 5` matrix: the Pfaffian of the principal minor
obtained by deleting row and column `i`. -/
def skewPfaffian5 {R : Type*} [CommRing R] (A : Matrix (Fin 5) (Fin 5) R) (i : Fin 5) : R :=
  pfaffian4 (A.submatrix (Fin.succAbove i) (Fin.succAbove i))

end Matrix

/-! ## 2. The five Pfaffian quadrics of a family of skew matrices of linear forms -/

variable {𝕜 : Type} [Field 𝕜]

/-- A family of `5 × 5` matrices over `𝕜` is **alternating** if each member is skew-symmetric with
vanishing diagonal.  These are the coefficient matrices of the `5 × 5` alternating matrix
`∑ₖ Xₖ Mₖ` of linear forms on `ℙ⁴`.

The diagonal condition is *not* redundant in characteristic `2`: there `-1 = 1`, so a symmetric
matrix with non-zero diagonal is "skew-symmetric" while the Pfaffian identities (`det = Pf²`, the
adjugate formula) fail for it — e.g. over `𝔽₂` the matrix `!![1,1;1,1]` has `det = 0 ≠ 1 = Pf²`
(for the Pfaffian of an even alternating matrix) and the diagonal is the only thing that can go
wrong (`Matrix.det_eq_pfaffian4_sq`, `Matrix.adjugate_eq_skewPfaffian5`). -/
def IsAlternatingFamily (M : Fin 5 → Matrix (Fin 5) (Fin 5) 𝕜) : Prop :=
  ∀ k : Fin 5, Matrix.transpose (M k) = -M k ∧ ∀ i : Fin 5, M k i i = 0

/-- The `5 × 5` matrix of linear forms `∑ₖ Xₖ Mₖ` with coefficients `M`. -/

def linFormMatrix (M : Fin 5 → Matrix (Fin 5) (Fin 5) 𝕜) :
    Matrix (Fin 5) (Fin 5) (MvPolynomial (Fin 5) 𝕜) :=
  fun a b => ∑ k : Fin 5, MvPolynomial.C (M k a b) * MvPolynomial.X k

/-- **The five Pfaffian quadrics** of the family `M`: the `4 × 4` Pfaffians of `∑ₖ Xₖ Mₖ`.  For a
skew family they are quadrics in `X₀,…,X₄`, and the elliptic quintic of the twist is the curve they
cut out in `ℙ⁴ = Proj 𝕜[X₀,…,X₄]`. -/
def pfaffianForm (M : Fin 5 → Matrix (Fin 5) (Fin 5) 𝕜) (i : Fin 5) :
    MvPolynomial (Fin 5) 𝕜 :=
  Matrix.skewPfaffian5 (linFormMatrix M) i

/-- The homogeneous ideal generated by the five Pfaffian quadrics: the ideal of the affine cone
over the Pfaffian quintic in `𝕜[X₀,…,X₄]`. -/
def pfaffianIdeal (M : Fin 5 → Matrix (Fin 5) (Fin 5) 𝕜) : Ideal (MvPolynomial (Fin 5) 𝕜) :=
  Ideal.span (Set.range (pfaffianForm M))

/-- The **dehomogenisation** of the five Pfaffian quadrics at the chart `X_i = 1`: the equations of
the Pfaffian quintic in the affine chart `D₊(X_i) ≅ 𝔸⁴ = Spec 𝕜[y₁,…,y₄]`
(`Work.Twist.chartDhomX`). -/
def dehomogenisedIdeal (M : Fin 5 → Matrix (Fin 5) (Fin 5) 𝕜) (i : Fin 5) :
    Ideal (MvPolynomial (Fin 4) 𝕜) :=
  Ideal.span (Set.range fun j : Fin 5 => Work.Twist.chartDhomX 𝕜 4 i (pfaffianForm M j))

/-- The affine chart model of the Pfaffian quintic at the chart `X_i = 1`: the closed subscheme of
`𝔸⁴ = Spec 𝕜[y₁,…,y₄]` cut out by the dehomogenised Pfaffians, i.e. the spectrum of the quotient
`𝕜[y₁,…,y₄] / (p₀,…,p₄)`. -/
def chartModel (M : Fin 5 → Matrix (Fin 5) (Fin 5) 𝕜) (i : Fin 5) : Scheme :=
  Spec (CommRingCat.of (MvPolynomial (Fin 4) 𝕜 ⧸ dehomogenisedIdeal M i))

/-! ## 3. The good-model locus -/

/-- **The good-model locus of the Pfaffian quintic.**  This is the open condition on the twist
parameters `M` (a family of `5 × 5` skew matrices of linear forms) that the paper's construction
imposes:

* `M` is skew-symmetric;
* the five Pfaffian quadrics generate a prime ideal of height `3` in `𝕜[X₀,…,X₄]`, i.e. they cut
  out a geometrically integral curve of dimension `1` and degree `5` in `ℙ⁴`;
* this remains true after every base change of the coefficient field (geometric integrality);
* the `5 × 5` matrix has rank `4` at every point of the curve (equivalently: the curve is smooth,
  the matrix representation is non-degenerate along it).

The first three conditions are literally the algebra of the model; the rank condition is stated
separately in `IsGoodModel.rank_condition` for the `𝕜`-rational cone points, since a full
formulation over all field extensions is exactly the Jacobian criterion that Mathlib's `Proj`
theory does not have (see `NOTES.md` §3). -/
def IsGoodModel (M : Fin 5 → Matrix (Fin 5) (Fin 5) 𝕜) : Prop :=
  IsAlternatingFamily M ∧ (pfaffianIdeal M).IsPrime ∧ Ideal.height (pfaffianIdeal M) = 3 ∧
    (∀ (K : Type) [Field K] [Algebra 𝕜 K],
      (Ideal.map (MvPolynomial.map (algebraMap 𝕜 K)) (pfaffianIdeal M)).IsPrime) ∧
    (∀ x : Fin 5 → 𝕜, x ≠ 0 →
      (∀ i : Fin 5, MvPolynomial.eval x (pfaffianForm M i) = 0) →
      Matrix.rank (fun a b : Fin 5 => ∑ k : Fin 5, M k a b * x k) = 4)

/-- The good-model locus implies that the coefficient family is alternating. -/
theorem IsGoodModel.isAlternatingFamily {M : Fin 5 → Matrix (Fin 5) (Fin 5) 𝕜}
    (h : IsGoodModel M) : IsAlternatingFamily M := h.1

/-! ## 4. The explicit form of the residual -/

/-- **`C` is cut out in `ℙ⁴` by the five Pfaffians of `M`.**  A closed immersion of `C` into
`ℙ⁴ = Proj 𝕜[X₀,…,X₄]`, over `𝕜`, whose restriction to the standard chart `D₊(X_i)` is the affine
model `chartModel M i` cut out by the dehomogenised Pfaffians.

This is the precise presentation statement a prover of the explicit twist model has to establish;
Mathlib has no construction of a closed subscheme of `Proj` by equations, so it is carried as data
here. -/
structure IsPfaffianCutOutBy (M : Fin 5 → Matrix (Fin 5) (Fin 5) 𝕜) (C : Scheme)
    [C.Over (Spec (CommRingCat.of 𝕜))] where
  /-- The closed immersion into `ℙ⁴`. -/
  ι : C ⟶ Work.PointlessIndexFive.projectiveSpace 𝕜 4
  /-- It is a closed immersion. -/
  [isClosedImmersion : IsClosedImmersion ι]
  /-- It is a morphism of `𝕜`-schemes. -/
  isOver : ι ≫ Work.PointlessIndexFive.projectiveSpaceToSpec 𝕜 4 = C ↘ Spec (CommRingCat.of 𝕜)
  /-- The chart `D₊(X_i)` of `C` is the affine Pfaffian model. -/
  chart_iso : ∀ i : Fin 5,
    Nonempty (Scheme.Opens.toScheme
        ((TopologicalSpace.Opens.map ι.base).obj
          (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 5) 𝕜) (MvPolynomial.X i)))
      ≅ chartModel M i)

/-- **The explicit twist model of a quintic twist**: a Pfaffian matrix on the good-model locus,
whose quintic in `ℙ⁴` is a curve model of `D` satisfying the two descent bridges.

This is the residual of this area in the form in which the paper's `§Elliptic curves` produces it;
`PfaffianTwistModel.toTwistModelData` forgets the explicit presentation. -/
structure PfaffianTwistModel {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (D : QuinticTwist 𝕜) where
  /-- The coefficients of the `5 × 5` skew matrix of linear forms. -/
  M : Fin 5 → Matrix (Fin 5) (Fin 5) 𝕜
  /-- The good-model locus condition. -/
  good : IsGoodModel M
  /-- The curve `Q(M) ⊂ ℙ⁴`. -/
  C : Scheme
  [variety : MotivicInvariants.Variety 𝕜 C]
  [isProper : IsProper (C ↘ Spec (CommRingCat.of 𝕜))]
  [isSmooth : Smooth (C ↘ Spec (CommRingCat.of 𝕜))]
  [isGeomIntegral : GeometricallyIntegral (C ↘ Spec (CommRingCat.of 𝕜))]
  /-- A curve is one-dimensional. -/
  dim_eq_one : topologicalKrullDim C = 1
  /-- `C` is cut out by the five Pfaffians of `M`. -/
  presented : IsPfaffianCutOutBy M C
  /-- Galois descent of points. -/
  point_bridge : PointBridge D C
  /-- The orbit divisor of degree `5`. -/
  divisor_five : Work.Arithmetic.HasRatDivisorOfDegree 𝕜 C 5
  /-- The rigidity of the divisor-degree bridge. -/
  rigid : DivisorRigidity D C

namespace PfaffianTwistModel

variable {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] {D : QuinticTwist 𝕜}

instance (M : PfaffianTwistModel D) : MotivicInvariants.Variety 𝕜 M.C := M.variety
instance (M : PfaffianTwistModel D) : M.C.Over (Spec (CommRingCat.of 𝕜)) :=
  MotivicInvariants.Variety.over
instance (M : PfaffianTwistModel D) : IsProper (M.C ↘ Spec (CommRingCat.of 𝕜)) := M.isProper
instance (M : PfaffianTwistModel D) : Smooth (M.C ↘ Spec (CommRingCat.of 𝕜)) := M.isSmooth
instance (M : PfaffianTwistModel D) :
    GeometricallyIntegral (M.C ↘ Spec (CommRingCat.of 𝕜)) := M.isGeomIntegral

/-- **Forgetting the explicit presentation**: an explicit Pfaffian twist model is a twist model in
the sense of `TwistModelData` (hence, by `nonempty_twistModelData_iff`, a `TwistCurveModel`). -/
def toTwistModelData (M : PfaffianTwistModel D) : TwistModelData D where
  C := M.C
  variety := M.variety
  isProper := M.isProper
  isSmooth := M.isSmooth
  isGeomIntegral := M.isGeomIntegral
  dim_eq_one := M.dim_eq_one
  point_bridge := M.point_bridge
  divisor_five := M.divisor_five
  rigid := M.rigid

end PfaffianTwistModel

/-- **The explicit twist model, with the corrected divisor predicate.**  The same as
`PfaffianTwistModel` above, but the two divisor conditions use
`Work.TwistModel.HasRatDivisorOfDegreeClosed` (support on closed points) and
`Work.TwistModel.DivisorRigidityClosed` — the honest residual, since the parent's
`Work.Arithmetic.HasRatDivisorOfDegree` is degenerate (`Work.TwistModel.Defect`). -/
structure PfaffianTwistModelClosed {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (D : QuinticTwist 𝕜) where
  /-- The coefficients of the `5 × 5` skew matrix of linear forms. -/
  M : Fin 5 → Matrix (Fin 5) (Fin 5) 𝕜
  /-- The good-model locus condition. -/
  good : IsGoodModel M
  /-- The curve `Q(M) ⊂ ℙ⁴`. -/
  C : Scheme
  [variety : MotivicInvariants.Variety 𝕜 C]
  [isProper : IsProper (C ↘ Spec (CommRingCat.of 𝕜))]
  [isSmooth : Smooth (C ↘ Spec (CommRingCat.of 𝕜))]
  [isGeomIntegral : GeometricallyIntegral (C ↘ Spec (CommRingCat.of 𝕜))]
  /-- A curve is one-dimensional. -/
  dim_eq_one : topologicalKrullDim C = 1
  /-- `C` is cut out by the five Pfaffians of `M`. -/
  presented : IsPfaffianCutOutBy M C
  /-- Galois descent of points. -/
  point_bridge : PointBridge D C
  /-- The orbit divisor of degree `5`. -/
  divisor_five : HasRatDivisorOfDegreeClosed 𝕜 C 5
  /-- The rigidity of the divisor-degree bridge. -/
  rigid : DivisorRigidityClosed D C

namespace PfaffianTwistModelClosed

variable {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] {D : QuinticTwist 𝕜}

instance (M : PfaffianTwistModelClosed D) : MotivicInvariants.Variety 𝕜 M.C := M.variety
instance (M : PfaffianTwistModelClosed D) : M.C.Over (Spec (CommRingCat.of 𝕜)) :=
  MotivicInvariants.Variety.over
instance (M : PfaffianTwistModelClosed D) : IsProper (M.C ↘ Spec (CommRingCat.of 𝕜)) :=
  M.isProper
instance (M : PfaffianTwistModelClosed D) : Smooth (M.C ↘ Spec (CommRingCat.of 𝕜)) := M.isSmooth
instance (M : PfaffianTwistModelClosed D) :
    GeometricallyIntegral (M.C ↘ Spec (CommRingCat.of 𝕜)) := M.isGeomIntegral

/-- Forgetting the presentation: an explicit corrected twist model is a corrected twist model. -/
def toTwistModelDataClosed (M : PfaffianTwistModelClosed D) : TwistModelDataClosed D where
  C := M.C
  variety := M.variety
  isProper := M.isProper
  isSmooth := M.isSmooth
  isGeomIntegral := M.isGeomIntegral
  dim_eq_one := M.dim_eq_one
  point_bridge := M.point_bridge
  divisor_five := M.divisor_five
  rigid := M.rigid

end PfaffianTwistModelClosed


end

end Work.TwistModel
