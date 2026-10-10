import Mathlib
import Submission.Work.CY3.Projective
import Submission.Work.Twist.away_chart_mvPolynomial

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `ℙ¹` and `𝔸¹` are birational

This file proves `Work.CY3.projectiveLine_birational_affineLine`.  The route actually taken is the
*chart* route, which is a good deal more concrete than the function-field route described in the
statement's docstring, and which reuses algebra that the workspace has already built:

* `Work.Twist.away_chart_mvPolynomial` computes the coordinate ring of the affine chart `D₊(X₀)` of
  `ℙ¹ = Proj 𝕜[X₀,X₁]`: the degree-zero part `A⁰_{X₀}` of the homogeneous localisation at `X₀` is a
  polynomial ring `𝕜[y]` (via the dehomogenisation `X₀ ↦ 1`);
* Mathlib's `Proj.basicOpenIsoSpec` identifies `D₊(X₀) ≅ Spec (A⁰_{X₀})`, and
  `AffineSpace.SpecIso` identifies `𝔸(Fin 1; Spec 𝕜) ≅ Spec 𝕜[y]`.

Composing the three isomorphisms exhibits the affine chart `D₊(X₀) ⊆ ℙ¹` as an open subscheme
isomorphic to `𝔸¹`.  The chart is dense in `ℙ¹` because `ℙ¹` is (pre)irreducible and the chart is a
nonempty open: the nonemptiness is witnessed by the homogeneous prime `(0)`, which is a point of
`D₊(X₀)` since `X₀ ≠ 0`.  A dense open subscheme isomorphic to `Y` is exactly a `PartialIso X Y`,
and `Scheme.PartialIso.toBirationalMap` (in `ChallengeDeps`) turns that into a `BirationalMap`, so
the birational map is produced without ever writing down a rational map by hand — the two
directions are mutually inverse by construction.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.CY3

open CategoryTheory AlgebraicGeometry

noncomputable section

/-- The coordinate `X₀` of `𝕜[X₀,X₁]`, homogeneous of degree one, defining the affine chart
`D₊(X₀)` of `ℙ¹` that is isomorphic to `𝔸¹`. -/
abbrev p1ChartCoordinate (𝕜 : Type) [Field 𝕜] : MvPolynomial (Fin 2) 𝕜 := MvPolynomial.X 0

/-- The open affine chart `D₊(X₀) ⊆ ℙ¹ = Proj 𝕜[X₀,X₁]`. -/
abbrev p1Chart (𝕜 : Type) [Field 𝕜] : (Proj (Work.Twist.stdGrading 𝕜 1)).Opens :=
  Proj.basicOpen (Work.Twist.stdGrading 𝕜 1) (p1ChartCoordinate 𝕜)

/-- **The chart ring of `ℙ¹` at `X₀` is `𝕜[y]`**: the degree-zero part of the homogeneous
localisation of `𝕜[X₀,X₁]` at `X₀` is a polynomial ring in one variable.  This is
`Work.Twist.away_chart_mvPolynomial` at `n = 1` (the case `i = 0` of
`Work.Twist.away_chart_mvPolynomial_X`). -/
noncomputable def p1ChartRingEquiv (𝕜 : Type) [Field 𝕜] :
    HomogeneousLocalization.Away (Work.Twist.stdGrading 𝕜 1) (p1ChartCoordinate 𝕜) ≃+*
      MvPolynomial (Fin 1) 𝕜 :=
  (Work.Twist.away_chart_mvPolynomial 𝕜 1).some

/-- **The affine chart `D₊(X₀)` of `ℙ¹` is `𝔸¹`.**  The isomorphism is the composite of Mathlib's
`Proj.basicOpenIsoSpec` (`D₊(X₀) ≅ Spec (A⁰_{X₀})`), the spectrum of `p1ChartRingEquiv`
(`Spec (A⁰_{X₀}) ≅ Spec 𝕜[y]`) and Mathlib's `AffineSpace.SpecIso`
(`Spec 𝕜[y] ≅ 𝔸(Fin 1; Spec 𝕜)`). -/
noncomputable def p1ChartIso (𝕜 : Type) [Field 𝕜] :
    (p1Chart 𝕜).toScheme ≅ AffineSpace (Fin 1) (Spec (CommRingCat.of 𝕜)) :=
  Proj.basicOpenIsoSpec (Work.Twist.stdGrading 𝕜 1) (p1ChartCoordinate 𝕜)
      (Work.Twist.X0_mem_stdGrading 𝕜 1) (by norm_num)
    ≪≫ Scheme.Spec.mapIso (p1ChartRingEquiv 𝕜).symm.toCommRingCatIso.op
    ≪≫ (AffineSpace.SpecIso (Fin 1) (CommRingCat.of 𝕜)).symm

/-- **The affine chart `D₊(X₀)` of `ℙ¹` is nonempty**, witnessed by the homogeneous prime ideal
`(0)`: it is relevant (because `X₀` is a nonzero element of the irrelevant ideal, i.e.
`Work.Twist.irrelevant_homogeneousSubmodule_ne_bot`) and it does not contain `X₀`. -/
lemma p1Chart_nonempty (𝕜 : Type) [Field 𝕜] : (p1Chart 𝕜 : Set (Proj (Work.Twist.stdGrading 𝕜 1))).Nonempty := by
  let q : ↥(Proj (Work.Twist.stdGrading 𝕜 1)) :=
    ⟨⊥, by rw [HomogeneousIdeal.toIdeal_bot]; exact Ideal.isPrime_bot,
      Work.Twist.irrelevant_homogeneousSubmodule_ne_bot 𝕜 1⟩
  refine ⟨q, ?_⟩
  change q ∈ Proj.basicOpen (Work.Twist.stdGrading 𝕜 1) (p1ChartCoordinate 𝕜)
  rw [Proj.mem_basicOpen]
  intro hcon
  have h3 : p1ChartCoordinate 𝕜 ∈ (⊥ : Ideal (MvPolynomial (Fin 2) 𝕜)) := hcon
  exact MvPolynomial.X_ne_zero (R := 𝕜) (0 : Fin 2) (Ideal.mem_bot.mp h3)

/-- **The affine chart `D₊(X₀)` of `ℙ¹` is dense.**  `ℙ¹` is irreducible
(`Work.Twist.irreducibleSpace_projectiveSpace`), so a nonempty open set is dense
(`IsOpen.dense`), and the chart is a nonempty open by `p1Chart_nonempty`. -/
lemma p1Chart_dense (𝕜 : Type) [Field 𝕜] : Dense (p1Chart 𝕜 : Set (Proj (Work.Twist.stdGrading 𝕜 1))) := by
  haveI : IrreducibleSpace (Proj (Work.Twist.stdGrading 𝕜 1)) :=
    Work.Twist.irreducibleSpace_projectiveSpace 𝕜 1
  exact IsOpen.dense (Proj.basicOpen _ _).isOpen (p1Chart_nonempty 𝕜)

/-- **`ℙ¹` and `𝔸¹` are birational.**  A stepping stone towards the statement that the
stable-birationality relation defined with products by affine space (as in `Work.K3.StablyBirational`,
used by the CY3 link) agrees with the relation defined with products by the projective line `ℙ¹`
(the form in which the paper states `c(ψ) = [ℙ¹ × Z] − [ℙ¹ × Z']`).
Route: `RationalMap.equivFunctionField`/`RationalMap.ofFunctionField` produce rational maps in
both directions from an identification of the function fields `κ(ℙ¹) ≅ κ(𝔸¹) = 𝕜(t)`, and
`RationalMap.eq_of_fromFunctionField_eq` identifies both composites with the identity; the
`IrreducibleSpace` instances for both sides are supplied by `Variety`.  `Work.CY3.Projective`
provides `ProjectiveLine` (= the project's `ℙ¹`) and its `Variety` instance; note the scoped
notation `𝔸(n; S)` needs `open AlgebraicGeometry`, which is why the statement below spells out
`AlgebraicGeometry.AffineSpace`. -/
theorem projectiveLine_birational_affineLine (𝕜 : Type) [Field 𝕜] :
    Nonempty (AlgebraicGeometry.Scheme.BirationalMap (Work.CY3.ProjectiveLine 𝕜)
      (AlgebraicGeometry.AffineSpace (Fin 1) (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)))) :=
  ⟨AlgebraicGeometry.Scheme.PartialIso.toBirationalMap
    { source := p1Chart 𝕜
      dense_source := p1Chart_dense 𝕜
      target := ⊤
      dense_target := dense_univ
      iso := p1ChartIso 𝕜 ≪≫
        (AlgebraicGeometry.AffineSpace (Fin 1)
          (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))).topIso.symm }⟩

end

end Work.CY3
