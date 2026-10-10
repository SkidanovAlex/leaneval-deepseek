/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.TwistModel
-/
import Mathlib
import ChallengeDeps
import Submission.Work.TwistModel.BaseChange
import Submission.Work.TwistModel.irreducibleSpace_of_openCover_of_pairwise
import Submission.Work.TwistModel.isIntegral_projectiveSpaceBaseChange
import Submission.Work.TwistModel.chartPullbackIso

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Geometric integrality of projective space, and `ProjectiveModelGap` discharged

`Work.PointlessIndexFive.ProjectiveModelGap 𝕜 n` was the three-part gap of the projective model
layer: `Smooth (ℙⁿ)`, `GeometricallyIntegral (ℙⁿ)` and `topologicalKrullDim (ℙⁿ) = n`.
`Work.Twist.ProjModel.projectiveModelGap_iff` reduced it to its **third** conjunct,
`GeometricallyIntegral (projectiveSpaceToSpec 𝕜 n)`; this file supplies that conjunct, hence
discharges the gap completely.

`GeometricallyIntegral f` unfolds (via `GeometricallyIntegral.eq_geometrically` and Mathlib's
`geometrically_iff_of_commRing`) to: for every field extension `K/𝕜` and every `y : Spec K ⟶ Spec 𝕜`,
the base change `ℙⁿ ×_{Spec 𝕜} Spec K` is integral.  Field extensions are exactly the morphisms
`Spec K ⟶ Spec 𝕜` (`Spec.map_surjective`), so it suffices to know the integrality of the base
change along `Spec.map (algebraMap 𝕜 K)`, i.e. of `projectiveSpaceBaseChange 𝕜 n K`
(`geometricallyIntegral_of_isIntegral_baseChange`); that is
`Work.TwistModel.isIntegral_projectiveSpaceBaseChange`, proved by the chart cover.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

namespace Work.TwistModel

noncomputable section

/-! ## 1. From the base change to geometric integrality -/

/-- **Geometric integrality from the base changes.**  If every base change `ℙⁿ_K` of `ℙⁿ_𝕜` along a
field extension is integral, then `ℙⁿ_𝕜` is geometrically integral over `Spec 𝕜`. -/
theorem geometricallyIntegral_of_isIntegral_baseChange (𝕜 : Type) [Field 𝕜] (n : ℕ)
    (h : ∀ (K : Type) [Field K] [Algebra 𝕜 K],
      IsIntegral (projectiveSpaceBaseChange 𝕜 n K)) :
    GeometricallyIntegral (Work.PointlessIndexFive.projectiveSpaceToSpec 𝕜 n) := by
  rw [GeometricallyIntegral.eq_geometrically, geometrically_iff_of_commRing]
  intro K _ _ Y fst snd hpb
  haveI : IsIntegral (Limits.pullback (Work.PointlessIndexFive.projectiveSpaceToSpec 𝕜 n)
      (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 K)))) := h K
  exact IsIntegral.of_isIso (hpb.isoPullback.symm.hom)

/-! ## 2. `ProjectiveModelGap` and a curve model, from the chart isomorphisms -/

/-- Geometric integrality of `ℙⁿ_𝕜`, from the chart isomorphisms of the base change: the charts
`chartPullback 𝕜 n K i` are the affine spaces `𝔸ⁿ_K`, and they cover the base change with pairwise
non-empty intersections (`Work.TwistModel.isIntegral_projectiveSpaceBaseChange`). -/
theorem geometricallyIntegral_projectiveSpaceToSpec_of_chartIso (𝕜 : Type) [Field 𝕜] (n : ℕ)
    (hiso : ∀ (K : Type) [Field K] [Algebra 𝕜 K] (i : Fin (n + 1)),
      Nonempty (chartPullback 𝕜 n K i ≅
        Spec (CommRingCat.of (MvPolynomial (Fin n) K)))) :
    GeometricallyIntegral (Work.PointlessIndexFive.projectiveSpaceToSpec 𝕜 n) :=
  geometricallyIntegral_of_isIntegral_baseChange 𝕜 n fun K _ _ =>
    isIntegral_projectiveSpaceBaseChange 𝕜 n K (hiso K)

/-- **The projective model layer, complete**: `ℙⁿ_𝕜` is smooth, geometrically integral and
`n`-dimensional, i.e. `ProjectiveModelGap 𝕜 n` holds. -/
theorem projectiveModelGap_of_chartIso (𝕜 : Type) [Field 𝕜] (n : ℕ)
    (hiso : ∀ (K : Type) [Field K] [Algebra 𝕜 K] (i : Fin (n + 1)),
      Nonempty (chartPullback 𝕜 n K i ≅
        Spec (CommRingCat.of (MvPolynomial (Fin n) K)))) :
    Work.PointlessIndexFive.ProjectiveModelGap 𝕜 n :=
  ⟨Work.Twist.smooth_projectiveSpaceToSpec 𝕜 n,
    geometricallyIntegral_projectiveSpaceToSpec_of_chartIso 𝕜 n hiso,
    Work.Twist.topologicalKrullDim_projectiveSpace 𝕜 n⟩

/-- **A curve model over `𝕜`, from the chart isomorphisms**: `ℙ¹_𝕜` is a smooth proper
geometrically integral curve of dimension one.  Up to the chart computation this is the first
`CurveModel` in the project. -/
theorem curveModel_projectiveSpace_one_of_chartIso (𝕜 : Type) [Field 𝕜]
    (hiso : ∀ (K : Type) [Field K] [Algebra 𝕜 K] (i : Fin 2),
      Nonempty (chartPullback 𝕜 1 K i ≅
        Spec (CommRingCat.of (MvPolynomial (Fin 1) K)))) :
    Nonempty (CurveModel 𝕜) :=
  Work.Twist.curveModel_projectiveSpace_one 𝕜
    (Work.Twist.smooth_projectiveSpaceToSpec 𝕜 1)
    (geometricallyIntegral_projectiveSpaceToSpec_of_chartIso 𝕜 1 hiso)
    (Work.Twist.topologicalKrullDim_projectiveSpace 𝕜 1)

/-! ## 3. The unconditional results -/

/-- **`ℙⁿ_𝕜` is geometrically integral over `Spec 𝕜`.**  This is the single remaining conjunct of
`Work.PointlessIndexFive.ProjectiveModelGap` (see `Work.Twist.ProjModel.projectiveModelGap_iff`),
now proved: the base change of `ℙⁿ` along any field extension is covered by the affine charts
`𝔸ⁿ_K` (`chartPullbackIso`), whose pairwise intersections are non-empty because the projection
`ℙⁿ_K ⟶ ℙⁿ` is surjective. -/
theorem geometricallyIntegral_projectiveSpaceToSpec (𝕜 : Type) [Field 𝕜] (n : ℕ) :
    GeometricallyIntegral (Work.PointlessIndexFive.projectiveSpaceToSpec 𝕜 n) :=
  geometricallyIntegral_projectiveSpaceToSpec_of_chartIso 𝕜 n fun K _ _ i =>
    chartPullbackIso 𝕜 n K i

/-- **The projective model layer is complete**: `ℙⁿ_𝕜` is smooth, geometrically integral and
`n`-dimensional over `Spec 𝕜`, i.e. `ProjectiveModelGap 𝕜 n` holds (for every `n`). -/
theorem projectiveModelGap (𝕜 : Type) [Field 𝕜] (n : ℕ) :
    Work.PointlessIndexFive.ProjectiveModelGap 𝕜 n :=
  projectiveModelGap_of_chartIso 𝕜 n fun K _ _ i => chartPullbackIso 𝕜 n K i

/-- **`ℙⁿ_𝕜` is a variety over `𝕜`**, unconditionally. -/
noncomputable def variety_projectiveSpace (𝕜 : Type) [Field 𝕜] (n : ℕ) :
    MotivicInvariants.Variety 𝕜 (Work.PointlessIndexFive.projectiveSpace 𝕜 n) :=
  Work.Twist.variety_projectiveSpace_uncond 𝕜 n

/-- **`ℙ¹_𝕜` is a curve model over `𝕜`**: a smooth, proper, geometrically integral curve of
dimension one.  This is the first `CurveModel` of the project, and it makes the trivial-class case
of the twist residual realizable (`Work.TwistModel.nonempty_twistCurveModelClosed_of_hasPoint`). -/
theorem curveModel_projectiveSpace_one (𝕜 : Type) [Field 𝕜] : Nonempty (CurveModel 𝕜) :=
  curveModel_projectiveSpace_one_of_chartIso 𝕜 fun K _ _ i => chartPullbackIso 𝕜 1 K i

end

end Work.TwistModel
